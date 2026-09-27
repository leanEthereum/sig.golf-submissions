import SigGolfCandidate.Keygen.Spec

/-!
# Invariants of `keygen` and their frame lemmas
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Tree array base (`addrTA`). -/
abbrev TA : Nat := 0x34100

/-- Doublewords kept at zero: the `P` parts of the PRF, chain, leaf and node buffers. -/
def zeroKeys : List Nat := [1712, 1720, 208, 216, 848, 856, 464, 472]

/-- Facts that hold from the end of the first block until the final block. -/
structure Base (W : List Word) (t : MachineState) : Prop where
  r5 : t.getReg .x5 = 0
  r8 : t.getReg .x8 = BitVec.ofNat 64 0
  r30 : t.getReg .x30 = BitVec.ofNat 64 0
  r9 : t.getReg .x9 = BitVec.ofNat 64 5
  r19 : t.getReg .x19 = BitVec.ofNat 64 TA
  sk : ∀ k < 4, t.getMem (BitVec.ofNat 64 (1728 + 8 * k)) = W.getD k 0
  zero : ∀ A ∈ zeroKeys, t.getMem (BitVec.ofNat 64 A) = 0
  w832 : t.getMem (BitVec.ofNat 64 832) = BitVec.ofNat 64 513
  cache : ∀ A, 0x44A0 ≤ A → A < 0x244A0 → t.getMem (BitVec.ofNat 64 A) = 0

/-- A doubleword key that does not touch `Base`. -/
def BaseSafe (k : Nat) : Prop :=
  k < 2 ^ 64 ∧ k ∉ [1728, 1736, 1744, 1752, 832] ∧ k ∉ zeroKeys ∧ (k < 0x44A0 ∨ 0x244A0 ≤ k)

theorem Base.frame {W : List Word} {s t : MachineState} {keys : List Nat} (h : Base W s)
    (hr : ∀ r, r = .x5 ∨ r = .x8 ∨ r = .x30 ∨ r = .x9 ∨ r = .x19 → t.getReg r = s.getReg r)
    (hf : Frame s t keys) (hk : ∀ k ∈ keys, BaseSafe k) : Base W t := by
  have fr : ∀ A < 2 ^ 64, (∀ k ∈ keys, A ≠ k) → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA hne => hf A hA (fun hm => hne A hm rfl)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr _ (by simp)]; exact h.r5
  · rw [hr _ (by simp)]; exact h.r8
  · rw [hr _ (by simp)]; exact h.r30
  · rw [hr _ (by simp)]; exact h.r9
  · rw [hr _ (by simp)]; exact h.r19
  · intro k hk4
    rw [fr _ (by omega) (fun k' hk' heq => by
      have := (hk k' hk').2.1; subst heq; interval_cases k <;> simp at this)]
    exact h.sk k hk4
  · intro A hA
    rw [fr _ (by simp [zeroKeys] at hA; omega) (fun k' hk' heq => (hk k' hk').2.2.1 (heq ▸ hA))]
    exact h.zero A hA
  · rw [fr _ (by omega) (fun k' hk' heq => (hk k' hk').2.1 (by simp [← heq]))]
    exact h.w832
  · intro A h1 h2
    rw [fr _ (by omega) (fun k' hk' heq => by have := (hk k' hk').2.2.2; omega)]
    exact h.cache A h1 h2

theorem Frame.trans {s t u : MachineState} {k₁ k₂ : List Nat} (h₁ : Frame s t k₁)
    (h₂ : Frame t u k₂) : Frame s u (k₁ ++ k₂) := by
  intro A hA hne
  rw [h₂ A hA (fun h => hne (List.mem_append_right _ h)), h₁ A hA (fun h => hne (List.mem_append_left _ h))]

theorem ValAt.frame {s t : MachineState} {keys : List Nat} {A : Nat} {v : Val} (h : ValAt s A v)
    (hf : Frame s t keys) (hA : A + 8 < 2 ^ 64) (hk : ∀ k ∈ keys, k + 8 ≤ A ∨ A + 16 ≤ k) :
    ValAt t A v := by
  constructor
  · rw [hf A (by omega) (fun hm => by have := hk A hm; omega)]; exact h.1
  · rw [hf (A + 8) (by omega) (fun hm => by have := hk (A + 8) hm; omega)]; exact h.2

theorem getMem_frame {s t : MachineState} {keys : List Nat} {A : Nat}
    (hf : Frame s t keys) (hA : A < 2 ^ 64) (hk : ∀ k ∈ keys, k ≠ A) :
    t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
  hf A hA (fun hm => hk A hm rfl)

theorem Frame.writeHash (t : MachineState) (a : BitVec 256) (B : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) (hB8 : B % 8 = 0) :
    Frame t (writeHash t a) [B, B + 8, B + 16, B + 24] := by
  intro A hA hne
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hne
  rw [getMem_writeHash t a B A h12 hB hA, if_neg hne.1, if_neg hne.2.1, if_neg hne.2.2.1,
    if_neg hne.2.2.2]

/-- Values stored at `A + 16 i`. -/
def Vals (t : MachineState) (A : Nat) (vs : List Val) : Prop :=
  (∀ v ∈ vs, v.length = 16) ∧ ∀ i < vs.length, ValAt t (A + 16 * i) (vs.getD i [])

theorem Vals.frame {s t : MachineState} {keys : List Nat} {A : Nat} {vs : List Val}
    (h : Vals s A vs) (hf : Frame s t keys) (hA : A + 16 * vs.length < 2 ^ 64)
    (hk : ∀ k ∈ keys, k + 8 ≤ A ∨ A + 16 * vs.length ≤ k) : Vals t A vs := by
  refine ⟨h.1, fun i hi => (h.2 i hi).frame hf (by omega) (fun k hk' => ?_)⟩
  have := hk k hk'
  omega

theorem Vals.snoc {t : MachineState} {A : Nat} {vs : List Val} {v : Val} (h : Vals t A vs)
    (hv : ValAt t (A + 16 * vs.length) v) (hl : v.length = 16) : Vals t A (vs ++ [v]) := by
  refine ⟨fun w hw => ?_, fun i hi => ?_⟩
  · rcases List.mem_append.mp hw with hw | hw
    · exact h.1 w hw
    · simp at hw; rw [hw]; exact hl
  · simp only [List.length_append, List.length_singleton] at hi
    by_cases hlt : i < vs.length
    · have := h.2 i hlt
      simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] using this
    · have : i = vs.length := by omega
      subst this
      simpa [List.getD_eq_getElem?_getD] using hv

end SigGolfCandidate.Keygen
