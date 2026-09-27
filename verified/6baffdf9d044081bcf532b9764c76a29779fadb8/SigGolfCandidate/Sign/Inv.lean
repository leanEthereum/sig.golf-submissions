import SigGolfCandidate.Sign.Base

/-!
# Frames: memory and registers that a segment leaves unchanged

* `Frame s t W` : every numeric address outside the write set `W` has the same dword in `t` as
  in `s` (`Frame.refl/.trans/.mono`, `Frame.readWords`, `frame_writeHash`, `frame_toState`).
* `RegsEq s t l` : registers outside `l` are unchanged.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def Frame (s t : MachineState) (W : Nat → Prop) : Prop :=
  ∀ a, a < 2 ^ 64 → ¬ W a → t.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)

theorem Frame.refl (s : MachineState) (W : Nat → Prop) : Frame s s W := fun _ _ _ => rfl

theorem Frame.trans {s t u : MachineState} {W₁ W₂ : Nat → Prop} (h₁ : Frame s t W₁)
    (h₂ : Frame t u W₂) : Frame s u (fun a => W₁ a ∨ W₂ a) := by
  intro a ha hW
  rw [h₂ a ha (fun h => hW (Or.inr h)), h₁ a ha (fun h => hW (Or.inl h))]

theorem Frame.mono {s t : MachineState} {W W' : Nat → Prop} (h : Frame s t W)
    (hW : ∀ a, W a → W' a) : Frame s t W' :=
  fun a ha hna => h a ha (fun h' => hna (hW a h'))

theorem Frame.trans' {s t u : MachineState} {W₁ W₂ W : Nat → Prop} (h₁ : Frame s t W₁)
    (h₂ : Frame t u W₂) (hW : ∀ a, W₁ a ∨ W₂ a → W a) : Frame s u W :=
  (h₁.trans h₂).mono hW

theorem Frame.getMem {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) {a : Nat}
    (ha : a < 2 ^ 64) (hW : ¬ W a) : t.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a) :=
  h a ha hW

theorem Frame.readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (a n : Nat)
    (ha : a + 8 * n < 2 ^ 64) (hW : ∀ i < n, ¬ W (a + 8 * i)) :
    t.readWords (BitVec.ofNat 64 a) n = s.readWords (BitVec.ofNat 64 a) n :=
  readWords_congr s t a n (fun i hi => h _ (by omega) (hW i hi))

theorem frame_writeHash (s : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    Frame s (writeHash s ans) (fun a => d ≤ a ∧ a < d + 32) := by
  intro a ha hW
  exact writeHash_getMem_frame s ans d a hd hd' ha (by omega)

/-- Frame of a block result from a proof that no written key equals an address outside `W`. -/
theorem frame_toState (r : Result) (s : MachineState) (W : Nat → Prop)
    (h : ∀ a, a < 2 ^ 64 → ¬ W a → ∀ p ∈ r.st.mem, BitVec.ofNat 64 a ≠ p.1.eval s) :
    Frame s (r.toState s) W := by
  intro a ha hW
  rw [Result.toState_getMem]
  exact memEval_frame s r.st.mem _ (h a ha hW)

def RegsEq (s t : MachineState) (l : List Reg) : Prop := ∀ r, r ∉ l → t.getReg r = s.getReg r

theorem RegsEq.refl (s : MachineState) (l : List Reg) : RegsEq s s l := fun _ _ => rfl

theorem RegsEq.trans {s t u : MachineState} {l₁ l₂ : List Reg} (h₁ : RegsEq s t l₁)
    (h₂ : RegsEq t u l₂) : RegsEq s u (l₁ ++ l₂) := by
  intro r hr
  rw [h₂ r (fun h => hr (List.mem_append_right _ h)), h₁ r (fun h => hr (List.mem_append_left _ h))]

theorem RegsEq.mono {s t : MachineState} {l l' : List Reg} (h : RegsEq s t l) (hl : ∀ r ∈ l, r ∈ l') :
    RegsEq s t l' := fun r hr => h r (fun h' => hr (hl r h'))

theorem RegsEq.trans' {s t u : MachineState} {l₁ l₂ l : List Reg} (h₁ : RegsEq s t l₁)
    (h₂ : RegsEq t u l₂) (hl : ∀ r, r ∈ l₁ ∨ r ∈ l₂ → r ∈ l) : RegsEq s u l :=
  (h₁.trans h₂).mono (fun r hr => hl r (List.mem_append.mp hr))

theorem RegsEq.get {s t : MachineState} {l : List Reg} (h : RegsEq s t l) (r : Reg)
    (hr : r ∉ l := by decide) : t.getReg r = s.getReg r := h r hr

theorem regsEq_writeHash (s : MachineState) (ans : BitVec 256) (l : List Reg) :
    RegsEq s (writeHash s ans) l := fun r _ => writeHash_getReg s ans r

/-- Registers of a block result: all registers whose symbolic value is `.reg r` are unchanged. -/
theorem regsEq_toState (r : Result) (s : MachineState) (l : List Reg)
    (h : ∀ x : Reg, x ∉ l → (r.st.regs.get x).eval s = s.getReg x) : RegsEq s (r.toState s) l := by
  intro x hx
  rw [Result.toState_getReg]
  exact h x hx

theorem getReg_x0 (s : MachineState) : s.getReg .x0 = 0 := rfl

/-! ## Arrays of 16-byte values -/

/-- `vs[i]` is stored at `B + 16 i`. -/
def Slots (t : MachineState) (B : Nat) (vs : List Val) : Prop :=
  ∀ i (hi : i < vs.length), t.readWords (BitVec.ofNat 64 (B + 16 * i)) 2 = wordsOf vs[i]

theorem Slots.nil (t : MachineState) (B : Nat) : Slots t B [] := fun i hi => by simp at hi

theorem Slots.snoc {t : MachineState} {B : Nat} {vs : List Val} {v : Val} (h : Slots t B vs)
    (hv : t.readWords (BitVec.ofNat 64 (B + 16 * vs.length)) 2 = wordsOf v) : Slots t B (vs ++ [v]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases h' : i < vs.length
  · rw [List.getElem_append_left h']; exact h i h'
  · have : i = vs.length := by omega
    subst this
    rw [List.getElem_append_right (le_refl _)]; simpa using hv

theorem Slots.frame {s t : MachineState} {W : Nat → Prop} {B : Nat} {vs : List Val}
    (h : Slots s B vs) (hf : Frame s t W) (hB : B + 16 * vs.length + 16 < 2 ^ 64)
    (hW : ∀ i < vs.length, ¬ W (B + 16 * i) ∧ ¬ W (B + 16 * i + 8)) : Slots t B vs := by
  intro i hi
  rw [hf.readWords _ _ (by omega) (by
    intro j hj
    have := hW i hi
    interval_cases j
    · simpa using this.1
    · simpa using this.2)]
  exact h i hi

theorem Slots.getD {t : MachineState} {B : Nat} {vs : List Val} (h : Slots t B vs) (i : Nat)
    (hi : i < vs.length) :
    t.readWords (BitVec.ofNat 64 (B + 16 * i)) 2 = wordsOf (vs.getD i []) := by
  rw [h i hi]; simp [List.getD, List.getElem?_eq_getElem hi]

theorem Slots.append {t : MachineState} {B : Nat} {l1 l2 : List Val} (h1 : Slots t B l1)
    (h2 : Slots t (B + 16 * l1.length) l2) : Slots t B (l1 ++ l2) := by
  intro i hi
  by_cases h : i < l1.length
  · rw [List.getElem_append_left h]; exact h1 i h
  · rw [List.getElem_append_right (by omega)]
    have := h2 (i - l1.length) (by simp at hi; omega)
    rw [show B + 16 * l1.length + 16 * (i - l1.length) = B + 16 * i by omega] at this
    exact this

theorem Slots.cons {t : MachineState} {B : Nat} {v : Val} {vs : List Val}
    (h1 : t.readWords (BitVec.ofNat 64 B) 2 = wordsOf v) (h2 : Slots t (B + 16) vs) :
    Slots t B (v :: vs) := by
  intro i hi
  cases i with
  | zero => simpa using h1
  | succ i =>
    have := h2 i (by simpa using hi)
    rw [show B + 16 * (i + 1) = B + 16 + 16 * i by ring]; simpa using this

end SigGolfCandidate.Sign
