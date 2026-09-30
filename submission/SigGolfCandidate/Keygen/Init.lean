import SigGolfCandidate.Keygen.State
import SigGolfCandidate.Submission

/-!
# The initial state of `keygen`: the secret key doublewords, zero elsewhere
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Mem

theorem getMem_setMem_ofNat (s : MachineState) (B A : Nat) (w : Word) (hB : B < 2 ^ 64)
    (hA : A < 2 ^ 64) :
    (s.setMem (BitVec.ofNat 64 B) w).getMem (BitVec.ofNat 64 A) =
      if A = B then w else s.getMem (BitVec.ofNat 64 A) := by
  simp only [MachineState.getMem, MachineState.setMem, beq_iff_eq, ofNat_inj hA hB]

theorem getMem_writeBytesAsWords (l : List (BitVec 8)) : ∀ (s : MachineState) (base A : Nat),
    base + 8 * ((l.length + 7) / 8) < 2 ^ 64 → A < 2 ^ 64 →
    (s.writeBytesAsWords (BitVec.ofNat 64 base) l).getMem (BitVec.ofNat 64 A) =
      if base ≤ A ∧ A < base + 8 * ((l.length + 7) / 8) ∧ (A - base) % 8 = 0 then
        bytesToWordLE ((l.drop (A - base)).take 8)
      else s.getMem (BitVec.ofNat 64 A) := by
  induction l using WellFounded.induction (r := fun x y : List (BitVec 8) => x.length < y.length) with
  | hwf => exact (measure List.length).wf
  | h l ih =>
    intro s base A hlen hA
    match l with
    | [] => simp only [MachineState.writeBytesAsWords_nil, List.length_nil]; rw [if_neg (by omega)]
    | b :: bs =>
      unfold MachineState.writeBytesAsWords
      simp only
      simp only [List.length_cons] at hlen
      rw [ofNat_add8, ih _ (by simp only [List.length_drop, List.length_cons]; omega) _ (base + 8) A
        (by simp only [List.length_drop, List.length_cons]; omega) hA,
        getMem_setMem_ofNat _ _ _ _ (by omega) hA]
      simp only [List.length_drop, List.length_cons]
      by_cases h1 : A = base
      · subst h1
        rw [if_neg (by omega), if_pos rfl, if_pos (by omega)]
        simp
      · by_cases h2 : base + 8 ≤ A ∧ A < base + 8 + 8 * ((bs.length + 1 - 8 + 7) / 8) ∧
            (A - (base + 8)) % 8 = 0
        · rw [if_pos h2, if_pos (by omega), List.drop_drop]
          congr 3; omega
        · rw [if_neg h2, if_neg h1, if_neg]
          omega

theorem extractByte_toNat' (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]

theorem word_ext_bytes {w₁ w₂ : Word} (h : ∀ j < 8, extractByte w₁ j = extractByte w₂ j) :
    w₁ = w₂ := by
  apply BitVec.eq_of_toNat_eq
  have e := fun j (hj : j < 8) => congrArg BitVec.toNat (h j hj)
  simp only [extractByte_toNat'] at e
  have h0 := e 0 (by decide); have h1 := e 1 (by decide); have h2 := e 2 (by decide)
  have h3 := e 3 (by decide); have h4 := e 4 (by decide); have h5 := e 5 (by decide)
  have h6 := e 6 (by decide); have h7 := e 7 (by decide)
  simp only [Nat.reducePow, Nat.reduceMul] at h0 h1 h2 h3 h4 h5 h6 h7
  have := w₁.isLt; have := w₂.isLt
  omega

theorem bytesToWordLE_eq (c : List Byte) : bytesToWordLE c = BitVec.ofNat 64 (leNat c) := by
  apply word_ext_bytes
  intro j hj
  rw [extractByte_bytesToWordLE _ _ hj]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat', BitVec.toNat_ofNat, ← leNat_div_mod]
  rw [show 256 ^ j = 2 ^ (8 * j) by rw [Nat.pow_mul]]
  interval_cases j <;> simp only [Nat.reducePow, Nat.reduceMul] <;> omega

end SigGolfCandidate.Keygen
