import SigGolfCandidate.Verify.ForsRuns
import SigGolfCandidate.Verify.LayArith

/-! # Digest-word arithmetic: idx, u_k, admissibility, FORS tweak words, counters -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem land1023 (n : Nat) : n &&& 1023 = n % 1024 := Nat.and_two_pow_sub_one_eq_mod n 10
theorem land63 (n : Nat) : n &&& 63 = n % 64 := Nat.and_two_pow_sub_one_eq_mod n 6

theorem or16 (x y : Nat) (hx : x < 64) (hy : y < 16) :
    x * 16 % 18446744073709551616 ||| y = x * 16 + y := by
  rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm, show (16 : Nat) = 2 ^ 4 from rfl,
    ← Nat.two_pow_add_eq_or_of_lt hy]

theorem uExprW_eval (w : Nat → Rv.E) (A : Nat) (s : MachineState)
    (hw : ∀ i, i < 3 → (w i).eval s = BitVec.ofNat 64 (A / 2 ^ (64 * i) % 2 ^ 64)) (k : Nat) (hk : k < 14) :
    (uExprW w k).eval s = BitVec.ofNat 64 (A / 2 ^ (34 + 10 * k) % 1024) := by
  have h0 := hw 0 (by decide); have h1 := hw 1 (by decide); have h2 := hw 2 (by decide)
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one, Nat.mul_one] at h0 h1 h2
  apply BitVec.eq_of_toNat_eq
  interval_cases k <;> simp only [uExprW] <;> norm_num <;>
    simp only [Rv.E.eval, BinOp.eval, cw, h0, h1, h2, BitVec.toNat_and, BitVec.toNat_or,
      BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
      Nat.shiftLeft_eq] <;> norm_num <;> (try simp only [land1023, land63]) <;>
    first
    | omega
    | (rw [or16 _ _ (Nat.mod_lt _ (by decide)) (by omega)]; omega)

theorem ext_toNat (a : BitVec 256) (i : Nat) (hi : i < 4) :
    (a.extractLsb' (64 * i) 64).toNat = a.toNat / 2 ^ (64 * i) % 2 ^ 64 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem idxE_eval (A : Nat) (s : MachineState) (h0 : (wLdE 0).eval s = BitVec.ofNat 64 (A % 2 ^ 64)) :
    idxE.eval s = BitVec.ofNat 64 (A % 2 ^ 34) := by
  apply BitVec.eq_of_toNat_eq
  have e : idxE.eval s = ((wLdE 0).eval s <<< ((BitVec.ofNat 64 30).toNat % 64)) >>>
      ((BitVec.ofNat 64 30).toNat % 64) := rfl
  rw [e, h0]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  norm_num
  omega

theorem admE_eval (A : Nat) (s : MachineState)
    (h2 : (wLdE 2).eval s = BitVec.ofNat 64 (A / 2 ^ 128 % 2 ^ 64)) :
    admE.eval s = BitVec.ofNat 64 (A / 2 ^ 174 % 1024) := by
  apply BitVec.eq_of_toNat_eq
  have e : admE.eval s = ((wLdE 2).eval s <<< ((BitVec.ofNat 64 8).toNat % 64)) >>>
      ((BitVec.ofNat 64 54).toNat % 64) := rfl
  rw [e, h2]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  norm_num
  omega


theorem hiE_eval (A : Nat) (s : MachineState) (h0 : (wLdE 0).eval s = BitVec.ofNat 64 (A % 2 ^ 64)) :
    hiE.eval s = BitVec.ofNat 64 (2 ^ 24 * (A % 2 ^ 34 / 2 ^ 32)) := by
  apply BitVec.eq_of_toNat_eq
  have e : hiE.eval s = ((idxE.eval s >>> ((BitVec.ofNat 64 32).toNat % 64)) <<<
      ((BitVec.ofNat 64 24).toNat % 64)) := rfl
  rw [e, idxE_eval A s h0]
  have hX : A % 2 ^ 34 < 2 ^ 34 := Nat.mod_lt _ (by decide)
  generalize A % 2 ^ 34 = X at *
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  norm_num
  omega

theorem sll63_cmp (X : E) (U : Nat) (hU : U < 2 ^ 64) (s : MachineState) (hX : X.eval s = BitVec.ofNat 64 U) :
    CmpOp.lt.eval ((E.bin .sll X (cw 63)).eval s) ((E.c 0).eval s) = decide (U % 2 = 1) ∧
    CmpOp.ge.eval ((E.bin .sll X (cw 63)).eval s) ((E.c 0).eval s) = decide (U % 2 = 0) := by
  have h1 : CmpOp.lt.eval ((E.bin .sll X (cw 63)).eval s) ((E.c 0).eval s) = decide (U % 2 = 1) := by
    simp only [CmpOp.eval, E.eval, BinOp.eval, cw, hX]
    rw [show (0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt hU]
    norm_num
    omega
  refine ⟨h1, ?_⟩
  have : CmpOp.ge.eval ((E.bin .sll X (cw 63)).eval s) ((E.c 0).eval s) =
      !CmpOp.lt.eval ((E.bin .sll X (cw 63)).eval s) ((E.c 0).eval s) := rfl
  rw [this, h1]
  by_cases h : U % 2 = 1 <;> simp [h] <;> omega

/-! ## The counter check -/

theorem or_disj (lo hi : Nat) (hlo : lo < 2 ^ 32) :
    (lo + 2 ^ 32 * hi) ||| (2 ^ 32 * lo) = lo + 2 ^ 32 * (hi ||| lo) := by
  apply Nat.eq_of_testBit_eq
  intro j
  have a1 : (lo + 2 ^ 32 * hi).testBit j = if j < 32 then lo.testBit j else hi.testBit (j - 32) := by
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlo]
  have a2 : (2 ^ 32 * lo).testBit j = if j < 32 then false else lo.testBit (j - 32) := by
    have := Nat.testBit_two_pow_mul_add lo (show 0 < 2 ^ 32 by decide) j
    rw [Nat.add_zero] at this; rw [this]; simp
  have a3 : (lo + 2 ^ 32 * (hi ||| lo)).testBit j =
      if j < 32 then lo.testBit j else (hi ||| lo).testBit (j - 32) := by
    rw [Nat.add_comm, Nat.testBit_two_pow_mul_add _ hlo]
  rw [Nat.testBit_or, a1, a2, a3]
  split <;> simp [Nat.testBit_or]

theorem ctr_shift_iff (x : Nat) (hx : x < 2 ^ 64) :
    (x ||| (x * 2 ^ 32 % 2 ^ 64)) / 2 ^ 54 = 0 ↔ x % 2 ^ 32 < 2 ^ 22 ∧ x / 2 ^ 32 < 2 ^ 22 := by
  have hd := Nat.div_add_mod x (2 ^ 32)
  have hlo : x % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hhi : x / 2 ^ 32 < 2 ^ 32 := by omega
  have e1 : x * 2 ^ 32 % 2 ^ 64 = 2 ^ 32 * (x % 2 ^ 32) := by omega
  have e3 : x ||| 2 ^ 32 * (x % 2 ^ 32) = x % 2 ^ 32 + 2 ^ 32 * (x / 2 ^ 32 ||| x % 2 ^ 32) := by
    rw [← or_disj _ _ hlo]; congr 1; omega
  rw [e1, e3]
  generalize x % 2 ^ 32 = lo at *
  generalize x / 2 ^ 32 = hi at *
  have hor : hi ||| lo < 2 ^ 32 := Nat.or_lt_two_pow hhi hlo
  constructor
  · intro h
    have : hi ||| lo < 2 ^ 22 := by omega
    exact ⟨lt_of_le_of_lt Nat.right_le_or this, lt_of_le_of_lt Nat.left_le_or this⟩
  · rintro ⟨h1, h2⟩
    have := Nat.or_lt_two_pow h2 h1
    omega

end SigGolfCandidate.Verify
