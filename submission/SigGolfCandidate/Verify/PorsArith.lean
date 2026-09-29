import SigGolfCandidate.Verify.PorsRuns
import SigGolfCandidate.Verify.LayArith

/-! # Digest-word arithmetic for the PORS phase: idx, the leaf indices, tweak words, counters -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem ext_toNat (a : BitVec 256) (i : Nat) :
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

/-- A 14-bit field inside one digest word. -/
theorem field_one (A w b : Nat) (hb : b + 14 ≤ 64) :
    A / 2 ^ (64 * w) % 2 ^ 64 / 2 ^ b % 2 ^ 14 = A / 2 ^ (64 * w + b) % 2 ^ 14 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  by_cases hj : j < 14
  · simp only [hj, decide_true, Bool.true_and, show j + b < 64 by omega]
    congr 1; omega
  · simp [hj]

/-- A 14-bit field across two digest words (`srl`, `sll`, `or`). -/
theorem field_two (A w b : Nat) (hb1 : 50 < b) (hb2 : b < 64) :
    (A / 2 ^ (64 * w) % 2 ^ 64 / 2 ^ b ||| A / 2 ^ (64 * (w + 1)) % 2 ^ 64 * 2 ^ (64 - b) % 2 ^ 64) %
      2 ^ 14 = A / 2 ^ (64 * w + b) % 2 ^ 14 := by
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_div_two_pow, Nat.testBit_mul_two_pow]
  by_cases hj : j < 14
  · simp only [hj, decide_true, Bool.true_and]
    by_cases h1 : j + b < 64
    · have h2 : ¬ (64 - b ≤ j) := by omega
      simp only [h1, h2, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_false,
        Bool.or_false]
      congr 1; omega
    · have h2 : 64 - b ≤ j := by omega
      simp only [h1, h2, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.false_or,
        show j < 64 by omega, show j - (64 - b) < 64 by omega]
      congr 1; omega
  · simp [hj]

theorem land16383 (n : Nat) : n &&& 16383 = n % 2 ^ 14 := Nat.and_two_pow_sub_one_eq_mod n 14

/-- The leaf index `v_r` computed by the setup (`pindE r`). -/
theorem pindE_eval (A : Nat) (s : MachineState)
    (hw : ∀ i, i < 4 → (wLdE i).eval s = BitVec.ofNat 64 (A / 2 ^ (64 * i) % 2 ^ 64)) (r : Nat)
    (hr : r < 15) : (pindE r).eval s = BitVec.ofNat 64 (A / 2 ^ (34 + 14 * r) % 2 ^ 14) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := Nat.mod_lt (A / 2 ^ (34 + 14 * r)) (show 2 ^ 14 > 0 by decide); omega)]
  unfold pindE
  dsimp only
  have hp : 34 + 14 * r = 64 * ((34 + 14 * r) / 64) + (34 + 14 * r) % 64 := by omega
  have hwl : (34 + 14 * r) / 64 < 4 := by omega
  by_cases h : (34 + 14 * r) % 64 + 14 ≤ 64
  · rw [if_pos h]
    show (((wLdE ((34 + 14 * r) / 64)).eval s >>> ((BitVec.ofNat 64 ((34 + 14 * r) % 64)).toNat % 64)) &&&
      BitVec.ofNat 64 16383).toNat = _
    rw [hw _ hwl]
    simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show (34 + 14 * r) % 64 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (34 + 14 * r) % 64 < 64 by omega), Nat.mod_mod,
      show 16383 % 2 ^ 64 = 16383 from rfl, land16383, field_one _ _ _ h, ← hp]
  · rw [if_neg h]
    have hwl1 : (34 + 14 * r) / 64 + 1 < 4 := by
      interval_cases r <;> simp_all
    show ((((wLdE ((34 + 14 * r) / 64)).eval s >>> ((BitVec.ofNat 64 ((34 + 14 * r) % 64)).toNat % 64)) |||
      ((wLdE ((34 + 14 * r) / 64 + 1)).eval s <<< ((BitVec.ofNat 64 (64 - (34 + 14 * r) % 64)).toNat % 64))) &&&
      BitVec.ofNat 64 16383).toNat = _
    rw [hw _ hwl, hw _ hwl1]
    simp only [BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
    rw [Nat.mod_eq_of_lt (show (34 + 14 * r) % 64 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show (34 + 14 * r) % 64 < 64 by omega),
      Nat.mod_eq_of_lt (show 64 - (34 + 14 * r) % 64 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 64 - (34 + 14 * r) % 64 < 64 by omega),
      show 16383 % 2 ^ 64 = 16383 from rfl, land16383]
    simp only [Nat.mod_mod]
    rw [field_two _ _ _ (by omega) (by omega), ← hp]

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
