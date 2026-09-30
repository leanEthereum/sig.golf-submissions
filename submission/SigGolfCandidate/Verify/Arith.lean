import SigGolfCandidate.Verify.Mem

/-! # Bit-level arithmetic facts about the machine values -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem replaceWord32_1_toNat (w : BitVec 64) (p : Nat) (hp : p < 2 ^ 32) :
    (replaceWord32 w 1 ((BitVec.ofNat 64 p).truncate 32)).toNat = w.toNat % 2 ^ 32 + 2 ^ 32 * p := by
  unfold replaceWord32
  have hm : (~~~(0xFFFFFFFF#64 <<< (1 * 32)) : BitVec 64) = BitVec.ofNat 64 (2 ^ 32 - 1) := by
    decide
  rw [hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have e1 : (2 ^ 32 - 1) % 2 ^ 64 = 2 ^ 32 - 1 := by norm_num
  have e2 : p % 2 ^ 64 % 2 ^ 32 = p := by omega
  have e3 : p % 2 ^ 64 * 2 ^ (1 * 32) % 2 ^ 64 = 2 ^ 32 * p := by
    rw [Nat.mod_eq_of_lt (by omega : p < 2 ^ 64)]; rw [Nat.mod_eq_of_lt (by norm_num; omega)]; ring
  rw [e1, e2, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq, e3]
  rw [Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt (Nat.mod_lt _ (by norm_num))]
  omega

/-- The merged tweak word of a chain step / node level. -/
theorem stMerge_eval (w : BitVec 64) (p lo : Nat) (hp : p < 2 ^ 32) (hw : w.toNat % 2 ^ 32 = lo) :
    StoreKind.merge .w w 4 (BitVec.ofNat 64 p) = BitVec.ofNat 64 (lo + 2 ^ 32 * p) := by
  apply BitVec.eq_of_toNat_eq
  simp only [StoreKind.merge]
  rw [show (4 : Nat) / 4 = 1 from rfl, replaceWord32_1_toNat w p hp, hw, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega)]

theorem stMerge_low (w : BitVec 64) (p : Nat) (hp : p < 2 ^ 32) :
    (StoreKind.merge .w w 4 (BitVec.ofNat 64 p)).toNat % 2 ^ 32 = w.toNat % 2 ^ 32 := by
  simp only [StoreKind.merge]
  rw [show (4 : Nat) / 4 = 1 from rfl, replaceWord32_1_toNat w p hp]
  omega

theorem geu_digit (D : BitVec 64) (r k : Nat) (hr : r ≤ 20) (hk : k < 8) :
    CmpOp.geu.eval (D <<< ((BitVec.ofNat 64 (61 - 3 * r)).toNat % 64)) (BitVec.ofNat 64 k <<< 61) =
      decide (k ≤ D.toNat / 8 ^ r % 8) := by
  simp only [CmpOp.eval, BitVec.ult, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have hD := D.isLt
  rw [Nat.mod_eq_of_lt (by omega : 61 - 3 * r < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 61 - 3 * r < 64),
    Nat.mod_eq_of_lt (by omega : k < 2 ^ 64)]
  have : k * 2 ^ 61 % 2 ^ 64 = k * 2 ^ 61 := Nat.mod_eq_of_lt (by omega)
  rw [this]
  interval_cases r <;> simp only [Bool.not_eq_eq_eq_not] <;>
    (simp only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul] at *; rw [Bool.eq_iff_iff]; simp; omega)

end SigGolfCandidate.Verify
