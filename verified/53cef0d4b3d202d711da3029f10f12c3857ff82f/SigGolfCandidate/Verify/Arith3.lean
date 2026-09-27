import SigGolfCandidate.Verify.Arith2
import SigGolfCandidate.Verify.ForsRuns
import SigGolfCandidate.Verify.FoldSem

/-! # Digest-word arithmetic: idx, u_k, admissibility, FORS tweak words -/

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

theorem or2305 (x c : Nat) (hx : x < 256) (hc : c < 2 ^ 24) :
    x * 2 ^ 24 % 2 ^ 64 ||| c = c + 2 ^ 24 * x := by
  rw [Nat.mod_eq_of_lt (by omega), Nat.mul_comm, ← Nat.two_pow_add_eq_or_of_lt hc]; omega

theorem fw0E_eval (A : Nat) (s : MachineState) (h0 : (wLdE 0).eval s = BitVec.ofNat 64 (A % 2 ^ 64)) :
    fw0E.eval s = BitVec.ofNat 64 (2305 + 2 ^ 24 * (A % 2 ^ 34 / 2 ^ 32)) := by
  apply BitVec.eq_of_toNat_eq
  have e : fw0E.eval s = ((idxE.eval s >>> ((BitVec.ofNat 64 32).toNat % 64)) <<<
      ((BitVec.ofNat 64 24).toNat % 64)) ||| BitVec.ofNat 64 2305 := rfl
  rw [e, idxE_eval A s h0]
  have hX : A % 2 ^ 34 < 2 ^ 34 := Nat.mod_lt _ (by decide)
  generalize A % 2 ^ 34 = X at *
  simp only [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show (32 : Nat) % 2 ^ 64 % 64 = 32 from rfl, show (24 : Nat) % 2 ^ 64 % 64 = 24 from rfl,
    Nat.mod_eq_of_lt (show X < 2 ^ 64 by omega), show (2305 : Nat) % 2 ^ 64 = 2305 from rfl,
    or2305 _ _ (by omega) (by norm_num), Nat.mod_eq_of_lt (by omega)]

theorem rw0E_eval (idx : Nat) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 idx) :
    rw0E.eval s = BitVec.ofNat 64 (2817 + 2 ^ 24 * (idx / 2 ^ 32)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [rw0E, Rv.E.eval, BinOp.eval, cw, h22, BitVec.toNat_or, BitVec.toNat_ushiftRight,
    BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  rw [show (32 : Nat) % 2 ^ 64 % 64 = 32 from rfl, show (24 : Nat) % 2 ^ 64 % 64 = 24 from rfl,
    Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega), show (2817 : Nat) % 2 ^ 64 = 2817 from rfl,
    or2305 _ _ (by omega) (by norm_num), Nat.mod_eq_of_lt (by omega)]

theorem gpF_eval (u : Rv.E) (U : Nat) (hU : U < 1024) (s : MachineState)
    (hu : u.eval s = BitVec.ofNat 64 U) :
    (gpF u).eval s = BitVec.ofNat 64 (16 * (U % 2)) ∧
      (Rv.E.bin .sll u (cw 4)).eval s = BitVec.ofNat 64 (16 * U) := by
  constructor <;> apply BitVec.eq_of_toNat_eq
  · have e : (gpF u).eval s = (u.eval s <<< ((BitVec.ofNat 64 4).toNat % 64)) &&& BitVec.ofNat 64 16 := rfl
    rw [e, hu]
    simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [show (4 : Nat) % 2 ^ 64 % 64 = 4 from rfl, show (16 : Nat) % 2 ^ 64 = 16 from rfl,
      Nat.mod_eq_of_lt (show U < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show U * 2 ^ 4 < 2 ^ 64 by omega),
      land16]
    omega
  · have e : (Rv.E.bin .sll u (cw 4)).eval s = u.eval s <<< ((BitVec.ofNat 64 4).toNat % 64) := rfl
    rw [e, hu]
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
    rw [show (4 : Nat) % 2 ^ 64 % 64 = 4 from rfl, Nat.mod_eq_of_lt (show U < 2 ^ 64 by omega)]
    omega

end SigGolfCandidate.Verify
