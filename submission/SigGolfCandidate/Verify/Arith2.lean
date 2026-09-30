import SigGolfCandidate.Verify.Arith
import SigGolfCandidate.Verify.Swar
import SigGolfCandidate.Verify.LayerRuns
import SigGolfCandidate.Verify.ChainSem

/-! # More bit-level facts (sub-word stores, loads, route, encoding check) -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem replaceWord32_0_toNat (w : BitVec 64) (v : BitVec 32) :
    (replaceWord32 w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat := by
  unfold replaceWord32
  have hm : (~~~(0xFFFFFFFF#64 <<< (0 * 32)) : BitVec 64) =
      BitVec.ofNat 64 (2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1)) := by decide
  rw [hm, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, Nat.zero_mul,
    Nat.shiftLeft_zero]
  have hv := v.isLt
  have hw := w.isLt
  rw [Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show v.toNat < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 2 ^ 32 * (2 ^ 32 - 1) + (2 ^ 0 - 1) < 2 ^ 64 by norm_num),
    land_split _ _ 0 32 (by decide), Nat.and_two_pow_sub_one_eq_mod, Nat.pow_zero, Nat.mod_one, Nat.add_zero,
    ← Nat.two_pow_add_eq_or_of_lt hv]
  ring

theorem merge_w0_toNat (w v : BitVec 64) :
    (StoreKind.merge .w w 0 v).toNat = w.toNat / 2 ^ 32 % 2 ^ 32 * 2 ^ 32 + v.toNat % 2 ^ 32 := by
  simp only [StoreKind.merge, show (0 : Nat) / 4 = 0 from rfl]
  rw [replaceWord32_0_toNat]
  simp [BitVec.toNat_setWidth]

theorem merge_w4_toNat (w v : BitVec 64) :
    (StoreKind.merge .w w 4 v).toNat = w.toNat % 2 ^ 32 + 2 ^ 32 * (v.toNat % 2 ^ 32) := by
  have := replaceWord32_1_toNat w (v.toNat % 2 ^ 32) (Nat.mod_lt _ (by decide))
  simp only [StoreKind.merge, show (4 : Nat) / 4 = 1 from rfl]
  have e : (BitVec.ofNat 64 (v.toNat % 2 ^ 32)).truncate 32 = v.truncate 32 := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_setWidth]
  rw [← e, this]

/-! ## Route -/

theorem layH_le (lay : Nat) : layH lay ≤ 5 := by unfold layH; split <;> omega
theorem layS_le (lay : Nat) (h : lay < 7) : layS lay ≤ 29 := by
  interval_cases lay <;> decide
theorem layS_layH (lay : Nat) (h : lay < 7) : 4 ≤ layS lay + layH lay := by
  interval_cases lay <;> decide

theorem uE_eval (lay idx : Nat) (hlay : lay < 7) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 idx) :
    (uE lay).eval s = BitVec.ofNat 64 (idx / 2 ^ layS lay % 2 ^ layH lay) := by
  have hH := layH_le lay
  have hS := layS_le lay hlay
  apply BitVec.eq_of_toNat_eq
  unfold uE
  split
  · rename_i h6; subst h6
    simp only [Rv.E.eval, BinOp.eval, cw, h22, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega), show (15 : Nat) % 2 ^ 64 = 2 ^ 4 - 1 by rfl,
      Nat.and_two_pow_sub_one_eq_mod]
    simp [layS, layH]; omega
  · simp only [Rv.E.eval, BinOp.eval, cw, h22, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have : 2 ^ layH lay ≤ 32 := by
      calc 2 ^ layH lay ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hH
        _ = 32 := rfl
    have hp : 1 ≤ 2 ^ layH lay := Nat.one_le_two_pow
    have hd : idx / 2 ^ layS lay ≤ idx := Nat.div_le_self _ _
    rw [Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show layS lay < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show layS lay < 64 by omega),
      Nat.mod_eq_of_lt (show 2 ^ layH lay - 1 < 2 ^ 64 by omega), Nat.and_two_pow_sub_one_eq_mod,
      Nat.mod_eq_of_lt (show idx / 2 ^ layS lay % 2 ^ layH lay < 2 ^ 64 by
        have := Nat.mod_lt (idx / 2 ^ layS lay) (show 0 < 2 ^ layH lay by omega); omega)]

theorem tauE_eval (lay idx : Nat) (hlay : lay < 7) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 idx) :
    (tauE lay).eval s = BitVec.ofNat 64 (idx / 2 ^ (layS lay + layH lay)) := by
  have hS := layS_le lay hlay
  have hH := layH_le lay
  apply BitVec.eq_of_toNat_eq
  simp only [tauE, Rv.E.eval, BinOp.eval, cw, h22, BitVec.toNat_ofNat, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have hd : idx / 2 ^ (layS lay + layH lay) ≤ idx := Nat.div_le_self _ _
  rw [Nat.mod_eq_of_lt (show idx < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show layS lay + layH lay < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show layS lay + layH lay < 64 by omega),
    Nat.mod_eq_of_lt (show idx / 2 ^ (layS lay + layH lay) < 2 ^ 64 by omega)]

theorem tau_lt (lay idx : Nat) (hlay : lay < 7) (hidx : idx < 2 ^ 34) :
    idx / 2 ^ (layS lay + layH lay) < 2 ^ 30 := by
  have h4 := layS_layH lay hlay
  apply Nat.div_lt_of_lt_mul
  calc idx < 2 ^ 34 := hidx
    _ = 2 ^ 4 * 2 ^ 30 := by norm_num
    _ ≤ 2 ^ (layS lay + layH lay) * 2 ^ 30 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h4)

theorem x31E_eval (lay idx : Nat) (hlay : lay < 7) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h22 : s.getReg .x22 = BitVec.ofNat 64 idx) :
    (x31E lay).eval s = BitVec.ofNat 64 (idx / 2 ^ (layS lay + layH lay) +
      2 ^ 32 * (idx / 2 ^ layS lay % 2 ^ layH lay)) := by
  have ht := tau_lt lay idx hlay hidx
  have hH := layH_le lay
  have he : idx / 2 ^ layS lay % 2 ^ layH lay < 32 := by
    have := Nat.mod_lt (idx / 2 ^ layS lay) (show 0 < 2 ^ layH lay from Nat.two_pow_pos _)
    have : 2 ^ layH lay ≤ 32 := by
      calc 2 ^ layH lay ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) hH
        _ = 32 := rfl
    omega
  have h1 : (x31E lay).eval s = (tauE lay).eval s ||| ((uE lay).eval s <<< ((BitVec.ofNat 64 32).toNat % 64)) := rfl
  rw [h1, tauE_eval lay idx hlay hidx s h22, uE_eval lay idx hlay hidx s h22]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  generalize idx / 2 ^ (layS lay + layH lay) = t at *
  generalize idx / 2 ^ layS lay % 2 ^ layH lay = e at *
  rw [Nat.mod_eq_of_lt (show t < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show e < 2 ^ 64 by omega),
    show (32 : Nat) % 2 ^ 64 % 64 = 32 by rfl, Nat.mod_eq_of_lt (show e * 2 ^ 32 < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show t + 2 ^ 32 * e < 2 ^ 64 by omega), Nat.or_comm, Nat.mul_comm,
    ← Nat.two_pow_add_eq_or_of_lt (show t < 2 ^ 32 by omega)]
  omega

theorem route_eq (idx lay : Nat) (hlay : lay < 7) :
    route idx lay = (idx / 2 ^ layS lay % 2 ^ layH lay, idx / 2 ^ (layS lay + layH lay)) := by
  unfold route
  interval_cases lay <;> rfl

/-! ## The counter -/

theorem leNat_slice8 (l : List Byte) (off : Nat) (h : off + 4 ≤ l.length) :
    leNat (slice l off 8) = leNat (slice l off 4) + 2 ^ 32 * leNat (slice l (off + 4) 4) := by
  have : slice l off 8 = slice l off 4 ++ slice l (off + 4) 4 := by
    simp only [slice]
    rw [show (8 : Nat) = 4 + 4 from rfl, List.take_add, List.drop_drop, Nat.add_comm off 4]
  rw [this, leNat_append]
  have : (slice l off 4).length = 4 := by simp [slice]; omega
  rw [this]; norm_num

theorem ctrE_eval (lay : Nat) (hlay : lay < 7) (wl : List Byte) (hwl : wl.length = 7756)
    (s : MachineState) (hW : WitOK wl s) :
    ((ctrE lay).eval s).toNat = witCounter wl lay := by
  have hw := wit_word hW (7728 + 8 * (lay / 2)) (by omega) (show 7728 + 8 * (lay / 2) < 7760 by omega)
  simp only [ctrE, ldE, Rv.E.eval, UnOp.eval, LoadKind.fromWord, cw]
  rw [show 0x2630 + 8 * (lay / 2) = 0x800 + (7728 + 8 * (lay / 2)) by omega, hw]
  simp only [extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [w64_toNat _ (by simp [slice]), leNat_slice8 _ _ (by omega), witCounter]
  have hA := leNat_lt (slice wl (7728 + 8 * (lay / 2)) 4)
  have hB := leNat_lt (slice wl (7728 + 8 * (lay / 2) + 4) 4)
  have l4 : ∀ o, (slice wl o 4).length ≤ 4 := fun o => by simp [slice]
  have hA' : leNat (slice wl (7728 + 8 * (lay / 2)) 4) < 2 ^ 32 :=
    lt_of_lt_of_le hA (le_trans (Nat.pow_le_pow_right (by decide) (l4 _)) (by norm_num))
  have hB' : leNat (slice wl (7728 + 8 * (lay / 2) + 4) 4) < 2 ^ 32 :=
    lt_of_lt_of_le hB (le_trans (Nat.pow_le_pow_right (by decide) (l4 _)) (by norm_num))
  rcases Nat.mod_two_eq_zero_or_one lay with h | h
  · rw [show 4 * (lay % 2) / 4 * 32 = 0 by rw [h], show witCounters + 4 * lay = 7728 + 8 * (lay / 2) by
      unfold witCounters; omega]
    generalize leNat (slice wl (7728 + 8 * (lay / 2)) 4) = A at *
    generalize leNat (slice wl (7728 + 8 * (lay / 2) + 4) 4) = B at *
    norm_num at hA' hB' ⊢
    omega
  · rw [show 4 * (lay % 2) / 4 * 32 = 32 by rw [h], show witCounters + 4 * lay = 7728 + 8 * (lay / 2) + 4 by
      unfold witCounters; omega]
    generalize leNat (slice wl (7728 + 8 * (lay / 2)) 4) = A at *
    generalize leNat (slice wl (7728 + 8 * (lay / 2) + 4) 4) = B at *
    norm_num at hA' hB' ⊢
    omega

theorem witCounter_lt (wl : List Byte) (lay : Nat) : witCounter wl lay < 2 ^ 32 := by
  unfold witCounter
  have := leNat_lt (slice wl (witCounters + 4 * lay) 4)
  have l4 : (slice wl (witCounters + 4 * lay) 4).length ≤ 4 := by simp [slice]
  exact lt_of_lt_of_le this (le_trans (Nat.pow_le_pow_right (by decide) l4) (by norm_num))

/-! ## The encoding check -/

theorem lt_or_eval (a b : Word) :
    CmpOp.lt.eval (a ||| b) (0 : Word) = decide (2 ^ 63 ≤ a.toNat ∨ 2 ^ 63 ≤ b.toNat) := by
  simp only [CmpOp.eval]
  rw [show (0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_or, BitVec.msb_eq_decide,
    BitVec.msb_eq_decide]
  simp

def swarOf (a b : Nat) : Nat := m6 (m3 ((sw1 a b + sw1 a b / 64) % 18446744073709551616)) % 2048

def swA3 : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl d0E (cw 3)) m1E) (.bin .and d0E m1E))
    (.bin .and (.bin .srl d1E (cw 3)) m1E)) (.bin .and d1E m1E)
def swA4 : E := .bin .add swA3 (.bin .srl swA3 (cw 6))
def swA5 : E := .bin .and swA4 m2E
def swA6 : E := .bin .add swA5 (.bin .srl swA5 (cw 12))
def swA7 : E := .bin .add swA6 (.bin .srl swA6 (cw 24))

theorem swX25_eq : swX25 = .bin .add (.bin .and (.bin .add swA7 (.bin .srl swA7 (cw 48))) (cw 2047))
    (cw (2 ^ 64 - 170)) := rfl

def dA (s : MachineState) : Nat := (s.getMem (BitVec.ofNat 64 0x140)).toNat
def dB (s : MachineState) : Nat := (s.getMem (BitVec.ofNat 64 0x148)).toNat

section
variable (s : MachineState)

theorem swA3_toNat : (swA3.eval s).toNat = sw1 (dA s) (dB s) := by
  simp only [swA3, d0E, d1E, m1E, ldE, cw, Rv.E.eval, BinOp.eval, BitVec.toNat_add,
    BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, sw1, dA, dB]
  try norm_num

theorem swA4_toNat : (swA4.eval s).toNat = (sw1 (dA s) (dB s) + sw1 (dA s) (dB s) / 64) % 18446744073709551616 := by
  rw [show swA4.eval s = swA3.eval s + (swA3.eval s >>> ((BitVec.ofNat 64 6).toNat % 64)) from rfl,
    BitVec.toNat_add, BitVec.toNat_ushiftRight, swA3_toNat, Nat.shiftRight_eq_div_pow]
  norm_num

theorem swA5_toNat : (swA5.eval s).toNat = m3 ((sw1 (dA s) (dB s) + sw1 (dA s) (dB s) / 64) % 18446744073709551616) := by
  rw [show swA5.eval s = swA4.eval s &&& 0xf03f03f03f03f03f#64 from rfl, BitVec.toNat_and,
    swA4_toNat]
  rfl

theorem swA6_toNat : (swA6.eval s).toNat = m4 (m3 ((sw1 (dA s) (dB s) + sw1 (dA s) (dB s) / 64) % 18446744073709551616)) := by
  rw [show swA6.eval s = swA5.eval s + (swA5.eval s >>> ((BitVec.ofNat 64 12).toNat % 64)) from rfl,
    BitVec.toNat_add, BitVec.toNat_ushiftRight, swA5_toNat, Nat.shiftRight_eq_div_pow]
  simp only [m4]; norm_num

theorem swA7_toNat : (swA7.eval s).toNat = m5 (m4 (m3 ((sw1 (dA s) (dB s) + sw1 (dA s) (dB s) / 64) % 18446744073709551616))) := by
  rw [show swA7.eval s = swA6.eval s + (swA6.eval s >>> ((BitVec.ofNat 64 24).toNat % 64)) from rfl,
    BitVec.toNat_add, BitVec.toNat_ushiftRight, swA6_toNat, Nat.shiftRight_eq_div_pow]
  simp only [m5]; norm_num

theorem swX25_toNat : (swX25.eval s).toNat = (swarOf (dA s) (dB s) + (2 ^ 64 - 170)) % 2 ^ 64 := by
  rw [swX25_eq]
  rw [show (Rv.E.bin .add (.bin .and (.bin .add swA7 (.bin .srl swA7 (cw 48))) (cw 2047))
      (cw (2 ^ 64 - 170))).eval s = ((swA7.eval s + (swA7.eval s >>> ((BitVec.ofNat 64 48).toNat % 64)))
        &&& BitVec.ofNat 64 2047) + BitVec.ofNat 64 (2 ^ 64 - 170) from rfl]
  rw [BitVec.toNat_add, BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ushiftRight, swA7_toNat,
    Nat.shiftRight_eq_div_pow]
  simp only [swarOf, m6, m6', BitVec.toNat_ofNat]
  rw [show (2047 : Nat) % 2 ^ 64 = 2 ^ 11 - 1 by rfl, Nat.and_two_pow_sub_one_eq_mod]
  norm_num

theorem swX25_eq_zero : swX25.eval s = 0 ↔ swarOf (dA s) (dB s) = 170 := by
  have h1 : swarOf (dA s) (dB s) < 2048 := Nat.mod_lt _ (by decide)
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [swX25_toNat] at this
    simp at this; omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [swX25_toNat, h]; rfl
end

end SigGolfCandidate.Verify
