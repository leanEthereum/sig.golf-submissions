import SigGolfCandidate.Verify.Arith
import SigGolfCandidate.Verify.Swar
import SigGolfCandidate.Verify.LayerRuns
import SigGolfCandidate.Verify.Common

/-! # Bit-level facts for the layer blocks (sub-word stores, counter, route, encoding check) -/

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

theorem leNat_slice8 (l : List Byte) (off : Nat) (h : off + 4 ≤ l.length) :
    leNat (slice l off 8) = leNat (slice l off 4) + 2 ^ 32 * leNat (slice l (off + 4) 4) := by
  have : slice l off 8 = slice l off 4 ++ slice l (off + 4) 4 := by
    simp only [slice]
    rw [show (8 : Nat) = 4 + 4 from rfl, List.take_add, List.drop_drop, Nat.add_comm off 4]
  rw [this, leNat_append]
  have : (slice l off 4).length = 4 := by simp [slice]; omega
  rw [this]; norm_num

theorem ctrE_eval (lay : Nat) (_hlay : lay < 7) (wl : List Byte) (hwl : wl.length = 7756)
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

theorem lt_or_eval (a b : Word) :
    CmpOp.lt.eval (a ||| b) (0 : Word) = decide (2 ^ 63 ≤ a.toNat ∨ 2 ^ 63 ≤ b.toNat) := by
  simp only [CmpOp.eval]
  rw [show (0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_or, BitVec.msb_eq_decide,
    BitVec.msb_eq_decide]
  simp

/-! ## Route -/

def layS (lay : Nat) : Nat := [29, 24, 19, 14, 9, 4, 0].getD lay 0

theorem heightL_eq (lay : Nat) : heightL lay = height lay := rfl

theorem route_eq (idx lay : Nat) (hlay : lay < 7) :
    route idx lay = (idx / 2 ^ layS lay % 2 ^ heightL lay, idx / 2 ^ (layS lay + heightL lay)) := by
  unfold route
  interval_cases lay <;> rfl

theorem layS_succ (lay : Nat) (h : lay < 6) : layS lay = layS (lay + 1) + heightL (lay + 1) := by
  interval_cases lay <;> rfl

theorem heightL_lt6 (lay : Nat) (h : lay < 6) : heightL lay = 5 := by
  unfold heightL; rw [if_neg (by omega)]

theorem and_mask_eval (s : MachineState) (r : Reg) (x k : Nat) (hx : x < 2 ^ 64) (hk : k ≤ 64)
    (h : s.getReg r = BitVec.ofNat 64 x) :
    (E.bin .and (.reg r) (cw (2 ^ k - 1))).eval s = BitVec.ofNat 64 (x % 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [E.eval, BinOp.eval, cw, h, BitVec.toNat_and, BitVec.toNat_ofNat]
  have : 2 ^ k ≤ 2 ^ 64 := Nat.pow_le_pow_right (by decide) hk
  have : x % 2 ^ k < 2 ^ 64 := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) this
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show 2 ^ k - 1 < 2 ^ 64 by omega),
    Nat.and_two_pow_sub_one_eq_mod, Nat.mod_eq_of_lt this]

theorem srl_reg_eval (s : MachineState) (r : Reg) (x k : Nat) (hx : x < 2 ^ 64) (hk : k < 64)
    (h : s.getReg r = BitVec.ofNat 64 x) :
    (E.bin .srl (.reg r) (cw k)).eval s = BitVec.ofNat 64 (x / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [E.eval, BinOp.eval, cw, h, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have : x / 2 ^ k ≤ x := Nat.div_le_self _ _
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (show k < 2 ^ 64 by omega), Nat.mod_eq_of_lt hk,
    Nat.mod_eq_of_lt (show x / 2 ^ k < 2 ^ 64 by omega)]

/-- The value the route reads: `idx` (layer 6, in `x22`) or `tau_{lay+1}` (in `x30`). -/
def routeIn (idx lay : Nat) : Nat := if lay = 6 then idx else idx / 2 ^ layS lay

def routeReg (lay : Nat) : Reg := if lay = 6 then .x22 else .x30

theorem routeIn_lt (idx lay : Nat) (hidx : idx < 2 ^ 34) : routeIn idx lay < 2 ^ 34 := by
  unfold routeIn; split
  · exact hidx
  · exact lt_of_le_of_lt (Nat.div_le_self _ _) hidx

theorem uEr_eval (idx lay : Nat) (hlay : lay < 7) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h : s.getReg (routeReg lay) = BitVec.ofNat 64 (routeIn idx lay)) :
    (uEr lay).eval s = BitVec.ofNat 64 (idx / 2 ^ layS lay % 2 ^ heightL lay) := by
  have hr := routeIn_lt idx lay hidx
  unfold uEr
  by_cases h6 : lay = 6
  · subst h6
    simp only [routeReg, routeIn, if_true] at h
    rw [if_pos rfl, show (15 : Nat) = 2 ^ 4 - 1 from rfl, and_mask_eval s _ idx 4 (by omega) (by omega) h]
    simp [layS, heightL]
  · simp only [routeReg, routeIn, if_neg h6] at h
    rw [if_neg h6, show (31 : Nat) = 2 ^ 5 - 1 from rfl,
      and_mask_eval s _ _ 5 (by unfold routeIn at hr; rw [if_neg h6] at hr; omega) (by omega) h,
      heightL_lt6 lay (by omega)]

theorem tauEr_eval (idx lay : Nat) (hlay : lay < 7) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h : s.getReg (routeReg lay) = BitVec.ofNat 64 (routeIn idx lay)) :
    (tauEr lay).eval s = BitVec.ofNat 64 (idx / 2 ^ (layS lay + heightL lay)) := by
  have hr := routeIn_lt idx lay hidx
  unfold tauEr
  by_cases h6 : lay = 6
  · subst h6
    simp only [routeReg, routeIn, if_true] at h
    rw [if_pos rfl, srl_reg_eval s _ idx 4 (by omega) (by omega) h]
    simp [layS, heightL]
  · simp only [routeReg, routeIn, if_neg h6] at h
    rw [if_neg h6, srl_reg_eval s _ _ 5 (by unfold routeIn at hr; rw [if_neg h6] at hr; omega)
      (by omega) h, heightL_lt6 lay (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add]

theorem tau_lt (lay idx : Nat) (hlay : lay < 7) (hidx : idx < 2 ^ 34) :
    idx / 2 ^ (layS lay + heightL lay) < 2 ^ 30 := by
  have h4 : 4 ≤ layS lay + heightL lay := by interval_cases lay <;> decide
  apply Nat.div_lt_of_lt_mul
  calc idx < 2 ^ 34 := hidx
    _ = 2 ^ 4 * 2 ^ 30 := by norm_num
    _ ≤ 2 ^ (layS lay + heightL lay) * 2 ^ 30 :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) h4)

theorem e_lt32 (lay idx : Nat) : idx / 2 ^ layS lay % 2 ^ heightL lay < 32 := by
  have := Nat.mod_lt (idx / 2 ^ layS lay) (show 0 < 2 ^ heightL lay from Nat.two_pow_pos _)
  have : 2 ^ heightL lay ≤ 32 := by unfold heightL; split <;> decide
  omega

theorem x31Er_eval (idx lay : Nat) (hlay : lay < 7) (hidx : idx < 2 ^ 34) (s : MachineState)
    (h : s.getReg (routeReg lay) = BitVec.ofNat 64 (routeIn idx lay)) :
    (x31Er lay).eval s = BitVec.ofNat 64 (idx / 2 ^ (layS lay + heightL lay) +
      2 ^ 32 * (idx / 2 ^ layS lay % 2 ^ heightL lay)) := by
  have ht := tau_lt lay idx hlay hidx
  have he := e_lt32 lay idx
  have h1 : (x31Er lay).eval s = (tauEr lay).eval s + ((uEr lay).eval s <<< ((BitVec.ofNat 64 32).toNat % 64)) := rfl
  rw [h1, tauEr_eval idx lay hlay hidx s h, uEr_eval idx lay hlay hidx s h]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  generalize idx / 2 ^ (layS lay + heightL lay) = t at *
  generalize idx / 2 ^ layS lay % 2 ^ heightL lay = e at *
  norm_num
  omega

/-! ## The encoding check -/

def dA (s : MachineState) : Nat := (s.getMem (BitVec.ofNat 64 320)).toNat
def dB (s : MachineState) : Nat := (s.getMem (BitVec.ofNat 64 328)).toNat

section
variable (s : MachineState)

theorem swA3_toNat : (swA3.eval s).toNat = sw1 (dA s) (dB s) := by
  simp only [swA3, d0E, d1E, m1E, M1w, ldE, cw, Rv.E.eval, BinOp.eval, BitVec.toNat_add,
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

def swarOf (a b : Nat) : Nat := m6 (m3 ((sw1 a b + sw1 a b / 64) % 18446744073709551616)) % 4096

theorem swS_toNat : (swS.eval s).toNat = swarOf (dA s) (dB s) * 2 ^ 52 := by
  rw [show swS.eval s = (swA7.eval s + (swA7.eval s >>> ((BitVec.ofNat 64 48).toNat % 64))) <<<
      ((BitVec.ofNat 64 52).toNat % 64) from rfl]
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_add, BitVec.toNat_ushiftRight, swA7_toNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  simp only [swarOf, m6, m6']
  norm_num
  generalize (m5 (m4 (m3 ((sw1 (dA s) (dB s) + sw1 (dA s) (dB s) / 64) % 18446744073709551616)))) = X
  omega

theorem swS_eq (h0 : dA s < 2 ^ 63) (h1 : dB s < 2 ^ 63) :
    swS.eval s = KT ↔ (digitsOfWord (dA s) ++ digitsOfWord (dB s)).sum = targetSum := by
  have hs := swar_nat (dA s) (dB s) h0 h1
  have hl : swarOf (dA s) (dB s) < 4096 := Nat.mod_lt _ (by decide)
  rw [← hs]
  change _ ↔ swarOf (dA s) (dB s) = targetSum
  have hK : KT = BitVec.ofNat 64 (179 * 2 ^ 52) := rfl
  rw [hK, show targetSum = 179 from rfl]
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [swS_toNat, BitVec.toNat_ofNat] at this
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    rw [swS_toNat, h]; rfl
end

end SigGolfCandidate.Verify
