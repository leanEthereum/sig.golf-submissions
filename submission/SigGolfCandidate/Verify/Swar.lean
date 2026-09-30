import SigGolfCandidate.Ref
import Mathlib.Data.Nat.Bitwise

/-! # The SWAR digit sum of the encoding check (Nat level) -/

set_option linter.unusedSimpArgs false
namespace SigGolfCandidate.Verify
open SigGolfCandidate.Ref

theorem land_split (n M w s : Nat) (hws : w ≤ s) :
    n &&& (2 ^ s * M + (2 ^ w - 1)) = 2 ^ s * ((n / 2 ^ s) &&& M) + n % 2 ^ w := by
  have hw : 2 ^ w - 1 < 2 ^ s := by
    have := Nat.pow_le_pow_right (show 0 < 2 by decide) hws
    have : 0 < 2 ^ w := Nat.two_pow_pos _
    omega
  have hm : n % 2 ^ w < 2 ^ s := lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.pow_le_pow_right (by decide) hws)
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_land, Nat.testBit_two_pow_mul_add _ hw, Nat.testBit_two_pow_mul_add _ hm]
  split
  · rw [Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    cases n.testBit j <;> simp
  · rw [Nat.testBit_land, Nat.testBit_div_two_pow, Nat.sub_add_cancel (by omega)]

theorem split3 (n M : Nat) : n &&& (64 * M + 7) = 64 * ((n / 64) &&& M) + n % 8 :=
  land_split n M 3 6 (by decide)
theorem split6 (n M : Nat) : n &&& (4096 * M + 63) = 4096 * ((n / 4096) &&& M) + n % 64 :=
  land_split n M 6 12 (by decide)
theorem and7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3
theorem and15 (n : Nat) : n &&& 15 = n % 16 := Nat.and_two_pow_sub_one_eq_mod n 4

theorem landM1 (n : Nat) : n &&& 8198552921648689607 =
    64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 / 64 / 64 % 8)
    + n / 64 / 64 / 64 / 64 % 8) + n / 64 / 64 / 64 % 8) + n / 64 / 64 % 8) + n / 64 % 8) + n % 8 := by
  rw [show (8198552921648689607 : Nat) = 64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * (64 * 7 + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7) + 7 by norm_num]
  simp only [split3, and7]

theorem landM2 (n : Nat) : n &&& 17311559823019733055 =
    4096 * (4096 * (4096 * (4096 * (4096 * (n / 4096 / 4096 / 4096 / 4096 / 4096 % 16)
    + n / 4096 / 4096 / 4096 / 4096 % 64) + n / 4096 / 4096 / 4096 % 64) + n / 4096 / 4096 % 64)
    + n / 4096 % 64) + n % 64 := by
  rw [show (17311559823019733055 : Nat) = 4096 * (4096 * (4096 * (4096 * (4096 * 15 + 63) + 63) + 63) + 63) + 63 by norm_num]
  simp only [split6, and15]

theorem digits_sum (a : Nat) : (digitsOfWord a).sum =
    a % 8 + a / 8 % 8 + a / 64 % 8 + a / 512 % 8 + a / 4096 % 8 + a / 32768 % 8 + a / 262144 % 8 +
    a / 2097152 % 8 + a / 16777216 % 8 + a / 134217728 % 8 + a / 1073741824 % 8 +
    a / 8589934592 % 8 + a / 68719476736 % 8 + a / 549755813888 % 8 + a / 4398046511104 % 8 +
    a / 35184372088832 % 8 + a / 281474976710656 % 8 + a / 2251799813685248 % 8 +
    a / 18014398509481984 % 8 + a / 144115188075855872 % 8 + a / 1152921504606846976 % 8 := by
  simp only [digitsOfWord, List.range, List.range.loop, List.map, List.sum_cons, List.sum_nil]
  norm_num
  omega

theorem hdiv64 (c R : Nat) (h : c < 64) : (c + 64 * R) / 64 = R := by omega
theorem hmod64 (c R : Nat) (h : c < 64) : (c + 64 * R) % 64 = c := by omega

theorem landM2' (n : Nat) : n &&& 17311559823019733055 =
    4096 * (4096 * (4096 * (4096 * (4096 * (n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 16)
    + n / 64 / 64 / 64 / 64 / 64 / 64 / 64 / 64 % 64) + n / 64 / 64 / 64 / 64 / 64 / 64 % 64)
    + n / 64 / 64 / 64 / 64 % 64) + n / 64 / 64 % 64) + n % 64 := by
  rw [landM2]; simp only [Nat.div_div_eq_div_mul]

def m3 (x2 : Nat) : Nat := x2 &&& 17311559823019733055
def m4 (x3 : Nat) : Nat := (x3 + x3 / 4096) % 18446744073709551616
def m5 (x4 : Nat) : Nat := (x4 + x4 / 16777216) % 18446744073709551616
def m6' (x5 : Nat) : Nat := (x5 + x5 / 281474976710656) % 18446744073709551616
def m6 (x3 : Nat) : Nat := m6' (m5 (m4 x3))

theorem hdiv4096 (c R : Nat) (h : c < 4096) : (c + 4096 * R) / 4096 = R := by omega

theorem swarTail (P0 P1 P2 P3 P4 P5 : Nat) (h0 : P0 ≤ 56) (h1 : P1 ≤ 56) (h2 : P2 ≤ 56) (h3 : P3 ≤ 56)
    (h4 : P4 ≤ 56) (h5 : P5 ≤ 14) :
    m6 (P0 + 4096 * (P1 + 4096 * (P2 + 4096 * (P3 + 4096 * (P4 + 4096 * P5))))) % 2048 =
      P0 + P1 + P2 + P3 + P4 + P5 := by
  have d1 : (P0 + 4096 * (P1 + 4096 * (P2 + 4096 * (P3 + 4096 * (P4 + 4096 * P5))))) / 4096 =
      P1 + 4096 * (P2 + 4096 * (P3 + 4096 * (P4 + 4096 * P5))) := hdiv4096 _ _ (by omega)
  have e4 : m4 (P0 + 4096 * (P1 + 4096 * (P2 + 4096 * (P3 + 4096 * (P4 + 4096 * P5))))) =
      (P0 + P1) + 4096 * ((P1 + P2) + 4096 * ((P2 + P3) + 4096 * ((P3 + P4) + 4096 * ((P4 + P5) + 4096 * P5)))) := by
    unfold m4; rw [d1, Nat.mod_eq_of_lt (by omega)]; omega
  have d2 : ((P0 + P1) + 4096 * ((P1 + P2) + 4096 * ((P2 + P3) + 4096 * ((P3 + P4) + 4096 * ((P4 + P5) + 4096 * P5))))) / 16777216 =
      (P2 + P3) + 4096 * ((P3 + P4) + 4096 * ((P4 + P5) + 4096 * P5)) := by
    rw [show (16777216 : Nat) = 4096 * 4096 by rfl, ← Nat.div_div_eq_div_mul, hdiv4096 _ _ (by omega),
      hdiv4096 _ _ (by omega)]
  have e5 : m5 (m4 (P0 + 4096 * (P1 + 4096 * (P2 + 4096 * (P3 + 4096 * (P4 + 4096 * P5)))))) =
      (P0 + P1 + P2 + P3) + 4096 * ((P1 + P2 + P3 + P4) + 4096 * ((P2 + P3 + P4 + P5) + 4096 * ((P3 + P4 + P5) + 4096 * ((P4 + P5) + 4096 * P5)))) := by
    rw [e4]; unfold m5; rw [d2, Nat.mod_eq_of_lt (by omega)]; omega
  have d3 : ((P0 + P1 + P2 + P3) + 4096 * ((P1 + P2 + P3 + P4) + 4096 * ((P2 + P3 + P4 + P5) + 4096 * ((P3 + P4 + P5) + 4096 * ((P4 + P5) + 4096 * P5))))) / 281474976710656 =
      (P4 + P5) + 4096 * P5 := by
    rw [show (281474976710656 : Nat) = 4096 * 4096 * 4096 * 4096 by rfl, ← Nat.div_div_eq_div_mul,
      ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, hdiv4096 _ _ (by omega),
      hdiv4096 _ _ (by omega), hdiv4096 _ _ (by omega), hdiv4096 _ _ (by omega)]
  unfold m6; rw [e5]; unfold m6'; rw [d3]
  generalize hY : (P0 + P1 + P2 + P3) + 4096 * ((P1 + P2 + P3 + P4) + 4096 * ((P2 + P3 + P4 + P5) + 4096 * ((P3 + P4 + P5) + 4096 * ((P4 + P5) + 4096 * P5)))) + ((P4 + P5) + 4096 * P5) = Y
  have hY' : Y = (P0 + P1 + P2 + P3 + P4 + P5) + 2048 * (2 * ((P1 + P2 + P3 + P4 + P5) + 4096 * ((P2 + P3 + P4 + P5) + 4096 * ((P3 + P4 + P5) + 4096 * ((P4 + P5) + 4096 * P5))))) := by omega
  have hlt : Y < 18446744073709551616 := by omega
  rw [Nat.mod_eq_of_lt hlt, hY', Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem swarLanes (L0 L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 : Nat) (h0 : L0 ≤ 28) (h1 : L1 ≤ 28) (h2 : L2 ≤ 28) (h3 : L3 ≤ 28) (h4 : L4 ≤ 28) (h5 : L5 ≤ 28) (h6 : L6 ≤ 28) (h7 : L7 ≤ 28) (h8 : L8 ≤ 28) (h9 : L9 ≤ 28) (h10 : L10 ≤ 14)
    (X : Nat) (hX : X = L0 + 64 * (L1 + 64 * (L2 + 64 * (L3 + 64 * (L4 + 64 * (L5 + 64 * (L6 + 64 * (L7 + 64 * (L8 + 64 * (L9 + 64 * (L10))))))))))) :
    m6 (m3 ((X + X / 64) % 18446744073709551616)) % 2048 = L0 + L1 + L2 + L3 + L4 + L5 + L6 + L7 + L8 + L9 + L10 := by
  have e1 : X / 64 = L1 + 64 * (L2 + 64 * (L3 + 64 * (L4 + 64 * (L5 + 64 * (L6 + 64 * (L7 + 64 * (L8 + 64 * (L9 + 64 * (L10))))))))) := by rw [hX]; exact hdiv64 _ _ (by omega)
  have e2 : X + X / 64 = (L0 + L1) + 64 * ((L1 + L2) + 64 * ((L2 + L3) + 64 * ((L3 + L4) + 64 * ((L4 + L5) + 64 * ((L5 + L6) + 64 * ((L6 + L7) + 64 * ((L7 + L8) + 64 * ((L8 + L9) + 64 * ((L9 + L10) + 64 * (L10)))))))))) := by
    omega
  have e3 : X + X / 64 < 18446744073709551616 := by rw [e2]; omega
  have e4 : m3 ((X + X / 64) % 18446744073709551616) = (L0 + L1) + 4096 * ((L2 + L3) + 4096 * ((L4 + L5) + 4096 * ((L6 + L7) + 4096 * ((L8 + L9) + 4096 * (L10))))) := by
    rw [Nat.mod_eq_of_lt e3, e2, m3, landM2']
    simp (disch := omega) only [hdiv64, hmod64]
    rw [Nat.mod_eq_of_lt (show L10 < 16 by omega)]
    omega
  rw [e4]
  rw [swarTail _ _ _ _ _ _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  omega


def sw1 (a b : Nat) : Nat :=
  ((((a / 8 &&& 8198552921648689607) + (a &&& 8198552921648689607)) % 18446744073709551616 +
    (b / 8 &&& 8198552921648689607)) % 18446744073709551616 + (b &&& 8198552921648689607)) % 18446744073709551616

theorem swar_nat (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    m6 (m3 ((sw1 a b + sw1 a b / 64) % 18446744073709551616)) % 2048 =
      (digitsOfWord a ++ digitsOfWord b).sum := by
  generalize hX : sw1 a b = X
  unfold sw1 at hX
  rw [List.sum_append, digits_sum, digits_sum]
  simp only [landM1, Nat.div_div_eq_div_mul] at hX
  norm_num at hX
  have ha' : a / 9223372036854775808 = 0 := Nat.div_eq_of_lt ha
  have hb' : b / 9223372036854775808 = 0 := Nat.div_eq_of_lt hb
  simp only [ha', hb', Nat.zero_mod, Nat.add_zero, Nat.mul_zero] at hX
  have ha0 : a % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a % 8 = a0 at *
  have ha1 : a / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 8 % 8 = a1 at *
  have ha2 : a / 64 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 64 % 8 = a2 at *
  have ha3 : a / 512 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 512 % 8 = a3 at *
  have ha4 : a / 4096 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 4096 % 8 = a4 at *
  have ha5 : a / 32768 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 32768 % 8 = a5 at *
  have ha6 : a / 262144 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 262144 % 8 = a6 at *
  have ha7 : a / 2097152 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 2097152 % 8 = a7 at *
  have ha8 : a / 16777216 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 16777216 % 8 = a8 at *
  have ha9 : a / 134217728 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 134217728 % 8 = a9 at *
  have ha10 : a / 1073741824 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 1073741824 % 8 = a10 at *
  have ha11 : a / 8589934592 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 8589934592 % 8 = a11 at *
  have ha12 : a / 68719476736 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 68719476736 % 8 = a12 at *
  have ha13 : a / 549755813888 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 549755813888 % 8 = a13 at *
  have ha14 : a / 4398046511104 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 4398046511104 % 8 = a14 at *
  have ha15 : a / 35184372088832 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 35184372088832 % 8 = a15 at *
  have ha16 : a / 281474976710656 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 281474976710656 % 8 = a16 at *
  have ha17 : a / 2251799813685248 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 2251799813685248 % 8 = a17 at *
  have ha18 : a / 18014398509481984 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 18014398509481984 % 8 = a18 at *
  have ha19 : a / 144115188075855872 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 144115188075855872 % 8 = a19 at *
  have ha20 : a / 1152921504606846976 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize a / 1152921504606846976 % 8 = a20 at *
  have hb0 : b % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b % 8 = b0 at *
  have hb1 : b / 8 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 8 % 8 = b1 at *
  have hb2 : b / 64 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 64 % 8 = b2 at *
  have hb3 : b / 512 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 512 % 8 = b3 at *
  have hb4 : b / 4096 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 4096 % 8 = b4 at *
  have hb5 : b / 32768 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 32768 % 8 = b5 at *
  have hb6 : b / 262144 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 262144 % 8 = b6 at *
  have hb7 : b / 2097152 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 2097152 % 8 = b7 at *
  have hb8 : b / 16777216 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 16777216 % 8 = b8 at *
  have hb9 : b / 134217728 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 134217728 % 8 = b9 at *
  have hb10 : b / 1073741824 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 1073741824 % 8 = b10 at *
  have hb11 : b / 8589934592 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 8589934592 % 8 = b11 at *
  have hb12 : b / 68719476736 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 68719476736 % 8 = b12 at *
  have hb13 : b / 549755813888 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 549755813888 % 8 = b13 at *
  have hb14 : b / 4398046511104 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 4398046511104 % 8 = b14 at *
  have hb15 : b / 35184372088832 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 35184372088832 % 8 = b15 at *
  have hb16 : b / 281474976710656 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 281474976710656 % 8 = b16 at *
  have hb17 : b / 2251799813685248 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 2251799813685248 % 8 = b17 at *
  have hb18 : b / 18014398509481984 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 18014398509481984 % 8 = b18 at *
  have hb19 : b / 144115188075855872 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 144115188075855872 % 8 = b19 at *
  have hb20 : b / 1152921504606846976 % 8 < 8 := Nat.mod_lt _ (by decide)
  generalize b / 1152921504606846976 % 8 = b20 at *
  clear ha' hb' ha hb
  rw [swarLanes (a0 + a1 + b0 + b1) (a2 + a3 + b2 + b3) (a4 + a5 + b4 + b5) (a6 + a7 + b6 + b7) (a8 + a9 + b8 + b9) (a10 + a11 + b10 + b11) (a12 + a13 + b12 + b13) (a14 + a15 + b14 + b15) (a16 + a17 + b16 + b17) (a18 + a19 + b18 + b19) (a20 + b20) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) X (by
    rw [← hX]
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    omega)]
  omega
end SigGolfCandidate.Verify
