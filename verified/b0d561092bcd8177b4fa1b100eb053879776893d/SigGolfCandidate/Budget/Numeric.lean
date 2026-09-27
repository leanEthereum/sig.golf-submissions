import SigGolfCandidate.Budget.Sign
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Budget: the numbers

With `z = 2 ^ (1 / 2^17)`, the digest search is bounded by `bD = 1.0140` (3 compressions per
trial, exact acceptance probability `p = 15! * Nadm / 2^210 ≈ 1/869.22`; minimal admissible
value 1.013983) and each counter search by `bC = 1.01284` (target sum 182, acceptance
`codeCount / 2^128 ≈ 2^-11.2265`; minimal 1.012834); the deterministic part is
`2 ^ (115442 / 2^17) ≈ 1.8410` (MAC 1025 + PORS tree 40959 + layers 1..4 73244 + top layer 214),
and `1.8410 * 1.0140 * 1.01284^5 ≈ 1.99010 ≤ 2` (analytic value 1.99001) (`V_signRef_le_two`).
Keygen: `z_K ^ 674814 ≤ 2` with
`z_K = 2 ^ (1 / 2^20)` (`V_keygenRef_le_two`).

Real bounds used: `log 2 < 0.6931471808`, `log 2 > 0.6931471803`, `exp x < 1 / (1 - x)` and
`1 + x + x^2/2 ≤ exp x` (x ≥ 0).
-/

namespace SigGolfCandidate.Budget
open SigGolf SigGolfCandidate.Ref OracleComp ENNReal

/-- `2 ^ (1 / B)` as an extended real. -/
noncomputable def zOf (B : Nat) : ℝ≥0∞ := ENNReal.ofReal ((2 : ℝ) ^ (1 / (B : ℝ)))

theorem zOf_pow (B n : Nat) :
    zOf B ^ n = ENNReal.ofReal ((2 : ℝ) ^ ((n : ℝ) / (B : ℝ))) := by
  unfold zOf
  rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num) _)]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  ring_nf

theorem one_le_zOf (B : Nat) : 1 ≤ zOf B := by
  unfold zOf
  rw [← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  exact Real.one_le_rpow (by norm_num) (by positivity)

/-- `2 ^ (1/B) ≤ 1 / (1 - 0.6931471808 / B)`. -/
theorem rpow_two_inv_le (B : Nat) (hB : 1 ≤ B) :
    (2 : ℝ) ^ (1 / (B : ℝ)) ≤ 1 / (1 - 0.6931471808 / (B : ℝ)) := by
  have hBr : (1 : ℝ) ≤ B := by exact_mod_cast hB
  have hl := Real.log_two_lt_d9
  have hl0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hx0 : 0 < Real.log 2 * (1 / (B : ℝ)) := by positivity
  have hx1 : Real.log 2 * (1 / (B : ℝ)) < 1 := by
    rw [mul_one_div, div_lt_one (by linarith)]; linarith
  refine (Real.exp_bound_div_one_sub_of_interval' hx0 hx1).le.trans ?_
  have h1 : Real.log 2 * (1 / (B : ℝ)) ≤ 0.6931471808 / (B : ℝ) := by
    rw [mul_one_div]; exact div_le_div_of_nonneg_right hl.le (by linarith)
  have h2 : 0.6931471808 / (B : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
  apply one_div_le_one_div_of_le (by linarith)
  linarith

/-- `2 ^ y ≥ 1 + x + x^2/2` with `x = 0.6931471803 y`, for `y ≥ 0`. -/
theorem rpow_two_ge (y : ℝ) (hy : 0 ≤ y) :
    1 + 0.6931471803 * y + (0.6931471803 * y) ^ 2 / 2 ≤ (2 : ℝ) ^ y := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have hl := Real.log_two_gt_d9
  have hx : 0.6931471803 * y ≤ Real.log 2 * y := mul_le_mul_of_nonneg_right hl.le hy
  have hx0 : 0 ≤ 0.6931471803 * y := by positivity
  have h := Real.quadratic_le_exp_of_nonneg (hx0.trans hx)
  nlinarith

/-! ## The per-trial probabilities as reals -/

theorem natCast_div_eq_ofReal (a b : Nat) (hb : 0 < b) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) = ENNReal.ofReal ((a : ℝ) / (b : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

theorem one_sub_ofReal (x : ℝ) (hx : 0 ≤ x) :
    1 - ENNReal.ofReal x = ENNReal.ofReal (1 - x) := by
  rw [ENNReal.ofReal_sub _ hx, ENNReal.ofReal_one]

/-- `15! * Nadm`, the number of admissible 15-tuples of leaf indices. -/
def admTuples : Nat := 1893082637492346289421899057770787543018786235522507341824000

theorem rhoD_eq : rhoD = ENNReal.ofReal (1 - (admTuples : ℝ) / 2 ^ 210) := by
  unfold rhoD
  rw [probEvent_not_admissible, Octopus.admissibleTuples_eq,
    show (2 : ℝ≥0∞) ^ 210 = ((2 ^ 210 : Nat) : ℝ≥0∞) by rw [Nat.cast_pow, Nat.cast_ofNat],
    natCast_div_eq_ofReal _ _ (by positivity), one_sub_ofReal _ (by positivity)]
  unfold admTuples
  norm_num

theorem rhoC_eq : rhoC = ENNReal.ofReal (1 - (codeCount : ℝ) / 2 ^ 128) := by
  unfold rhoC
  rw [probEvent_decode_none,
    show (2 : ℝ≥0∞) ^ 256 = ((2 ^ 256 : Nat) : ℝ≥0∞) by rw [Nat.cast_pow, Nat.cast_ofNat],
    natCast_div_eq_ofReal _ _ (by positivity), one_sub_ofReal _ (by positivity)]
  congr 2
  push_cast
  field_simp
  ring

theorem epsD_eq : epsD = ENNReal.ofReal (1 / 2 ^ 108) := by
  unfold epsD
  rw [show (2 : ℝ≥0∞) ^ 20 / 2 ^ 128 = ((2 ^ 20 : Nat) : ℝ≥0∞) / ((2 ^ 128 : Nat) : ℝ≥0∞) by
      rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat],
    natCast_div_eq_ofReal _ _ (by positivity)]
  norm_num

/-! ## The step conditions -/

/-- The digest-search bound. -/
noncomputable def bD : ℝ≥0∞ := ENNReal.ofReal 1.0140
/-- The counter-search bound. -/
noncomputable def bC : ℝ≥0∞ := ENNReal.ofReal 1.01284

theorem zS_le : zOf (2 ^ 17) ≤ ENNReal.ofReal (1 / (1 - 0.6931471808 / 131072)) := by
  unfold zOf
  refine ENNReal.ofReal_le_ofReal ?_
  have := rpow_two_inv_le (2 ^ 17) (by norm_num)
  simpa using this

theorem stepD : zOf (2 ^ 17) ^ 3 * ((epsD + rhoD) * bD + (1 - rhoD)) ≤ bD := by
  have hp0 : 0 ≤ (admTuples : ℝ) / 2 ^ 210 := by positivity
  have hp1 : (admTuples : ℝ) / 2 ^ 210 ≤ 1 := by
    rw [div_le_one (by positivity)]; unfold admTuples; norm_num
  rw [rhoD_eq, epsD_eq, one_sub_ofReal _ (by linarith), bD]
  set zb : ℝ := 1 / (1 - 0.6931471808 / 131072)
  calc zOf (2 ^ 17) ^ 3 * ((ENNReal.ofReal (1 / 2 ^ 108) +
        ENNReal.ofReal (1 - (admTuples : ℝ) / 2 ^ 210)) * ENNReal.ofReal 1.0140 +
        ENNReal.ofReal (1 - (1 - (admTuples : ℝ) / 2 ^ 210)))
      ≤ ENNReal.ofReal zb ^ 3 * ((ENNReal.ofReal (1 / 2 ^ 108) +
        ENNReal.ofReal (1 - (admTuples : ℝ) / 2 ^ 210)) * ENNReal.ofReal 1.0140 +
        ENNReal.ofReal (1 - (1 - (admTuples : ℝ) / 2 ^ 210))) := by
        gcongr; exact zS_le
    _ = ENNReal.ofReal (zb ^ 3 * ((1 / 2 ^ 108 + (1 - (admTuples : ℝ) / 2 ^ 210)) * 1.0140 +
          (1 - (1 - (admTuples : ℝ) / 2 ^ 210)))) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by linarith),
          ← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) (by linarith),
          ← ENNReal.ofReal_pow (by norm_num [zb]), ← ENNReal.ofReal_mul (by norm_num [zb])]
    _ ≤ ENNReal.ofReal 1.0140 := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold admTuples
        norm_num [zb]

theorem stepC : zOf (2 ^ 17) * (rhoC * bC + (1 - rhoC)) ≤ bC := by
  have hc0 : 0 ≤ (codeCount : ℝ) / 2 ^ 128 := by positivity
  have hc : (codeCount : ℝ) / 2 ^ 128 ≤ 1 := by
    rw [div_le_one (by positivity)]; unfold codeCount; norm_num
  rw [rhoC_eq, one_sub_ofReal _ (by linarith), bC]
  set zb : ℝ := 1 / (1 - 0.6931471808 / 131072)
  calc zOf (2 ^ 17) * (ENNReal.ofReal (1 - (codeCount : ℝ) / 2 ^ 128) * ENNReal.ofReal 1.01284 +
        ENNReal.ofReal (1 - (1 - (codeCount : ℝ) / 2 ^ 128)))
      ≤ ENNReal.ofReal zb * (ENNReal.ofReal (1 - (codeCount : ℝ) / 2 ^ 128) *
        ENNReal.ofReal 1.01284 + ENNReal.ofReal (1 - (1 - (codeCount : ℝ) / 2 ^ 128))) := by
        gcongr; exact zS_le
    _ = ENNReal.ofReal (zb * ((1 - (codeCount : ℝ) / 2 ^ 128) * 1.01284 +
          (1 - (1 - (codeCount : ℝ) / 2 ^ 128)))) := by
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) (by linarith),
          ← ENNReal.ofReal_mul (by norm_num [zb])]
    _ ≤ ENNReal.ofReal 1.01284 := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold codeCount
        norm_num [zb]

/-! ## The final bounds -/

theorem final_sign :
    zOf (2 ^ 17) ^ 1025 * signBound (zOf (2 ^ 17)) bD bC ≤ 2 := by
  have e : zOf (2 ^ 17) ^ 1025 * signBound (zOf (2 ^ 17)) bD bC =
      bD * bC ^ 5 * zOf (2 ^ 17) ^ 115442 := by
    rw [show 115442 = 1025 + (40959 + (73244 + 214)) by norm_num, pow_add, pow_add]
    simp only [signBound]; ring
  rw [e, zOf_pow, bD, bC, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsplit : (2 : ℝ) ^ (((115442 : Nat) : ℝ) / ((2 ^ 17 : Nat) : ℝ)) =
      2 / (2 : ℝ) ^ ((15630 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  rw [hsplit]
  have hlow := rpow_two_ge (15630 / 131072) (by norm_num)
  have hpos : 0 < (2 : ℝ) ^ ((15630 : ℝ) / 131072) := Real.rpow_pos_of_pos (by norm_num) _
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem V_signRef_le_two (sk : Bytes 32) (cache : Cache) (m : Bytes 32) (c : RCache)
    (hinv : CacheInv Inv0 c) : V (zOf (2 ^ 17)) (signRef sk cache m) c ≤ 2 := by
  have h1 : 1 ≤ bD := by rw [bD, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h2 : 1 ≤ bC := by rw [bC, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact (V_signRef _ bD bC (one_le_zOf _) h1 h2 stepD stepC sk cache m c hinv).trans final_sign

theorem V_keygenRef_le_two (sk : Bytes 32) (cache : RCache) :
    V (zOf (2 ^ 20)) (keygenRef sk) cache ≤ 2 := by
  refine ((spec_keygenRef sk).V_le (one_le_zOf _) cache).trans ?_
  rw [keygenCost_eq]
  rw [zOf_pow, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (2 : ℝ) ^ ((674814 : Nat) / ((2 ^ 20 : Nat) : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

end SigGolfCandidate.Budget
