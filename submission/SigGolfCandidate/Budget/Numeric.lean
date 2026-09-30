import SigGolfCandidate.Budget.Sign
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Budget: the numbers

With `z = 2 ^ (1 / 2^17)`, the digest search is bounded by `bD = 1.023` and each counter search
by `bC = 1.0027`; the deterministic part is `2 ^ (115375 / 2^17) ≈ 1.8408`, and
`1.8408 * 1.023 * 1.0027^7 ≈ 1.92 ≤ 2` (`V_signRef_le_two`). Keygen: `z_K ^ 11135 ≤ 2` with
`z_K = 2 ^ (1 / 2^20)` (`V_keygenRef_le_two`).

Real bounds used: `log 2 < 0.6931471808`, `log 2 > 0.6931471803`, `exp x < 1 / (1 - x)` and
`1 + x ≤ exp x`.
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

/-- `2 ^ y ≥ 1 + 0.6931471803 y` for `y ≥ 0`. -/
theorem rpow_two_ge (y : ℝ) (hy : 0 ≤ y) : 1 + 0.6931471803 * y ≤ (2 : ℝ) ^ y := by
  rw [Real.rpow_def_of_pos (by norm_num)]
  have := Real.add_one_le_exp (Real.log 2 * y)
  have hl := Real.log_two_gt_d9
  nlinarith

/-! ## The per-trial probabilities as reals -/

theorem natCast_div_eq_ofReal (a b : Nat) (hb : 0 < b) :
    (a : ℝ≥0∞) / (b : ℝ≥0∞) = ENNReal.ofReal ((a : ℝ) / (b : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hb), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

theorem one_sub_ofReal (x : ℝ) (hx : 0 ≤ x) :
    1 - ENNReal.ofReal x = ENNReal.ofReal (1 - x) := by
  rw [ENNReal.ofReal_sub _ hx, ENNReal.ofReal_one]

theorem rhoD_eq : rhoD = ENNReal.ofReal (1 - 1 / 1024) := by
  unfold rhoD
  rw [probEvent_not_admissible,
    show (2 : ℝ≥0∞) ^ 246 / 2 ^ 256 = ((2 ^ 246 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) by
      rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat],
    natCast_div_eq_ofReal _ _ (by positivity), one_sub_ofReal _ (by positivity)]
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
noncomputable def bD : ℝ≥0∞ := ENNReal.ofReal 1.023
/-- The counter-search bound. -/
noncomputable def bC : ℝ≥0∞ := ENNReal.ofReal 1.0027

theorem zS_le : zOf (2 ^ 17) ≤ ENNReal.ofReal (1 / (1 - 0.6931471808 / 131072)) := by
  unfold zOf
  refine ENNReal.ofReal_le_ofReal ?_
  have := rpow_two_inv_le (2 ^ 17) (by norm_num)
  simpa using this

theorem stepD : zOf (2 ^ 17) ^ 4 * ((epsD + rhoD) * bD + (1 - rhoD)) ≤ bD := by
  rw [rhoD_eq, epsD_eq, one_sub_ofReal _ (by norm_num), bD]
  set zb : ℝ := 1 / (1 - 0.6931471808 / 131072)
  calc zOf (2 ^ 17) ^ 4 * ((ENNReal.ofReal (1 / 2 ^ 108) + ENNReal.ofReal (1 - 1 / 1024)) *
        ENNReal.ofReal 1.023 + ENNReal.ofReal (1 - (1 - 1 / 1024)))
      ≤ ENNReal.ofReal zb ^ 4 * ((ENNReal.ofReal (1 / 2 ^ 108) + ENNReal.ofReal (1 - 1 / 1024)) *
        ENNReal.ofReal 1.023 + ENNReal.ofReal (1 - (1 - 1 / 1024))) := by
        gcongr; exact zS_le
    _ = ENNReal.ofReal (zb ^ 4 * ((1 / 2 ^ 108 + (1 - 1 / 1024)) * 1.023 +
          (1 - (1 - 1 / 1024)))) := by
        rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
          ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by norm_num) (by norm_num),
          ← ENNReal.ofReal_pow (by norm_num [zb]), ← ENNReal.ofReal_mul (by norm_num [zb])]
    _ ≤ ENNReal.ofReal 1.023 := by
        refine ENNReal.ofReal_le_ofReal ?_
        norm_num [zb]

theorem stepC : zOf (2 ^ 17) * (rhoC * bC + (1 - rhoC)) ≤ bC := by
  have hc0 : 0 ≤ (codeCount : ℝ) / 2 ^ 128 := by positivity
  have hc : (codeCount : ℝ) / 2 ^ 128 ≤ 1 := by
    rw [div_le_one (by positivity)]; unfold codeCount; norm_num
  rw [rhoC_eq, one_sub_ofReal _ (by linarith), bC]
  set zb : ℝ := 1 / (1 - 0.6931471808 / 131072)
  calc zOf (2 ^ 17) * (ENNReal.ofReal (1 - (codeCount : ℝ) / 2 ^ 128) * ENNReal.ofReal 1.0027 +
        ENNReal.ofReal (1 - (1 - (codeCount : ℝ) / 2 ^ 128)))
      ≤ ENNReal.ofReal zb * (ENNReal.ofReal (1 - (codeCount : ℝ) / 2 ^ 128) *
        ENNReal.ofReal 1.0027 + ENNReal.ofReal (1 - (1 - (codeCount : ℝ) / 2 ^ 128))) := by
        gcongr; exact zS_le
    _ = ENNReal.ofReal (zb * ((1 - (codeCount : ℝ) / 2 ^ 128) * 1.0027 +
          (1 - (1 - (codeCount : ℝ) / 2 ^ 128)))) := by
        rw [← ENNReal.ofReal_mul (by linarith), ← ENNReal.ofReal_add (by positivity) (by linarith),
          ← ENNReal.ofReal_mul (by norm_num [zb])]
    _ ≤ ENNReal.ofReal 1.0027 := by
        refine ENNReal.ofReal_le_ofReal ?_
        unfold codeCount
        norm_num [zb]

/-! ## The final bounds -/

theorem final_sign :
    bD * (zOf (2 ^ 17) ^ (14 * 3071 + 4) * (bC ^ 7 * zOf (2 ^ 17) ^ 72377)) ≤ 2 := by
  have e : bD * (zOf (2 ^ 17) ^ (14 * 3071 + 4) * (bC ^ 7 * zOf (2 ^ 17) ^ 72377)) =
      bD * bC ^ 7 * zOf (2 ^ 17) ^ 115375 := by
    rw [show 115375 = (14 * 3071 + 4) + 72377 by norm_num, pow_add]; ring
  rw [e, zOf_pow, bD, bC, ← ENNReal.ofReal_pow (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  have hsplit : (2 : ℝ) ^ (((115375 : Nat) : ℝ) / ((2 ^ 17 : Nat) : ℝ)) =
      2 / (2 : ℝ) ^ ((15697 : ℝ) / 131072) := by
    rw [_root_.eq_div_iff (by positivity), ← Real.rpow_add (by norm_num)]
    norm_num
  rw [hsplit]
  have hlow := rpow_two_ge (15697 / 131072) (by norm_num)
  have hpos : 0 < (2 : ℝ) ^ ((15697 : ℝ) / 131072) := Real.rpow_pos_of_pos (by norm_num) _
  rw [mul_div_assoc', div_le_iff₀ hpos]
  nlinarith

theorem V_signRef_le_two (sk m : Bytes 32) (cache : RCache) (hinv : CacheInv Inv0 cache) :
    V (zOf (2 ^ 17)) (signRef sk m) cache ≤ 2 := by
  have h1 : 1 ≤ bD := by rw [bD, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  have h2 : 1 ≤ bC := by rw [bC, ← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal (by norm_num)
  exact (V_signRef _ bD bC (one_le_zOf _) h1 h2 stepD stepC sk m cache hinv).trans final_sign

theorem V_keygenRef_le_two (sk : Bytes 32) (cache : RCache) :
    V (zOf (2 ^ 20)) (keygenRef sk) cache ≤ 2 := by
  refine ((spec_keygenRef sk).V_le (one_le_zOf _) cache).trans ?_
  rw [zOf_pow, show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  refine ENNReal.ofReal_le_ofReal ?_
  calc (2 : ℝ) ^ ((11135 : Nat) / ((2 ^ 20 : Nat) : ℝ)) ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    _ = 2 := Real.rpow_one 2

end SigGolfCandidate.Budget
