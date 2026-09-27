import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.SmallBound
/-!
# Closing arithmetic for the capped adversary

At budget `q + 1` with `keygenHashCost ≤ q < budgetSplit`, the small-budget bound of the capped adversary
is at most `q / 2^127`. Compared with the query-bounded closing, the full-certificate excess is paid at
the crude budget `297 (q + 1)`, which costs about `0.05 x` of the `0.147 x` slack, and the extra query
of the marker costs `2^-127`, which the slack absorbs since `q ≥ keygenHashCost`.
-/

namespace SphincsSecurity.Concrete.EventSmall

open ENNReal

set_option exponentiation.threshold 1024

private theorem visRangeClosing (x : ℝ) (hlow : 9472 / 2 ^ 128 ≤ x) (hhigh : x ≤ 3 / 16384) :
    7 / 4 * x + 297 * 11 / 2 ^ 16 * x + 1 / 2 ^ 700 + x ^ 2 * 2 +
      16384 / 16381 * x * (557 * x + 14 * (297 * x / 2 ^ 25) + 14 / 2 ^ 700) ≤ 2 * x - 2 / 2 ^ 128 := by
  have hn : 0 ≤ x := le_trans (by positivity) hlow
  have hsq : x * x ≤ x * (3 / 16384) := mul_le_mul_of_nonneg_left hhigh hn
  have htail : (1 : ℝ) / 2 ^ 700 ≤ x / 2 ^ 572 := by
    calc
      (1 : ℝ) / 2 ^ 700 = (1 / 2 ^ 128) / 2 ^ 572 := by norm_num
      _ ≤ x / 2 ^ 572 := div_le_div_of_nonneg_right (le_trans (by norm_num) hlow) (by positivity)
  have hsmall : (2 : ℝ) / 2 ^ 128 ≤ x / 4736 := by
    calc
      (2 : ℝ) / 2 ^ 128 = (9472 / 2 ^ 128) / 4736 := by norm_num
      _ ≤ x / 4736 := div_le_div_of_nonneg_right hlow (by positivity)
  norm_num at hsq htail hsmall ⊢
  nlinarith [hsq, htail, hn, hlow, hhigh, hsmall]

theorem visSmallBound_le (q : Nat) (hq : keygenHashCost ≤ q) (hsmall : q + 1 ≤ budgetSplit) :
    visSmallBound (q + 1) ≤ (q : ENNReal) / 2 ^ 127 := by
  rw [budgetSplit_def] at hsmall
  rw [keygenHashCost_eq] at hq
  unfold visSmallBound FtsGuessHash.nearMixedBound
  rw [primitiveCoefficient_def, fullCertificateExcessRate_def, proposalPrefixExceptionBound_def, nearCertificatePrice_def,
    show Fintype.card FtsTree = 14 from Fintype.card_fin _, signRatio]
  set b := q + 1 with hbdef
  have hx : ((b : Nat) : ENNReal) / 2 ^ 128 ≤ 3 / 16384 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_div, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat,
      ENNReal.toReal_ofNat, ENNReal.toReal_ofNat]
    have hq' : ((b : Nat) : ℝ) ≤ 3 * 2 ^ 114 := by exact_mod_cast hsmall
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hhalf : (2 : ENNReal)⁻¹ ≤ 1 - ((b : Nat) : ENNReal) / 2 ^ 128 := by
    refine le_trans ?_ (tsub_le_tsub_left hx 1)
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_sub_of_le (by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [ENNReal.toReal_div]) (by finiteness)]
    norm_num [ENNReal.toReal_div, ENNReal.toReal_inv]
  have hpair : FtsGuessHash.pairRate b ≤ (((b : Nat) : ENNReal) / 2 ^ 128) ^ 2 * 2 := by
    refine (FtsGuessHash.pairRate_le_normalized b).trans ?_
    rw [ENNReal.div_le_iff_le_mul (Or.inr (by finiteness)) (Or.inl (by finiteness)), mul_assoc]
    apply le_trans (le_of_eq (mul_one _).symm)
    apply mul_le_mul' le_rfl
    calc
      (1 : ENNReal) = 2 * (2 * ((2 : ENNReal)⁻¹) ^ 2) := by
        apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).mp
        norm_num [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_inv]
      _ ≤ _ := mul_le_mul' le_rfl (mul_le_mul' le_rfl (pow_le_pow_left' hhalf 2))
  have hinv : ((2 ^ 128 - b : Nat) : ENNReal)⁻¹ ≤ (16381 * 2 ^ 114 : ENNReal)⁻¹ := by
    apply ENNReal.inv_le_inv.mpr
    have h : ((16381 * 2 ^ 114 : Nat) : ENNReal) ≤ ((2 ^ 128 - b : Nat) : ENNReal) := by
      exact_mod_cast (show 16381 * 2 ^ 114 ≤ 2 ^ 128 - b by omega)
    exact_mod_cast h
  have hcache : ((297 * b : Nat) : ENNReal) * certificateCacheExceptionRate ≤ ((297 * b : Nat) : ENNReal) * (2 ^ 153 : ENNReal)⁻¹ :=
    mul_le_mul' le_rfl certificateCacheExceptionRate_le
  refine le_trans (add_le_add (add_le_add le_rfl hpair)
    (mul_le_mul' hinv (mul_le_mul' le_rfl (mul_le_mul' le_rfl (add_le_add le_rfl (add_le_add hcache le_rfl)))))) ?_
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp (disch := finiteness) only [ENNReal.toReal_add, ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_inv,
    ENNReal.toReal_pow, ENNReal.toReal_natCast, ENNReal.toReal_ofNat, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_mul]
  have hlow : 9472 / 2 ^ 128 ≤ ((b : Nat) : ℝ) / 2 ^ 128 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast (show 9472 ≤ b by omega)
  have hhigh : ((b : Nat) : ℝ) / 2 ^ 128 ≤ 3 / 16384 := by
    have hq' : ((b : Nat) : ℝ) ≤ 3 * 2 ^ 114 := by exact_mod_cast hsmall
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hqb : (q : ℝ) = ((b : Nat) : ℝ) - 1 := by
    rw [hbdef]; push_cast; ring
  rw [hqb]
  have h := visRangeClosing (((b : Nat) : ℝ) / 2 ^ 128) hlow hhigh
  convert h using 1 <;> ring

end SphincsSecurity.Concrete.EventSmall
