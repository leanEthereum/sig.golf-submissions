import VCVio.OracleComp.Constructions.SampleableType
import SigGolfCandidate.SphincsSecurity.Completeness.Octopus.Tuples

/-!
# PORS+FP admissibility: the probability of one fresh digest

For a uniform 256-bit answer `u`, `admissible u.toNat` (the signer's test: distinct leaf indices
and octopus size `≤ 120`) holds with probability exactly

  `p = 15! * Nadm / 2^210 ≈ 2^-9.76358 ≈ 0.00115046`

(`probEvent_admissibleDigest`), and fails with probability `1 - p`
(`probEvent_not_admissibleDigest`). Bounds: `1/870 ≤ p ≤ 1/869`, in particular `2^-10 ≤ p`.
-/

namespace SphincsSecurity.Completeness.Octopus
open OracleComp Finset ENNReal

theorem card_bitVec_filter' (n : ℕ) (P : ℕ → Prop) [DecidablePred P] :
    (univ.filter fun u : BitVec n => P u.toNat).card = ((range (2 ^ n)).filter P).card := by
  refine Finset.card_nbij' (fun u => u.toNat) (fun k => BitVec.ofNat n k) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, mem_range] at hu ⊢
    exact ⟨u.isLt, hu⟩
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_univ, true_and] at hk ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk.1]; exact hk.2
  · intro u _; simp
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hk
    simp [Nat.mod_eq_of_lt hk.1]

theorem probEvent_uniform_toNat' (P : ℕ → Prop) [DecidablePred P] :
    Pr[fun u : BitVec 256 => P u.toNat | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      (((range (2 ^ 256)).filter P).card : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  rw [probEvent_uniformSample, card_bitVec_filter', Fintype.card_bitVec, Nat.cast_pow,
    Nat.cast_ofNat]

/-- `15! * Nadm`, the number of admissible 15-tuples of 14-bit values. -/
theorem admissibleTuples_eq :
    Nat.factorial 15 * Nadm = 1893082637492346289421899057770787543018786235522507341824000 := by
  unfold Nadm; norm_num [Nat.factorial]

theorem admissibleTuples_bounds :
    2 ^ 210 ≤ 870 * (Nat.factorial 15 * Nadm) ∧ 869 * (Nat.factorial 15 * Nadm) ≤ 2 ^ 210 ∧
      2 ^ 200 ≤ Nat.factorial 15 * Nadm := by
  rw [admissibleTuples_eq]; norm_num

/-- **Exact acceptance probability** of a fresh digest. -/
theorem probEvent_admissibleDigest :
    Pr[fun u : BitVec 256 => admissible u.toNat = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 := by
  rw [probEvent_uniform_toNat' (fun N => admissible N = true), card_admissibleDigests]
  have e : (2 : ℝ≥0∞) ^ 256 = 2 ^ 46 * 2 ^ 210 := by rw [← pow_add]
  rw [e, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.mul_div_mul_left _ _ (by simp) (by simp)]

/-- **Exact rejection probability** of a fresh digest. -/
theorem probEvent_not_admissibleDigest :
    Pr[fun u : BitVec 256 => ¬ admissible u.toNat = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      1 - ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 := by
  have hc := probEvent_compl ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    (fun u : BitVec 256 => admissible u.toNat = true)
  have hfail : Pr[⊥ | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = 0 := by simp
  rw [hfail, tsub_zero] at hc
  rw [ENNReal.eq_sub_of_add_eq probEvent_ne_top ((add_comm _ _).trans hc),
    probEvent_admissibleDigest]

/-- Lower bound: `p ≥ 1/870`. -/
theorem admissibleProb_ge :
    (1 : ℝ≥0∞) / 870 ≤ ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 := by
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), one_div,
    ← ENNReal.div_eq_inv_mul]
  apply ENNReal.div_le_of_le_mul
  have h := admissibleTuples_bounds.1
  rw [mul_comm] at h
  exact_mod_cast h

/-- Upper bound: `p ≤ 1/869`. -/
theorem admissibleProb_le :
    ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 ≤ (1 : ℝ≥0∞) / 869 := by
  rw [ENNReal.div_le_iff (by simp) (by simp), one_div, ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  have h := admissibleTuples_bounds.2.1
  rw [mul_comm] at h
  exact_mod_cast h

/-- `p ≥ 2^-10`. -/
theorem admissibleProb_ge_two_pow :
    (1 : ℝ≥0∞) / 2 ^ 10 ≤ ((Nat.factorial 15 * Nadm : ℕ) : ℝ≥0∞) / 2 ^ 210 :=
  le_trans (ENNReal.div_le_div_left (by norm_num) 1) admissibleProb_ge

/-- The acceptance probability of a fresh digest is at least `2^-10`. -/
theorem probEvent_admissibleDigest_ge :
    (1 : ℝ≥0∞) / 2 ^ 10 ≤ Pr[fun u : BitVec 256 => admissible u.toNat = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
  rw [probEvent_admissibleDigest]; exact admissibleProb_ge_two_pow

end SphincsSecurity.Completeness.Octopus
