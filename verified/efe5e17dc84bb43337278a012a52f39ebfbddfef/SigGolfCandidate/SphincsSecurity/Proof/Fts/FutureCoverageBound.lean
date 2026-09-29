import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeFresh
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem expected_uniformHashOutput_admissible_weight (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0)) =
      admissibleProbability *
        ∑' target, Pr[= target | signerViewSample] * weight target := by
  have hexpand (output : HashOutput) :
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0) =
        ∑' target, if Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target then weight target else 0 := by
    by_cases h : Admissible (truncateMessageDigest output) <;> simp only [h, true_and, false_and, if_true, if_false, tsum_zero]
    simp
  simp_rw [hexpand, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro target
  calc
    _ = Pr[fun output => Admissible (truncateMessageDigest output) ∧ hashOutputFewTimeView output = target |
        ($ᵗ HashOutput : ProbComp HashOutput)] * weight target := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      split_ifs <;> simp
    _ = _ := by
      simp only [← signAttemptResultOfOutput_ne_none_iff]
      rw [probEvent_uniformHashOutput_admissible_view (fun view => view = target),
        probEvent_eq_eq_probOutput, mul_assoc]

/-- A fresh answer's view is uniform: averaging a weight of the view over the answer. -/
theorem expected_uniformHashOutput_view_weight (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * weight (hashOutputFewTimeView output)) =
      ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight target := by
  have hexpand (output : HashOutput) :
      weight (hashOutputFewTimeView output) =
        ∑' target, if hashOutputFewTimeView output = target then weight target else 0 := by
    rw [tsum_eq_single (hashOutputFewTimeView output) (fun other hother => if_neg (Ne.symm hother)), if_pos rfl]
  simp_rw [hexpand, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  apply tsum_congr
  intro target
  calc
    _ = Pr[fun output => hashOutputFewTimeView output = target | ($ᵗ HashOutput : ProbComp HashOutput)] * weight target := by
      rw [probEvent_eq_tsum_ite, ← ENNReal.tsum_mul_right]
      apply tsum_congr
      intro output
      split_ifs <;> simp
    _ = _ := by
      rw [probEvent_uniformHashOutput_view (fun view => view = target), probEvent_eq_eq_probOutput]

/-- The admissibility of an adversary's fresh target is dropped: its view is then uniform. -/
theorem expected_uniformHashOutput_admissible_weight_le_uniform (weight : FewTimeView → ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then weight (hashOutputFewTimeView output) else 0)) ≤
      ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * weight target := by
  rw [← expected_uniformHashOutput_view_weight]
  apply ENNReal.tsum_le_tsum
  intro output
  apply mul_le_mul' le_rfl
  split_ifs <;> simp

end SphincsSecurity.Concrete
