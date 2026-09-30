import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ConcreteTargetShapeQuery
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FreshTargetShapeAverage
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetIndexEnvelope
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeExpectation
/-!
# The forecast of a fresh target, averaged at its creation

A fresh target's forecast uses its own exact coverage rates. Averaged over a uniform target, the rates
and the moments factor over the target's coordinates (`leafAverage_targetShapeEnvelope_le`), so the
averaged forecast is at most `2^-34` times the index-level envelope with the constant rates `2^-34`
(signing) and `p · 2^-34` (arrival). An adversary's target is a raw answer: its admissibility is dropped
(no credit). A target created by the signer has the signer's view law, whose density against the uniform
view law is at most `1/p`.
-/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem expected_uniformFewTimeView_eq_leafAverage (f : FewTimeView → ENNReal) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * f target) =
      (Fintype.card Index : ENNReal)⁻¹ * ∑ index : Index, leafAverage (fun leaves => f (index, leaves)) := by
  simp only [probOutput_uniformFewTimeView, tsum_fintype, Fintype.sum_prod_type, leafAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro leaves _
  rw [Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  ring

theorem expected_signerViewSample_le (f : FewTimeView → ENNReal) :
    (∑' target, Pr[= target | signerViewSample] * f target) ≤
      admissibleProbability⁻¹ * ∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] * f target := by
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro target
  rw [← mul_assoc]
  apply mul_le_mul' _ le_rfl
  have h := probOutput_uniformFewTimeView_admissible target
  have hle : admissibleProbability * Pr[= target | signerViewSample] ≤
      Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] := by
    rw [← h]
    split_ifs <;> simp
  calc
    Pr[= target | signerViewSample] =
        admissibleProbability⁻¹ * (admissibleProbability * Pr[= target | signerViewSample]) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel admissibleProbability_pos admissibleProbability_ne_top, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl hle

/-- The averaged forecast of a uniform target (Design R: Fubini through the envelope). -/
theorem expected_fresh_targetShapeEnvelope_le (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : cache (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' target, Pr[= target | ($ᵗ FewTimeView : ProbComp FewTimeView)] *
      targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
        (targetShapeMoments key cache log payload target) groups remaining) ≤
        (Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
            (targetIndexMoments key cache log) groups.card remaining.card := by
  rw [expected_uniformFewTimeView_eq_leafAverage]
  apply mul_le_mul' le_rfl
  rw [← targetShapeEnvelope_lift _ _ _ _ _ _ groups remaining hvalid]
  calc
    _ ≤ ∑ index : Index, targetShapeEnvelope (constRate (Fintype.card Index : ENNReal)⁻¹) reuse (constRate cachedIndexRate)
        queries signings (liftTargetIndexVector (indexPowerMoments key cache log index)) groups remaining := by
      apply Finset.sum_le_sum
      intro index _
      have hfubini := leafAverage_targetShapeEnvelope_le (L := FtsLeaf)
        (F := fun leaves => targetShapeMoments key cache log payload (index, leaves))
        (rate := fun leaves => signerRate (index, leaves)) (arrival := fun leaves => arrivalRate (index, leaves)) reuse
        (targetShapeMoments_shapeLocal key cache log payload index) (signerRate_local index) (arrivalRate_local index)
        (fun coords hne => leafAverage_signerRate_le index coords hne)
        (fun coords hne => leafAverage_arrivalRate_le index coords hne) queries signings groups remaining hvalid
      refine hfubini.trans ?_
      exact targetShapeEnvelope_mono _ _ _ queries signings
        (averagedShape_targetShapeMoments_le key cache log payload hfresh hsigned index) groups remaining hvalid
    _ = _ := by
      have hsum : liftTargetIndexVector (targetIndexMoments key cache log) =
          fun G R => ∑' index : Index, liftTargetIndexVector (indexPowerMoments key cache log index) G R := by
        funext G R
        simp only [liftTargetIndexVector, targetIndexMoments, indexPowerMoments, tsum_fintype]
      rw [hsum, targetShapeEnvelope_tsum, tsum_fintype]

theorem targetShapeMoments_cacheQuery_self_vector (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) (output : HashOutput)
    (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) :
    targetShapeMoments key (before.cacheQuery (tweakableHashInput key.parameter .message payload) output) log payload target =
      targetShapeMoments key before log payload target := by
  funext groups remaining
  exact targetShapeMoments_cacheQuery_unchanged key before log payload target groups remaining _ output hfresh hsigned (Or.inr rfl)

/-- The creation charge of an adversary's fresh message query. -/
theorem expected_cacheQuery_freshTargetEnvelope_le (key : SecretKey) (before : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : before (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter before key.root log) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        targetShapeEnvelope (signerRate (hashOutputFewTimeView output)) reuse (arrivalRate (hashOutputFewTimeView output))
          queries signings
          (targetShapeMoments key (before.cacheQuery (tweakableHashInput key.parameter .message payload) output) log payload
            (hashOutputFewTimeView output)) groups remaining else 0)) ≤
      (Fintype.card Index : ENNReal)⁻¹ *
        targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
          (targetIndexMoments key before log) groups.card remaining.card := by
  simp only [targetShapeMoments_cacheQuery_self_vector key before log payload _ _ hfresh hsigned]
  exact (expected_uniformHashOutput_admissible_weight_le_uniform
    (fun target => targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
      (targetShapeMoments key before log payload target) groups remaining)).trans
    (expected_fresh_targetShapeEnvelope_le key before log payload hfresh hsigned reuse queries signings groups remaining hvalid)

/-- The averaged forecast of a target with the signer's view law. -/
theorem expected_signer_targetShapeEnvelope_le (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : cache (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (reuse : ENNReal) (queries signings : Nat)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    (∑' target, Pr[= target | signerViewSample] *
      targetShapeEnvelope (signerRate target) reuse (arrivalRate target) queries signings
        (targetShapeMoments key cache log payload target) groups remaining) ≤
        admissibleProbability⁻¹ * ((Fintype.card Index : ENNReal)⁻¹ *
          targetIndexEnvelope (Fintype.card Index : ENNReal)⁻¹ reuse cachedIndexRate queries signings
            (targetIndexMoments key cache log) groups.card remaining.card) :=
  (expected_signerViewSample_le _).trans (mul_le_mul' le_rfl
    (expected_fresh_targetShapeEnvelope_le key cache log payload hfresh hsigned reuse queries signings groups remaining hvalid))

end SphincsSecurity.Concrete
