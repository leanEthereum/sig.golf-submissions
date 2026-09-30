import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.NormalizedTargetCacheQuery
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetMixedGrowthPolynomial
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetSigningMatchFactors
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) (source : FewTimeView) : ENNReal :=
  ∑ selected ∈ required.powerset.erase ∅, normalizedSourceSubsetMatch target source selected *
    normalizedTargetLogProduct key cache log payload target (required \ selected)

theorem normalizedTargetLogProduct_add_increment (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) (source : FewTimeView) :
    normalizedTargetLogProduct key cache log payload target required + normalizedTargetLogIncrement key cache log payload target required source =
      ∏ tree ∈ required, (normalizedTargetLogMatch key cache log payload target tree + normalizedSourceSubsetMatch target source {tree}) := by
  rw [targetLogProduct_insert_expansion, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset required)]
  simp only [normalizedSourceSubsetMatch, Finset.card_empty, pow_zero, sourceSubsetMatch,
    Finset.prod_empty, Nat.cast_one, one_mul, Finset.sdiff_empty, normalizedTargetLogIncrement, normalizedTargetLogProduct]

theorem normalizedTargetLogProduct_append_none (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (entry : SigningEntry) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hnone : eligibleSigningView? (messageAnswers key.parameter after) key.root payload entry = none) :
    normalizedTargetLogProduct key after (log ++ [entry]) payload target required =
      normalizedTargetLogProduct key before log payload target required := by
  apply Finset.prod_congr rfl
  intro tree _
  have hstep := targetTreeMatchCount_log_append_singleton log entry
    (eligibleSigningView? (messageAnswers key.parameter after) key.root payload) target tree
  change targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload (log ++ [entry])) target tree =
    targetTreeMatchCount (eligibleSigningViews (messageAnswers key.parameter after) key.root payload log) target tree + _ at hstep
  simp only [hnone, reduceCtorEq, false_and, exists_false, if_false, add_zero,
    eligibleSigningViews_cache_stable key before after log payload hcache hsigned] at hstep
  exact congrArg (fun count : Nat => coverNormalization * (count : ENNReal)) hstep

theorem expected_normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) :
    (∑' source, Pr[= source | signerViewSample] * normalizedTargetLogIncrement key cache log payload target required source) =
      ∑ selected ∈ required.powerset.erase ∅,
        signerRate target selected * normalizedTargetLogProduct key cache log payload target (required \ selected) := by
  simp only [normalizedTargetLogIncrement, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply Finset.sum_congr rfl
  intro selected hselected
  simp only [← mul_assoc, ENNReal.tsum_mul_right]
  rfl

theorem cached_normalizedTargetLogIncrement (key : SecretKey) (cache : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (required : Finset IndexGroup) :
    cacheMessageWeight key.parameter (fun input source => if input = tweakableHashInput key.parameter .message payload then 0
      else normalizedTargetLogIncrement key cache log payload target required source) cache =
      ∑ selected ∈ required.powerset.erase ∅,
        normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) target selected *
          normalizedTargetLogProduct key cache log payload target (required \ selected) := by
  have hpoint (input : HashInput) (source : FewTimeView) :
      (if input = tweakableHashInput key.parameter .message payload then 0 else normalizedTargetLogIncrement key cache log payload target required source) =
      ∑ selected ∈ required.powerset.erase ∅,
        (if input = tweakableHashInput key.parameter .message payload then 0 else normalizedSourceSubsetMatch target source selected) *
          normalizedTargetLogProduct key cache log payload target (required \ selected) := by
    unfold normalizedTargetLogIncrement
    split_ifs <;> simp only [zero_mul, Finset.sum_const_zero]
  simp only [hpoint, cacheMessageWeight_sum, cacheMessageWeight_mul_right, normalizedCachedTargetSubsetMatch_eq_weight]

end SphincsSecurity.Concrete
