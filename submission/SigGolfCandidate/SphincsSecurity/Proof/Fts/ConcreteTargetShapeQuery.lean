import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ConcreteTargetShapeSigning
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeEnvelope
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem normalizedTargetLogProduct_cache_stable (key : SecretKey) (before after : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView) (remaining : Finset IndexGroup)
    (hcache : before ≤ after) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    normalizedTargetLogProduct key after log payload target remaining = normalizedTargetLogProduct key before log payload target remaining := by
  simp only [normalizedTargetLogProduct, normalizedTargetLogMatch, eligibleSigningViews_cache_stable key before after log payload hcache hsigned]

theorem sourceSubsetMatch_family (target source : FewTimeView) (family : Finset (Finset IndexGroup)) :
    (∏ group ∈ family, sourceSubsetMatch target source group) =
      sourceSubsetMatch target source (groupCoordinates family) := by
  induction family using Finset.induction_on with
  | empty => simp [sourceSubsetMatch, groupCoordinates]
  | @insert group family hnot ih =>
      rw [Finset.prod_insert hnot, ih, sourceSubsetMatch_mul, groupCoordinates_insert]

theorem normalizedSourceSubsetMatch_family (target source : FewTimeView) (family : Finset (Finset IndexGroup))
    (hdisjoint : (family : Set (Finset IndexGroup)).PairwiseDisjoint id) :
    (∏ group ∈ family, normalizedSourceSubsetMatch target source group) =
      normalizedSourceSubsetMatch target source (groupCoordinates family) := by
  simp only [normalizedSourceSubsetMatch, Finset.prod_mul_distrib, ← Nat.cast_prod,
    Finset.prod_pow_eq_pow_sum, sourceSubsetMatch_family]
  congr 2
  exact (Finset.card_biUnion hdisjoint).symm

theorem TargetShapeValid.pairwiseDisjoint {groups family : Finset (Finset IndexGroup)} {remaining : Finset IndexGroup}
    (hvalid : TargetShapeValid groups remaining) (hfamily : family ⊆ groups) :
    (family : Set (Finset IndexGroup)).PairwiseDisjoint id :=
  fun first hfirst second hsecond hne => hvalid.disjoint first (hfamily hfirst) second (hfamily hsecond) hne

theorem prod_add_family_expand (groups : Finset (Finset IndexGroup)) (a x : Finset IndexGroup → ENNReal) (c : ENNReal) :
    (∏ group ∈ groups, (a group + x group)) * c =
      ∑ removed ∈ groups.powerset, (∏ group ∈ removed, x group) * ((∏ group ∈ groups \ removed, a group) * c) := by
  rw [show (∏ group ∈ groups, (a group + x group)) = ∏ group ∈ groups, (x group + a group) by
    simp only [add_comm], Finset.prod_add, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro _ _
  ring

theorem expected_cacheQuery_targetShapeMoments (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining)
    (input : HashInput) (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hmessage : FtsProbeSimulation.MessageHashInput key.parameter input) (hne : input ≠ tweakableHashInput key.parameter .message payload) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      targetShapeMoments key (before.cacheQuery input output) log payload target groups remaining) =
        targetShapeQuery (arrivalRate target) (targetShapeMoments key before log payload target) groups remaining := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  have hexpand (output : HashOutput) :
      targetShapeMoments key (before.cacheQuery input output) log payload target groups remaining =
        ∑ removed ∈ groups.powerset, (∏ group ∈ removed,
          (if Admissible (truncateMessageDigest output) then
            normalizedSourceSubsetMatch target (hashOutputFewTimeView output) group else 0)) *
          targetShapeMoments key before log payload target (groups \ removed) remaining := by
    simp only [targetShapeMoments,
      normalizedTargetLogProduct_cache_stable key before _ log payload target _ (QueryCache.le_cacheQuery before hfresh) hsigned,
      normalizedCachedTargetSubsetMatch_cacheQuery key.parameter before _ target _ input output hfresh hmessage hne]
    exact prod_add_family_expand groups _ _ _
  have hfamily (output : HashOutput) (removed : Finset (Finset IndexGroup)) (hremoved : removed ∈ groups.powerset.erase ∅) :
      (∏ group ∈ removed, (if Admissible (truncateMessageDigest output) then
          normalizedSourceSubsetMatch target (hashOutputFewTimeView output) group else 0)) =
        if Admissible (truncateMessageDigest output) then
          normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groupCoordinates removed) else 0 := by
    by_cases hadmissible : Admissible (truncateMessageDigest output)
    · simp only [hadmissible, if_true]
      exact normalizedSourceSubsetMatch_family target _ removed
        (hvalid.pairwiseDisjoint (Finset.mem_powerset.mp (Finset.mem_erase.mp hremoved).2))
    · simp only [hadmissible, if_false]
      obtain ⟨group, hgroup⟩ := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hremoved).1
      exact Finset.prod_eq_zero hgroup rfl
  simp only [hexpand, Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable), ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset groups)]
  simp only [Finset.prod_empty, one_mul, Finset.sdiff_empty]
  unfold targetShapeQuery targetArrivalStep
  congr 1
  · rw [ENNReal.tsum_mul_right, hmass, one_mul]
  · apply Finset.sum_congr rfl
    intro removed hremoved
    simp only [← mul_assoc, ENNReal.tsum_mul_right]
    congr 1
    rw [← expected_hash_normalizedSourceSubsetMatch target (groupCoordinates removed)]
    apply tsum_congr
    intro output
    rw [hfamily output removed hremoved]

theorem targetShapeMoments_cacheQuery_unchanged (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (input : HashInput) (output : HashOutput)
    (hfresh : before input = none) (hsigned : SigningDigestsCached key.parameter before key.root log)
    (hskip : ¬ FtsProbeSimulation.MessageHashInput key.parameter input ∨ input = tweakableHashInput key.parameter .message payload) :
    targetShapeMoments key (before.cacheQuery input output) log payload target groups remaining =
      targetShapeMoments key before log payload target groups remaining := by
  simp only [targetShapeMoments,
    normalizedTargetLogProduct_cache_stable key before _ log payload target remaining (QueryCache.le_cacheQuery before hfresh) hsigned]
  congr 1
  apply Finset.prod_congr rfl
  intro group _
  rcases hskip with hmessage | rfl
  · simp only [normalizedCachedTargetSubsetMatch, cachedTargetSubsetMatch_cacheQuery key.parameter before _ target group input output hfresh,
      hmessage, false_and, if_false, add_zero]
  · simp only [normalizedCachedTargetSubsetMatch, cachedTargetSubsetMatch_cacheQuery_self key.parameter before _ target group output hfresh]

theorem expected_randomOracle_targetShapeMoments_le (key : SecretKey) (before : QueryCache HashSpec)
    (log : QueryLog SigningSpec) (payload : HashInput) (target : FewTimeView)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining)
    (input : HashInput) (hsigned : SigningDigestsCached key.parameter before key.root log) :
    (∑' result, Pr[= result | (randomOracle input).run before] *
      targetShapeMoments key result.2 log payload target groups remaining) ≤
        targetShapeQuery (arrivalRate target)
          (targetShapeMoments key before log payload target) groups remaining := by
  have hmass : (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)]) = 1 := tsum_probOutput_eq_one' (by simp)
  by_cases hfresh : before input = none
  · rw [randomOracle, QueryImpl.withCaching_run_none _ hfresh, tsum_probOutput_map_mul]
    change (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      targetShapeMoments key (before.cacheQuery input output) log payload target groups remaining) ≤ _
    by_cases hmessage : FtsProbeSimulation.MessageHashInput key.parameter input
    · by_cases heq : input = tweakableHashInput key.parameter .message payload
      · simp only [targetShapeMoments_cacheQuery_unchanged key before log payload target groups remaining input _ hfresh hsigned (Or.inr heq),
          ENNReal.tsum_mul_right, hmass, one_mul]
        exact le_self_add
      · exact (expected_cacheQuery_targetShapeMoments key before log payload target groups remaining hvalid input hfresh hsigned hmessage heq).le
    · simp only [targetShapeMoments_cacheQuery_unchanged key before log payload target groups remaining input _ hfresh hsigned (Or.inl hmessage),
        ENNReal.tsum_mul_right, hmass, one_mul]
      exact le_self_add
  · obtain ⟨output, houtput⟩ := Option.ne_none_iff_exists'.mp hfresh
    rw [randomOracle, QueryImpl.withCaching_run_some _ houtput, tsum_probOutput_pure_mul]
    exact le_self_add

end SphincsSecurity.Concrete
