import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CacheIndexMultiplicity
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedTargetIncrement
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ConcreteTargetShapeSigning
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeCardinality
/-!
# The moments of a fresh target, averaged over its leaves

For a fresh target on a fixed index, every factor of its moment vector depends only on the coordinates it
covers: a cached-source group factor on the group, a logged-signing factor on its slot. Since the valid
shapes use disjoint coordinates, the average over the target's (uniform, independent) leaves factorizes,
and each factor averages to at most the number of cached admissible inputs, respectively logged signings,
on the index: a source opens at most fifteen leaves, and the normalization is `2^14/15` per slot.
-/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
open FtsProbeSimulation (messageAnswers)
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetIndexMoments (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec) (power degree : Nat) : ENNReal :=
  ∑ index : Index, cachedIndexMultiplicity key.parameter cache index ^ power *
    ((signingSlotsAtIndex (observedOptionalSigningViews (FtsProbeSimulation.messageAnswers key.parameter cache) key.root log) index).card : ENNReal) ^ degree

/-- The index-level moments of one index. -/
noncomputable def indexPowerMoments (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (index : Index) : TargetIndexVector := fun power degree =>
  cachedIndexMultiplicity key.parameter cache index ^ power *
    ((signingSlotsAtIndex (observedOptionalSigningViews (FtsProbeSimulation.messageAnswers key.parameter cache) key.root log) index).card : ENNReal) ^ degree

theorem normalizedCachedTargetSubsetMatch_local (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (index : Index) (group : Finset IndexGroup) :
    LocalTo group (fun leaves => normalizedCachedTargetSubsetMatch parameter cache targetInput (index, leaves) group) := by
  intro first second hagree
  dsimp only
  simp only [normalizedCachedTargetSubsetMatch_eq_weight]
  congr 1
  funext input source
  split_ifs
  · rfl
  · have h := normalizedSourceSubsetMatch_local index source group first second hagree
    dsimp only at h
    exact h

theorem leafAverage_normalizedCachedTargetSubsetMatch_le (parameter : PublicParameter) (cache : QueryCache HashSpec)
    (targetInput : HashInput) (index : Index) (group : Finset IndexGroup) (hgroup : group.Nonempty) :
    leafAverage (fun leaves => normalizedCachedTargetSubsetMatch parameter cache targetInput (index, leaves) group) ≤
      cachedIndexMultiplicity parameter cache index := by
  simp only [normalizedCachedTargetSubsetMatch_eq_weight, cachedIndexMultiplicity, cacheMessageWeight]
  rw [leafAverage_tsum_plain]
  apply ENNReal.tsum_le_tsum
  intro input
  unfold cacheMessageEntryWeight
  cases cache input with
  | none => rw [leafAverage_const]
  | some output =>
      simp only
      by_cases hmessage : FtsProbeSimulation.MessageHashInput parameter input ∧ Admissible (truncateMessageDigest output)
      · simp only [if_pos hmessage]
        by_cases hsame : input = targetInput
        · simp only [hsame, if_true]
          rw [leafAverage_const]
          exact zero_le
        · simp only [hsame, if_false]
          exact leafAverage_normalizedSourceSubsetMatch_le index _ group hgroup
      · simp only [if_neg hmessage]
        rw [leafAverage_const]

/-- A logged-signing coverage count as a sum of single-slot normalized matches. -/
theorem normalizedTargetLogMatch_eq_sum (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (target : FewTimeView) (tree : IndexGroup) :
    normalizedTargetLogMatch key cache log payload target tree =
      ∑ slot : Fin log.length, (eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log slot).elim 0
        (fun source => normalizedSourceSubsetMatch target source {tree}) := by
  unfold normalizedTargetLogMatch targetTreeMatchCount
  rw [Nat.cast_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro slot _
  cases hview : eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log slot with
  | none => simp
  | some source =>
      simp only [Option.elim_some, normalizedSourceSubsetMatch_singleton, sourceTreeMatch, Option.some.injEq,
        exists_eq_left']
      try (split_ifs <;> simp)

theorem normalizedTargetLogMatch_local (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (index : Index) (tree : IndexGroup) :
    LocalTo {tree} (fun leaves => normalizedTargetLogMatch key cache log payload (index, leaves) tree) := by
  intro first second hagree
  dsimp only
  simp only [normalizedTargetLogMatch_eq_sum]
  apply Finset.sum_congr rfl
  intro slot _
  cases eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log slot with
  | none => rfl
  | some source =>
      have h := normalizedSourceSubsetMatch_local index source {tree} first second hagree
      dsimp only at h
      exact h

theorem leafAverage_normalizedTargetLogMatch_le (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (index : Index) (tree : IndexGroup) :
    leafAverage (fun leaves => normalizedTargetLogMatch key cache log payload (index, leaves) tree) ≤
      ((signingSlotsAtIndex (eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log) index).card : ENNReal) := by
  simp only [normalizedTargetLogMatch_eq_sum]
  rw [leafAverage_sum, signingSlotsAtIndex, Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_le_sum
  intro slot _
  cases hview : eligibleSigningViews (messageAnswers key.parameter cache) key.root payload log slot with
  | none =>
      simp only [Option.elim_none]
      rw [leafAverage_const]
      exact zero_le
  | some source =>
      simp only [Option.elim_some]
      refine (leafAverage_normalizedSourceSubsetMatch_le index source {tree} (Finset.singleton_nonempty tree)).trans ?_
      by_cases hindex : source.1 = index <;> simp [hindex]

theorem targetShapeMoments_shapeLocal (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (index : Index) :
    ShapeLocal (fun leaves => targetShapeMoments key cache log payload (index, leaves)) := by
  intro groups remaining _
  unfold targetShapeMoments normalizedTargetLogProduct
  apply LocalTo.mul
  · have h := LocalTo.prod (L := FtsLeaf) groups id
      (g := fun group leaves => normalizedCachedTargetSubsetMatch key.parameter cache
        (tweakableHashInput key.parameter .message payload) (index, leaves) group)
      (fun group _ => normalizedCachedTargetSubsetMatch_local key.parameter cache _ index group)
    exact h
  · have h := LocalTo.prod (L := FtsLeaf) remaining (fun tree => {tree})
      (g := fun tree leaves => normalizedTargetLogMatch key cache log payload (index, leaves) tree)
      (fun tree _ => normalizedTargetLogMatch_local key cache log payload index tree)
    simpa using h

theorem averagedShape_targetShapeMoments_le (key : SecretKey) (cache : QueryCache HashSpec) (log : QueryLog SigningSpec)
    (payload : HashInput) (hfresh : cache (tweakableHashInput key.parameter .message payload) = none)
    (hsigned : SigningDigestsCached key.parameter cache key.root log) (index : Index) :
    TargetShapeLE (averagedShape (fun leaves => targetShapeMoments key cache log payload (index, leaves)))
      (liftTargetIndexVector (indexPowerMoments key cache log index)) := by
  intro groups remaining hvalid
  unfold averagedShape targetShapeMoments normalizedTargetLogProduct liftTargetIndexVector indexPowerMoments
  have hgroupsLocal : LocalTo (groupCoordinates groups) (fun leaves => ∏ group ∈ groups,
      normalizedCachedTargetSubsetMatch key.parameter cache (tweakableHashInput key.parameter .message payload) (index, leaves) group) :=
    LocalTo.prod (L := FtsLeaf) groups id
      (fun group _ => normalizedCachedTargetSubsetMatch_local key.parameter cache _ index group)
  have hremainingLocal : LocalTo remaining (fun leaves => ∏ tree ∈ remaining,
      normalizedTargetLogMatch key cache log payload (index, leaves) tree) := by
    have h := LocalTo.prod (L := FtsLeaf) remaining (fun tree => {tree})
      (g := fun tree leaves => normalizedTargetLogMatch key cache log payload (index, leaves) tree)
      (fun tree _ => normalizedTargetLogMatch_local key cache log payload index tree)
    simpa using h
  have hdisjoint : Disjoint (groupCoordinates groups) remaining := by
    rw [Finset.disjoint_left]
    intro i hi hr
    obtain ⟨group, hgroup, hig⟩ := mem_groupCoordinates.mp hi
    exact Finset.disjoint_left.mp (hvalid.remaining group hgroup) hig hr
  rw [leafAverage_mul_of_disjoint hgroupsLocal hremainingLocal hdisjoint,
    leafAverage_prod_disjoint groups id
      (fun group _ => normalizedCachedTargetSubsetMatch_local key.parameter cache _ index group)
      (fun first hfirst second hsecond hne => hvalid.disjoint first hfirst second hsecond hne),
    leafAverage_prod_disjoint remaining (fun tree => {tree})
      (fun tree _ => normalizedTargetLogMatch_local key cache log payload index tree)
      (fun first _ second _ hne => Finset.disjoint_singleton.mpr hne)]
  rw [← eligibleSigningViews_fresh_eq_observed key.parameter key.root cache log payload hfresh hsigned]
  apply mul_le_mul'
  · exact Finset.prod_le_pow_card _ _ _ (fun group hgroup =>
      leafAverage_normalizedCachedTargetSubsetMatch_le key.parameter cache _ index group (hvalid.nonempty group hgroup))
  · exact Finset.prod_le_pow_card _ _ _ (fun tree _ => leafAverage_normalizedTargetLogMatch_le key cache log payload index tree)

end SphincsSecurity.Concrete
