import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualBudget
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting UniformTableCompletion
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

noncomputable def initialMemory (words : OtsReferenceWords) (exposedValues : InitialPublicLabels words) : Memory :=
  ⟨⟨fun _ => none, keygenHashCost, 0⟩, ⟨fun _ _ _ => False, initialKnown words exposedValues⟩, [], [], []⟩

noncomputable def initialState (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) : State inputs :=
  ⟨initialAllowed words exposedValues, fun _ => none, initialMemory words exposedValues⟩

noncomputable def initialContext (parameter : PublicParameter) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs parameter ⊆ inputs) (auxiliary : ReferenceAuxiliary inputs)
    (hauxiliary : auxiliary ∈ (referenceAuxiliarySample inputs).support) (dummy : OtsReferenceWords)
    (exposedValues : InitialPublicLabels (referenceFamilyWords auxiliary.selections dummy))
    (high : CanonicalGraphHighHalves) (labels : Labels) : Context inputs where
  key := ⟨parameter, knownRoot (initialKnown (referenceFamilyWords auxiliary.selections dummy) exposedValues),
    coordinateOtsSecrets labels, coordinateFtsSecrets labels, graphTop (coordinateGraphLabels labels high)⟩
  graph := coordinateGraphLabels labels high
  auxiliary := auxiliary
  encoding := hencoding
  auxiliary_valid := hauxiliary
  dummy := dummy
  publicReplies := coordinateGraphLabels (initialKnown (referenceFamilyWords auxiliary.selections dummy) exposedValues) high
  top_graph := fun _ _ _ _ => rfl

theorem initialState_rowsCovered (inputs : Finset HashInput) (words : OtsReferenceWords)
    (exposedValues : InitialPublicLabels words) : ResidualByteFrontend.RowsCovered inputs (project (initialState inputs words exposedValues)) := by
  intro input answer hanswer
  cases hanswer

/-- The table key generation builds under the context's oracle. -/
noncomputable abbrev Context.keygenTop {inputs : Finset HashInput} (context : Context inputs) : Nat → Nat → Digest :=
  honestTop context.oracle context.key.parameter (context.key.otsSecret topLayer rootTree)

theorem Context.keygen_record {inputs : Finset HashInput} (context : Context inputs)
    (_hroot : context.key.root = canonicalGraphRoot context.graph) :
    fixedBoundaryRun context.key.parameter context.oracle
      (liftM (keygenTable context.key.parameter (context.key.otsSecret topLayer rootTree) :
        OracleComp HashSpec (Nat → Nat → Digest))) =
        pure (context.keygenTop, (FreeMonoid.of none) ^ keygenHashCost) := by
  rw [fixedBoundaryRun_lift_hash, boundaryEval_keygen]
  rfl

theorem Context.keygenTop_root {inputs : Finset HashInput} (context : Context inputs)
    (hroot : context.key.root = canonicalGraphRoot context.graph) :
    context.keygenTop (layerHeight topLayer) 0 = context.key.root := by
  rw [Context.keygenTop, honestTop_root, hroot]
  have h := canonicalGraphLabels_root context.key.parameter context.key.otsSecret context.key.ftsSecret context.oracle
  unfold Context.oracle at h ⊢
  rw [canonicalGraphLabels_programmedHash] at h
  rw [h]
  rfl

theorem Context.keygenTop_region {inputs : Finset HashInput} (context : Context inputs) :
    TopRegionEq (m := OracleComp HashSpec) (fun level nodeIdx => pure (context.keygenTop level nodeIdx))
      (fun level nodeIdx => pure (context.key.top level nodeIdx)) := by
  intro level hlevel nodeIdx hnodeIdx
  have h := context.keyTopHonest level hlevel nodeIdx hnodeIdx
  rw [evalWithAnswerFn_pure] at h
  show pure _ = pure _
  rw [h, Context.keygenTop, honestTop, eval_keygenTable context.oracle _ _ level (by
    change level ≤ maxLayerHeight; omega) nodeIdx hnodeIdx]

/-- The game after key generation under the context's oracle is the game with the context's key. -/
theorem Context.gameRest_keygen {inputs : Finset HashInput} (context : Context inputs)
    (hroot : context.key.root = canonicalGraphRoot context.graph) (adversary : Adversary) :
    gameRest scheme adversary ⟨context.keygenTop (layerHeight topLayer) 0, context.key.parameter⟩
      ⟨context.key.parameter, context.keygenTop (layerHeight topLayer) 0, context.key.otsSecret,
        context.key.ftsSecret, context.keygenTop⟩ =
      gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key := by
  rw [context.keygenTop_root hroot]
  exact gameRest_congr_top adversary _ _ _ rfl rfl rfl rfl context.keygenTop_region

theorem Context.rest_queryBound {inputs : Finset HashInput} (context : Context inputs)
    (hroot : context.key.root = canonicalGraphRoot context.graph)
    (hparameter : context.key.parameter ∈ support sampleParameter) (adversary : Adversary) (q : Nat)
    (hq : HasHashQueryBound scheme adversary q) :
    keygenHashCost ≤ q ∧ FixedHashQueryBound context.oracle
      (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key) (q - keygenHashCost) := by
  have hots : context.key.otsSecret ∈ support sampleOtsSecrets := by
    unfold sampleOtsSecrets
    exact otsSecretsSampleableType.mem_support_selectElem _
  have hfts : context.key.ftsSecret ∈ support sampleFtsSecrets := by
    unfold sampleFtsSecrets
    exact ftsSecretsSampleableType.mem_support_selectElem _
  have hbound := hashQueryBound_fixed context.oracle _ q
    (hashQueryBound_gameAfterSecrets adversary q hq hparameter hots hfts)
  rw [gameAfterSecrets] at hbound
  have hresult : 𝒮[fixedBoundaryRun context.key.parameter context.oracle
      (liftM (keygenTable context.key.parameter (context.key.otsSecret topLayer rootTree) :
        OracleComp HashSpec (Nat → Nat → Digest)))]
        (context.keygenTop, (FreeMonoid.of none) ^ keygenHashCost) ≠ 0 := by
    rw [context.keygen_record hroot, evalSPMF_pure, SPMF.pure_apply_self]
    exact one_ne_zero
  have h := fixedBoundaryRun_bind_query_bound context.key.parameter context.oracle _ _ q hbound _ hresult
  simp only [SigningBoundaryTrace.hashCalls_pow_none] at h
  rw [context.gameRest_keygen hroot adversary] at h
  exact h

end SphincsSecurity.Concrete.RetainedResidual
