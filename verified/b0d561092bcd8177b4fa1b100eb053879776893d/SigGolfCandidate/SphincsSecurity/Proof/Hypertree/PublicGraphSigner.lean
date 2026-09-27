import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingFamilyOracleSplit
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.PublicGraphOpenings
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] instFintypePosition boundaryEval referenceEncodingSearch

def publicSignLayer (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (index : Index) (lay : Layer) : Option LayerPart × Nat :=
  let search := referenceSelectionResult (selections ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩)
  match search.1 with
  | none => (none, search.2)
  | some (counter, word) =>
      (some (counter, knownFrontier known words lay (treeIndexAt index lay) (leafIndexAt index lay),
        knownTreePath known lay (treeIndexAt index lay) (leafIndexAt index lay)),
        search.2 + if lay = topLayer then OtsCode.signingSteps word else treeNodeHashCost (layerHeight lay))

/-- A signature known up to the PORS opening: the randomizer, the PORS tree's nodes as the public labels know
them, and the layers. -/
structure PublicSigningPlan where
  randomness : Randomness
  ftsNodes : Nat → Nat → Digest
  parts : Layer → LayerPart

/-- The honest PORS opening with the secrets given per digest slot (`secrets r` is the secret of leaf
`leaves r`). -/
def honestFtsOfSlots (leaves : IndexGroup → FtsLeaf) (secrets : IndexGroup → Digest) (node : Nat → Nat → Digest) :
    FtsSignature :=
  { honestFts leaves (fun _ => 0) node with
    secrets := fun s => secrets ((sortedSlots leaves).getD s.val ⟨0, by decide⟩) }

theorem honestFtsOfSlots_secrets (leaves : IndexGroup → FtsLeaf) (secrets : IndexGroup → Digest)
    (node : Nat → Nat → Digest) (s : Fin ftsOpenings) :
    (honestFtsOfSlots leaves secrets node).secrets s = secrets ((sortedSlots leaves).getD s.val ⟨0, by decide⟩) :=
  rfl

theorem honestFtsOfSlots_comp (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest)
    (node : Nat → Nat → Digest) :
    honestFtsOfSlots leaves (fun slot => secret (leaves slot)) node = honestFts leaves secret node := rfl

/-- The signature, once the digest's leaves and the opened leaves' secrets (per digest slot) are supplied. -/
def PublicSigningPlan.finish (plan : PublicSigningPlan) (leaves : IndexGroup → FtsLeaf) (secrets : IndexGroup → Digest) :
    Signature where
  randomness := plan.randomness
  fts := honestFtsOfSlots leaves secrets plan.ftsNodes
  layers := fun lay => LayerSignature.ofPadded lay (plan.parts lay)

def publicSignPlan (known : Labels) (words : OtsReferenceWords) (selections : ReferenceFamily)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) : Option PublicSigningPlan × Nat :=
  let layers := fun lay => publicSignLayer known words selections index lay
  ((sequenceFin (m := Option) (fun lay => (layers lay).1)).map (fun parts =>
      ⟨randomness, knownFtsNodes known index, parts⟩),
    ftsOpenHashCost + sequenceLayersHashCost layers)

variable (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords)
  (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
  (hagrees : PublicAgreement words disclosed known
    (CanonicalCoordinate.value key.otsSecret key.ftsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)))

include hagrees in
theorem frontierSignLayer_eq_public (index : Index) (lay : Layer) :
    frontierSignLayer key.parameter f key.ftsSecret words
        (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words) index lay =
      publicSignLayer known words (referenceTableSelection key f) index lay := by
  have hfrontier : IsSigningFrontier key f words
      (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words) := by
    rw [canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f words key.root key.top]
    exact isSigningFrontier_canonical key f words
  have hsearch : frontierLayerSearch key.parameter f key.ftsSecret words
      (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words) index lay =
        referenceSelectionResult (referenceTableSelection key f ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩) := by
    rw [referenceSelectionResult_eq_search, canonicalEncodingSearch_at, frontierLayerSearch,
      eval_frontierLayerMessage key f words _ hfrontier index lay]
  have hpath := eval_frontierTreePath key.parameter f lay (treeIndexAt index lay)
    (key.otsSecret lay (treeIndexAt index lay)) (words lay (treeIndexAt index lay))
    (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words lay
      (treeIndexAt index lay)) (hfrontier lay (treeIndexAt index lay)) (leafIndexAt index lay)
  rw [← knownTreePath_eq key.parameter key.otsSecret key.ftsSecret f words disclosed known hagrees] at hpath
  simp only [frontierSignLayer, publicSignLayer, hsearch, hpath,
    knownFrontier_eq key.otsSecret key.ftsSecret _ words disclosed known hagrees]
  rfl

include hagrees in
theorem frontierSignAfterDigest_eq_publicPlan (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    frontierSignAfterDigest key.parameter f key.ftsSecret words
        (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words)
        randomness index leaves =
      ((publicSignPlan known words (referenceTableSelection key f) randomness index leaves).1.map
        (fun plan => plan.finish leaves (fun slot => key.ftsSecret index porsTree (leaves slot))),
        (publicSignPlan known words (referenceTableSelection key f) randomness index leaves).2) := by
  simp only [frontierSignAfterDigest, publicSignPlan,
    frontierSignLayer_eq_public key f words disclosed known hagrees,
    ← knownFtsOpening_eq key.parameter key.otsSecret key.ftsSecret f words disclosed known hagrees,
    Option.map_map, Function.comp_def, PublicSigningPlan.finish, honestFtsOfSlots_comp]

theorem boundaryEval_signAfterDigest_public (htop : KeyTopHonest f key) (dummy : OtsReferenceWords)
    (hagrees : PublicAgreement (canonicalReferenceWords key f dummy) disclosed known
      (CanonicalCoordinate.value key.otsSecret key.ftsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)))
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    boundaryEval key.parameter f (signAfterDigest key randomness index leaves) =
      ((publicSignPlan known (canonicalReferenceWords key f dummy) (referenceTableSelection key f) randomness index leaves).1.map
        (fun plan => plan.finish leaves (fun slot => key.ftsSecret index porsTree (leaves slot))),
        (FreeMonoid.of none) ^
          (publicSignPlan known (canonicalReferenceWords key f dummy) (referenceTableSelection key f) randomness index leaves).2) := by
  have h := frontierSignAfterDigest_eq_publicPlan key f (canonicalReferenceWords key f dummy) disclosed known hagrees randomness index leaves
  rw [canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f _ key.root key.top] at h
  rw [boundaryEval_signAfterDigest_canonical key f htop dummy, h]

end SphincsSecurity.Concrete
