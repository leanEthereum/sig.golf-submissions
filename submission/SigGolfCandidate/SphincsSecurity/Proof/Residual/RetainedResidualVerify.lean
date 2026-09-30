import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualRecovery
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  signDigestLoop sequenceFin chainWalk
set_option backward.isDefEq.respectTransparency false

theorem Context.root_value {inputs : Finset HashInput} (context : Context inputs) :
    canonicalGraphRoot context.graph = honestNode context.oracle context.key.parameter topLayer rootTree
      (context.key.otsSecret topLayer rootTree) (layerHeight topLayer) 0 := by
  rw [← context.graph_eq, canonicalGraphLabels_root]
  rfl

theorem Compatible.layer_frame_reference {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (index : Index) (signature : Signature) (lay : Layer)
    (message target leafValue : Digest)
    (hword : OtsCode.Valid (context.words lay (treeIndexAt index lay) (leafIndexAt index lay)))
    (hframe : LayerFrame context.oracle memory.external.cache context.key.parameter index signature lay message target leafValue)
    (hfold : foldValue context.oracle context.key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (signaturePath signature lay) leafValue (layerHeight lay) =
      honestNode context.oracle context.key.parameter lay (treeIndexAt index lay)
        (context.key.otsSecret lay (treeIndexAt index lay)) (layerHeight lay) 0) :
    message = evalWithAnswerFn context.oracle (layerMessage context.key index lay) ∧
      HonestLayerOpening context.oracle context.key.parameter context.key.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay) (evalWithAnswerFn context.oracle (layerMessage context.key index lay))
        (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay) ∧
      CachedRun memory.external.cache context.oracle (otsLeafAttempt context.key.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn context.oracle (layerMessage context.key index lay))
        (signature.counter lay) (signature.chainValue lay)) := by
  have hhonest := hcompatible.layer_honest lay (treeIndexAt index lay) (leafIndexAt index lay)
    (leafIndexAt_lt index lay) message (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay)
    leafValue hframe.1 hfold hframe.2.2.1 hframe.2.2.2.1
  obtain ⟨_, _, hmessage, _⟩ := hcompatible.layer_reference lay (treeIndexAt index lay) (leafIndexAt index lay)
    message (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay) hword hhonest hframe.2.2.1
  have heq := hmessage.trans (context.layer_message index lay)
  refine ⟨heq, ?_⟩
  rw [← heq]
  exact ⟨hhonest, hframe.2.2.1⟩

theorem Compatible.hypertree_honest {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (hdummy : ∀ lay tree leaf, OtsCode.Valid (context.dummy lay tree leaf))
    (hroot : context.key.root = canonicalGraphRoot context.graph) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (signature : Signature)
    (hverify : evalWithAnswerFn context.oracle
      (verifyLayers context.key.parameter index signature numLayers
        (evalWithAnswerFn context.oracle (ftsRecover context.key.parameter index leaves signature.ftsSecret signature.ftsPath))) =
      some context.key.root)
    (hlayersRun : CachedRun memory.external.cache context.oracle
      (verifyLayers context.key.parameter index signature numLayers
        (evalWithAnswerFn context.oracle (ftsRecover context.key.parameter index leaves signature.ftsSecret signature.ftsPath))))
    (hftsRun : CachedRun memory.external.cache context.oracle
      (ftsRecover context.key.parameter index leaves signature.ftsSecret signature.ftsPath)) :
    FullyHonestOpening context.oracle memory.external.cache context.key index leaves signature ∧
      ∀ tree, memory.routing.disclosed index tree (leaves (ftsIndexOf tree)) := by
  let ftsPublicKey := evalWithAnswerFn context.oracle
    (ftsRecover context.key.parameter index leaves signature.ftsSecret signature.ftsPath)
  have hwalk := hypertree_walk (f := context.oracle) (cache := memory.external.cache) context.key index signature
    (fun lay => HonestLayerOpening context.oracle context.key.parameter context.key.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay) (evalWithAnswerFn context.oracle (layerMessage context.key index lay))
        (signature.counter lay) (signature.chainValue lay) (signaturePath signature lay) ∧
      CachedRun memory.external.cache context.oracle (otsLeafAttempt context.key.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn context.oracle (layerMessage context.key index lay))
        (signature.counter lay) (signature.chainValue lay)))
    (fun lay message leafValue hframe hfold =>
      hcompatible.layer_frame_reference index signature lay message context.key.root leafValue
        (context.words_valid hdummy _ _ _) hframe hfold)
    (by rw [hroot, context.root_value]) ftsPublicKey hverify hlayersRun
  have hftsKey : ftsPublicKey = honestFtsKey context.oracle context.key.parameter index (context.key.ftsSecret index) := by
    rw [hwalk.2, layerMessage_bottomLayer]
    rfl
  have hftsHonest := hcompatible.ftsRecover_honest index leaves signature.ftsSecret signature.ftsPath hftsKey hftsRun
  exact ⟨⟨hwalk.1, hftsHonest, hftsRun⟩,
    hcompatible.ftsRecover_disclosed index leaves signature.ftsSecret signature.ftsPath hftsKey hftsRun⟩

theorem Compatible.verify_honest {inputs : Finset HashInput} {context : Context inputs} {memory : Memory}
    (hcompatible : Compatible context memory) (hdummy : ∀ lay tree leaf, OtsCode.Valid (context.dummy lay tree leaf))
    (hroot : context.key.root = canonicalGraphRoot context.graph) (message : Message) (signature : Signature)
    (hverify : evalWithAnswerFn context.oracle (verify ⟨context.key.root, context.key.parameter⟩ message signature) = true)
    (hrun : CachedRun memory.external.cache context.oracle (verify ⟨context.key.root, context.key.parameter⟩ message signature)) :
    ∃ digest, evalWithAnswerFn context.oracle (messageDigest context.key.parameter context.key.root message signature.randomness) = digest ∧
      CachedRun memory.external.cache context.oracle (messageDigest context.key.parameter context.key.root message signature.randomness) ∧
      Admissible digest ∧
      FullyHonestOpening context.oracle memory.external.cache context.key (digestIndex digest) (digestLeaves digest) signature ∧
      ∀ tree, memory.routing.disclosed (digestIndex digest) tree (digestLeaves digest (ftsIndexOf tree)) := by
  obtain ⟨digest, hdigest, hdigestRun, hadmissible, hlayers, hftsRun, hlayersRun⟩ :=
    verify_extract ⟨context.key.root, context.key.parameter⟩ message signature hverify hrun
  exact ⟨digest, hdigest, hdigestRun, hadmissible,
    hcompatible.hypertree_honest hdummy hroot (digestIndex digest) (digestLeaves digest) signature hlayers hlayersRun hftsRun⟩

end SphincsSecurity.Concrete.RetainedResidual
