import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferenceLayerWitness
import SigGolfCandidate.SphincsSecurity.Proof.Reference.VerifierTraceDescent
namespace SphincsSecurity.Concrete.OtsVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] chainWalk sequenceFin canonicalEncodingInputs canonicalGraphInputs instFintypePosition

variable (f : QueryImpl HashSpec Id) (key : SecretKey) (words : OtsReferenceWords)
  (messages : EncodingPosition → Digest) (selections : ReferenceFamily)

def LayerException (trace : Trace) : Prop :=
  EncodingOutputMatch key.parameter words messages selections trace ∨
    ∃ lay tree leaf, TreeOutputMatch f key.parameter lay tree (key.otsSecret lay tree) trace ∨
      LeafOutputMatch f key.parameter lay tree leaf (key.otsSecret lay tree leaf) trace ∨
        ChainException f key.parameter words lay tree leaf (key.otsSecret lay tree leaf) trace

def ReferenceLayerOpening (index : Index) (signature : Signature) (lay : Layer) : Prop :=
  ∃ selected, selections ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = some selected ∧
    signature.counter lay = BitVec.ofNat counterBits selected.1.val ∧
    evalWithAnswerFn f (encodeAttempt key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage key index lay)) (signature.counter lay)) = some (words lay (treeIndexAt index lay) (leafIndexAt index lay)) ∧
    (∀ chain, signature.chainValue lay chain = frontier f key.parameter words lay (treeIndexAt index lay) (leafIndexAt index lay)
      (key.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay)) chain) ∧
    ∀ level, level < layerHeight lay → signaturePath signature lay level =
      honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay)) level
        (Nat.xor ((leafIndexAt index lay).val / 2 ^ level) 1)

theorem layer_frame_reference (index : Index) (signature : Signature) (lay : Layer) (message target leafValue : Digest) (trace : Trace)
    (hvalid : OtsCode.Valid (words lay (treeIndexAt index lay) (leafIndexAt index lay)))
    (hmessages : messages ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = evalWithAnswerFn f (layerMessage key index lay))
    (hclean : ¬LayerException f key words messages selections trace)
    (hframe : LayerFrame f (recordedCache f trace) key.parameter index signature lay message target leafValue)
    (hfold : foldValue f key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) (signaturePath signature lay) leafValue (layerHeight lay) =
      honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay)) (layerHeight lay) 0) :
    message = evalWithAnswerFn f (layerMessage key index lay) ∧ ReferenceLayerOpening f key words selections index signature lay := by
  cases hencode : evalWithAnswerFn f (encodeAttempt key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message (signature.counter lay)) with
  | none =>
      have hots := hframe.1
      simp only [otsLeafAttempt, evalWithAnswerFn_bind, hencode, evalWithAnswerFn_pure, reduceCtorEq] at hots
  | some candidate =>
      have h := layer_reference_classification f key.parameter words messages selections lay (treeIndexAt index lay)
        (key.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay) (leafIndexAt_lt index lay) (signaturePath signature lay)
        message (signature.counter lay) (signature.chainValue lay) candidate leafValue trace hvalid hencode hframe.1 hfold
        ((recordedCache_run_iff f trace _).mp hframe.2.2.1) ((recordedCache_run_iff f trace _).mp hframe.2.2.2.1)
      rcases h with ⟨selected, hs, hm, hc, hw, hv, hp⟩ | ht | hl | hc | he
      · refine ⟨hm.trans hmessages, selected, hs, hc, ?_, hv, hp⟩
        rw [← hm.trans hmessages, ← hw]
        exact hencode
      · exact False.elim (hclean (Or.inr ⟨lay, treeIndexAt index lay, leafIndexAt index lay, Or.inl ht⟩))
      · exact False.elim (hclean (Or.inr ⟨lay, treeIndexAt index lay, leafIndexAt index lay, Or.inr (Or.inl hl)⟩))
      · exact False.elim (hclean (Or.inr ⟨lay, treeIndexAt index lay, leafIndexAt index lay, Or.inr (Or.inr hc)⟩))
      · exact False.elim (hclean (Or.inl he))

theorem hypertree_reference (index : Index) (leaves : IndexGroup → FtsLeaf) (signature : Signature) (trace : Trace)
    (hvalid : ∀ lay, OtsCode.Valid (words lay (treeIndexAt index lay) (leafIndexAt index lay)))
    (hmessages : ∀ lay, messages ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = evalWithAnswerFn f (layerMessage key index lay))
    (hroot : key.root = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) (layerHeight topLayer) 0)
    (hclean : ¬LayerException f key words messages selections trace)
    (hverify : evalWithAnswerFn f (verifyLayers key.parameter index signature numLayers (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath))) = some key.root)
    (hrun : ContainsRun f trace (verifyLayers key.parameter index signature numLayers (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)))) :
    (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)) = honestFtsKey f key.parameter index (key.ftsSecret index) ∧
      ∀ lay, ReferenceLayerOpening f key words selections index signature lay ∧
        CachedRun (recordedCache f trace) f (otsLeafAttempt key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (evalWithAnswerFn f (layerMessage key index lay)) (signature.counter lay) (signature.chainValue lay)) := by
  have hwalk := hypertree_walk (f := f) (cache := recordedCache f trace) key index signature
    (fun lay => ReferenceLayerOpening f key words selections index signature lay ∧
      CachedRun (recordedCache f trace) f (otsLeafAttempt key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage key index lay)) (signature.counter lay) (signature.chainValue lay)))
    (fun lay message leafValue hframe hfold => by
      have h := layer_frame_reference f key words messages selections index signature lay message key.root leafValue trace
        (hvalid _) (hmessages _) hclean hframe hfold
      refine ⟨h.1, h.2, ?_⟩
      rw [← h.1]
      exact hframe.2.2.1)
    hroot _ hverify hrun.cached
  refine ⟨?_, hwalk.1⟩
  rw [hwalk.2, layerMessage_bottomLayer]
  rfl

theorem hypertree_classification (index : Index) (leaves : IndexGroup → FtsLeaf) (signature : Signature) (trace : Trace)
    (hvalid : ∀ lay, OtsCode.Valid (words lay (treeIndexAt index lay) (leafIndexAt index lay)))
    (hmessages : ∀ lay, messages ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = evalWithAnswerFn f (layerMessage key index lay))
    (hroot : key.root = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) (layerHeight topLayer) 0)
    (hverify : evalWithAnswerFn f (verifyLayers key.parameter index signature numLayers (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath))) = some key.root)
    (hrun : ContainsRun f trace (verifyLayers key.parameter index signature numLayers (evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)))) :
    ((evalWithAnswerFn f (ftsRecover key.parameter index leaves signature.ftsSecret signature.ftsPath)) = honestFtsKey f key.parameter index (key.ftsSecret index) ∧ ∀ lay, ReferenceLayerOpening f key words selections index signature lay ∧
        CachedRun (recordedCache f trace) f (otsLeafAttempt key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (evalWithAnswerFn f (layerMessage key index lay)) (signature.counter lay) (signature.chainValue lay))) ∨
      LayerException f key words messages selections trace := by
  by_cases h : LayerException f key words messages selections trace
  · exact Or.inr h
  · exact Or.inl (hypertree_reference f key words messages selections index leaves signature trace hvalid hmessages hroot h hverify hrun)

end SphincsSecurity.Concrete.OtsVerifierWitness
