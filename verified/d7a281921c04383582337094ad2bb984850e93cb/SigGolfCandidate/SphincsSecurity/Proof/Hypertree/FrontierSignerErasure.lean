import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.FrontierSigningEvaluation
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.FrontierTreeEvaluation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval sequenceFin chainWalk referenceEncodingSearch

abbrev OtsReferenceWords := Layer → TreeIndex → LeafIndex → Encoding
abbrev OtsFrontierValues := Layer → TreeIndex → LeafIndex → ChainIndex → Digest

def IsSigningFrontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) : Prop :=
  ∀ lay tree, IsOtsFrontier key.parameter f lay tree (key.otsSecret lay tree) (words lay tree) (frontier lay tree)

def frontierLayerMessage (parameter : PublicParameter) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (index : Index) (lay : Layer) :
    OracleComp HashSpec Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    frontierTreeNode parameter below (treeIndexAt index below)
      (words below (treeIndexAt index below)) (frontier below (treeIndexAt index below)) (layerHeight below) 0
  else ftsKey parameter index (ftsSecret index)

def frontierLayerSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) : Option (Counter × Encoding) × Nat :=
  referenceEncodingSearch parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
    (evalWithAnswerFn f (frontierLayerMessage parameter ftsSecret words frontier index lay)) encodingAttemptLimit 0

def FrontierReferenceWord (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) : Prop :=
  ∀ counter word, (frontierLayerSearch parameter f ftsSecret words frontier index lay).1 = some (counter, word) →
    word = words lay (treeIndexAt index lay) (leafIndexAt index lay)

def frontierSignLayer (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (index : Index) (lay : Layer) : Option LayerPart × Nat :=
  let search := frontierLayerSearch parameter f ftsSecret words frontier index lay
  match search.1 with
  | none => (none, search.2)
  | some (counter, _) =>
      (some (counter, frontier lay (treeIndexAt index lay) (leafIndexAt index lay),
        evalWithAnswerFn f (frontierTreePath parameter lay (treeIndexAt index lay)
          (words lay (treeIndexAt index lay)) (frontier lay (treeIndexAt index lay)) (leafIndexAt index lay))),
        search.2 + treeNodeHashCost (layerHeight lay))

theorem eval_frontierLayerMessage (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (frontierLayerMessage key.parameter key.ftsSecret words frontier index lay) =
      evalWithAnswerFn f (layerMessage key index lay) := by
  unfold frontierLayerMessage layerMessage
  split_ifs
  · rw [treeRoot]
    exact eval_frontierTreeNode _ _ _ _ _ _ _ (hfrontier _ _) _ _
  · rfl

theorem eval_signLayer_search (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (signLayer key index lay) =
      (referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0).1.map fun result =>
          (result.1, fun chainIdx => evalWithAnswerFn f
            (chainWalk key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx 0
              (result.2 chainIdx).val (key.otsSecret lay (treeIndexAt index lay) (leafIndexAt index lay) chainIdx)),
            evalWithAnswerFn f (treePath key.parameter lay (treeIndexAt index lay)
              (key.otsSecret lay (treeIndexAt index lay)) (leafIndexAt index lay))) := by
  simp only [signLayer, evalWithAnswerFn_bind, otsSign, eval_otsSignFrom, eval_encodingSearch]
  cases (referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0).1 with
  | none => rfl
  | some result => simp only [Option.map_some, evalWithAnswerFn_bind, evalWithAnswerFn_pure]

theorem specLayerCost_isSome (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index) (lay : Layer) :
    (specLayerCost key f index lay).1.isSome = (evalWithAnswerFn f (signLayer key index lay)).isSome := by
  rw [eval_signLayer_search, specLayerCost, Option.isSome_map]

theorem layersHashCostFrom_congr {α β : Type} (A : Layer → Option α × Nat) (B : Layer → Option β × Nat)
    (hcost : ∀ lay, (A lay).2 = (B lay).2) (hsome : ∀ lay, (A lay).1.isSome = (B lay).1.isSome)
    (remaining : Nat) : layersHashCostFrom A remaining = layersHashCostFrom B remaining := by
  induction remaining with
  | zero => rfl
  | succ r ih =>
      simp only [layersHashCostFrom, ih, hcost, hsome]

/-- The frontier layer is the specification's layer, value and cost. -/
theorem frontierSignLayer_eq_spec (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (index : Index) (lay : Layer)
    (hword : FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay) :
    frontierSignLayer key.parameter f key.ftsSecret words frontier index lay =
      (evalWithAnswerFn f (signLayer key index lay), (specLayerCost key f index lay).2) := by
  have hsearch : frontierLayerSearch key.parameter f key.ftsSecret words frontier index lay =
      referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0 := by
    rw [frontierLayerSearch, eval_frontierLayerMessage key f words frontier hfrontier]
  have hpath := (eval_frontierTreePath key.parameter f lay (treeIndexAt index lay)
    (key.otsSecret lay (treeIndexAt index lay)) (words lay (treeIndexAt index lay))
    (frontier lay (treeIndexAt index lay)) (hfrontier _ _) (leafIndexAt index lay))
  have hspec := eval_signLayer_search key f index lay
  rw [hspec, specLayerCost]
  simp only [frontierSignLayer]
  rw [hsearch]
  cases hs : (referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0).1 with
  | none => simp only [Option.map_none, Option.elim_none, Nat.add_zero]
  | some result =>
      obtain ⟨counter, word⟩ := result
      have hw : word = words lay (treeIndexAt index lay) (leafIndexAt index lay) :=
        hword counter word (by rw [hsearch]; exact hs)
      simp only [Option.map_some, Option.elim_some, hpath, Prod.mk.injEq, Option.some.injEq, and_true,
        true_and]
      funext chainIdx
      rw [hw]
      exact (hfrontier _ _ _ _).symm

def frontierSignAfterDigest (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    Option Signature × Nat :=
  let layers := fun lay => frontierSignLayer parameter f ftsSecret words frontier index lay
  let paths := evalWithAnswerFn f (ftsOpen parameter index leaves (ftsSecret index))
  ((sequenceFin (m := Option) (fun lay => (layers lay).1)).map (fun parts =>
      { randomness := randomness
        ftsSecret := fun tree => ftsSecret index tree (leaves (ftsIndexOf tree))
        ftsPath := paths
        layers := fun lay => LayerSignature.ofPadded lay (parts lay) }),
    ftsOpenHashCost + sequenceLayersHashCost layers)

theorem boundaryEval_signAfterDigest_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf)
    (hwords : ∀ lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay) :
    boundaryEval key.parameter f (signAfterDigest key randomness index leaves) =
      ((frontierSignAfterDigest key.parameter f key.ftsSecret words frontier randomness index leaves).1,
        (FreeMonoid.of none) ^
          (frontierSignAfterDigest key.parameter f key.ftsSecret words frontier randomness index leaves).2) := by
  have hlayers : (fun lay => frontierSignLayer key.parameter f key.ftsSecret words frontier index lay) =
      fun lay => (evalWithAnswerFn f (signLayer key index lay), (specLayerCost key f index lay).2) :=
    funext fun lay => frontierSignLayer_eq_spec key f words frontier hfrontier index lay (hwords lay)
  have hcost : sequenceLayersHashCost (fun lay => frontierSignLayer key.parameter f key.ftsSecret words frontier index lay) =
      sequenceLayersHashCost (specLayerCost key f index) := by
    rw [hlayers]
    exact layersHashCostFrom_congr
      (fun lay => (evalWithAnswerFn f (signLayer key index lay), (specLayerCost key f index lay).2))
      (specLayerCost key f index) (fun _ => rfl) (fun lay => (specLayerCost_isSome key f index lay).symm) _
  rw [boundaryEval_signAfterDigest]
  simp only [frontierSignAfterDigest, hcost, signatureValue]
  congr 2
  simp only [hlayers]

end SphincsSecurity.Concrete
