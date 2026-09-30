import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Reference.BoundaryHashEvaluation
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.BuildEval
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval sequenceFin chainWalk

def referenceEncodingSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) :
    Nat → Nat → Option (Counter × Encoding) × Nat
  | 0, _ => (none, 0)
  | attempts + 1, counter =>
      match evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter)) with
      | some word => (some (BitVec.ofNat counterBits counter, word), 1)
      | none =>
          let rest := referenceEncodingSearch parameter f lay tree leaf message attempts (counter + 1)
          (rest.1, 1 + rest.2)

theorem boundaryEval_encode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (counter : Counter) :
    boundaryEval parameter f (encodeAttempt parameter lay tree leaf message counter) =
      (evalWithAnswerFn f (encodeAttempt parameter lay tree leaf message counter), FreeMonoid.of none) := by
  apply boundaryEval_eq_of_snd
  rw [encodeAttempt, boundaryEval_bind,
    boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields]), boundaryEval_pure, mul_one]

theorem boundaryEval_otsValues (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest) (word : Encoding) :
    boundaryEval parameter f (sequenceFin fun chainIdx =>
      chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)) =
      (fun chainIdx => evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)),
        (FreeMonoid.of none) ^ OtsCode.signingSteps word) := by
  have h := boundaryEval_sequenceFin parameter f
    (fun chainIdx => chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx))
    (fun chainIdx => (word chainIdx).val) (fun chainIdx => by
      apply congrArg Prod.snd (boundaryEval_chainWalk _ _ _ _ _ _ _ _ _ ?_)
      have hdigit := (word chainIdx).isLt
      omega)
  simpa only [OtsCode.signingSteps] using h

theorem boundaryEval_otsSignFrom_frontier (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret frontier : ChainIndex → Digest)
    (message : Digest) (attempts counter : Nat)
    (hfrontier : ∀ c word,
      (referenceEncodingSearch parameter f lay tree leaf message attempts counter).1 = some (c, word) →
      ∀ chainIdx, evalWithAnswerFn f
        (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)) = frontier chainIdx) :
    boundaryEval parameter f (otsSignFrom parameter lay tree leaf secret message attempts counter) =
      ((referenceEncodingSearch parameter f lay tree leaf message attempts counter).1.map
          (fun result => (result.1, frontier)),
        (FreeMonoid.of none) ^ ((referenceEncodingSearch parameter f lay tree leaf message attempts counter).2 +
          (referenceEncodingSearch parameter f lay tree leaf message attempts counter).1.elim 0
            (fun result => OtsCode.signingSteps result.2))) := by
  induction attempts generalizing counter with
  | zero => simp [otsSignFrom, referenceEncodingSearch]
  | succ attempts ih =>
      rw [otsSignFrom, boundaryEval_bind, boundaryEval_encode]
      cases hencode : evalWithAnswerFn f
          (encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter)) with
      | none =>
          have ht : ∀ c word,
              (referenceEncodingSearch parameter f lay tree leaf message attempts (counter + 1)).1 = some (c, word) →
              ∀ chainIdx, evalWithAnswerFn f
                (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx)) = frontier chainIdx := by
            intro c word hw
            apply hfrontier c word
            simpa only [referenceEncodingSearch, hencode] using hw
          rw [ih (counter + 1) ht]
          simp only [referenceEncodingSearch, hencode, Nat.add_assoc, pow_add, pow_one]
      | some word =>
          have hv : (fun chainIdx => evalWithAnswerFn f
              (chainWalk parameter lay tree leaf chainIdx 0 (word chainIdx).val (secret chainIdx))) = frontier := by
            funext chainIdx
            exact hfrontier (BitVec.ofNat counterBits counter) word
              (by simp only [referenceEncodingSearch, hencode]) chainIdx
          rw [boundaryEval_bind, boundaryEval_otsValues]
          simp only [boundaryEval_pure, evalWithAnswerFn_sequenceFin, hv, mul_one,
            referenceEncodingSearch, hencode, Option.map_some, Option.elim_some, pow_add, pow_one]

/-! ### The signer's layers and their cost -/

theorem boundaryEval_encodingSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (attempts counter : Nat) :
    boundaryEval parameter f (encodingSearch parameter lay tree leaf message attempts counter) =
      ((referenceEncodingSearch parameter f lay tree leaf message attempts counter).1,
        (FreeMonoid.of none) ^ (referenceEncodingSearch parameter f lay tree leaf message attempts counter).2) := by
  induction attempts generalizing counter with
  | zero => simp only [encodingSearch, referenceEncodingSearch, boundaryEval_pure, pow_zero]
  | succ attempts ih =>
      rw [encodingSearch, encode_eq, boundaryEval_bind, boundaryEval_encode]
      cases hencode : evalWithAnswerFn f
          (encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter)) with
      | none =>
          rw [ih (counter + 1)]
          simp only [referenceEncodingSearch, hencode, pow_add, pow_one]
      | some word =>
          simp only [boundaryEval_pure, referenceEncodingSearch, hencode, mul_one, pow_one]

theorem eval_encodingSearch (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (attempts counter : Nat) :
    evalWithAnswerFn f (encodingSearch parameter lay tree leaf message attempts counter) =
      (referenceEncodingSearch parameter f lay tree leaf message attempts counter).1 := by
  rw [← boundaryEval_fst parameter f, boundaryEval_encodingSearch]

/-- One layer of the signer, from the specification's message: the counter search and, when it
succeeds, the tree built once. -/
noncomputable def specLayerCost (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index)
    (lay : Layer) : Option (Counter × Encoding) × Nat :=
  let search := referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
    (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0
  (search.1, search.2 + search.1.elim 0 (fun _ => treeNodeHashCost (layerHeight lay)))

theorem boundaryEval_signLayers (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index)
    (remaining : Nat) (hremaining : remaining ≤ numLayers) (message : Digest)
    (hmessage : ∀ h : 0 < remaining,
      message = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by omega⟩)) :
    (boundaryEval key.parameter f (signLayers key.parameter index
      (fun lay tree leaf chainIdx => pure (key.otsSecret lay tree leaf chainIdx)) remaining message)).2 =
      (FreeMonoid.of none) ^ layersHashCostFrom (specLayerCost key f index) remaining := by
  induction remaining generalizing message with
  | zero => simp only [signLayers, boundaryEval_pure, layersHashCostFrom, pow_zero]
  | succ remaining ih =>
      have hlayer : remaining < numLayers := by omega
      let lay : Layer := ⟨remaining, hlayer⟩
      have hmsg : message = evalWithAnswerFn f (layerMessage key index lay) := hmessage (by omega)
      rw [signLayers, dif_pos hlayer, layersHashCostFrom, dif_pos hlayer, boundaryEval_bind,
        boundaryEval_encodingSearch, eval_encodingSearch]
      simp only [show (⟨remaining, hlayer⟩ : Layer) = lay from rfl]
      change _ = (FreeMonoid.of none) ^ ((specLayerCost key f index lay).2 +
        if (specLayerCost key f index lay).1.isSome then layersHashCostFrom (specLayerCost key f index) remaining else 0)
      simp only [specLayerCost, ← hmsg]
      cases hsearch : (referenceEncodingSearch key.parameter f lay (treeIndexAt index lay)
          (leafIndexAt index lay) message encodingAttemptLimit 0).1 with
      | none =>
          simp only [boundaryEval_pure, mul_one, Option.elim_none, Nat.add_zero,
            Option.isSome_none, Bool.false_eq_true, if_false]
      | some result =>
          obtain ⟨counter, word⟩ := result
          simp only [Option.elim_some, Option.isSome_some, if_true]
          have hroot := eval_buildLayerTree_root f key.parameter lay (treeIndexAt index lay)
            (fun leaf chainIdx => pure (key.otsSecret lay (treeIndexAt index lay) leaf chainIdx))
            (leafIndexAt index lay) (leafIndexAt_lt index lay) word
          rw [boundaryEval_bind, boundaryEval_buildLayerTree_pure]
          revert hroot
          generalize evalWithAnswerFn f (buildLayerTree key.parameter lay (treeIndexAt index lay)
            (fun leaf chainIdx => pure (key.otsSecret lay (treeIndexAt index lay) leaf chainIdx))
            (leafIndexAt index lay) word) = built
          rcases built with ⟨values, path, root⟩
          intro hroot
          simp only [evalWithAnswerFn_pure] at hroot
          have hnext : ∀ h : 0 < remaining,
              root = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by omega⟩) := by
            intro h
            have hbelow : remaining - 1 + 1 < numLayers := by omega
            rw [layerMessage, dif_pos hbelow]
            have hl : (⟨remaining - 1 + 1, hbelow⟩ : Layer) = lay := Fin.ext (by simp [lay]; omega)
            simp only [hl, hroot]
          rw [boundaryEval_bind, ih (by omega) root hnext]
          cases evalWithAnswerFn f (signLayers key.parameter index
              (fun lay tree leaf chainIdx => pure (key.otsSecret lay tree leaf chainIdx)) remaining root) <;>
            simp only [boundaryEval_pure, mul_one, pow_add, mul_assoc]

/-- **The table signer after the digest loop**: the specification's signature, at the cost of the
forest and of the layers it walks. -/
theorem boundaryEval_signAfterDigest (key : SecretKey) (f : QueryImpl HashSpec Id)
    (randomness : Randomness) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    boundaryEval key.parameter f (signAfterDigest key randomness index leaves) =
      (signatureValue f key randomness index leaves,
        (FreeMonoid.of none) ^ (ftsOpenHashCost + sequenceLayersHashCost (specLayerCost key f index))) := by
  rw [← eval_signAfterDigest f key randomness index leaves]
  apply boundaryEval_eq_of_snd
  have hforest := eval_buildForest f key.parameter index
    (fun tree leaf => pure (key.ftsSecret index tree leaf)) leaves
  rw [signAfterDigest_eq_signFrom, signFrom, boundaryEval_bind, boundaryEval_buildForest_pure]
  revert hforest
  generalize evalWithAnswerFn f (buildForest key.parameter index
    (fun tree leaf => pure (key.ftsSecret index tree leaf)) leaves) = forest
  rcases forest with ⟨secrets, ftsPath, ftsPublicKey⟩
  rintro ⟨_, _, hkey⟩
  simp only [evalWithAnswerFn_pure] at hkey
  rw [boundaryEval_bind, boundaryEval_signLayers key f index numLayers le_rfl ftsPublicKey (by
    intro _
    rw [hkey]
    change _ = evalWithAnswerFn f (layerMessage key index bottomLayer)
    rw [layerMessage_bottomLayer_eq])]
  cases evalWithAnswerFn f (signLayers key.parameter index
      (fun lay tree leaf chainIdx => pure (key.otsSecret lay tree leaf chainIdx)) numLayers ftsPublicKey) <;>
    simp only [boundaryEval_pure, mul_one, pow_add, sequenceLayersHashCost]

/-- Key generation: the specification's root, at the cost of one top tree. -/
theorem boundaryEval_keygen (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (secret : LeafIndex → ChainIndex → Digest) :
    boundaryEval parameter f (keygenRoot parameter secret) =
      (evalWithAnswerFn f (treeRoot parameter topLayer rootTree secret), (FreeMonoid.of none) ^ keygenHashCost) := by
  rw [boundaryEval_keygenRoot, eval_keygenRoot]

end SphincsSecurity.Concrete
