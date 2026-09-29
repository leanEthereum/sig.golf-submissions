import SigGolfCandidate.SphincsSecurity.Proof.Scheme.BuildEval

/-!
# The paired builders, evaluated

The seeded signer derives the secrets of two chains (or two few-time leaves) with one query and walks
the pair's members right after it (for the PORS tree: the two leaf hashes). Under a fixed answer function `f` the order of the work does not
matter, only what each member is handed: member `2k` gets the first half of the pair's answer and
member `2k + 1` the second. So each paired builder evaluates to its per-secret counterpart run with
the secrets `unpairedOts f g` (resp. `unpairedFts f g`) read off the evaluated pair getter `g`, and
everything proved about the per-secret builders (`BuildEval.lean`) applies.
-/

open OracleComp

namespace SphincsSecurity.Completeness

open Concrete

variable (f : QueryImpl HashSpec Id)

/-! ## Members of a pair -/

theorem evenChain_chainPairOf {chainIdx : ChainIndex} (h : chainIdx.val % 2 = 0) :
    evenChain (chainPairOf chainIdx) = chainIdx := by
  apply Fin.ext
  simp only [evenChain, chainPairOf]
  omega

theorem oddChain_chainPairOf {chainIdx : ChainIndex} (h : ¬ chainIdx.val % 2 = 0) :
    oddChain (chainPairOf chainIdx) = chainIdx := by
  apply Fin.ext
  simp only [oddChain, chainPairOf]
  omega

theorem evenFtsLeaf_ftsPairOf {leaf : FtsLeaf} (h : leaf.val % 2 = 0) :
    evenFtsLeaf (ftsPairOf leaf) = leaf := by
  apply Fin.ext
  simp only [evenFtsLeaf, ftsPairOf]
  omega

theorem oddFtsLeaf_ftsPairOf {leaf : FtsLeaf} (h : ¬ leaf.val % 2 = 0) :
    oddFtsLeaf (ftsPairOf leaf) = leaf := by
  apply Fin.ext
  simp only [oddFtsLeaf, ftsPairOf]
  omega

/-- Spreading a pairwise map of the members is mapping the spread members. -/
theorem unpairChains_map {α β : Type} (F : ChainIndex → α → β) (pairs : ChainPair → α × α)
    (mapped : ChainPair → β × β)
    (hmapped : ∀ pair, mapped pair = (F (evenChain pair) (pairs pair).1, F (oddChain pair) (pairs pair).2))
    (chainIdx : ChainIndex) :
    unpairChains mapped chainIdx = F chainIdx (unpairChains pairs chainIdx) := by
  unfold unpairChains
  split
  next h => rw [hmapped, evenChain_chainPairOf h]
  next h => rw [hmapped, oddChain_chainPairOf h]

theorem unpairFtsLeaves_map {α β : Type} (F : FtsLeaf → α → β) (pairs : FtsPair → α × α)
    (mapped : FtsPair → β × β)
    (hmapped : ∀ pair, mapped pair = (F (evenFtsLeaf pair) (pairs pair).1, F (oddFtsLeaf pair) (pairs pair).2))
    (leaf : FtsLeaf) :
    unpairFtsLeaves mapped leaf = F leaf (unpairFtsLeaves pairs leaf) := by
  unfold unpairFtsLeaves
  split
  next h => rw [hmapped, evenFtsLeaf_ftsPairOf h]
  next h => rw [hmapped, oddFtsLeaf_ftsPairOf h]

/-- The chain secrets a pair getter hands out under `f`. -/
def unpairedOts (g : ChainPair → OracleComp HashSpec (Digest × Digest)) : ChainIndex → Digest :=
  unpairChains fun pair => evalWithAnswerFn f (g pair)

/-- The few-time leaf secrets a pair getter hands out under `f`. -/
def unpairedFts (g : FtsPair → OracleComp HashSpec (Digest × Digest)) : FtsLeaf → Digest :=
  unpairFtsLeaves fun pair => evalWithAnswerFn f (g pair)

/-- Evaluations agree along a bind when the heads agree and the continuations agree pointwise. -/
theorem eval_bind_congr {α β : Type} {x x' : OracleComp HashSpec α}
    {k k' : α → OracleComp HashSpec β}
    (hx : evalWithAnswerFn f x = evalWithAnswerFn f x')
    (hk : ∀ v, evalWithAnswerFn f (k v) = evalWithAnswerFn f (k' v)) :
    evalWithAnswerFn f (x >>= k) = evalWithAnswerFn f (x' >>= k') := by
  rw [evalWithAnswerFn_bind, evalWithAnswerFn_bind, hx, hk]

/-! ## Layer trees -/

theorem eval_buildLeafPaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (g : ChainPair → OracleComp HashSpec (Digest × Digest)) (digits : Encoding) :
    evalWithAnswerFn f (buildLeafPaired parameter lay tree leaf g digits)
      = evalWithAnswerFn f (buildLeaf parameter lay tree leaf
          (fun chainIdx => pure (unpairedOts f g chainIdx)) digits) := by
  have hchains := unpairChains_map
    (fun chainIdx (secret : Digest) => evalWithAnswerFn f
      (buildChain parameter lay tree leaf chainIdx (pure secret) (digits chainIdx).val))
    (fun pair => evalWithAnswerFn f (g pair))
  simp only [buildLeafPaired, buildLeaf, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    evalWithAnswerFn_pure]
  simp only [hchains _ (fun _ => rfl), unpairedOts]

theorem eval_buildLayerTablePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (g : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)) (leaf : LeafIndex)
    (digits : Encoding) :
    evalWithAnswerFn f (buildLayerTablePaired parameter lay tree g leaf digits)
      = evalWithAnswerFn f (buildLayerTable parameter lay tree
          (fun leaf chainIdx => pure (unpairedOts f (g leaf) chainIdx)) leaf digits) := by
  unfold buildLayerTablePaired buildLayerTable
  refine eval_bind_congr f ?_ (fun _ => rfl)
  simp only [evalWithAnswerFn_sequenceFin, eval_buildLeafPaired]

theorem eval_buildLayerTreePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (g : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)) (leaf : LeafIndex)
    (digits : Encoding) :
    evalWithAnswerFn f (buildLayerTreePaired parameter lay tree g leaf digits)
      = evalWithAnswerFn f (buildLayerTree parameter lay tree
          (fun leaf chainIdx => pure (unpairedOts f (g leaf) chainIdx)) leaf digits) := by
  rw [buildLayerTree_eq_table, evalWithAnswerFn_map]
  unfold buildLayerTreePaired
  rw [evalWithAnswerFn_bind, eval_buildLayerTablePaired]
  rfl

/-! ## The PORS tree -/

theorem eval_buildFtsTreePaired (parameter : PublicParameter) (index : Index)
    (g : FtsPair → OracleComp HashSpec (Digest × Digest)) :
    evalWithAnswerFn f (buildFtsTreePaired parameter index g)
      = evalWithAnswerFn f (buildFtsTree parameter index (fun leaf => pure (unpairedFts f g leaf))) := by
  have hleaves := unpairFtsLeaves_map
    (fun leaf (secret : Digest) =>
      (secret, evalWithAnswerFn f (ftsLeafHash parameter index porsTree leaf.val secret)))
    (fun pair => evalWithAnswerFn f (g pair))
  unfold buildFtsTreePaired buildFtsTree
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure,
    hleaves _ (fun _ => rfl), unpairedFts]

/-! ## Signing -/

theorem eval_signTopLayerPaired (parameter : PublicParameter) (index : Index)
    (g : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (message : Digest) :
    evalWithAnswerFn f (signTopLayerPaired parameter index g topNode message)
      = evalWithAnswerFn f (signTopLayer parameter index
          (fun leaf chainIdx => pure (unpairedOts f (g leaf) chainIdx)) topNode message) := by
  unfold signTopLayerPaired signTopLayer
  refine eval_bind_congr f rfl (fun result => ?_)
  rcases result with _ | ⟨counter, encoding⟩
  · rfl
  · have hvalues := unpairChains_map
      (fun chainIdx (secret : Digest) => evalWithAnswerFn f (chainWalk parameter topLayer
        (treeIndexAt index topLayer) (leafIndexAt index topLayer) chainIdx 0
        (encoding chainIdx).val secret))
      (fun pair => evalWithAnswerFn f (g (leafIndexAt index topLayer) pair))
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin, evalWithAnswerFn_pure]
    rw [show (unpairChains fun pair =>
        (evalWithAnswerFn f (chainWalk parameter topLayer (treeIndexAt index topLayer)
          (leafIndexAt index topLayer) (evenChain pair) 0 (encoding (evenChain pair)).val
          (evalWithAnswerFn f (g (leafIndexAt index topLayer) pair)).1),
        evalWithAnswerFn f (chainWalk parameter topLayer (treeIndexAt index topLayer)
          (leafIndexAt index topLayer) (oddChain pair) 0 (encoding (oddChain pair)).val
          (evalWithAnswerFn f (g (leafIndexAt index topLayer) pair)).2)))
        = fun chainIdx => evalWithAnswerFn f (chainWalk parameter topLayer (treeIndexAt index topLayer)
          (leafIndexAt index topLayer) chainIdx 0 (encoding chainIdx).val
          (unpairedOts f (g (leafIndexAt index topLayer)) chainIdx)) from
      funext fun chainIdx => hvalues _ (fun _ => rfl) chainIdx]

theorem eval_signLayersPaired (parameter : PublicParameter) (index : Index)
    (g : Layer → TreeIndex → LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest) :
    ∀ (remaining : Nat) (message : Digest),
      evalWithAnswerFn f (signLayersPaired parameter index g topNode remaining message)
        = evalWithAnswerFn f (signLayers parameter index
            (fun lay tree leaf chainIdx => pure (unpairedOts f (g lay tree leaf) chainIdx))
            topNode remaining message) := by
  intro remaining
  induction remaining with
  | zero => intro message; rfl
  | succ remaining ih =>
      intro message
      rw [signLayersPaired, signLayers]
      split
      next hlayer =>
        split
        next hzero =>
          exact eval_bind_congr f (eval_signTopLayerPaired f parameter index _ topNode message)
            (fun _ => rfl)
        next hzero =>
          refine eval_bind_congr f rfl (fun result => ?_)
          rcases result with _ | ⟨counter, encoding⟩
          · rfl
          · refine eval_bind_congr f (eval_buildLayerTreePaired f _ _ _ _ _ _) (fun built => ?_)
            rcases built with ⟨values, path, root⟩
            exact eval_bind_congr f (ih root) (fun _ => rfl)
      next hlayer => rfl

/-- **The paired signer evaluates like the per-secret signer**, with the secrets the pair getters hand
out under `f`. -/
theorem eval_signFromPaired (parameter : PublicParameter) (index : Index)
    (ftsGet : FtsTree → FtsPair → OracleComp HashSpec (Digest × Digest))
    (otsGet : Layer → TreeIndex → LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (randomness : Randomness)
    (leaves : IndexGroup → FtsLeaf) :
    evalWithAnswerFn f (signFromPaired parameter index ftsGet otsGet topNode randomness leaves)
      = evalWithAnswerFn f (signFrom parameter index
          (fun tree leaf => pure (unpairedFts f (ftsGet tree) leaf))
          (fun lay tree leaf chainIdx => pure (unpairedOts f (otsGet lay tree leaf) chainIdx))
          topNode randomness leaves) := by
  unfold signFromPaired signFrom
  refine eval_bind_congr f (eval_buildFtsTreePaired f _ _ _) (fun tree => ?_)
  rcases tree with ⟨secrets, table⟩
  exact eval_bind_congr f (eval_signLayersPaired f _ _ _ _ _ _) (fun _ => rfl)

end SphincsSecurity.Completeness
