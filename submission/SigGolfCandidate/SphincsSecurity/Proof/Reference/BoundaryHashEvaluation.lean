import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Reference.BoundaryHashCost

/-! ## AuthenticationQueryCost -/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

def authenticationHashCost (lay : Layer) : Nat :=
  ∑ level : Fin maxLayerHeight, if level.val < layerHeight lay then treeNodeHashCost level.val else 0

def layerMessageHashCost (lay : Layer) : Nat :=
  if hbelow : lay.val + 1 < numLayers then
    treeNodeHashCost (layerHeight ⟨lay.val + 1, hbelow⟩)
  else ftsKeyHashCost

end SphincsSecurity.Concrete

/-! ## FtsSigningReserve -/

namespace SphincsSecurity.Concrete.FtsProbeSimulation

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem tweakableHashInput_tag_eq (parameter : PublicParameter) (first second : HashDomain)
    (firstPayload secondPayload : HashInput)
    (heq : tweakableHashInput parameter first firstPayload = tweakableHashInput parameter second secondPayload) :
    (hashDomainFields first).tag = (hashDomainFields second).tag := by
  simp only [tweakableHashInput] at heq
  obtain ⟨hprefix, _⟩ := List.append_inj heq (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact congrArg TweakFields.tag (tweakBytes_eq_iff.mp htweak)

end SphincsSecurity.Concrete.FtsProbeSimulation

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem SigningBoundaryTrace.hashCalls_pow_none (cost : Nat) :
    SigningBoundaryTrace.hashCalls ((FreeMonoid.of none : SigningBoundaryTrace) ^ cost) = cost := by
  induction cost with
  | zero => rfl
  | succ cost ih =>
      rw [pow_succ, SigningBoundaryTrace.hashCalls_mul, ih]
      rfl

theorem SigningBoundaryTrace.messageCalls_pow_none (cost : Nat) :
    SigningBoundaryTrace.messageCalls ((FreeMonoid.of none : SigningBoundaryTrace) ^ cost) = [] := by
  induction cost with
  | zero => rfl
  | succ cost ih =>
      rw [pow_succ, SigningBoundaryTrace.messageCalls_mul, ih]
      rfl

noncomputable def boundaryEval {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) : α × SigningBoundaryTrace :=
  (simulateQ (f.withTrace (fun input output => signingBoundaryTrace parameter (.inr input) output))
    computation).run

@[simp] theorem boundaryEval_pure {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (value : α) : boundaryEval parameter f (pure value) = (value, 1) := rfl

theorem boundaryEval_fst {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) :
    (boundaryEval parameter f computation).1 = evalWithAnswerFn f computation := by
  exact QueryImpl.fst_map_run_withTrace f
    (fun input output => signingBoundaryTrace parameter (.inr input) output) computation

theorem boundaryEval_bind {α β : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (first : OracleComp HashSpec α) (next : α → OracleComp HashSpec β) :
    boundaryEval parameter f (first >>= next) =
      ((boundaryEval parameter f (next (evalWithAnswerFn f first))).1,
        (boundaryEval parameter f first).2 *
          (boundaryEval parameter f (next (evalWithAnswerFn f first))).2) := by
  simp only [boundaryEval, simulateQ_bind, WriterT.run_bind]
  rw [← boundaryEval_fst parameter f first]
  rfl

theorem boundaryEval_tweakableHash (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (domain : HashDomain) (payload : HashInput) (hmessage : (hashDomainFields domain).tag ≠ 12#8) :
    boundaryEval parameter f (tweakableHash parameter domain payload) =
      (truncateHash (f (tweakableHashInput parameter domain payload)), FreeMonoid.of none) := by
  have hn : ¬ FtsProbeSimulation.MessageHashInput parameter (tweakableHashInput parameter domain payload) := by
    rintro ⟨otherPayload, heq⟩
    exact hmessage (FtsProbeSimulation.tweakableHashInput_tag_eq parameter domain .message
      payload otherPayload heq.symm)
  simp [boundaryEval, tweakableHash, oracleHash, QueryImpl.withTrace_apply,
    signingBoundaryTrace_nonmessage _ _ _ hn]
  rfl

theorem boundaryEval_eq_of_snd {α : Type} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : OracleComp HashSpec α) (trace : SigningBoundaryTrace)
    (htrace : (boundaryEval parameter f computation).2 = trace) :
    boundaryEval parameter f computation = (evalWithAnswerFn f computation, trace) := by
  exact Prod.ext (boundaryEval_fst _ _ _) htrace

theorem boundaryEval_sequenceFin {α : Type} {n : Nat} (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (computation : Fin n → OracleComp HashSpec α) (cost : Fin n → Nat)
    (hcost : ∀ i, (boundaryEval parameter f (computation i)).2 = (FreeMonoid.of none) ^ cost i) :
    boundaryEval parameter f (sequenceFin computation) =
      (fun i => evalWithAnswerFn f (computation i), (FreeMonoid.of none) ^ (∑ i, cost i)) := by
  rw [← evalWithAnswerFn_sequenceFin]
  apply boundaryEval_eq_of_snd
  induction n with
  | zero => simp [sequenceFin]
  | succ n ih =>
      rw [sequenceFin, boundaryEval_bind]
      have ht := ih (fun i => computation i.succ) (fun i => cost i.succ) (fun i => hcost i.succ)
      simp only [boundaryEval_bind, boundaryEval_pure, mul_one, hcost, ht,
        Fin.sum_univ_succ, pow_add]

/-- The cost of the layers from `remaining - 1` down to `0`, each its own cost, stopping after the
first layer that fails. -/
def layersHashCostFrom {α : Type} (layers : Layer → Option α × Nat) : Nat → Nat
  | 0 => 0
  | remaining + 1 =>
      if hlayer : remaining < numLayers then
        (layers ⟨remaining, hlayer⟩).2 +
          if (layers ⟨remaining, hlayer⟩).1.isSome then layersHashCostFrom layers remaining else 0
      else 0

/-- The cost of walking all layers from the bottom up, stopping after the first failure. -/
def sequenceLayersHashCost {α : Type} (layers : Layer → Option α × Nat) : Nat :=
  layersHashCostFrom layers numLayers

theorem boundaryEval_chainWalk (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (start steps : Nat) (value : Digest) (hsteps : start + steps ≤ chainLength - 1) :
    boundaryEval parameter f (chainWalk parameter lay tree leaf chainIdx start steps value) =
      (evalWithAnswerFn f (chainWalk parameter lay tree leaf chainIdx start steps value),
        (FreeMonoid.of none) ^ steps) := by
  apply boundaryEval_eq_of_snd
  induction steps with
  | zero => simp [chainWalk]
  | succ steps ih =>
      have hstep : start + steps < chainLength - 1 := by omega
      rw [chainWalk, boundaryEval_bind, dif_pos hstep,
        boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields]), ih (by omega), pow_succ]

theorem boundaryEval_oneTimePublicKey (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest) :
    boundaryEval parameter f (oneTimePublicKey parameter lay tree leaf secret) =
      (evalWithAnswerFn f (oneTimePublicKey parameter lay tree leaf secret), (FreeMonoid.of none) ^ oneTimeKeyHashCost) := by
  rw [oneTimePublicKey]
  have h := boundaryEval_sequenceFin parameter f
    (fun chainIdx => chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx))
    (fun _ => chainLength - 1)
    (fun chainIdx => congrArg Prod.snd (boundaryEval_chainWalk _ _ _ _ _ _ _ _ _ (by omega)))
  simpa only [evalWithAnswerFn_sequenceFin, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← oneTimeKeyHashCost_def] using h

theorem boundaryEval_treeNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    boundaryEval parameter f (treeNode parameter lay tree secret level nodeIdx) =
      (evalWithAnswerFn f (treeNode parameter lay tree secret level nodeIdx),
        (FreeMonoid.of none) ^ treeNodeHashCost level) := by
  apply boundaryEval_eq_of_snd
  induction level generalizing nodeIdx with
  | zero =>
      rw [treeNode_zero_eq, boundaryEval_bind, boundaryEval_oneTimePublicKey]
      simp only [leafHash, boundaryEval_tweakableHash parameter f (.leaf lay tree (leafOfNat nodeIdx)) _
        (by simp [hashDomainFields, tweakFields])]
      rw [← pow_succ, treeNodeHashCost_zero]
  | succ level ih =>
      rw [treeNode_succ_eq, boundaryEval_bind]
      simp only [boundaryEval_bind, ih, boundaryEval_tweakableHash parameter f (.node lay tree (level + 1) nodeIdx) _
        (by simp [hashDomainFields, tweakFields])]
      rw [← pow_succ, ← pow_add, treeNodeHashCost_succ]

theorem boundaryEval_treePath (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) :
    boundaryEval parameter f (treePath parameter lay tree secret leaf) =
      (evalWithAnswerFn f (treePath parameter lay tree secret leaf),
        (FreeMonoid.of none) ^ authenticationHashCost lay) := by
  unfold treePath authenticationHashCost
  rw [evalWithAnswerFn_sequenceFin]
  apply boundaryEval_sequenceFin
  intro level
  split_ifs
  · exact congrArg Prod.snd (boundaryEval_treeNode _ _ _ _ _ _ _)
  · simp

theorem boundaryEval_ftsNode (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (tree : FtsTree) (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    boundaryEval parameter f (ftsNode parameter index tree secret level nodeIdx) =
      (evalWithAnswerFn f (ftsNode parameter index tree secret level nodeIdx),
        (FreeMonoid.of none) ^ (2 ^ (level + 1) - 1)) := by
  apply boundaryEval_eq_of_snd
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq, ftsLeafHash, boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields])]
      simp
  | succ level ih =>
      rw [ftsNode_succ_eq, boundaryEval_bind]
      simp only [boundaryEval_bind, ih,
        boundaryEval_tweakableHash parameter f (.ftsNode index tree (ftsHeapIndex (level + 1) nodeIdx)) _
          (by simp [hashDomainFields, tweakFields])]
      rw [← pow_succ, ← pow_add]
      congr 1
      have hp : 0 < 2 ^ (level + 1) := by positivity
      rw [pow_succ]
      omega

theorem boundaryEval_ftsKey (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : FtsTree → FtsLeaf → Digest) :
    boundaryEval parameter f (ftsKey parameter index secret) =
      (evalWithAnswerFn f (ftsKey parameter index secret), (FreeMonoid.of none) ^ ftsKeyHashCost) := by
  rw [ftsKey, boundaryEval_ftsNode, ftsKeyHashCost_def]

theorem boundaryEval_layerMessage (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index) (lay : Layer) :
    boundaryEval key.parameter f (layerMessage key index lay) =
      (evalWithAnswerFn f (layerMessage key index lay), (FreeMonoid.of none) ^ layerMessageHashCost lay) := by
  rw [layerMessage, layerMessageHashCost]
  split_ifs
  · rw [treeRoot]
    exact boundaryEval_treeNode _ _ _ _ _ _ _
  · exact boundaryEval_ftsKey _ _ _ _

theorem boundaryEval_hash_query (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (input : HashInput) :
    boundaryEval parameter f (liftM (HashSpec.query input)) =
      (f input, signingBoundaryTrace parameter (.inr input) (f input)) := rfl

/-! ### The builders -/

theorem boundaryEval_node_hash (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (lay : Layer)
    (tree : TreeIndex) (level nodeIdx : Nat) (left right : Digest) :
    (boundaryEval parameter f (tweakableHash parameter (.node lay tree level nodeIdx)
      (nodePayload left right))).2 = FreeMonoid.of none := by
  rw [boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields])]

theorem boundaryEval_ftsNode_hash (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (tree : FtsTree) (heapIdx : Nat) (left right : Digest) :
    (boundaryEval parameter f (tweakableHash parameter (.ftsNode index tree heapIdx)
      (nodePayload left right))).2 = FreeMonoid.of none := by
  rw [boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields])]

theorem boundaryEval_buildLevel (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (hashNode : Nat → Digest → Digest → OracleComp HashSpec Digest)
    (hhash : ∀ nodeIdx left right, (boundaryEval parameter f (hashNode nodeIdx left right)).2 = FreeMonoid.of none)
    (width : Nat) (below : Nat → Digest) :
    (boundaryEval parameter f (buildLevel hashNode width below)).2 = (FreeMonoid.of none) ^ width := by
  unfold buildLevel
  rw [boundaryEval_bind, boundaryEval_sequenceFin parameter f _ (fun _ => 1)
    (fun nodeIdx => by rw [hhash, pow_one])]
  simp only [boundaryEval_pure, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, Nat.mul_one]

/-- The nodes of levels `1, ..., levels` of a tree of height `height`. -/
def levelsHashCost (height : Nat) : Nat → Nat
  | 0 => 0
  | levels + 1 => levelsHashCost height levels + 2 ^ (height - (levels + 1))

theorem levelsHashCost_eq (height levels : Nat) (hlevels : levels ≤ height) :
    levelsHashCost height levels = 2 ^ height - 2 ^ (height - levels) := by
  induction levels with
  | zero => simp [levelsHashCost]
  | succ levels ih =>
      rw [levelsHashCost, ih (by omega)]
      have hpow : 2 ^ (height - levels) = 2 * 2 ^ (height - (levels + 1)) := by
        rw [← pow_succ']
        congr 1
        omega
      have hle : 2 ^ (height - levels) ≤ 2 ^ height := Nat.pow_le_pow_right (by omega) (by omega)
      omega

theorem levelsHashCost_self (height : Nat) : levelsHashCost height height = 2 ^ height - 1 := by
  rw [levelsHashCost_eq height height le_rfl, Nat.sub_self, pow_zero]

theorem boundaryEval_buildLevels (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (hashNode : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (hhash : ∀ level nodeIdx left right,
      (boundaryEval parameter f (hashNode level nodeIdx left right)).2 = FreeMonoid.of none)
    (height : Nat) (leaves : Nat → Digest) (levels : Nat) :
    (boundaryEval parameter f (buildLevels hashNode height leaves levels)).2 =
      (FreeMonoid.of none) ^ levelsHashCost height levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      rw [buildLevels, boundaryEval_bind, ih, boundaryEval_bind,
        boundaryEval_buildLevel _ _ _ (hhash (levels + 1))]
      simp only [boundaryEval_pure, mul_one, levelsHashCost, pow_add]

theorem boundaryEval_buildChain_pure (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : Digest)
    (digit : Nat) (hdigit : digit ≤ chainLength - 1) :
    (boundaryEval parameter f (buildChain parameter lay tree leaf chainIdx (pure secret) digit)).2 =
      (FreeMonoid.of none) ^ (chainLength - 1) := by
  unfold buildChain
  rw [pure_bind, boundaryEval_bind, boundaryEval_chainWalk _ _ _ _ _ _ _ _ _ (by omega),
    boundaryEval_bind, boundaryEval_chainWalk _ _ _ _ _ _ _ _ _ (by omega)]
  simp only [boundaryEval_pure, mul_one, ← pow_add]
  congr 1
  omega

theorem boundaryEval_buildLeaf_pure (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (secret : ChainIndex → Digest)
    (digits : Encoding) :
    (boundaryEval parameter f (buildLeaf parameter lay tree leaf (fun chainIdx => pure (secret chainIdx))
      digits)).2 = (FreeMonoid.of none) ^ (oneTimeKeyHashCost + 1) := by
  unfold buildLeaf
  rw [boundaryEval_bind, boundaryEval_sequenceFin parameter f _ (fun _ => chainLength - 1)
    (fun chainIdx => boundaryEval_buildChain_pure _ _ _ _ _ _ _ _ (by
      have := (digits chainIdx).isLt
      simp only [chainLength, winternitzBits] at this ⊢
      omega))]
  rw [boundaryEval_bind, leafHash, boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields])]
  simp only [boundaryEval_pure, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, pow_succ, oneTimeKeyHashCost_def]

/-- **A layer's tree built once from table secrets costs exactly a tree node at its height.** -/
theorem boundaryEval_buildLayerTree_pure (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex)
    (digits : Encoding) :
    (boundaryEval parameter f (buildLayerTree parameter lay tree
      (fun leaf chainIdx => pure (secret leaf chainIdx)) leaf digits)).2 =
      (FreeMonoid.of none) ^ treeNodeHashCost (layerHeight lay) := by
  unfold buildLayerTree
  rw [boundaryEval_bind, boundaryEval_sequenceFin parameter f _ (fun _ => oneTimeKeyHashCost + 1)
    (fun leafNat => boundaryEval_buildLeaf_pure _ _ _ _ _ _ _)]
  rw [boundaryEval_bind, boundaryEval_buildLevels _ _ _ (fun _ _ _ _ => boundaryEval_node_hash _ _ _ _ _ _ _ _),
    levelsHashCost_self]
  simp only [boundaryEval_pure, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← pow_add]
  congr 1
  rw [treeNodeHashCost_def]
  have hpos : 0 < 2 ^ layerHeight lay := Nat.two_pow_pos _
  have : (oneTimeKeyHashCost + 2) * 2 ^ layerHeight lay =
      2 ^ layerHeight lay * (oneTimeKeyHashCost + 1) + 2 ^ layerHeight lay := by ring
  omega

/-- **A layer's tree table built once from table secrets costs exactly a tree node at its height.** -/
theorem boundaryEval_buildLayerTable_pure (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (lay : Layer) (tree : TreeIndex) (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex)
    (digits : Encoding) :
    (boundaryEval parameter f (buildLayerTable parameter lay tree
      (fun leaf chainIdx => pure (secret leaf chainIdx)) leaf digits)).2 =
      (FreeMonoid.of none) ^ treeNodeHashCost (layerHeight lay) := by
  unfold buildLayerTable
  rw [boundaryEval_bind, boundaryEval_sequenceFin parameter f _ (fun _ => oneTimeKeyHashCost + 1)
    (fun leafNat => boundaryEval_buildLeaf_pure _ _ _ _ _ _ _)]
  rw [boundaryEval_bind, boundaryEval_buildLevels _ _ _ (fun _ _ _ _ => boundaryEval_node_hash _ _ _ _ _ _ _ _),
    levelsHashCost_self]
  simp only [boundaryEval_pure, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← pow_add]
  congr 1
  rw [treeNodeHashCost_def]
  have hpos : 0 < 2 ^ layerHeight lay := Nat.two_pow_pos _
  have : (oneTimeKeyHashCost + 2) * 2 ^ layerHeight lay =
      2 ^ layerHeight lay * (oneTimeKeyHashCost + 1) + 2 ^ layerHeight lay := by ring
  omega

/-- Key generation's table costs exactly one top tree. -/
theorem boundaryEval_keygenTable (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (secret : LeafIndex → ChainIndex → Digest) :
    boundaryEval parameter f (keygenTable parameter secret) =
      (evalWithAnswerFn f (keygenTable parameter secret), (FreeMonoid.of none) ^ keygenHashCost) := by
  apply boundaryEval_eq_of_snd
  unfold keygenTable
  rw [boundaryEval_bind, boundaryEval_buildLayerTable_pure, keygenHashCost_def]
  split
  simp only [boundaryEval_pure, mul_one]

theorem boundaryEval_keygenRoot (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (secret : LeafIndex → ChainIndex → Digest) :
    boundaryEval parameter f (keygenRoot parameter secret) =
      (evalWithAnswerFn f (keygenRoot parameter secret), (FreeMonoid.of none) ^ keygenHashCost) := by
  apply boundaryEval_eq_of_snd
  unfold keygenRoot
  rw [boundaryEval_bind, boundaryEval_buildLayerTree_pure, keygenHashCost_def]
  -- `split` keeps the scrutinee opaque; generalizing it makes the kernel evaluate the tree build
  split
  simp only [boundaryEval_pure, mul_one]

theorem boundaryEval_buildFtsTree_pure_snd (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : FtsLeaf → Digest) :
    (boundaryEval parameter f (buildFtsTree parameter index (fun leaf => pure (secret leaf)))).2 =
      (FreeMonoid.of none) ^ (2 ^ (ftsTreeHeight + 1) - 1) := by
  unfold buildFtsTree
  rw [boundaryEval_bind, boundaryEval_sequenceFin parameter f _ (fun _ => 1)
    (fun leafIdx => by
      rw [pure_bind, boundaryEval_bind, ftsLeafHash,
        boundaryEval_tweakableHash _ _ _ _ (by simp [hashDomainFields, tweakFields])]
      simp only [boundaryEval_pure, mul_one, pow_one])]
  rw [boundaryEval_bind, boundaryEval_buildLevels _ _ _
    (fun _ _ _ _ => boundaryEval_ftsNode_hash _ _ _ _ _ _ _), levelsHashCost_self]
  simp only [boundaryEval_pure, mul_one, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, ← pow_add]
  congr 1

/-- **The PORS tree built once from table secrets costs exactly `ftsOpenHashCost`** (its `2^14` leaves and
`2^14 - 1` nodes). -/
theorem boundaryEval_buildFtsTree_pure (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (index : Index) (secret : FtsLeaf → Digest) :
    boundaryEval parameter f (buildFtsTree parameter index (fun leaf => pure (secret leaf))) =
      (evalWithAnswerFn f (buildFtsTree parameter index (fun leaf => pure (secret leaf))),
        (FreeMonoid.of none) ^ ftsOpenHashCost) := by
  apply boundaryEval_eq_of_snd
  rw [boundaryEval_buildFtsTree_pure_snd, ftsOpenHashCost_def]

end SphincsSecurity.Concrete
