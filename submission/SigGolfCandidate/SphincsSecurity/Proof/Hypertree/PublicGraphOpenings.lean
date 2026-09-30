import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.CanonicalGraphHonest
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.CanonicalProbeRouting
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FtsProbeGame
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec CanonicalProbeRouting
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] instFintypePosition

theorem openingSibling_lt (height leaf level : Nat) (hlevel : level < height) (hleaf : leaf < 2 ^ height) :
    Nat.xor (leaf / 2 ^ level) 1 < 2 ^ height := by
  have hspan := FtsProbeSimulation.sibling_node_bound height leaf level hlevel hleaf
  have hpow : 1 ≤ (2 : Nat) ^ level := Nat.one_le_pow level 2 (by decide)
  nlinarith

def treeOpeningPosition (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (level : Fin maxLayerHeight) : Position :=
  let sibling : LeafIndex := ⟨Nat.xor (leaf.val / 2 ^ level.val) 1,
    openingSibling_lt maxLayerHeight leaf.val level.val level.isLt leaf.isLt⟩
  if level.val = 0 then .leaf lay tree sibling
  else .node lay tree ⟨level.val - 1, by have := level.isLt; omega⟩ sibling

/-- The graph position of node `(level, nodeIdx)` of the PORS tree of `index`: the leaf at level `0`, else
the node with heap index `2^(14 - level) + nodeIdx` (heap index `0`, no node, outside the tree). -/
def ftsNodePosition (index : Index) (level nodeIdx : Nat) : Position :=
  if level = 0 then .ftsLeaf index porsTree (ftsLeafOfNat nodeIdx)
  else if h : ftsHeapIndex level nodeIdx < 2 ^ ftsTreeHeight then
    .ftsNode index porsTree ⟨ftsHeapIndex level nodeIdx, h⟩
  else .ftsNode index porsTree ⟨0, Nat.two_pow_pos _⟩

theorem treeOpeningPosition_bound (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (level : Fin maxLayerHeight) :
    (treeOpeningPosition lay tree leaf level).TreeBound := by
  unfold treeOpeningPosition
  split_ifs with hzero
  · trivial
  · simp only [Position.TreeBound, show level.val - 1 + 1 = level.val by omega]
    exact FtsProbeSimulation.sibling_node_bound maxLayerHeight leaf.val level.val level.isLt leaf.isLt

theorem ftsNodePosition_bound (index : Index) (level nodeIdx : Nat) (hlevel : level ≤ ftsTreeHeight)
    (hnode : nodeIdx < 2 ^ (ftsTreeHeight - level)) :
    (ftsNodePosition index level nodeIdx).TreeBound := by
  unfold ftsNodePosition
  split_ifs with hzero hheap
  · trivial
  · change 0 < ftsHeapIndex level nodeIdx
    unfold ftsHeapIndex
    have := Nat.two_pow_pos (ftsTreeHeight - level)
    omega
  · exfalso
    apply hheap
    unfold ftsHeapIndex
    have hpow : 2 ^ (ftsTreeHeight - level) * 2 ≤ 2 ^ ftsTreeHeight := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right (by omega) (by omega)
    omega

theorem treeOpeningPosition_public (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (level : Fin maxLayerHeight) :
    ¬CanonicalCoordinate.Hidden words disclosed (.graph (treeOpeningPosition lay tree leaf level)) := by
  unfold treeOpeningPosition
  split_ifs <;> simp only [CanonicalCoordinate.Hidden, not_false_eq_true]

theorem ftsNodePosition_public (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop)
    (index : Index) (level nodeIdx : Nat) :
    ¬CanonicalCoordinate.Hidden words disclosed (.graph (ftsNodePosition index level nodeIdx)) := by
  unfold ftsNodePosition
  split_ifs <;> simp only [CanonicalCoordinate.Hidden, not_false_eq_true]

def knownTreePath (known : Labels) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) : Fin maxLayerHeight → Digest :=
  fun level => if level.val < layerHeight lay then known (.graph (treeOpeningPosition lay tree leaf level)) else 0

/-- The PORS tree's nodes as the public labels know them. -/
def knownFtsNodes (known : Labels) (index : Index) : Nat → Nat → Digest :=
  fun level nodeIdx => known (.graph (ftsNodePosition index level nodeIdx))

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (f : QueryImpl HashSpec Id)

theorem canonicalGraph_treeOpening (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (level : Fin maxLayerHeight) :
    truncateHash (canonicalGraphLabels parameter otsSecret ftsSecret f (treeOpeningPosition lay tree leaf level)) =
      evalWithAnswerFn f (treeNode parameter lay tree (otsSecret lay tree) level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)) := by
  rw [canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _ (treeOpeningPosition_bound lay tree leaf level)]
  change honestValue f parameter otsSecret ftsSecret (treeOpeningPosition lay tree leaf level) = _
  unfold treeOpeningPosition
  split_ifs with hzero
  · rw [honestValue_leaf]
    simp only [hzero, honestNode]
  · rw [honestValue_node, show level.val - 1 + 1 = level.val by omega]
    rfl

theorem canonicalGraph_ftsNode (index : Index) (level nodeIdx : Nat) (hlevel : level ≤ ftsTreeHeight)
    (hnode : nodeIdx < 2 ^ (ftsTreeHeight - level)) :
    truncateHash (canonicalGraphLabels parameter otsSecret ftsSecret f (ftsNodePosition index level nodeIdx)) =
      honestFtsNode f parameter index porsTree (ftsSecret index porsTree) level nodeIdx := by
  rw [canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _
    (ftsNodePosition_bound index level nodeIdx hlevel hnode)]
  change honestValue f parameter otsSecret ftsSecret (ftsNodePosition index level nodeIdx) = _
  unfold ftsNodePosition
  split_ifs with hzero hheap
  · subst hzero
    rw [honestValue_ftsLeaf]
    have hlt : nodeIdx < 2 ^ ftsTreeHeight := by simpa using hnode
    simp only [ftsLeafOfNat, Nat.mod_eq_of_lt hlt]
  · rw [honestValue_ftsNode _ _ _ _ _ _ _ (by
      change 0 < ftsHeapIndex level nodeIdx
      unfold ftsHeapIndex
      have := Nat.two_pow_pos (ftsTreeHeight - level)
      omega)]
    exact (honestFtsNode_eq_heap f parameter index porsTree _ level nodeIdx hlevel hnode).symm
  · exact absurd (ftsNodePosition_bound index level nodeIdx hlevel hnode) (by
      unfold ftsNodePosition
      rw [if_neg hzero, dif_neg hheap]
      exact Nat.lt_irrefl 0)

theorem knownTreePath_eq (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement words disclosed known
      (CanonicalCoordinate.value otsSecret ftsSecret (canonicalGraphLabels parameter otsSecret ftsSecret f)))
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) :
    knownTreePath known lay tree leaf = evalWithAnswerFn f (treePath parameter lay tree (otsSecret lay tree) leaf) := by
  simp only [treePath, evalWithAnswerFn_sequenceFin]
  funext level
  rw [knownTreePath]
  split_ifs
  · rw [hagrees _ (treeOpeningPosition_public words disclosed lay tree leaf level)]
    exact canonicalGraph_treeOpening parameter otsSecret ftsSecret f lay tree leaf level
  · rfl

/-- **The public opening.** Read off the public labels, the honest PORS opening is the specification's. -/
theorem knownFtsOpening_eq (words : OtsReferenceWords) (disclosed : Index → FtsTree → FtsLeaf → Prop)
    (known : Labels)
    (hagrees : PublicAgreement words disclosed known
      (CanonicalCoordinate.value otsSecret ftsSecret (canonicalGraphLabels parameter otsSecret ftsSecret f)))
    (index : Index) (leaves : IndexGroup → FtsLeaf) :
    honestFts leaves (ftsSecret index porsTree) (knownFtsNodes known index) =
      evalWithAnswerFn f (ftsOpen parameter index leaves (ftsSecret index)) := by
  rw [eval_ftsOpen]
  apply honestFts_congr_tree
  intro level nodeIdx hlevel hnode
  rw [knownFtsNodes, hagrees _ (ftsNodePosition_public words disclosed index level nodeIdx)]
  exact canonicalGraph_ftsNode parameter otsSecret ftsSecret f index level nodeIdx hlevel.le hnode

def knownFrontier (known : Labels) (words : OtsReferenceWords) : OtsFrontierValues :=
  fun lay tree leaf chain =>
    if hzero : (words lay tree leaf chain).val = 0 then known (.otsStart lay tree leaf chain)
    else known (.graph (.chain lay tree leaf chain
      ⟨(words lay tree leaf chain).val - 1, by
        have hdigit := (words lay tree leaf chain).isLt
        omega⟩))

theorem knownFrontier_eq (labels : CanonicalGraphLabels) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret labels)) :
    knownFrontier known words = canonicalGraphFrontier otsSecret labels words := by
  funext lay tree leaf chain
  rw [knownFrontier, canonicalGraphFrontier]
  split_ifs with hzero
  · exact hagrees _ (by simp only [CanonicalCoordinate.Hidden, hzero, lt_self_iff_false, not_false_eq_true])
  · apply hagrees
    simp only [CanonicalCoordinate.Hidden]
    omega

def knownRoot (known : Labels) : Digest :=
  known (.graph (.node topLayer rootTree ⟨maxLayerHeight - 1, by decide⟩ ⟨0, by positivity⟩))

theorem knownRoot_eq (labels : CanonicalGraphLabels) (words : OtsReferenceWords)
    (disclosed : Index → FtsTree → FtsLeaf → Prop) (known : Labels)
    (hagrees : PublicAgreement words disclosed known (CanonicalCoordinate.value otsSecret ftsSecret labels)) :
    knownRoot known = canonicalGraphRoot labels :=
  hagrees _ (by simp only [CanonicalCoordinate.Hidden, not_false_eq_true])

end SphincsSecurity.Concrete
