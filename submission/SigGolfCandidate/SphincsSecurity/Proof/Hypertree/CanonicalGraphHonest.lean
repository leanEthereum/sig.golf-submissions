import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.CanonicalGraph
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.CanonicalSigningFrontier
namespace SphincsSecurity

namespace Position

def TreeBound : Position → Prop
  | .node _ _ level index => 2 ^ (level.val + 1) * (index.val + 1) ≤ 2 ^ maxLayerHeight
  | .ftsNode _ _ level index => 2 ^ (level.val + 1) * (index.val + 1) ≤ 2 ^ ftsTreeHeight
  | _ => True

theorem TreeBound.valid (position : Position) (h : position.TreeBound) : position.Valid := by
  cases position with
  | node lay tree level index =>
      have hpow : 0 < (2 : Nat) ^ level.val := pow_pos (by decide) _
      have hmul := Nat.mul_le_mul_right (index.val + 1) (show 2 ≤ 2 ^ (level.val + 1) by
        rw [pow_succ]; omega)
      change 2 ^ (level.val + 1) * (index.val + 1) ≤ 2 ^ maxLayerHeight at h
      change 2 * index.val + 1 < 2 ^ maxLayerHeight
      omega
  | ftsNode index tree level node =>
      have hpow : 0 < (2 : Nat) ^ level.val := pow_pos (by decide) _
      have hmul := Nat.mul_le_mul_right (node.val + 1) (show 2 ≤ 2 ^ (level.val + 1) by
        rw [pow_succ]; omega)
      change 2 ^ (level.val + 1) * (node.val + 1) ≤ 2 ^ ftsTreeHeight at h
      change 2 * node.val + 1 < 2 ^ ftsTreeHeight
      omega
  | chain | leaf | ftsLeaf | ftsRoots => trivial

private theorem treeBound_children_arithmetic (height level index : Nat)
    (h : 2 ^ (level + 1) * (index + 1) ≤ 2 ^ height) :
    2 ^ level * (2 * index + 1) ≤ 2 ^ height ∧
      2 ^ level * (2 * index + 1 + 1) ≤ 2 ^ height := by
  rw [pow_succ] at h
  constructor <;> nlinarith [Nat.zero_le (2 ^ level)]

theorem TreeBound.child {position child : Position} (h : position.TreeBound)
    (hchild : child ∈ position.children) : child.TreeBound := by
  cases position with
  | chain lay tree leaf chain step =>
      simp only [children] at hchild
      split_ifs at hchild with hstep
      · rw [List.mem_singleton] at hchild
        subst child
        trivial
      · simp at hchild
  | leaf lay tree leaf =>
      simp only [children, List.mem_ofFn] at hchild
      obtain ⟨chain, rfl⟩ := hchild
      trivial
  | node lay tree level index =>
      have hvalid : 2 * index.val + 1 < 2 ^ maxLayerHeight := TreeBound.valid _ h
      rw [children, dif_pos hvalid] at hchild
      split_ifs at hchild with hlevel
      · have bounds := treeBound_children_arithmetic maxLayerHeight level.val index.val h
        rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;>
          simp only [TreeBound, show level.val - 1 + 1 = level.val by omega] <;>
          first | exact bounds.1 | exact bounds.2
      · rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;> trivial
  | ftsLeaf => simp [children] at hchild
  | ftsNode index tree level node =>
      have hvalid : 2 * node.val + 1 < 2 ^ ftsTreeHeight := TreeBound.valid _ h
      rw [children, dif_pos hvalid] at hchild
      split_ifs at hchild with hlevel
      · have bounds := treeBound_children_arithmetic ftsTreeHeight level.val node.val h
        rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;>
          simp only [TreeBound, show level.val - 1 + 1 = level.val by omega] <;>
          first | exact bounds.1 | exact bounds.2
      · rcases List.mem_pair.mp hchild with hchild | hchild <;> subst child <;> trivial
  | ftsRoots index =>
      simp only [children, List.mem_ofFn] at hchild
      obtain ⟨tree, rfl⟩ := hchild
      norm_num [TreeBound, ftsTreeHeight]

end Position

namespace Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

variable (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

theorem canonicalGraphLabels_eq_honest (f : QueryImpl HashSpec Id)
    (position : Position) (hbound : position.TreeBound) :
    canonicalGraphLabels parameter otsSecret ftsSecret f position =
      f (honestInput f parameter otsSecret ftsSecret position) := by
  induction hdepth : position.depth using Nat.strong_induction_on generalizing position with
  | h depth ih =>
      rw [canonicalGraphLabels_consistent]
      apply congrArg f
      apply canonicalGraphInput_eq_honest parameter otsSecret ftsSecret f position (hbound.valid position)
      intro child hchild
      have hlt : child.depth < depth := by
        rw [← hdepth]
        exact Position.depth_lt_of_mem_children hchild
      rw [ih child.depth hlt child (hbound.child hchild) rfl]
      rfl

theorem canonicalGraphLabels_chain (f : QueryImpl HashSpec Id) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chain : ChainIndex) (step : ChainStep) :
    truncateHash (canonicalGraphLabels parameter otsSecret ftsSecret f (.chain lay tree leaf chain step)) =
      honestChain f parameter lay tree leaf chain (otsSecret lay tree leaf chain) (step.val + 1) := by
  rw [canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _ (by trivial)]
  exact honestValue_chain f parameter otsSecret ftsSecret lay tree leaf chain step

def canonicalGraphRoot (labels : CanonicalGraphLabels) : Digest :=
  truncateHash (labels (.node topLayer rootTree ⟨maxLayerHeight - 1, by decide⟩ ⟨0, by positivity⟩))

theorem canonicalGraphLabels_root (f : QueryImpl HashSpec Id) :
    canonicalGraphRoot (canonicalGraphLabels parameter otsSecret ftsSecret f) =
      evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree)) := by
  rw [canonicalGraphRoot, canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _
    (by norm_num [Position.TreeBound, maxLayerHeight])]
  change honestValue f parameter otsSecret ftsSecret _ = _
  rw [honestValue_node]
  rfl

/-- The top tree's node table read off graph labels: node `(0, j)` is the label of leaf `j`, node
`(l + 1, j)` the label of node position `(l, j)`; zero outside the tree. -/
def graphTop (labels : CanonicalGraphLabels) (level nodeIdx : Nat) : Digest :=
  if hnode : nodeIdx < 2 ^ maxLayerHeight then
    if level = 0 then truncateHash (labels (.leaf topLayer rootTree ⟨nodeIdx, hnode⟩))
    else if hlevel : level - 1 < maxLayerHeight then
      truncateHash (labels (.node topLayer rootTree ⟨level - 1, hlevel⟩ ⟨nodeIdx, hnode⟩))
    else 0
  else 0

theorem graphTop_canonical (f : QueryImpl HashSpec Id) (level : Nat) (hlevel : level ≤ maxLayerHeight)
    (nodeIdx : Nat) (hnodeIdx : nodeIdx < 2 ^ (maxLayerHeight - level)) :
    graphTop (canonicalGraphLabels parameter otsSecret ftsSecret f) level nodeIdx =
      honestNode f parameter topLayer rootTree (otsSecret topLayer rootTree) level nodeIdx := by
  have hnode : nodeIdx < 2 ^ maxLayerHeight :=
    Nat.lt_of_lt_of_le hnodeIdx (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  unfold graphTop
  rw [dif_pos hnode]
  split_ifs with hzero hlevel'
  · subst hzero
    rw [canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f (.leaf topLayer rootTree ⟨nodeIdx, hnode⟩) trivial]
    exact honestValue_leaf f parameter otsSecret ftsSecret topLayer rootTree ⟨nodeIdx, hnode⟩
  · have hbound : (Position.node topLayer rootTree ⟨level - 1, hlevel'⟩ ⟨nodeIdx, hnode⟩).TreeBound := by
      change 2 ^ (level - 1 + 1) * (nodeIdx + 1) ≤ 2 ^ maxLayerHeight
      rw [show level - 1 + 1 = level by omega]
      have h1 : nodeIdx + 1 ≤ 2 ^ (maxLayerHeight - level) := hnodeIdx
      calc 2 ^ level * (nodeIdx + 1) ≤ 2 ^ level * 2 ^ (maxLayerHeight - level) :=
            Nat.mul_le_mul_left _ h1
        _ = 2 ^ maxLayerHeight := by rw [← pow_add]; congr 1; omega
    rw [canonicalGraphLabels_eq_honest parameter otsSecret ftsSecret f _ hbound]
    have h := honestValue_node f parameter otsSecret ftsSecret topLayer rootTree ⟨level - 1, hlevel'⟩ ⟨nodeIdx, hnode⟩
    simp only [show level - 1 + 1 = level by omega] at h
    exact h
  · omega

/-- A key whose table is read off the canonical graph labels of `f` passes the top-tree check. -/
theorem keyTopHonest_of_graphTop (key : SecretKey) (f : QueryImpl HashSpec Id)
    (htop : ∀ level, level < maxLayerHeight → ∀ nodeIdx, nodeIdx < 2 ^ (maxLayerHeight - level) →
      key.top level nodeIdx =
        graphTop (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) level nodeIdx) :
    KeyTopHonest f key := by
  intro level hlevel nodeIdx hnodeIdx
  rw [evalWithAnswerFn_pure, htop level hlevel nodeIdx hnodeIdx]
  exact graphTop_canonical key.parameter key.otsSecret key.ftsSecret f level hlevel.le nodeIdx hnodeIdx

/-- The key's table is the one read off `labels`, on the cached region. -/
def TopFromGraph (key : SecretKey) (labels : CanonicalGraphLabels) : Prop :=
  ∀ level, level < maxLayerHeight → ∀ nodeIdx, nodeIdx < 2 ^ (maxLayerHeight - level) →
    key.top level nodeIdx = graphTop labels level nodeIdx

/-- The key the game signs with once key generation has run under `f`: root `root` and key generation's
node table. -/
noncomputable abbrev keyAtRoot (f : QueryImpl HashSpec Id) (key : SecretKey) (root : Digest) : SecretKey :=
  { key with root := root, top := honestTop f key.parameter (key.otsSecret topLayer rootTree) }

/-- The key with the root and the top-tree table read off graph labels `labels`. -/
abbrev keyAtLabels (key : SecretKey) (labels : CanonicalGraphLabels) : SecretKey :=
  { key with root := canonicalGraphRoot labels, top := graphTop labels }

theorem topFromGraph_keyAtLabels (key : SecretKey) (labels : CanonicalGraphLabels) :
    TopFromGraph (keyAtLabels key labels) labels := fun _ _ _ _ => rfl

theorem keyTopHonest_keyAtRoot (f : QueryImpl HashSpec Id) (key : SecretKey) (root : Digest) :
    KeyTopHonest f (keyAtRoot f key root) :=
  keyTopHonest_of_eq f _ rfl

/-- Key generation's table under `f` is, on the cached region, the one read off `f`'s canonical graph. -/
theorem topFromGraph_keyAtRoot (f : QueryImpl HashSpec Id) (key : SecretKey) (root : Digest) :
    TopFromGraph (keyAtRoot f key root) (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) := by
  intro level hlevel nodeIdx hnodeIdx
  have h := keyTopHonest_keyAtRoot f key root level hlevel nodeIdx hnodeIdx
  rw [evalWithAnswerFn_pure] at h
  rw [h]
  exact (graphTop_canonical key.parameter key.otsSecret key.ftsSecret f level hlevel.le nodeIdx hnodeIdx).symm

def canonicalGraphFrontier (labels : CanonicalGraphLabels) (words : OtsReferenceWords) : OtsFrontierValues :=
  fun lay tree leaf chain =>
    if h : (words lay tree leaf chain).val = 0 then otsSecret lay tree leaf chain
    else truncateHash (labels (.chain lay tree leaf chain
      ⟨(words lay tree leaf chain).val - 1, by have := (words lay tree leaf chain).isLt; omega⟩))

theorem canonicalGraphLabels_frontier (f : QueryImpl HashSpec Id) (words : OtsReferenceWords)
    (root : Digest) (top : Nat → Nat → Digest) :
    canonicalGraphFrontier otsSecret (canonicalGraphLabels parameter otsSecret ftsSecret f) words =
      canonicalFrontierValues ⟨parameter, root, otsSecret, ftsSecret, top⟩ f words := by
  funext lay tree leaf chain
  simp only [canonicalGraphFrontier, canonicalFrontierValues]
  split_ifs with hzero
  · rw [hzero]
    simp [chainWalk]
  · rw [canonicalGraphLabels_chain]
    have hstep : (words lay tree leaf chain).val - 1 + 1 = (words lay tree leaf chain).val := by omega
    simp only [hstep, honestChain]

end Concrete

end SphincsSecurity
