import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.Extract
/-!
# The honest PORS tree

The value the honest PORS tree of an instance carries, in the two coordinates the development uses:
`(level, nodeIdx)`, the recursion of the specification (`ftsNode`), and the heap index `H` the tree hashes
its nodes under and the verifier's stack machine works with (leaf `j` is `2^14 + j`, the root is `1`, the
children of `H` are `2H` and `2H + 1`). `honestFtsHeap_node` and `honestFtsHeap_leaf` are the two
equations of the heap view; `honestFtsNode_eq_heap` identifies the two views on the tree.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index) (tree : FtsTree)
  (secret : FtsLeaf → Digest)

theorem ftsLeafOfNat_val (leaf : FtsLeaf) : ftsLeafOfNat leaf.val = leaf := by
  ext
  simp [ftsLeafOfNat, Nat.mod_eq_of_lt leaf.isLt]

/-- The value the honest PORS tree carries at node `(level, nodeIdx)`. -/
def honestFtsNode (level nodeIdx : Nat) : Digest :=
  evalWithAnswerFn f (ftsNode parameter index tree secret level nodeIdx)

theorem honestFtsNode_succ (level nodeIdx : Nat) :
    honestFtsNode f parameter index tree secret (level + 1) nodeIdx
      = truncateHash (f (tweakableHashInput parameter
          (.ftsNode index tree (ftsHeapIndex (level + 1) nodeIdx))
          (nodePayload (honestFtsNode f parameter index tree secret level (2 * nodeIdx))
            (honestFtsNode f parameter index tree secret level (2 * nodeIdx + 1))))) := by
  simp only [honestFtsNode, ftsNode_succ_eq, evalWithAnswerFn_bind, eval_tweakableHash]

theorem honestFtsNode_zero (leafIdx : FtsLeaf) :
    honestFtsNode f parameter index tree secret 0 leafIdx.val
      = truncateHash (f (tweakableHashInput parameter (.ftsLeaf index tree leafIdx.val)
          (digestBytes (secret leafIdx)))) := by
  simp only [honestFtsNode, ftsNode_zero_eq, ftsLeafOfNat_val, ftsLeafHash, eval_tweakableHash]

/-! ### The heap view -/

/-- The value the honest PORS tree carries at heap index `heap`: a node (`1 ≤ heap < 2^14`) hashes its
children `2 heap` and `2 heap + 1` under its heap index; anything else reads the leaf `heap - 2^14`
(so heap index `0` has no meaning, and heap indices at or above `2^15` wrap in the leaf reduction). -/
def honestFtsHeap (heap : Nat) : Digest :=
  if h : 0 < heap ∧ heap < 2 ^ ftsTreeHeight then
    truncateHash (f (tweakableHashInput parameter (.ftsNode index tree heap)
      (nodePayload (honestFtsHeap (2 * heap)) (honestFtsHeap (2 * heap + 1)))))
  else
    honestFtsNode f parameter index tree secret 0 (heap - 2 ^ ftsTreeHeight)
termination_by 2 ^ ftsTreeHeight - heap
decreasing_by all_goals omega

theorem honestFtsHeap_node (heap : Nat) (hpos : 0 < heap) (hlt : heap < 2 ^ ftsTreeHeight) :
    honestFtsHeap f parameter index tree secret heap
      = truncateHash (f (tweakableHashInput parameter (.ftsNode index tree heap)
          (nodePayload (honestFtsHeap f parameter index tree secret (2 * heap))
            (honestFtsHeap f parameter index tree secret (2 * heap + 1))))) := by
  rw [honestFtsHeap, dif_pos ⟨hpos, hlt⟩]

theorem honestFtsHeap_leaf (leafIdx : Nat) :
    honestFtsHeap f parameter index tree secret (2 ^ ftsTreeHeight + leafIdx)
      = honestFtsNode f parameter index tree secret 0 leafIdx := by
  rw [honestFtsHeap, dif_neg (by omega), Nat.add_sub_cancel_left]

theorem honestFtsHeap_leaf' (leaf : FtsLeaf) :
    honestFtsHeap f parameter index tree secret (2 ^ ftsTreeHeight + leaf.val)
      = truncateHash (f (tweakableHashInput parameter (.ftsLeaf index tree leaf.val)
          (digestBytes (secret leaf)))) := by
  rw [honestFtsHeap_leaf, honestFtsNode_zero]

theorem ftsHeapIndex_zero (nodeIdx : Nat) : ftsHeapIndex 0 nodeIdx = 2 ^ ftsTreeHeight + nodeIdx := rfl

/-- The two views agree on the tree: node `(level, nodeIdx)` is heap index `2^(14 - level) + nodeIdx`. -/
theorem honestFtsNode_eq_heap (level nodeIdx : Nat) (hlevel : level ≤ ftsTreeHeight)
    (hnode : nodeIdx < 2 ^ (ftsTreeHeight - level)) :
    honestFtsNode f parameter index tree secret level nodeIdx
      = honestFtsHeap f parameter index tree secret (ftsHeapIndex level nodeIdx) := by
  induction level generalizing nodeIdx with
  | zero => rw [ftsHeapIndex_zero, honestFtsHeap_leaf]
  | succ level ih =>
      have hpow : 2 ^ (ftsTreeHeight - level) = 2 * 2 ^ (ftsTreeHeight - (level + 1)) := by
        rw [← pow_succ']; congr 1; omega
      have hpos : 0 < 2 ^ (ftsTreeHeight - (level + 1)) := Nat.two_pow_pos _
      have hle : 2 ^ (ftsTreeHeight - (level + 1)) ≤ 2 ^ (ftsTreeHeight - 1) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      have htop : 2 ^ (ftsTreeHeight - 1) * 2 = 2 ^ ftsTreeHeight := by decide
      rw [honestFtsNode_succ, honestFtsHeap_node f parameter index tree secret _
        (by unfold ftsHeapIndex; omega) (by unfold ftsHeapIndex; omega),
        ih (2 * nodeIdx) (by omega) (by omega), ih (2 * nodeIdx + 1) (by omega) (by omega)]
      have h1 : ftsHeapIndex level (2 * nodeIdx) = 2 * ftsHeapIndex (level + 1) nodeIdx := by
        unfold ftsHeapIndex; omega
      have h2 : ftsHeapIndex level (2 * nodeIdx + 1) = 2 * ftsHeapIndex (level + 1) nodeIdx + 1 := by
        unfold ftsHeapIndex; omega
      rw [h1, h2]

/-- The value of the honest PORS tree's root, the instance's few-time public key. -/
def honestFtsKey (secret : FtsTree → FtsLeaf → Digest) : Digest :=
  evalWithAnswerFn f (ftsKey parameter index secret)

theorem honestFtsKey_eq_node (secret : FtsTree → FtsLeaf → Digest) :
    honestFtsKey f parameter index secret
      = honestFtsNode f parameter index porsTree (secret porsTree) ftsTreeHeight 0 := rfl

theorem honestFtsKey_eq_heap (secret : FtsTree → FtsLeaf → Digest) :
    honestFtsKey f parameter index secret
      = honestFtsHeap f parameter index porsTree (secret porsTree) 1 := by
  rw [honestFtsKey_eq_node, honestFtsNode_eq_heap f parameter index porsTree _ ftsTreeHeight 0
    le_rfl (by decide)]
  rfl

end SphincsSecurity.Concrete
