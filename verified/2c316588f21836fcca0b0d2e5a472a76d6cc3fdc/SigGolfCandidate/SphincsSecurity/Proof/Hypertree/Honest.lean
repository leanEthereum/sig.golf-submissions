import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.HonestFts
import SigGolfCandidate.SphincsSecurity.Proof.Ots.ExtractOts
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.Position
/-!
# The honest key at a position

One payload per position, one input, one value, all as functions of an answer function and the
sampled secrets. Nothing here is a recursion: each family reads the honest computation the statement
already defines, `honestChain`, `honestNode` and `honestFtsHeap` (the PORS tree in heap coordinates,
`Fts/HonestFts`), so the value at a position is
whatever those say. What the accounting needs of them is `honestPayload_congr`: the payload at a
position is a function of the values at its children, so two answer functions that agree on the
children agree on the input, which is what pins the honest structure to a cache.

`Valid` excludes the positions `Position` over-approximates, a node whose children would fall
outside the index width, and the PORS heap index `0`. They carry no honest meaning, and excluding them is what keeps
`honestPayload_congr` true of every position the accounting settles.
-/

namespace SphincsSecurity

open OracleComp

namespace Concrete

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter)

theorem honestChain_zero (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (secret : Digest) :
    honestChain f parameter lay tree leafIdx chainIdx secret 0 = secret := by
  simp [honestChain, chainWalk]

end Concrete

variable (f g : QueryImpl HashSpec Id) (parameter : PublicParameter)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest)

/-- The payload the honest key hashes at a position. -/
noncomputable def honestPayload : Position → HashInput
  | .chain lay tree leafIdx chainIdx step =>
      Concrete.digestBytes (Concrete.honestChain f parameter lay tree leafIdx chainIdx
        (otsSecret lay tree leafIdx chainIdx) step.val)
  | .leaf lay tree leafIdx =>
      Concrete.leafPayload
        (Concrete.honestEndpoints f parameter lay tree (otsSecret lay tree) leafIdx)
  | .node lay tree level nodeIdx =>
      Concrete.nodePayload
        (Concrete.honestNode f parameter lay tree (otsSecret lay tree) level.val (2 * nodeIdx.val))
        (Concrete.honestNode f parameter lay tree (otsSecret lay tree) level.val
          (2 * nodeIdx.val + 1))
  | .ftsLeaf index tree leafIdx => Concrete.digestBytes (ftsSecret index tree leafIdx)
  | .ftsNode index tree heap =>
      Concrete.nodePayload
        (Concrete.honestFtsHeap f parameter index tree (ftsSecret index tree) (2 * heap.val))
        (Concrete.honestFtsHeap f parameter index tree (ftsSecret index tree) (2 * heap.val + 1))

/-- The input the honest key hashes at a position. -/
noncomputable def honestInput (p : Position) : HashInput :=
  tweakableHashInput parameter p.domain (honestPayload f parameter otsSecret ftsSecret p)

/-- The value the honest key carries at a position. -/
noncomputable def honestValue (p : Position) : Digest :=
  truncateHash (f (honestInput f parameter otsSecret ftsSecret p))

/-! ### What the value at a position is

The honest computations of the statement, read off the definitions above. -/

theorem honestValue_chain (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex)
    (chainIdx : ChainIndex) (step : ChainStep) :
    honestValue f parameter otsSecret ftsSecret (.chain lay tree leafIdx chainIdx step)
      = Concrete.honestChain f parameter lay tree leafIdx chainIdx
          (otsSecret lay tree leafIdx chainIdx) (step.val + 1) := by
  rw [Concrete.honestChain_succ f parameter lay tree leafIdx chainIdx _ step.val step.isLt]
  rfl

theorem honestValue_leaf (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) :
    honestValue f parameter otsSecret ftsSecret (.leaf lay tree leafIdx)
      = Concrete.honestNode f parameter lay tree (otsSecret lay tree) 0 leafIdx.val := by
  rw [Concrete.honestNode_zero_eq_leafHash f parameter lay tree (otsSecret lay tree) leafIdx]
  rfl

theorem honestValue_node (lay : Layer) (tree : TreeIndex) (level : Fin maxLayerHeight)
    (nodeIdx : LeafIndex) :
    honestValue f parameter otsSecret ftsSecret (.node lay tree level nodeIdx)
      = Concrete.honestNode f parameter lay tree (otsSecret lay tree) (level.val + 1)
          nodeIdx.val := by
  rw [Concrete.honestNode_succ f parameter lay tree (otsSecret lay tree) level.val nodeIdx.val]
  rfl

theorem honestValue_ftsLeaf (index : Index) (tree : FtsTree) (leafIdx : FtsLeaf) :
    honestValue f parameter otsSecret ftsSecret (.ftsLeaf index tree leafIdx)
      = Concrete.honestFtsNode f parameter index tree (ftsSecret index tree) 0 leafIdx.val := by
  rw [Concrete.honestFtsNode_zero f parameter index tree (ftsSecret index tree) leafIdx]
  rfl

theorem honestValue_ftsNode (index : Index) (tree : FtsTree) (heap : Fin (2 ^ ftsTreeHeight))
    (hpos : 0 < heap.val) :
    honestValue f parameter otsSecret ftsSecret (.ftsNode index tree heap)
      = Concrete.honestFtsHeap f parameter index tree (ftsSecret index tree) heap.val := by
  rw [Concrete.honestFtsHeap_node f parameter index tree (ftsSecret index tree) heap.val hpos heap.isLt]
  rfl

/-- The root of the PORS tree of an instance: heap index `1`. -/
def Position.ftsRoot (index : Index) : Position := .ftsNode index Concrete.porsTree ⟨1, by decide⟩

theorem honestValue_ftsRoot (index : Index) :
    honestValue f parameter otsSecret ftsSecret (Position.ftsRoot index)
      = Concrete.honestFtsKey f parameter index (ftsSecret index) := by
  rw [Position.ftsRoot, honestValue_ftsNode f parameter otsSecret ftsSecret index _ _ (by decide),
    Concrete.honestFtsKey_eq_heap]

/-! ### The payload is a concatenation of the values below

Every payload of the instance is the same shape: the values at the position's children, written as
`16` bytes each, one after another, or the secret the family starts from. Reading it that way once is
what makes the accounting generic: the payload is a function of the children's values, and it
determines each of them.
-/

/-- The positions `Position` over-approximates: a node whose children would fall outside the index
width. Nothing honest lives there, and the accounting never settles one. -/
def Position.Valid : Position → Prop
  | .node _ _ _ nodeIdx => 2 * nodeIdx.val + 1 < 2 ^ maxLayerHeight
  | .ftsNode _ _ heap => 0 < heap.val
  | _ => True

/-- The values at a position's children. -/
noncomputable def childValues (p : Position) : List Digest :=
  p.children.map (honestValue f parameter otsSecret ftsSecret)

/-- The values a position's payload concatenates: those at its children, or the secret its family
starts from. -/
noncomputable def slots : Position → List Digest
  | .chain lay tree leafIdx chainIdx step =>
      if step.val = 0 then [otsSecret lay tree leafIdx chainIdx]
      else childValues f parameter otsSecret ftsSecret (.chain lay tree leafIdx chainIdx step)
  | .ftsLeaf index tree leafIdx => [ftsSecret index tree leafIdx]
  | p => childValues f parameter otsSecret ftsSecret p

/-- **The payload is the values below it.** -/
theorem honestPayload_eq_slots {p : Position} (hvalid : p.Valid) :
    honestPayload f parameter otsSecret ftsSecret p
      = (slots f parameter otsSecret ftsSecret p).flatMap Concrete.digestBytes := by
  cases p with
  | chain lay tree leafIdx chainIdx step =>
      rcases Nat.eq_zero_or_pos step.val with hstep | hstep
      · have hslots : slots f parameter otsSecret ftsSecret
            (.chain lay tree leafIdx chainIdx step) = [otsSecret lay tree leafIdx chainIdx] := by
          simp only [slots, if_pos hstep]
        rw [hslots]
        simp only [honestPayload, hstep, Concrete.honestChain_zero, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
      · obtain ⟨s, hs⟩ : ∃ s, step.val = s + 1 := ⟨step.val - 1, by omega⟩
        have hslt : s < chainLength - 1 := by have := step.isLt; omega
        have hchildren : (Position.chain lay tree leafIdx chainIdx step).children
            = [.chain lay tree leafIdx chainIdx ⟨s, hslt⟩] := by
          rw [Position.children, dif_pos hstep]
          simp only [List.cons.injEq, Position.chain.injEq, Fin.mk.injEq, and_true, true_and]
          omega
        have hslots : slots f parameter otsSecret ftsSecret
            (.chain lay tree leafIdx chainIdx step)
            = [honestValue f parameter otsSecret ftsSecret
                (.chain lay tree leafIdx chainIdx ⟨s, hslt⟩)] := by
          simp only [slots, if_neg (by omega : ¬ step.val = 0), childValues, hchildren,
            List.map_cons, List.map_nil]
        rw [hslots, honestValue_chain]
        simp only [honestPayload, List.flatMap_cons, List.flatMap_nil, List.append_nil, hs]
  | leaf lay tree leafIdx =>
      have hslots : slots f parameter otsSecret ftsSecret (.leaf lay tree leafIdx)
          = List.ofFn fun chainIdx : ChainIndex => honestValue f parameter otsSecret ftsSecret
              (.chain lay tree leafIdx chainIdx Position.lastChainStep) := by
        simp only [slots, childValues, Position.children, List.map_ofFn, Function.comp_def]
      rw [hslots]
      simp only [honestPayload, Concrete.leafPayload]
      refine congrArg _ (congrArg _ (funext fun chainIdx => ?_))
      rw [honestValue_chain]
      rfl
  | node lay tree level nodeIdx =>
      simp only [Position.Valid] at hvalid
      rcases Nat.eq_zero_or_pos level.val with hlevel | hlevel
      · have hchildren : (Position.node lay tree level nodeIdx).children
            = [.leaf lay tree ⟨2 * nodeIdx.val, by omega⟩,
              .leaf lay tree ⟨2 * nodeIdx.val + 1, by omega⟩] := by
          rw [Position.children, dif_pos hvalid, dif_neg (by omega)]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_leaf, honestValue_leaf, hlevel]
      · have hchildren : (Position.node lay tree level nodeIdx).children
            = [.node lay tree ⟨level.val - 1, by have := level.isLt; omega⟩
                ⟨2 * nodeIdx.val, by omega⟩,
              .node lay tree ⟨level.val - 1, by have := level.isLt; omega⟩
                ⟨2 * nodeIdx.val + 1, by omega⟩] := by
          rw [Position.children, dif_pos hvalid, dif_pos hlevel]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_node, honestValue_node, show level.val - 1 + 1 = level.val from by omega]
  | ftsLeaf index tree leafIdx =>
      simp [slots, honestPayload]
  | ftsNode index tree heap =>
      simp only [Position.Valid] at hvalid
      have hheap := heap.isLt
      have heven : (2 : Nat) ^ ftsTreeHeight = 2 * 2 ^ (ftsTreeHeight - 1) := rfl
      by_cases hidx : 2 * heap.val + 1 < 2 ^ ftsTreeHeight
      · have hchildren : (Position.ftsNode index tree heap).children
            = [.ftsNode index tree ⟨2 * heap.val, by omega⟩,
              .ftsNode index tree ⟨2 * heap.val + 1, hidx⟩] := by
          rw [Position.children, dif_pos hvalid, dif_pos hidx]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_ftsNode _ _ _ _ _ _ _ (by simp only; omega),
          honestValue_ftsNode _ _ _ _ _ _ _ (by simp only; omega)]
      · have hchildren : (Position.ftsNode index tree heap).children
            = [.ftsLeaf index tree ⟨2 * heap.val - 2 ^ ftsTreeHeight, by omega⟩,
              .ftsLeaf index tree ⟨2 * heap.val + 1 - 2 ^ ftsTreeHeight, by omega⟩] := by
          rw [Position.children, dif_pos hvalid, dif_neg hidx]
        simp only [slots, childValues, hchildren, List.map_cons, List.map_nil, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, honestPayload, Concrete.nodePayload]
        rw [honestValue_ftsLeaf, honestValue_ftsLeaf, ← Concrete.honestFtsHeap_leaf,
          ← Concrete.honestFtsHeap_leaf]
        simp only
        rw [show 2 ^ ftsTreeHeight + (2 * heap.val - 2 ^ ftsTreeHeight) = 2 * heap.val by omega,
          show 2 ^ ftsTreeHeight + (2 * heap.val + 1 - 2 ^ ftsTreeHeight) = 2 * heap.val + 1 by omega]

end SphincsSecurity
