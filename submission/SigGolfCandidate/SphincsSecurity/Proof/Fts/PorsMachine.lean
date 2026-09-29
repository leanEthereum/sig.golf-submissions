import SigGolfCandidate.SphincsSecurity.Proof.Fts.HonestFts
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Support
/-!
# The PORS stack machine under an answer function

`ftsRecover` (Scheme.lean) is a monadic stack machine. Under a fixed answer function `f` it is a pure
function; this module writes that function out (`recoverRun`), with ghost fields recording what the run
did: every query it made (`queries`), the query whose answer is the current node (`last`), and the items
of the signature it consumed, each with the position it was consumed at (`reads`: the sibling heap index of
a fold and the node supplied there; `parities`: the start heap index of a segment that folds and its parity
bit; `openings`: a leaf value and the secret supplied for it).

* `eval_ftsRecover`: `evalWithAnswerFn f (ftsRecover …) = (recoverRun …).map (·.node)`.
* `queriedInputs_ftsRecover`: an accepted run's recorded queries are exactly the queries of `ftsRecover`.

The control flow (heap indices, the stack's sibling heap indices, fold and segment counters) never depends
on a node value, which is what the hash-free structure of `PorsStructure` uses.
-/

namespace SphincsSecurity.Concrete

open OracleComp

namespace PorsMachine

/-- The run's state: the stack machine's state and the ghost record. -/
structure Run extends RecoverState where
  /-- The query whose answer is `node`. -/
  last : HashInput
  /-- Every query so far, in order. -/
  queries : List HashInput
  /-- Per fold: the sibling's heap index and the node the signature supplied there. -/
  reads : List (Nat × Digest)
  /-- Per segment with at least one fold: its start heap index and its parity bit. -/
  parities : List (Nat × Bool)
  /-- Per leaf: its value and the secret the signature supplied for it. -/
  openings : List (Nat × Digest)

/-! ### Heap-index arithmetic -/

theorem xor_one_cases (e : Nat) :
    (e % 2 = 0 ∧ e ^^^ 1 = e + 1) ∨ (e % 2 = 1 ∧ e ^^^ 1 = e - 1) := by
  obtain ⟨j, h | h⟩ := index_sibling_cases e
  · left
    rw [← nat_xor_eq]
    omega
  · right
    rw [← nat_xor_eq]
    omega

theorem xor_one_xor_one (e : Nat) : e ^^^ 1 ^^^ 1 = e := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

theorem two_pow_or_eq_add (value : Nat) (hvalue : value < 2 ^ ftsTreeHeight) :
    2 ^ ftsTreeHeight ||| value = 2 ^ ftsTreeHeight + value := by
  rw [Nat.or_comm, Nat.or_two_pow_eq_add_of_lt hvalue, Nat.add_comm]

/-- The start: nothing computed, nothing consumed. -/
def Run.initial : Run := ⟨RecoverState.initial, 0 |> fun _ => [], [], [], [], []⟩

theorem Run.initial_toRecoverState : Run.initial.toRecoverState = RecoverState.initial := rfl

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)

/-- The input of a PORS node hash at heap index `heap`. -/
def nodeInput (heap : Nat) (payload : HashInput) : HashInput :=
  tweakableHashInput parameter (.ftsNode index porsTree heap) payload

/-- The input of a PORS leaf hash of leaf `value`. -/
def leafInput (value : Nat) (secret : Digest) : HashInput :=
  tweakableHashInput parameter (.ftsLeaf index porsTree value) (digestBytes secret)

/-- The child order of fold `position` from heap index `heap`: the segment's parity for the first fold,
bit `0` of the heap index after. -/
def foldRight (segment : Segment) (position heap : Nat) : Bool :=
  if position = 0 then segment.parity else decide (heap % 2 = 1)

/-- The input fold `position` of a segment hashes, from `current` at heap index `heap`. -/
def foldInput (segment : Segment) (position heap : Nat) (current : Digest) : HashInput :=
  nodeInput parameter index (heap / 2)
    (foldPayload (foldRight segment position heap) (segment.node position) current)

/-- The input of a pending hash, the current node being `current`. -/
def pendingInput (pending : PendingHash) (current : Digest) : HashInput :=
  match pending with
  | .leaf value secret => leafInput parameter index value secret
  | .merge heapIdx left => nodeInput parameter index heapIdx (nodePayload left current)

/-- The openings a pending hash consumes: a leaf's value and secret. -/
def pendingOpenings (pending : PendingHash) : List (Nat × Digest) :=
  match pending with
  | .leaf value secret => [(value, secret)]
  | .merge _ _ => []

/-- One query: its answer becomes the node. -/
def Run.hash (r : Run) (input : HashInput) : Run :=
  { r with node := truncateHash (f input), last := input, queries := r.queries ++ [input] }

@[simp] theorem Run.hash_stack (r : Run) (input : HashInput) : (r.hash f input).stack = r.stack := rfl
@[simp] theorem Run.hash_heap (r : Run) (input : HashInput) : (r.hash f input).heap = r.heap := rfl
@[simp] theorem Run.hash_folds (r : Run) (input : HashInput) : (r.hash f input).folds = r.folds := rfl
@[simp] theorem Run.hash_segment (r : Run) (input : HashInput) : (r.hash f input).segment = r.segment := rfl
@[simp] theorem Run.hash_node (r : Run) (input : HashInput) :
    (r.hash f input).node = truncateHash (f input) := rfl

/-- `foldSegment`, pure. -/
def foldRun (segment : Segment) : Nat → Nat → Run → Run
  | 0, _, r => r
  | remaining + 1, position, r =>
      let input := foldInput parameter index segment position r.heap r.node
      foldRun segment remaining (position + 1)
        { r.hash f input with
          heap := r.heap / 2
          reads := r.reads ++ [(r.heap ^^^ 1, segment.node position)]
          parities := if position = 0 then r.parities ++ [(r.heap, segment.parity)] else r.parities }

/-- The verifier's two rejections of a segment before its pending hash: more than `14` folds, or folds with a
parity bit that is not bit `0` of the start heap index. -/
def SegmentRejects (segment : Segment) (heap : Nat) : Prop :=
  ftsTreeHeight < segment.folds.val ∨ (segment.folds.val ≠ 0 ∧ segment.parity ≠ decide (heap % 2 = 1))

instance (segment : Segment) (heap : Nat) : Decidable (SegmentRejects segment heap) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- `recoverSegments`, pure. -/
def segmentsRun (segments : Fin ftsSegments → Segment) : Nat → PendingHash → Run → Option Run
  | 0, _, _ => none
  | fuel + 1, pending, r =>
      if hsegment : r.segment < ftsSegments then
        let segment := segments ⟨r.segment, hsegment⟩
        if SegmentRejects segment r.heap then
          none
        else
          let started : Run := { r.hash f (pendingInput parameter index pending r.node) with
            openings := r.openings ++ pendingOpenings pending }
          let folded := foldRun f parameter index segment segment.folds.val 0 started
          let next : Run := { folded with folds := r.folds + segment.folds.val, segment := r.segment + 1 }
          if segment.merge then
            match next.stack with
            | [] => none
            | (left, sibling) :: rest =>
                if sibling = next.heap then
                  segmentsRun segments fuel (.merge (next.heap / 2) left)
                    { next with stack := rest, heap := next.heap / 2 }
                else
                  none
          else
            some next
      else
        none

/-- `recoverLeaves`, pure. -/
def leavesRun (values : SlotCode → Nat) (fts : FtsSignature) : Nat → Nat → Nat → Run → Option Run
  | 0, _, _, r => some r
  | remaining + 1, position, previous, r =>
      if hposition : position < ftsOpenings then
        let value := values (fts.perm ⟨position, hposition⟩)
        if 0 < position ∧ ¬ previous < value then
          none
        else if position + 1 = ftsOpenings ∧ ¬ value < 2 ^ ftsTreeHeight then
          none
        else
          match segmentsRun f parameter index fts.segments ftsSegments
              (.leaf value (fts.secrets ⟨position, hposition⟩))
              { r with heap := 2 ^ ftsTreeHeight ||| value } with
          | none => none
          | some r' =>
              leavesRun values fts remaining (position + 1) value
                (if position + 1 < ftsOpenings then
                  { r' with stack := (r'.node, r'.heap ^^^ 1) :: r'.stack } else r')
      else
        none

/-- The final test of `ftsRecover`. -/
def Accepts (r : Run) : Prop := r.folds ≤ ftsAuthCapacity ∧ r.heap = 1 ∧ r.stack = []

instance (r : Run) : Decidable (Accepts r) := inferInstanceAs (Decidable (_ ∧ _))

/-- `ftsRecover`, pure: the accepted final run. -/
def recoverRun (values : SlotCode → Nat) (fts : FtsSignature) : Option Run :=
  match leavesRun f parameter index values fts ftsOpenings 0 0 Run.initial with
  | none => none
  | some r => if Accepts r then some r else none

/-! ### Honest values and honest consumption -/

/-- The honest value of the instance's PORS tree at a heap index. -/
abbrev honest (secret : FtsLeaf → Digest) (heap : Nat) : Digest :=
  honestFtsHeap f parameter index porsTree secret heap

/-- Everything the run consumed is honest at the position it consumed it at: every folded node is the honest
node at its sibling heap index, every folding segment's parity is bit `0` of its start heap index, and every
secret is the true secret of its leaf. -/
def Consumed (secret : FtsLeaf → Digest) (r : Run) : Prop :=
  (∀ read ∈ r.reads, read.2 = honest f parameter index secret read.1) ∧
    (∀ parity ∈ r.parities, parity.2 = decide (parity.1 % 2 = 1)) ∧
    ∀ opening ∈ r.openings, opening.2 = secret (ftsLeafOfNat opening.1)

/-! ### Evaluation -/

theorem evalWithAnswerFn_dite {α : Type} (c : Prop) [Decidable c] (a : c → OracleComp HashSpec α)
    (b : ¬ c → OracleComp HashSpec α) :
    evalWithAnswerFn f (if h : c then a h else b h)
      = if h : c then evalWithAnswerFn f (a h) else evalWithAnswerFn f (b h) := by
  split <;> rfl

theorem evalWithAnswerFn_ite {α : Type} (c : Prop) [Decidable c] (a b : OracleComp HashSpec α) :
    evalWithAnswerFn f (if c then a else b) = if c then evalWithAnswerFn f a else evalWithAnswerFn f b := by
  split <;> rfl

theorem eval_foldSegment (segment : Segment) (remaining position : Nat) (r : Run) :
    evalWithAnswerFn f (foldSegment parameter index segment remaining position r.node r.heap)
      = ((foldRun f parameter index segment remaining position r).node,
          (foldRun f parameter index segment remaining position r).heap) := by
  induction remaining generalizing position r with
  | zero => rfl
  | succ remaining ih =>
      simp only [foldSegment, evalWithAnswerFn_bind, eval_tweakableHash, foldRun]
      rw [← ih]
      rfl

theorem eval_foldSegment' (segment : Segment) (remaining position : Nat) (r : Run) (current : Digest)
    (heap : Nat) (hnode : r.node = current) (hheap : r.heap = heap) :
    evalWithAnswerFn f (foldSegment parameter index segment remaining position current heap)
      = ((foldRun f parameter index segment remaining position r).node,
          (foldRun f parameter index segment remaining position r).heap) := by
  subst hnode hheap
  exact eval_foldSegment f parameter index segment remaining position r

@[simp] theorem foldRun_stack (segment : Segment) (remaining position : Nat) (r : Run) :
    (foldRun f parameter index segment remaining position r).stack = r.stack := by
  induction remaining generalizing position r with
  | zero => rfl
  | succ remaining ih => simp only [foldRun, ih]; rfl

@[simp] theorem foldRun_folds (segment : Segment) (remaining position : Nat) (r : Run) :
    (foldRun f parameter index segment remaining position r).folds = r.folds := by
  induction remaining generalizing position r with
  | zero => rfl
  | succ remaining ih => simp only [foldRun, ih]; rfl

@[simp] theorem foldRun_segment (segment : Segment) (remaining position : Nat) (r : Run) :
    (foldRun f parameter index segment remaining position r).segment = r.segment := by
  induction remaining generalizing position r with
  | zero => rfl
  | succ remaining ih => simp only [foldRun, ih]; rfl

theorem eval_recoverSegments (segments : Fin ftsSegments → Segment) (fuel : Nat) (pending : PendingHash)
    (r : Run) :
    evalWithAnswerFn f (recoverSegments parameter index segments fuel pending r.toRecoverState)
      = (segmentsRun f parameter index segments fuel pending r).map Run.toRecoverState := by
  induction fuel generalizing pending r with
  | zero => rfl
  | succ fuel ih =>
      rw [recoverSegments, segmentsRun, evalWithAnswerFn_dite]
      by_cases hsegment : r.segment < ftsSegments
      · rw [dif_pos hsegment, dif_pos hsegment]
        dsimp only
        rw [evalWithAnswerFn_ite]
        by_cases hfolds : ftsTreeHeight < (segments ⟨r.segment, hsegment⟩).folds.val
        · rw [if_pos hfolds, if_pos (show SegmentRejects _ _ from Or.inl hfolds)]
          rfl
        rw [if_neg hfolds, evalWithAnswerFn_ite]
        by_cases hparity : (segments ⟨r.segment, hsegment⟩).folds.val ≠ 0 ∧
            (segments ⟨r.segment, hsegment⟩).parity ≠ decide (r.heap % 2 = 1)
        · rw [if_pos hparity, if_pos (show SegmentRejects _ _ from Or.inr hparity)]
          rfl
        · rw [if_neg hparity, if_neg (show ¬ SegmentRejects _ _ by rintro (h | h) <;> contradiction)]
          cases pending
          case' leaf value secret =>
              simp only [evalWithAnswerFn_bind, ftsLeafHash, eval_tweakableHash]
              rw [eval_foldSegment' f parameter index _ _ _
                { r.hash f (pendingInput parameter index (.leaf value secret) r.node) with
                  openings := r.openings ++ pendingOpenings (.leaf value secret) }
                (truncateHash (f (tweakableHashInput parameter (.ftsLeaf index porsTree value)
                  (bytesLE 16 secret)))) r.heap rfl rfl]
          case' merge heapIdx left =>
              simp only [evalWithAnswerFn_bind, eval_tweakableHash]
              rw [eval_foldSegment' f parameter index _ _ _
                { r.hash f (pendingInput parameter index (.merge heapIdx left) r.node) with
                  openings := r.openings ++ pendingOpenings (.merge heapIdx left) }
                (truncateHash (f (tweakableHashInput parameter (.ftsNode index porsTree heapIdx)
                  (nodePayload left r.node)))) r.heap rfl rfl]
          all_goals
            dsimp only
            rw [evalWithAnswerFn_ite]
            simp only [foldRun_stack, Run.hash_stack]
            by_cases hmerge : (segments ⟨r.segment, hsegment⟩).merge = true
            · rw [if_pos hmerge, if_pos hmerge]
              rcases hstack : r.stack with _ | ⟨⟨left, sibling⟩, rest⟩
              · rfl
              · dsimp only
                rw [evalWithAnswerFn_ite]
                split_ifs
                · rw [← ih]
                · rfl
            · rw [if_neg hmerge, if_neg hmerge]
              rfl
      · rw [dif_neg hsegment, dif_neg hsegment]
        rfl

theorem eval_recoverLeaves (values : SlotCode → Nat) (fts : FtsSignature) (remaining position previous : Nat)
    (r : Run) :
    evalWithAnswerFn f (recoverLeaves parameter index values fts remaining position previous r.toRecoverState)
      = (leavesRun f parameter index values fts remaining position previous r).map Run.toRecoverState := by
  induction remaining generalizing position previous r with
  | zero => rfl
  | succ remaining ih =>
      rw [recoverLeaves, leavesRun, evalWithAnswerFn_dite]
      by_cases hposition : position < ftsOpenings
      · rw [dif_pos hposition, dif_pos hposition]
        dsimp only
        rw [evalWithAnswerFn_ite]
        by_cases horder : 0 < position ∧ ¬ previous < values (fts.perm ⟨position, hposition⟩)
        · rw [if_pos horder, if_pos horder]
          rfl
        · rw [if_neg horder, if_neg horder, evalWithAnswerFn_ite]
          by_cases hlast : position + 1 = ftsOpenings ∧
              ¬ values (fts.perm ⟨position, hposition⟩) < 2 ^ ftsTreeHeight
          · rw [if_pos hlast, if_pos hlast]
            rfl
          · rw [if_neg hlast, if_neg hlast, evalWithAnswerFn_bind]
            have hsegments := eval_recoverSegments f parameter index fts.segments ftsSegments
              (.leaf (values (fts.perm ⟨position, hposition⟩)) (fts.secrets ⟨position, hposition⟩))
              { r with heap := 2 ^ ftsTreeHeight ||| values (fts.perm ⟨position, hposition⟩) }
            erw [hsegments]
            rcases segmentsRun f parameter index fts.segments ftsSegments _ _ with _ | r'
            · rfl
            · dsimp only
              rw [← ih]
              by_cases hpush : position + 1 < ftsOpenings
              · simp only [hpush, if_true]
                rfl
              · simp only [hpush, if_false]
                rfl
      · rw [dif_neg hposition, dif_neg hposition]
        rfl

theorem eval_ftsRecover (values : SlotCode → Nat) (fts : FtsSignature) :
    evalWithAnswerFn f (ftsRecover parameter index values fts)
      = (recoverRun f parameter index values fts).map (·.node) := by
  rw [ftsRecover, recoverRun, evalWithAnswerFn_bind, ← Run.initial_toRecoverState, eval_recoverLeaves]
  rcases leavesRun f parameter index values fts ftsOpenings 0 0 Run.initial with _ | r
  · rfl
  · simp only [Option.map_some]
    rw [evalWithAnswerFn_ite]
    by_cases haccept : Accepts r
    · rw [if_pos haccept, if_pos (show r.folds ≤ ftsAuthCapacity ∧ r.heap = 1 ∧ r.stack = [] from haccept)]
      rfl
    · rw [if_neg haccept, if_neg (show ¬(r.folds ≤ ftsAuthCapacity ∧ r.heap = 1 ∧ r.stack = []) from haccept)]
      rfl

/-! ### Queries -/

theorem queriedInputs_dite {α : Type} (c : Prop) [Decidable c] (a : c → OracleComp HashSpec α)
    (b : ¬ c → OracleComp HashSpec α) :
    queriedInputs f (if h : c then a h else b h)
      = if h : c then queriedInputs f (a h) else queriedInputs f (b h) := by
  split <;> rfl

theorem queriedInputs_ite {α : Type} (c : Prop) [Decidable c] (a b : OracleComp HashSpec α) :
    queriedInputs f (if c then a else b) = if c then queriedInputs f a else queriedInputs f b := by
  split <;> rfl

theorem foldRun_queries (segment : Segment) (remaining position : Nat) (r : Run) :
    (foldRun f parameter index segment remaining position r).queries
      = r.queries ++ queriedInputs f (foldSegment parameter index segment remaining position r.node r.heap) := by
  induction remaining generalizing position r with
  | zero => simp [foldRun, foldSegment]
  | succ remaining ih =>
      rw [foldRun, ih, foldSegment, queriedInputs_bind, queriedInputs_tweakableHash, eval_tweakableHash]
      simp only [Run.hash, List.append_assoc, List.singleton_append]
      rfl

theorem segmentsRun_queries (segments : Fin ftsSegments → Segment) (fuel : Nat) (pending : PendingHash)
    (r r' : Run) (hrun : segmentsRun f parameter index segments fuel pending r = some r') :
    r'.queries = r.queries ++ queriedInputs f (recoverSegments parameter index segments fuel pending r.toRecoverState) := by
  induction fuel generalizing pending r with
  | zero => simp [segmentsRun] at hrun
  | succ fuel ih =>
      rw [recoverSegments, queriedInputs_dite]
      rw [segmentsRun] at hrun
      by_cases hsegment : r.segment < ftsSegments
      · rw [dif_pos hsegment]
        rw [dif_pos hsegment] at hrun
        dsimp only at hrun ⊢
        rw [queriedInputs_ite]
        by_cases hfolds : ftsTreeHeight < (segments ⟨r.segment, hsegment⟩).folds.val
        · rw [if_pos (show SegmentRejects _ _ from Or.inl hfolds)] at hrun
          simp at hrun
        rw [if_neg hfolds, queriedInputs_ite]
        by_cases hparity : (segments ⟨r.segment, hsegment⟩).folds.val ≠ 0 ∧
            (segments ⟨r.segment, hsegment⟩).parity ≠ decide (r.heap % 2 = 1)
        · rw [if_pos (show SegmentRejects _ _ from Or.inr hparity)] at hrun
          simp at hrun
        · rw [if_neg hparity]
          rw [if_neg (show ¬ SegmentRejects _ _ by rintro (h | h) <;> contradiction)] at hrun
          -- the pure run's pieces
          set started : Run := { r.hash f (pendingInput parameter index pending r.node) with
            openings := r.openings ++ pendingOpenings pending } with hstarted
          have hfolded := foldRun_queries f parameter index (segments ⟨r.segment, hsegment⟩)
            (segments ⟨r.segment, hsegment⟩).folds.val 0 started
          have heval := eval_foldSegment f parameter index (segments ⟨r.segment, hsegment⟩)
            (segments ⟨r.segment, hsegment⟩).folds.val 0 started
          cases pending
          case' leaf value secret =>
            simp only [ftsLeafHash]
            rw [queriedInputs_bind, queriedInputs_tweakableHash]
            simp only [eval_tweakableHash]
            rw [queriedInputs_bind]
            erw [heval]
          case' merge heapIdx left =>
            rw [queriedInputs_bind, queriedInputs_tweakableHash]
            simp only [eval_tweakableHash]
            rw [queriedInputs_bind]
            erw [heval]
          all_goals
            have hq : started.queries = r.queries ++ [started.last] := rfl
            rw [hq] at hfolded
            have hstack : started.stack = r.stack := rfl
            simp only [foldRun_stack, hstack] at hrun
            rw [queriedInputs_ite]
            by_cases hmerge : (segments ⟨r.segment, hsegment⟩).merge = true
            · rw [if_pos hmerge] at hrun ⊢
              rcases hst : r.stack with _ | ⟨⟨left', sibling⟩, rest⟩
              · rw [hst] at hrun
                simp at hrun
              · rw [hst] at hrun
                dsimp only at hrun ⊢
                rw [queriedInputs_ite]
                by_cases hsibling : sibling = (foldRun f parameter index (segments ⟨r.segment, hsegment⟩)
                    (segments ⟨r.segment, hsegment⟩).folds.val 0 started).heap
                · rw [if_pos hsibling] at hrun
                  rw [if_pos hsibling]
                  rw [ih _ _ hrun]
                  simp only [hfolded, List.append_assoc]
                  rfl
                · rw [if_neg hsibling] at hrun
                  simp at hrun
            · rw [if_neg hmerge] at hrun ⊢
              cases hrun
              simp only [hfolded, List.append_assoc, queriedInputs_pure, List.append_nil]
              rfl
      · rw [dif_neg hsegment] at hrun
        simp at hrun

theorem leavesRun_queries (values : SlotCode → Nat) (fts : FtsSignature) (remaining position previous : Nat)
    (r r' : Run) (hrun : leavesRun f parameter index values fts remaining position previous r = some r') :
    r'.queries = r.queries
      ++ queriedInputs f (recoverLeaves parameter index values fts remaining position previous r.toRecoverState) := by
  induction remaining generalizing position previous r with
  | zero =>
      cases hrun
      simp [recoverLeaves]
  | succ remaining ih =>
      rw [recoverLeaves, queriedInputs_dite]
      rw [leavesRun] at hrun
      by_cases hposition : position < ftsOpenings
      · rw [dif_pos hposition]
        rw [dif_pos hposition] at hrun
        dsimp only at hrun ⊢
        rw [queriedInputs_ite]
        by_cases horder : 0 < position ∧ ¬ previous < values (fts.perm ⟨position, hposition⟩)
        · rw [if_pos horder] at hrun
          simp at hrun
        · rw [if_neg horder] at hrun ⊢
          rw [queriedInputs_ite]
          by_cases hlast : position + 1 = ftsOpenings ∧
              ¬ values (fts.perm ⟨position, hposition⟩) < 2 ^ ftsTreeHeight
          · rw [if_pos hlast] at hrun
            simp at hrun
          · rw [if_neg hlast] at hrun ⊢
            rw [queriedInputs_bind]
            have heval := eval_recoverSegments f parameter index fts.segments ftsSegments
              (.leaf (values (fts.perm ⟨position, hposition⟩)) (fts.secrets ⟨position, hposition⟩))
              { r with heap := 2 ^ ftsTreeHeight ||| values (fts.perm ⟨position, hposition⟩) }
            have hq := segmentsRun_queries f parameter index fts.segments ftsSegments
              (.leaf (values (fts.perm ⟨position, hposition⟩)) (fts.secrets ⟨position, hposition⟩))
              { r with heap := 2 ^ ftsTreeHeight ||| values (fts.perm ⟨position, hposition⟩) }
            erw [heval]
            rcases hsegments : segmentsRun f parameter index fts.segments ftsSegments _ _ with _ | r''
            · rw [hsegments] at hrun
              simp at hrun
            · rw [hsegments] at hrun
              dsimp only at hrun ⊢
              rw [ih _ _ _ hrun]
              have hq := hq r'' hsegments
              by_cases hpush : position + 1 < ftsOpenings
              · simp only [hpush, if_true]
                erw [hq]
                simp only [List.append_assoc]
                rfl
              · simp only [hpush, if_false]
                erw [hq]
                simp only [List.append_assoc]
                rfl
      · rw [dif_neg hposition] at hrun
        simp at hrun

theorem recoverRun_queries (values : SlotCode → Nat) (fts : FtsSignature) (r : Run)
    (hrun : recoverRun f parameter index values fts = some r) :
    r.queries = queriedInputs f (ftsRecover parameter index values fts) := by
  rw [recoverRun] at hrun
  rcases hleaves : leavesRun f parameter index values fts ftsOpenings 0 0 Run.initial with _ | r'
  · rw [hleaves] at hrun
    simp at hrun
  · rw [hleaves] at hrun
    dsimp only at hrun
    split_ifs at hrun with haccept
    cases hrun
    have hq := leavesRun_queries f parameter index values fts ftsOpenings 0 0 Run.initial r hleaves
    rw [ftsRecover, queriedInputs_bind, ← Run.initial_toRecoverState, eval_recoverLeaves, hleaves]
    simp only [Option.map_some]
    rw [queriedInputs_ite, if_pos (show r.folds ≤ ftsAuthCapacity ∧ r.heap = 1 ∧ r.stack = [] from haccept),
      queriedInputs_pure, List.append_nil, hq]
    rfl

/-- **E4.** Every query an accepted run records is a query of `ftsRecover`. -/
theorem mem_queriedInputs_of_recoverRun (values : SlotCode → Nat) (fts : FtsSignature) (r : Run)
    (hrun : recoverRun f parameter index values fts = some r) {input : HashInput} (hinput : input ∈ r.queries) :
    input ∈ queriedInputs f (ftsRecover parameter index values fts) := by
  rwa [← recoverRun_queries f parameter index values fts r hrun]

end PorsMachine

end SphincsSecurity.Concrete
