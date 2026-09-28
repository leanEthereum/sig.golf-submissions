import SigGolfCandidate.SphincsSecurity.Proof.Fts.PorsStructure
/-!
# Extracting a PORS opening from an accepted stack-machine run (E1)

If the stack machine accepts and its root is the honest root of the instance, then either everything the
signature supplied is honest at the position the run consumed it at — every secret is the true secret of
its leaf, every authentication node is the honest node at the sibling heap index it was folded with, and
every segment that folds has the parity bit of its start heap index — or some query of the run hit:

* `NodeHit`: a node query whose payload is not the honest one but whose answer is the honest node;
* `LeafHit`: a leaf query of a secret other than the true one answering the honest leaf.

The argument is a forward invariant over the run: for the live nodes (the current node at its heap index,
the stack's nodes at their sibling's sibling), "all live nodes are honest" implies "everything consumed so
far is honest, or a query hit". Every hash of the run either keeps it (its payload is the honest payload
with the children in the right order) or is a node hit. The children are always in the right order: a fold
orders them by the heap index (the first fold of a segment by the parity bit, which the verifier checks
against the heap index), and a merge's current node is always a right child (`merge_heap_odd`: the node on the
stack lies on the climb of a smaller leaf).
-/

namespace SphincsSecurity.Concrete

open OracleComp

namespace PorsMachine

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
  (secret : FtsLeaf → Digest)

/-! ### Hits -/

/-- A node query at heap index `heap` whose payload is not the honest one, answering the honest node. -/
def NodeHit (input : HashInput) : Prop :=
  ∃ (heap : Nat) (left right : Digest), 0 < heap ∧ heap < 2 ^ ftsTreeHeight ∧
    input = nodeInput parameter index heap (nodePayload left right) ∧
    nodePayload left right ≠ nodePayload (honest f parameter index secret (2 * heap))
      (honest f parameter index secret (2 * heap + 1)) ∧
    truncateHash (f input) = honest f parameter index secret heap

/-- A leaf query of a secret other than the true one, answering the honest leaf. -/
def LeafHit (input : HashInput) : Prop :=
  ∃ (leaf : FtsLeaf) (candidate : Digest), input = leafInput parameter index leaf.val candidate ∧
    candidate ≠ secret leaf ∧
    truncateHash (f input) = honest f parameter index secret (2 ^ ftsTreeHeight + leaf.val)

/-- One of the two hits. -/
def Hit (input : HashInput) : Prop :=
  NodeHit f parameter index secret input ∨ LeafHit f parameter index secret input

/-- Some query of the run hit. -/
def Exception (r : Run) : Prop := ∃ input ∈ r.queries, Hit f parameter index secret input

/-! ### The invariant -/

/-- The heap indices stay inside the tree. -/
def Bounds (r : Run) : Prop :=
  r.heap < 2 ^ (ftsTreeHeight + 1) ∧ ∀ entry ∈ r.stack, entry.2 ^^^ 1 < 2 ^ (ftsTreeHeight + 1)

/-- Every stack node is honest at its position (the sibling of the heap index it waits for). -/
def StackHonest (r : Run) : Prop :=
  ∀ entry ∈ r.stack, 2 ≤ entry.2 ∧ entry.1 = honest f parameter index secret (entry.2 ^^^ 1)

/-- Every live node is honest at its position. -/
def LiveHonest (r : Run) : Prop :=
  1 ≤ r.heap ∧ r.node = honest f parameter index secret r.heap ∧ StackHonest f parameter index secret r

/-- The invariant inside a leaf (after its leaf hash). -/
def LeafInv (r : Run) : Prop :=
  Bounds r ∧
    (LiveHonest f parameter index secret r →
      Consumed f parameter index secret r ∨ Exception f parameter index secret r)

/-- The invariant between leaves: only the stack is live. -/
def BoundaryInv (r : Run) : Prop :=
  (∀ entry ∈ r.stack, entry.2 ^^^ 1 < 2 ^ (ftsTreeHeight + 1)) ∧
    (StackHonest f parameter index secret r →
      Consumed f parameter index secret r ∨ Exception f parameter index secret r)

theorem exception_mono {r r' : Run} (hqueries : ∀ input ∈ r.queries, input ∈ r'.queries)
    (h : Exception f parameter index secret r) : Exception f parameter index secret r' := by
  obtain ⟨input, hinput, hhit⟩ := h
  exact ⟨input, hqueries input hinput, hhit⟩

/-- The honest node above heap index `heap`, whose children are `heap` and its sibling. -/
theorem honest_parent (heap : Nat) (hlow : 2 ≤ heap) (hhigh : heap < 2 ^ (ftsTreeHeight + 1)) :
    honest f parameter index secret (heap / 2)
      = truncateHash (f (nodeInput parameter index (heap / 2)
          (nodePayload (honest f parameter index secret (2 * (heap / 2)))
            (honest f parameter index secret (2 * (heap / 2) + 1))))) := by
  have h2 : 2 ^ (ftsTreeHeight + 1) = 2 * 2 ^ ftsTreeHeight := by rw [pow_succ]; ring
  exact honestFtsHeap_node f parameter index porsTree secret (heap / 2) (by omega) (by omega)

/-! ### One fold -/

theorem consumed_fold (r : Run) (segment : Segment) (position : Nat) (hcons : Consumed f parameter index secret r)
    (hread : segment.node position = honest f parameter index secret (r.heap ^^^ 1))
    (hparity : position = 0 → segment.parity = decide (r.heap % 2 = 1)) :
    Consumed f parameter index secret
      { r.hash f (foldInput parameter index segment position r.heap r.node) with
        heap := r.heap / 2
        reads := r.reads ++ [(r.heap ^^^ 1, segment.node position)]
        parities := if position = 0 then r.parities ++ [(r.heap, segment.parity)] else r.parities } := by
  obtain ⟨hreads, hparities, hopenings⟩ := hcons
  refine ⟨fun read hmem => ?_, fun parity hmem => ?_, hopenings⟩
  · rcases List.mem_append.mp hmem with hmem | hmem
    · exact hreads read hmem
    · rw [List.mem_singleton] at hmem
      subst hmem
      exact hread
  · dsimp only at hmem
    split_ifs at hmem with hzero
    · rcases List.mem_append.mp hmem with hmem | hmem
      · exact hparities parity hmem
      · rw [List.mem_singleton] at hmem
        subst hmem
        exact hparity hzero
    · exact hparities parity hmem

theorem foldStep_inv (segment : Segment) (position : Nat) (r : Run)
    (hright : foldRight segment position r.heap = decide (r.heap % 2 = 1))
    (hinv : LeafInv f parameter index secret r) :
    LeafInv f parameter index secret
      { r.hash f (foldInput parameter index segment position r.heap r.node) with
        heap := r.heap / 2
        reads := r.reads ++ [(r.heap ^^^ 1, segment.node position)]
        parities := if position = 0 then r.parities ++ [(r.heap, segment.parity)] else r.parities } := by
  obtain ⟨⟨hheap, hstackBound⟩, himp⟩ := hinv
  have hbound : 2 ^ (ftsTreeHeight + 1) = 2 * 2 ^ ftsTreeHeight := by rw [pow_succ]; ring
  refine ⟨⟨show r.heap / 2 < 2 ^ (ftsTreeHeight + 1) by omega, hstackBound⟩, ?_⟩
  rintro ⟨hpos, hnode, hstack⟩
  dsimp only [Run.hash] at hpos hnode hstack ⊢
  have hlow : 2 ≤ r.heap := by omega
  have hqueries : ∀ input ∈ r.queries, input ∈ r.queries ++
      [foldInput parameter index segment position r.heap r.node] :=
    fun input h => List.mem_append_left _ h
  rw [honest_parent f parameter index secret r.heap hlow hheap] at hnode
  by_cases hpay : foldPayload (foldRight segment position r.heap) (segment.node position) r.node
      = nodePayload (honest f parameter index secret (2 * (r.heap / 2)))
          (honest f parameter index secret (2 * (r.heap / 2) + 1))
  · -- the children in the right order: the current node and the sibling are honest
    have hhonest : r.node = honest f parameter index secret r.heap
        ∧ segment.node position = honest f parameter index secret (r.heap ^^^ 1) := by
      rw [hright] at hpay
      rcases xor_one_cases r.heap with ⟨hmod, hxor⟩ | ⟨hmod, hxor⟩
      · simp only [hmod, foldPayload] at hpay
        obtain ⟨h1, h2⟩ := nodePayload_injective hpay
        rw [hxor, h1, h2]
        exact ⟨by congr 1; omega, by congr 1; omega⟩
      · simp only [hmod, foldPayload] at hpay
        obtain ⟨h1, h2⟩ := nodePayload_injective hpay
        rw [hxor, h1, h2]
        exact ⟨by congr 1; omega, by congr 1; omega⟩
    rcases himp ⟨by omega, hhonest.1, hstack⟩ with hcons | hexc
    · left
      refine consumed_fold f parameter index secret r segment position hcons hhonest.2 ?_
      intro hzero
      rw [← hright, foldRight, if_pos hzero]
    · right
      exact exception_mono f parameter index secret hqueries hexc
  · right
    refine ⟨foldInput parameter index segment position r.heap r.node, by simp, Or.inl ?_⟩
    have hform : ∃ left right, foldPayload (foldRight segment position r.heap) (segment.node position) r.node
        = nodePayload left right := by
      simp only [foldPayload]
      split
      · exact ⟨_, _, rfl⟩
      · exact ⟨_, _, rfl⟩
    obtain ⟨left, right, hform⟩ := hform
    refine ⟨r.heap / 2, left, right, by omega, by omega, ?_, ?_, ?_⟩
    · rw [foldInput, hform]
    · rw [← hform]
      exact hpay
    · rw [hnode, honest_parent f parameter index secret r.heap hlow hheap]

theorem foldRun_inv (segment : Segment) (remaining position : Nat) (r : Run)
    (hparity : position = 0 → remaining ≠ 0 → segment.parity = decide (r.heap % 2 = 1))
    (hinv : LeafInv f parameter index secret r) :
    LeafInv f parameter index secret (foldRun f parameter index segment remaining position r) := by
  induction remaining generalizing position r with
  | zero => exact hinv
  | succ remaining ih =>
      rw [foldRun]
      refine ih _ _ (fun h => by omega) (foldStep_inv f parameter index secret segment position r ?_ hinv)
      rw [foldRight]
      split_ifs with hzero
      · exact hparity hzero (by omega)
      · rfl

/-! ### The pending hash -/

/-- What holds before a segment's pending hash: before a leaf hash, the boundary invariant at the leaf's
start heap index; before a merge, the leaf invariant of the state before the pop (current node at `heap`, a
right child, the popped node waiting for `heap` on top of the stack). -/
def PendingInv (pending : PendingHash) (r : Run) : Prop :=
  match pending with
  | .leaf value _ => value < 2 ^ ftsTreeHeight ∧ r.heap = 2 ^ ftsTreeHeight + value ∧
      BoundaryInv f parameter index secret r
  | .merge heapIdx left => ∃ heap, heapIdx = heap / 2 ∧ r.heap = heap / 2 ∧ (2 ≤ heap → heap % 2 = 1) ∧
      LeafInv f parameter index secret { r with heap := heap, stack := (left, heap) :: r.stack }

theorem pendingStep_inv (pending : PendingHash) (r : Run)
    (hpre : PendingInv f parameter index secret pending r) :
    LeafInv f parameter index secret
      { r.hash f (pendingInput parameter index pending r.node) with
        openings := r.openings ++ pendingOpenings pending } := by
  have hbound : 2 ^ (ftsTreeHeight + 1) = 2 * 2 ^ ftsTreeHeight := by rw [pow_succ]; ring
  cases pending with
  | leaf value candidate =>
      obtain ⟨hvalue, hheap, hstackBound, himp⟩ := hpre
      refine ⟨⟨show r.heap < 2 ^ (ftsTreeHeight + 1) by omega, hstackBound⟩, ?_⟩
      rintro ⟨_, hnode, hstack⟩
      let leaf : FtsLeaf := ⟨value, hvalue⟩
      have hhonest : honest f parameter index secret (2 ^ ftsTreeHeight + value)
          = truncateHash (f (leafInput parameter index value (secret leaf))) :=
        honestFtsHeap_leaf' f parameter index porsTree secret leaf
      change truncateHash (f (leafInput parameter index value candidate))
        = honest f parameter index secret r.heap at hnode
      rw [hheap] at hnode
      have hqueries : ∀ input ∈ r.queries, input ∈ r.queries ++
          [leafInput parameter index value candidate] := fun input h => List.mem_append_left _ h
      by_cases hsecret : candidate = secret leaf
      · rcases himp hstack with ⟨hreads, hparities, hopenings⟩ | hexc
        · left
          refine ⟨hreads, hparities, fun opening hmem => ?_⟩
          rcases List.mem_append.mp hmem with hmem | hmem
          · exact hopenings opening hmem
          · simp only [pendingOpenings, List.mem_singleton] at hmem
            subst hmem
            have hleaf : ftsLeafOfNat value = leaf := by
              ext
              simp [ftsLeafOfNat, leaf, Nat.mod_eq_of_lt hvalue]
            rw [hleaf]
            exact hsecret
        · right
          exact exception_mono f parameter index secret hqueries hexc
      · right
        exact ⟨leafInput parameter index value candidate, by simp [Run.hash, pendingInput],
          Or.inr ⟨leaf, candidate, rfl, hsecret, hnode⟩⟩
  | merge heapIdx left =>
      obtain ⟨heap, hidx, hheap, hodd, ⟨hpreHeap, hpreStack⟩, himp⟩ := hpre
      subst hidx
      change heap < 2 ^ (ftsTreeHeight + 1) at hpreHeap
      change ∀ entry ∈ (left, heap) :: r.stack, entry.2 ^^^ 1 < 2 ^ (ftsTreeHeight + 1) at hpreStack
      refine ⟨⟨show r.heap < 2 ^ (ftsTreeHeight + 1) by omega,
        fun entry hmem => hpreStack entry (List.mem_cons_of_mem _ hmem)⟩, ?_⟩
      rintro ⟨hpos, hnode, hstack⟩
      change 1 ≤ r.heap at hpos
      change truncateHash (f (nodeInput parameter index (heap / 2) (nodePayload left r.node)))
        = honest f parameter index secret r.heap at hnode
      rw [hheap] at hpos hnode
      have hlow : 2 ≤ heap := by omega
      have hqueries : ∀ input ∈ r.queries, input ∈ r.queries ++
          [nodeInput parameter index (heap / 2) (nodePayload left r.node)] :=
        fun input h => List.mem_append_left _ h
      have hparent := honest_parent f parameter index secret heap hlow hpreHeap
      by_cases hpay : nodePayload left r.node = nodePayload (honest f parameter index secret (2 * (heap / 2)))
          (honest f parameter index secret (2 * (heap / 2) + 1))
      · obtain ⟨hleft, hcur⟩ := nodePayload_injective hpay
        have hmod := hodd hlow
        rcases xor_one_cases heap with ⟨hmod', _⟩ | ⟨_, hxor⟩
        · omega
        have hlive : LiveHonest f parameter index secret
            { r with heap := heap, stack := (left, heap) :: r.stack } := by
          refine ⟨show 1 ≤ heap by omega, ?_, ?_⟩
          · show r.node = honest f parameter index secret heap
            rw [hcur]
            congr 1; omega
          · intro entry hmem
            rcases List.mem_cons.mp hmem with hmem | hmem
            · subst hmem
              refine ⟨hlow, ?_⟩
              show left = honest f parameter index secret (heap ^^^ 1)
              rw [hleft, hxor]
              congr 1; omega
            · exact hstack entry hmem
        rcases himp hlive with hcons | hexc
        · left
          obtain ⟨hreads, hparities, hopenings⟩ := hcons
          exact ⟨hreads, hparities, by simpa [pendingOpenings] using hopenings⟩
        · right
          exact exception_mono f parameter index secret hqueries hexc
      · right
        refine ⟨nodeInput parameter index (heap / 2) (nodePayload left r.node), by simp [Run.hash, pendingInput],
          Or.inl ⟨heap / 2, left, r.node, by omega, by omega, rfl, hpay, ?_⟩⟩
        rw [hnode]

/-! ### Segments and leaves -/

/-- Along one leaf of value `v`: every heap index is on `v`'s climb, and the stack's nodes are on the climbs
of smaller leaves. -/
def OnClimb (v : Nat) (r : Run) : Prop :=
  (∃ k, r.heap = (2 ^ ftsTreeHeight + v) / 2 ^ k) ∧ StackOrigins r.stack v

theorem segmentsRun_inv (segments : Fin ftsSegments → Segment) (v : Nat) (hv : v < 2 ^ ftsTreeHeight)
    (fuel : Nat) (pending : PendingHash)
    (r r' : Run) (hrun : segmentsRun f parameter index segments fuel pending r = some r')
    (hclimb : OnClimb v r) (hpre : PendingInv f parameter index secret pending r) :
    LeafInv f parameter index secret r' := by
  induction fuel generalizing pending r with
  | zero => simp [segmentsRun] at hrun
  | succ fuel ih =>
      rw [segmentsRun] at hrun
      by_cases hsegment : r.segment < ftsSegments
      · rw [dif_pos hsegment] at hrun
        dsimp only at hrun
        by_cases hfolds : SegmentRejects (segments ⟨r.segment, hsegment⟩) r.heap
        · rw [if_pos hfolds] at hrun
          simp at hrun
        · rw [if_neg hfolds] at hrun
          have hstarted := pendingStep_inv f parameter index secret pending r hpre
          have hfolded := foldRun_inv f parameter index secret (segments ⟨r.segment, hsegment⟩)
            (segments ⟨r.segment, hsegment⟩).folds.val 0 _
            (fun _ hne => by
              by_contra hpar
              exact hfolds (Or.inr ⟨hne, hpar⟩))
            hstarted
          set folded := foldRun f parameter index (segments ⟨r.segment, hsegment⟩)
            (segments ⟨r.segment, hsegment⟩).folds.val 0
            { r.hash f (pendingInput parameter index pending r.node) with
              openings := r.openings ++ pendingOpenings pending } with hfoldedDef
          have hfheap : folded.heap = r.heap / 2 ^ (segments ⟨r.segment, hsegment⟩).folds.val :=
            foldRun_heap f parameter index _ _ _ _
          have hfstack : folded.stack = r.stack := foldRun_stack f parameter index _ _ _ _
          obtain ⟨⟨k, hk⟩, horigins⟩ := hclimb
          by_cases hmerge : (segments ⟨r.segment, hsegment⟩).merge = true
          · rw [if_pos hmerge] at hrun
            rcases hstack : folded.stack with _ | ⟨⟨left, sibling⟩, rest⟩
            · rw [hstack] at hrun
              simp at hrun
            · rw [hstack] at hrun
              dsimp only at hrun
              by_cases hsibling : sibling = folded.heap
              · rw [if_pos hsibling] at hrun
                have hEform : folded.heap
                    = (2 ^ ftsTreeHeight + v) / 2 ^ (k + (segments ⟨r.segment, hsegment⟩).folds.val) := by
                  rw [hfheap, hk, Nat.div_div_eq_div_mul, ← pow_add]
                have hentry : (left, sibling) ∈ r.stack := by
                  rw [← hfstack, hstack]; exact List.mem_cons_self
                refine ih _ _ hrun ⟨⟨k + (segments ⟨r.segment, hsegment⟩).folds.val + 1, ?_⟩, ?_⟩
                  ⟨folded.heap, rfl, rfl, ?_, ?_⟩
                · show folded.heap / 2 = _
                  rw [hEform, Nat.div_div_eq_div_mul, ← pow_succ]
                · intro entry hmem
                  apply horigins entry
                  rw [← hfstack, hstack]
                  exact List.mem_cons_of_mem _ hmem
                · intro htwo
                  obtain ⟨w, b, hwv, hw, hwform⟩ := horigins _ hentry
                  simp only at hwform
                  rw [hsibling, hEform] at hwform
                  rw [hEform] at htwo ⊢
                  exact merge_heap_odd v w _ b hv hw hwv hwform htwo
                · obtain ⟨⟨hb1, hb2⟩, himp⟩ := hfolded
                  rw [hstack, hsibling] at hb2
                  refine ⟨⟨hb1, hb2⟩, ?_⟩
                  intro hlive
                  refine himp ?_
                  obtain ⟨h1, h2, h3⟩ := hlive
                  refine ⟨h1, h2, ?_⟩
                  intro entry hmem
                  rw [hstack, hsibling] at hmem
                  exact h3 entry hmem
              · rw [if_neg hsibling] at hrun
                simp at hrun
          · rw [if_neg hmerge] at hrun
            cases hrun
            exact hfolded
      · rw [dif_neg hsegment] at hrun
        simp at hrun

theorem boundaryInv_push (r : Run) (hinv : LeafInv f parameter index secret r) :
    BoundaryInv f parameter index secret { r with stack := (r.node, r.heap ^^^ 1) :: r.stack } := by
  obtain ⟨⟨hheap, hstackBound⟩, himp⟩ := hinv
  refine ⟨fun entry hmem => ?_, fun hstack => ?_⟩
  · rcases List.mem_cons.mp hmem with hmem | hmem
    · subst hmem
      show r.heap ^^^ 1 ^^^ 1 < _
      rw [xor_one_xor_one]
      exact hheap
    · exact hstackBound entry hmem
  · obtain ⟨hlow, hnode⟩ := hstack _ List.mem_cons_self
    refine himp ⟨?_, ?_, fun entry hmem => hstack entry (List.mem_cons_of_mem _ hmem)⟩
    · change 2 ≤ r.heap ^^^ 1 at hlow
      rcases xor_one_cases r.heap with ⟨_, hxor⟩ | ⟨_, hxor⟩ <;> omega
    · change r.node = honest f parameter index secret (r.heap ^^^ 1 ^^^ 1) at hnode
      rwa [xor_one_xor_one] at hnode

theorem leavesRun_inv (values : SlotCode → Nat) (fts : FtsSignature)
    (hvalues : ∀ s : Fin ftsOpenings, values (fts.perm s) < 2 ^ ftsTreeHeight) :
    ∀ (remaining position previous : Nat) (r r' : Run), remaining + position = ftsOpenings → 0 < remaining →
      leavesRun f parameter index values fts remaining position previous r = some r' →
      (position = 0 → r.stack = []) →
      (∀ entry ∈ r.stack, ∃ w b, w ≤ previous ∧ w < 2 ^ ftsTreeHeight ∧
        entry.2 ^^^ 1 = (2 ^ ftsTreeHeight + w) / 2 ^ b) →
      BoundaryInv f parameter index secret r → LeafInv f parameter index secret r' := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _ hsum hpos; omega
  | succ remaining ih =>
      intro position previous r r' hsum _ hrun hfirst horigins hinv
      have hposition : position < ftsOpenings := by omega
      obtain ⟨r1, hleaf, hrest⟩ := leavesRun_succ_eq f parameter index values fts _ _ _ _ _ hposition hrun
      have hv := hvalues ⟨position, hposition⟩
      have hstart := two_pow_or_eq_add _ hv
      -- the order check passed
      have horder : 0 < position → previous < values (fts.perm ⟨position, hposition⟩) := by
        intro hpos
        rw [leavesRun, dif_pos hposition] at hrun
        dsimp only at hrun
        by_contra hlt
        rw [if_pos ⟨hpos, hlt⟩] at hrun
        simp at hrun
      have hleafInv := segmentsRun_inv f parameter index secret fts.segments _ hv ftsSegments _ _ r1 hleaf
        ⟨⟨0, by simp [hstart]⟩, fun entry hmem => by
          obtain ⟨w, b, hw, hwlt, hform⟩ := horigins entry hmem
          rcases Nat.eq_zero_or_pos position with hzero | hpos
          · rw [hfirst hzero] at hmem; simp at hmem
          · exact ⟨w, b, by have := horder hpos; omega, hwlt, hform⟩⟩
        ⟨hv, by simp [hstart], hinv⟩
      by_cases hpush : position + 1 < ftsOpenings
      · rw [if_pos hpush] at hrest
        obtain ⟨popped, hpop, _, _, hclimb, _⟩ := segmentsRun_shape f parameter index _ _ _ _ _ hleaf
        simp only [hstart] at hpop hclimb
        refine ih (position + 1) _ _ r' (by omega) (by omega) hrest (fun h => by omega) ?_
          (boundaryInv_push f parameter index secret r1 hleafInv)
        intro entry hmem
        rcases List.mem_cons.mp hmem with hmem | hmem
        · subst hmem
          obtain ⟨b, hb⟩ : ∃ b, r1.heap = (2 ^ ftsTreeHeight + values (fts.perm ⟨position, hposition⟩)) / 2 ^ b :=
            ⟨_, hclimb⟩
          refine ⟨values (fts.perm ⟨position, hposition⟩), b, le_rfl, hv, ?_⟩
          show r1.heap ^^^ 1 ^^^ 1 = _
          rw [xor_one_xor_one, hb]
        · have hmem' : entry ∈ r.stack := by
            rw [hpop]; exact List.mem_append_right _ hmem
          obtain ⟨w, b, hw, hwlt, hform⟩ := horigins entry hmem'
          rcases Nat.eq_zero_or_pos position with hzero | hpos
          · rw [hfirst hzero] at hmem'; simp at hmem'
          · exact ⟨w, b, by have := horder hpos; omega, hwlt, hform⟩
      · rw [if_neg hpush] at hrest
        have hzero : remaining = 0 := by omega
        subst hzero
        rw [leavesRun_zero_eq f parameter index values fts _ _ _ _ hrest]
        exact hleafInv

/-- **E1, the extraction.** An accepted run whose root is the honest root consumed only honest items (at
the positions it consumed them at), or one of its queries hit. -/
theorem recoverRun_extract (values : SlotCode → Nat) (fts : FtsSignature)
    (hvalues : ∀ s : Fin ftsOpenings, values (fts.perm s) < 2 ^ ftsTreeHeight) (r : Run)
    (hrun : recoverRun f parameter index values fts = some r)
    (hroot : r.node = honest f parameter index secret 1) :
    Consumed f parameter index secret r ∨ Exception f parameter index secret r := by
  rw [recoverRun] at hrun
  rcases hleaves : leavesRun f parameter index values fts ftsOpenings 0 0 Run.initial with _ | r'
  · rw [hleaves] at hrun
    simp at hrun
  · rw [hleaves] at hrun
    dsimp only at hrun
    split_ifs at hrun with haccept
    cases hrun
    have hinv := leavesRun_inv f parameter index secret values fts hvalues ftsOpenings 0 0 Run.initial r
      rfl (by decide) hleaves (fun _ => rfl) (fun _ h => by simp [Run.initial, RecoverState.initial] at h)
      ⟨fun _ h => by simp [Run.initial, RecoverState.initial] at h,
        fun _ => Or.inl ⟨fun _ h => by simp [Run.initial] at h, fun _ h => by simp [Run.initial] at h,
          fun _ h => by simp [Run.initial] at h⟩⟩
    obtain ⟨_, hheap, hstack⟩ := haccept
    refine hinv.2 ⟨by omega, by rw [hheap]; exact hroot, ?_⟩
    intro entry hmem
    rw [hstack] at hmem
    simp at hmem

end PorsMachine

end SphincsSecurity.Concrete
