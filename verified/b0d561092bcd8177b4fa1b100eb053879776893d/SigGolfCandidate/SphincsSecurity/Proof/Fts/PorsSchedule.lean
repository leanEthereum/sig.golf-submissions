import SigGolfCandidate.SphincsSecurity.Proof.Fts.PorsStructure

/-!
# An accepted run follows the honest schedule (E3)

The stack machine of an accepted run makes exactly the decisions of `schedule` (Scheme.lean): at every height
of a leaf's climb it merges when the stack's top waits for the current heap index and folds otherwise, and the
leaf ends at the height below its lowest common ancestor with the next leaf. The merges are forced by the
machine's check; the folds by the chain at the end of the leaf (`PorsStructure`): a pending node that is not
merged when the climb passes it can never be merged again. So the run's segments have the schedule's fold
counts and merge flags, its folds read the schedule's positions, and its segments start at the schedule's heap
indices.

With the extraction's `Consumed` (every consumed item honest at its position), the signature is the honest
one: `recoverRun_honest`, the canonicity (strong unforgeability) step.
-/

namespace SphincsSecurity.Concrete

open OracleComp

namespace PorsMachine

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)

/-! ### What a segment's folds record -/

theorem foldRun_reads (segment : Segment) (remaining position : Nat) (r : Run) :
    (foldRun f parameter index segment remaining position r).reads
      = r.reads ++ List.ofFn fun i : Fin remaining =>
          (r.heap / 2 ^ i.val ^^^ 1, segment.node (position + i.val)) := by
  induction remaining generalizing position r with
  | zero => simp [foldRun]
  | succ remaining ih =>
      rw [foldRun, ih, List.ofFn_succ]
      simp only [List.append_assoc, List.singleton_append, Fin.val_zero, pow_zero, Nat.div_one,
        Nat.add_zero, Fin.val_succ]
      congr 3
      funext i
      show (r.heap / 2 / 2 ^ i.val ^^^ 1, segment.node (position + 1 + i.val)) = _
      rw [Nat.div_div_eq_div_mul, ← pow_succ', Nat.add_assoc, Nat.add_comm 1 i.val]

theorem foldRun_parities (segment : Segment) (remaining position : Nat) (r : Run) :
    (foldRun f parameter index segment remaining position r).parities
      = r.parities ++ (if position = 0 ∧ remaining ≠ 0 then [(r.heap, segment.parity)] else []) := by
  induction remaining generalizing position r with
  | zero => simp [foldRun]
  | succ remaining ih =>
      rw [foldRun, ih]
      by_cases hposition : position = 0
      · subst hposition
        simp
      · simp [hposition]

theorem foldRun_openings (segment : Segment) (remaining position : Nat) (r : Run) :
    (foldRun f parameter index segment remaining position r).openings = r.openings := by
  induction remaining generalizing position r with
  | zero => rfl
  | succ remaining ih => rw [foldRun, ih]; rfl

/-! ### What the schedule does on folds and merges -/

/-- The read position of a fold at height `height` from heap index `heap`. -/
def foldRead (height heap : Nat) : Nat × Nat := (height, (heap ^^^ 1) - 2 ^ (ftsTreeHeight - height))

theorem scheduleStep_fold (state : ScheduleState) (height : Nat)
    (hnot : ∀ q ∈ state.stack.head?, q ≠ state.heap) :
    scheduleStep state height
      = { state with reads := state.reads ++ [foldRead height state.heap], heap := state.heap / 2 } := by
  unfold scheduleStep
  cases hstack : state.stack with
  | nil => rfl
  | cons q rest =>
      rw [hstack] at hnot
      simp only [List.head?_cons, Option.mem_def, Option.some.injEq, forall_eq'] at hnot
      simp only [if_neg hnot]
      rfl

theorem scheduleStep_merge (state : ScheduleState) (height : Nat) (rest : List Nat)
    (hstack : state.stack = state.heap :: rest) :
    scheduleStep state height
      = { state with done := state.done ++ [⟨true, state.parity, state.reads⟩], stack := rest,
                     heap := state.heap / 2, parity := decide (state.heap / 2 % 2 = 1), reads := [] } := by
  unfold scheduleStep
  rw [hstack]
  simp

/-- Heights `height, …, height + a - 1` where the stack's top never waits: `a` folds. -/
theorem foldl_scheduleStep_folds (a : Nat) : ∀ (height : Nat) (state : ScheduleState),
    (∀ i < a, ∀ q ∈ state.stack.head?, q ≠ state.heap / 2 ^ i) →
    (List.range' height a).foldl scheduleStep state
      = { state with
          reads := state.reads ++ List.ofFn fun i : Fin a => foldRead (height + i.val) (state.heap / 2 ^ i.val),
          heap := state.heap / 2 ^ a } := by
  induction a with
  | zero => intro height state _; simp
  | succ a ih =>
      intro height state hnot
      rw [List.range'_succ, List.foldl_cons, scheduleStep_fold state height (by simpa using hnot 0 (by omega))]
      rw [ih (height + 1) _ (fun i hi q hq => by
        have := hnot (i + 1) (by omega) q hq
        simpa [Nat.div_div_eq_div_mul, ← pow_succ'] using this)]
      simp only [List.ofFn_succ, List.append_assoc, List.singleton_append, Fin.val_zero, pow_zero,
        Nat.div_one, Nat.add_zero, Fin.val_succ, Nat.div_div_eq_div_mul, ← pow_succ']
      congr 3
      apply congrArg List.ofFn
      funext i
      rw [Nat.add_assoc, Nat.add_comm 1 i.val]

theorem div_pow_div_pow (x a b : Nat) : x / 2 ^ a / 2 ^ b = x / 2 ^ (a + b) := by
  rw [Nat.div_div_eq_div_mul, ← pow_add]

theorem div_pow_half (x a : Nat) : x / 2 ^ a / 2 = x / 2 ^ (a + 1) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ]

/-- The heap index of a read position. -/
def readHeap (read : Nat × Nat) : Nat := ftsHeapIndex read.1 read.2

/-- The node a fold at height `height < 14` reads, from leaf `v`'s ancestor: the ancestor's sibling. -/
theorem readHeap_foldRead (v height : Nat) (hv : v < 2 ^ ftsTreeHeight) (hheight : height < ftsTreeHeight) :
    readHeap (foldRead height ((2 ^ ftsTreeHeight + v) / 2 ^ height))
      = (2 ^ ftsTreeHeight + v) / 2 ^ height ^^^ 1 := by
  obtain ⟨hlow, hhigh⟩ := start_div_bounds v height hv hheight.le
  have heven : 2 ^ (ftsTreeHeight - height) % 2 = 0 := by
    rw [show ftsTreeHeight - height = (ftsTreeHeight - height - 1) + 1 by omega, pow_succ]; simp
  unfold readHeap foldRead ftsHeapIndex
  simp only
  rcases xor_one_cases ((2 ^ ftsTreeHeight + v) / 2 ^ height) with ⟨hmod, hxor⟩ | ⟨hmod, hxor⟩ <;>
    rw [hxor] <;> omega

/-- Segment `j` of the signature has the fold count, the merge flag, the start parity and (as recorded by the
run `r`) the nodes at the read positions of the schedule's segment `sseg`. -/
def SegmentMatches (fts : FtsSignature) (r : Run) (j : Fin ftsSegments) (sseg : ScheduleSegment) : Prop :=
  (fts.segments j).folds.val = sseg.reads.length ∧ (fts.segments j).merge = sseg.merge ∧
    ((fts.segments j).folds.val ≠ 0 →
      ∃ heap, (heap, (fts.segments j).parity) ∈ r.parities ∧ sseg.parity = decide (heap % 2 = 1)) ∧
    ∀ i (hi : i < sseg.reads.length), (readHeap sseg.reads[i], (fts.segments j).node i) ∈ r.reads

theorem SegmentMatches.mono {fts : FtsSignature} {r r' : Run} {j : Fin ftsSegments} {sseg : ScheduleSegment}
    (h : SegmentMatches fts r j sseg) (hreads : ∀ x ∈ r.reads, x ∈ r'.reads)
    (hparities : ∀ x ∈ r.parities, x ∈ r'.parities) : SegmentMatches fts r' j sseg := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, fun hne => ?_, fun i hi => hreads _ (h4 i hi)⟩
  obtain ⟨heap, hmem, hpar⟩ := h3 hne
  exact ⟨heap, hparities _ hmem, hpar⟩

/-- The run's finished segments match the schedule's finished segments. -/
def DoneMatch (fts : FtsSignature) (r : Run) (done : List ScheduleSegment) : Prop :=
  done.length = r.segment ∧
    ∀ j : Fin ftsSegments, j.val < r.segment → SegmentMatches fts r j (done.getD j.val default)

/-- One more matching segment. -/
theorem DoneMatch.snoc {fts : FtsSignature} {r r' : Run} {done : List ScheduleSegment} (sseg : ScheduleSegment)
    (h : DoneMatch fts r done) (hsegment : r'.segment = r.segment + 1) (hlt : r.segment < ftsSegments)
    (hreads : ∀ x ∈ r.reads, x ∈ r'.reads) (hparities : ∀ x ∈ r.parities, x ∈ r'.parities)
    (hlast : SegmentMatches fts r' ⟨r.segment, hlt⟩ sseg) : DoneMatch fts r' (done ++ [sseg]) := by
  obtain ⟨hlen, hmatch⟩ := h
  refine ⟨by simp [hlen, hsegment], fun j hj => ?_⟩
  rcases Nat.lt_or_ge j.val r.segment with hlt' | hge
  · rw [List.getD_append _ _ _ _ (by omega)]
    exact (hmatch j hlt').mono hreads hparities
  · have hj' : j.val = r.segment := by omega
    rw [List.getD_append_right _ _ _ _ (by omega), hj', ← hlen, Nat.sub_self]
    have : j = ⟨r.segment, hlt⟩ := Fin.ext hj'
    rw [this]
    exact hlast

/-- The segment the run just finished matches a schedule segment with `a` fold reads from `heap`. -/
theorem segmentMatches_folds (fts : FtsSignature) (v height : Nat) (hv : v < 2 ^ ftsTreeHeight)
    (r : Run) (hsegment : r.segment < ftsSegments) (merge parity : Bool) (hheap : r.heap = (2 ^ ftsTreeHeight + v) / 2 ^ height)
    (hparity : parity = decide (r.heap % 2 = 1))
    (hmerge : (fts.segments ⟨r.segment, hsegment⟩).merge = merge)
    (hroom : height + (fts.segments ⟨r.segment, hsegment⟩).folds.val ≤ ftsTreeHeight)
    (r' : Run)
    (hreads : r'.reads = r.reads ++ List.ofFn fun i : Fin (fts.segments ⟨r.segment, hsegment⟩).folds.val =>
        (r.heap / 2 ^ i.val ^^^ 1, (fts.segments ⟨r.segment, hsegment⟩).node (0 + i.val)))
    (hparities : r'.parities = r.parities ++ (if 0 = 0 ∧ (fts.segments ⟨r.segment, hsegment⟩).folds.val ≠ 0
        then [(r.heap, (fts.segments ⟨r.segment, hsegment⟩).parity)] else [])) :
    SegmentMatches fts r' ⟨r.segment, hsegment⟩
      ⟨merge, parity, List.ofFn fun i : Fin (fts.segments ⟨r.segment, hsegment⟩).folds.val =>
        foldRead (height + i.val) (r.heap / 2 ^ i.val)⟩ := by
  refine ⟨by simp, hmerge, fun hne => ⟨r.heap, ?_, hparity⟩, fun i hi => ?_⟩
  · rw [hparities, if_pos ⟨rfl, hne⟩]
    simp
  · simp only [List.length_ofFn] at hi
    simp only [List.getElem_ofFn]
    rw [hreads]
    apply List.mem_append_right
    rw [List.mem_ofFn]
    refine ⟨⟨i, hi⟩, ?_⟩
    simp only [Nat.zero_add]
    congr 1
    rw [hheap, div_pow_div_pow, readHeap_foldRead v _ hv (by omega)]

/-- **One leaf follows the schedule.** From a segment boundary at height `height` of leaf `v`'s climb, if the
leaf ends at height `top` with the stack a chain there, the run's segments are the schedule's for the
remaining heights. -/
theorem segmentsRun_schedule (fts : FtsSignature) (v : Nat) (hv : v < 2 ^ ftsTreeHeight) (top : Nat)
    (htop : top ≤ ftsTreeHeight) :
    ∀ (fuel : Nat) (pending : PendingHash) (r r1 : Run) (state : ScheduleState) (height : Nat),
      segmentsRun f parameter index fts.segments fuel pending r = some r1 →
      r.heap = (2 ^ ftsTreeHeight + v) / 2 ^ height → height ≤ top →
      r1.heap = (2 ^ ftsTreeHeight + v) / 2 ^ top → Chain (r1.stack.map Prod.snd) (r1.heap / 2) →
      state.heap = r.heap → state.stack = r.stack.map Prod.snd → state.reads = [] →
      state.parity = decide (r.heap % 2 = 1) → DoneMatch fts r state.done →
      ((List.range' height (top - height)).foldl scheduleStep state).heap = r1.heap ∧
      ((List.range' height (top - height)).foldl scheduleStep state).stack = r1.stack.map Prod.snd ∧
      DoneMatch fts r1 (((List.range' height (top - height)).foldl scheduleStep state).done ++
        [⟨false, ((List.range' height (top - height)).foldl scheduleStep state).parity,
          ((List.range' height (top - height)).foldl scheduleStep state).reads⟩]) := by
  intro fuel
  induction fuel with
  | zero => intro _ _ _ _ _ hrun; simp [segmentsRun] at hrun
  | succ fuel ih =>
      intro pending r r1 state height hrun hheap hheight hend hchain hsheap hsstack hsreads hsparity hdone
      rw [segmentsRun] at hrun
      by_cases hsegment : r.segment < ftsSegments
      swap
      · rw [dif_neg hsegment] at hrun; simp at hrun
      rw [dif_pos hsegment] at hrun
      dsimp only at hrun
      by_cases hfolds : SegmentRejects (fts.segments ⟨r.segment, hsegment⟩) r.heap
      · rw [if_pos hfolds] at hrun; simp at hrun
      rw [if_neg hfolds] at hrun
      set segment := fts.segments ⟨r.segment, hsegment⟩ with hsegmentDef
      set a := segment.folds.val with ha
      set started : Run := { r.hash f (pendingInput parameter index pending r.node) with
        openings := r.openings ++ pendingOpenings pending } with hstarted
      set folded := foldRun f parameter index segment a 0 started with hfoldedDef
      have hfheap : folded.heap = r.heap / 2 ^ a := foldRun_heap f parameter index _ _ _ _
      have hfstack : folded.stack = r.stack := foldRun_stack f parameter index _ _ _ _
      have hfreads := foldRun_reads f parameter index segment a 0 started
      have hfparities := foldRun_parities f parameter index segment a 0 started
      have hheapPos : ∀ i, height + i ≤ ftsTreeHeight → 1 ≤ r.heap / 2 ^ i := by
        intro i hi
        rw [hheap, div_pow_div_pow]
        exact start_div_pos v _ hv hi
      by_cases hmerge : segment.merge = true
      · -- a merge follows the folds
        rw [if_pos hmerge] at hrun
        rcases hstack : folded.stack with _ | ⟨⟨left, sibling⟩, rest⟩
        · rw [hstack] at hrun; simp at hrun
        rw [hstack] at hrun
        dsimp only at hrun
        by_cases hsibling : sibling = folded.heap
        swap
        · rw [if_neg hsibling] at hrun; simp at hrun
        rw [if_pos hsibling] at hrun
        -- the rest of the leaf climbs from height `height + a + 1`
        obtain ⟨popped, _, _, _, hclimb, _⟩ := segmentsRun_shape f parameter index _ _ _ _ _ hrun
        simp only at hclimb
        have hnext : folded.heap / 2 = (2 ^ ftsTreeHeight + v) / 2 ^ (height + a + 1) := by
          rw [hfheap, hheap, div_pow_div_pow, div_pow_half]
        rw [hnext, div_pow_div_pow] at hclimb
        have htopEq := start_div_inj v top _ hv htop (hend.symm.trans hclimb)
        -- the schedule: `a` folds, then the merge
        have hsplit : List.range' height (top - height)
            = List.range' height a ++ (height + a) :: List.range' (height + a + 1) (top - (height + a + 1)) := by
          rw [← List.range'_succ, List.range'_append_1]
          congr 1
          omega
        have hnot : ∀ i < a, ∀ q ∈ state.stack.head?, q ≠ state.heap / 2 ^ i := by
          intro i hi q hq
          rw [hsstack, ← hfstack, hstack] at hq
          simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hq
          rw [← hq, hsibling, hfheap, hsheap]
          have hpos := hheapPos i (by omega)
          have : r.heap / 2 ^ a = r.heap / 2 ^ i / 2 ^ (a - i) := by
            rw [div_pow_div_pow]; congr 2; omega
          rw [this]
          exact Nat.ne_of_lt (Nat.div_lt_self (by omega) (Nat.one_lt_two_pow (by omega)))
        rw [hsplit, List.foldl_append, foldl_scheduleStep_folds a height state hnot, List.foldl_cons]
        set state1 := { state with
          reads := state.reads ++ List.ofFn fun i : Fin a => foldRead (height + i.val) (state.heap / 2 ^ i.val),
          heap := state.heap / 2 ^ a } with hstate1
        have hstack1 : state1.stack = state1.heap :: rest.map Prod.snd := by
          simp only [hstate1, hsstack, ← hfstack, hstack, List.map_cons, hsibling, hfheap, hsheap]
        rw [scheduleStep_merge state1 (height + a) _ hstack1]
        -- the rest of the leaf, by induction
        refine ih _ _ r1 _ (height + a + 1) hrun hnext (by omega) hend hchain ?_ ?_ rfl ?_ ?_
        · simp [hstate1, hsheap, hfheap]
        · simp
        · simp [hstate1, hsheap, hfheap]
        · -- the finished segments, with the one that just ended
          refine DoneMatch.snoc _ hdone rfl hsegment ?_ ?_ ?_
          · intro x hx
            show x ∈ folded.reads
            rw [hfreads]
            exact List.mem_append_left _ hx
          · intro x hx
            show x ∈ folded.parities
            rw [hfparities]
            exact List.mem_append_left _ hx
          · have := segmentMatches_folds fts v height hv r hsegment true state.parity hheap
              (by rw [hsparity]) hmerge (by show height + a ≤ ftsTreeHeight; omega) folded hfreads hfparities
            simp only [hstate1, hsreads, hsheap, List.nil_append] at this ⊢
            exact this
      · -- the leaf ends after the folds
        rw [if_neg hmerge] at hrun
        cases hrun
        have hr1heap : folded.heap = (2 ^ ftsTreeHeight + v) / 2 ^ (height + a) := by
          rw [hfheap, hheap, div_pow_div_pow]
        have htopEq := start_div_inj v top _ hv htop (hend.symm.trans hr1heap)
        rw [show top - height = a by omega]
        have hnot : ∀ i < a, ∀ q ∈ state.stack.head?, q ≠ state.heap / 2 ^ i := by
          intro i hi q hq
          rw [hsstack, ← hfstack] at hq
          cases hst : folded.stack with
          | nil => rw [hst] at hq; simp at hq
          | cons top' rest =>
              rw [hst] at hq hchain
              simp only [List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq] at hq
              simp only [List.map_cons] at hchain
              rw [← hq, hsheap]
              apply chain_top_ne (a - i + 1) (by omega) (hheapPos i (by omega))
              have : r.heap / 2 ^ i / 2 ^ (a - i + 1) = folded.heap / 2 := by
                rw [hfheap, div_pow_div_pow, div_pow_half]
                congr 2; omega
              rw [this]
              exact hchain
        rw [foldl_scheduleStep_folds a height state hnot]
        refine ⟨by simp [hsheap, hfheap], by simp [hsstack, hfstack], ?_⟩
        refine DoneMatch.snoc _ hdone rfl hsegment ?_ ?_ ?_
        · intro x hx
          show x ∈ folded.reads
          rw [hfreads]
          exact List.mem_append_left _ hx
        · intro x hx
          show x ∈ folded.parities
          rw [hfparities]
          exact List.mem_append_left _ hx
        · have := segmentMatches_folds fts v height hv r hsegment false state.parity hheap
            (by rw [hsparity]) (by simpa using hmerge) (by show height + a ≤ ftsTreeHeight; omega) _ hfreads
            hfparities
          simp only [hsreads, hsheap, List.nil_append] at this ⊢
          exact this

/-! ### All the leaves -/

/-- The leaf values from leaf `position` on. -/
def valuesFrom (values : SlotCode → Nat) (fts : FtsSignature) (position : Nat) : List Nat :=
  (List.ofFn fun s : Fin ftsOpenings => leafValue values fts s.val).drop position

theorem valuesFrom_cons (values : SlotCode → Nat) (fts : FtsSignature) (position : Nat)
    (hposition : position < ftsOpenings) :
    valuesFrom values fts position = leafValue values fts position :: valuesFrom values fts (position + 1) := by
  unfold valuesFrom
  rw [List.drop_eq_getElem_cons (by simpa using hposition), List.getElem_ofFn]

theorem valuesFrom_last (values : SlotCode → Nat) (fts : FtsSignature) :
    valuesFrom values fts ftsOpenings = [] := by
  simp [valuesFrom]

/-- One leaf of the schedule, unfolded. -/
theorem scheduleLeaves_cons (v : Nat) (rest : List Nat) (state : ScheduleState) :
    scheduleLeaves (v :: rest) state =
      let top := match rest with
        | [] => ftsTreeHeight
        | w :: _ => bitLength (v ^^^ w) - 1
      let climbed := (List.range top).foldl scheduleStep
        { state with heap := 2 ^ ftsTreeHeight ||| v,
                     parity := decide ((2 ^ ftsTreeHeight ||| v) % 2 = 1), reads := [] }
      let closed := { climbed with done := climbed.done ++ [⟨false, climbed.parity, climbed.reads⟩] }
      scheduleLeaves rest (match rest with
        | [] => closed
        | _ :: _ => { closed with stack := (closed.heap ^^^ 1) :: closed.stack }) := by
  rfl

theorem segmentsRun_openings (segments : Fin ftsSegments → Segment) (fuel : Nat) (pending : PendingHash)
    (r r' : Run) (hrun : segmentsRun f parameter index segments fuel pending r = some r') :
    ∀ x ∈ r.openings ++ pendingOpenings pending, x ∈ r'.openings := by
  induction fuel generalizing pending r with
  | zero => simp [segmentsRun] at hrun
  | succ fuel ih =>
      intro x hx
      rw [segmentsRun] at hrun
      by_cases hsegment : r.segment < ftsSegments
      swap
      · rw [dif_neg hsegment] at hrun; simp at hrun
      rw [dif_pos hsegment] at hrun
      dsimp only at hrun
      by_cases hfolds : SegmentRejects (segments ⟨r.segment, hsegment⟩) r.heap
      · rw [if_pos hfolds] at hrun; simp at hrun
      rw [if_neg hfolds] at hrun
      set folded := foldRun f parameter index (segments ⟨r.segment, hsegment⟩)
        (segments ⟨r.segment, hsegment⟩).folds.val 0
        { r.hash f (pendingInput parameter index pending r.node) with
          openings := r.openings ++ pendingOpenings pending } with hfoldedDef
      have hfopen : folded.openings = r.openings ++ pendingOpenings pending :=
        foldRun_openings f parameter index _ _ _ _
      by_cases hmerge : (segments ⟨r.segment, hsegment⟩).merge = true
      · rw [if_pos hmerge] at hrun
        rcases hstack : folded.stack with _ | ⟨⟨left, sibling⟩, rest⟩
        · rw [hstack] at hrun; simp at hrun
        rw [hstack] at hrun
        dsimp only at hrun
        by_cases hsibling : sibling = folded.heap
        swap
        · rw [if_neg hsibling] at hrun; simp at hrun
        rw [if_pos hsibling] at hrun
        apply ih _ _ hrun
        apply List.mem_append_left
        show x ∈ folded.openings
        rw [hfopen]
        exact hx
      · rw [if_neg hmerge] at hrun
        cases hrun
        show x ∈ folded.openings
        rw [hfopen]
        exact hx

theorem leavesRun_openings (values : SlotCode → Nat) (fts : FtsSignature) :
    ∀ (remaining position previous : Nat) (r r' : Run),
      leavesRun f parameter index values fts remaining position previous r = some r' →
      ∀ x ∈ r.openings, x ∈ r'.openings := by
  intro remaining
  induction remaining with
  | zero =>
      intro position previous r r' hrun x hx
      rw [leavesRun_zero_eq f parameter index values fts _ _ _ _ hrun]
      exact hx
  | succ remaining ih =>
      intro position previous r r' hrun x hx
      by_cases hposition : position < ftsOpenings
      · obtain ⟨r1, hleaf, hrest⟩ := leavesRun_succ_eq f parameter index values fts _ _ _ _ _ hposition hrun
        have h1 := segmentsRun_openings f parameter index _ _ _ _ _ hleaf x (List.mem_append_left _ hx)
        apply ih _ _ _ _ hrest
        split_ifs
        · exact h1
        · exact h1
      · rw [leavesRun, dif_neg hposition] at hrun
        simp at hrun

/-- **All leaves follow the schedule.** -/
theorem leavesRun_schedule (fts : FtsSignature) (values : SlotCode → Nat)
    (hvalues : ∀ s (hs : s < ftsOpenings), values (fts.perm ⟨s, hs⟩) < 2 ^ ftsTreeHeight) :
    ∀ (remaining position previous : Nat) (r r' : Run) (state : ScheduleState),
      leavesRun f parameter index values fts remaining position previous r = some r' →
      remaining + position = ftsOpenings → 0 < remaining → r'.heap = 1 → r'.stack = [] →
      state.stack = r.stack.map Prod.snd → DoneMatch fts r state.done →
      DoneMatch fts r' (scheduleLeaves (valuesFrom values fts position) state).done ∧
        ∀ s (hs : s < ftsOpenings), position ≤ s → (leafValue values fts s, fts.secrets ⟨s, hs⟩) ∈ r'.openings := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _ _ _ _ h; omega
  | succ remaining ih =>
      intro position previous r r' state hrun hsum _ hheap hstack hsstack hdone
      have hposition : position < ftsOpenings := by omega
      obtain ⟨r1, hleaf, hrest⟩ := leavesRun_succ_eq f parameter index values fts _ _ _ _ _ hposition hrun
      have hv := hvalues position hposition
      have hstart := two_pow_or_eq _ hv
      obtain ⟨popped, _, _, _, hclimb, _⟩ := segmentsRun_shape f parameter index _ _ _ _ _ hleaf
      simp only [hstart] at hclimb
      have hopen1 := segmentsRun_openings f parameter index _ _ _ _ _ hleaf
      rw [valuesFrom_cons values fts position hposition, scheduleLeaves_cons]
      -- the leaf's climb height and the chain at its end
      obtain ⟨top, htop, hr1heap, hchain1, htopEq⟩ : ∃ top, top ≤ ftsTreeHeight ∧
          r1.heap = (2 ^ ftsTreeHeight + leafValue values fts position) / 2 ^ top ∧
          Chain (r1.stack.map Prod.snd) (r1.heap / 2) ∧
          top = (match valuesFrom values fts (position + 1) with
            | [] => ftsTreeHeight
            | w :: _ => bitLength (leafValue values fts position ^^^ w) - 1) := by
        rw [leafValue_of_lt values fts _ hposition]
        by_cases hpush : position + 1 < ftsOpenings
        · rw [if_pos hpush] at hrest
          have hchain := leavesRun_chain f parameter index values fts hvalues remaining (position + 1) _ _ _
            hrest (by omega) (by omega) hheap hstack hpush
          obtain ⟨⟨b, hb⟩, htwo, hchainRest⟩ := hchain
          simp only at hb htwo hchainRest
          rw [hclimb] at hb htwo
          obtain ⟨hk, hklt⟩ := climb_eq_of_sibling _ _ _ _ hv (hvalues _ hpush) hb htwo
          refine ⟨_, hklt.le, hclimb, ?_, ?_⟩
          · rw [xor_one_div_two'] at hchainRest
            exact hchainRest
          · rw [valuesFrom_cons values fts (position + 1) hpush, leafValue_of_lt values fts _ hpush]
            exact hk
        · rw [if_neg hpush] at hrest
          have hzero : remaining = 0 := by omega
          subst hzero
          have := leavesRun_zero_eq f parameter index values fts _ _ _ _ hrest
          subst this
          have hroot : (2 ^ ftsTreeHeight + values (fts.perm ⟨position, hposition⟩)) / 2 ^ ftsTreeHeight = 1 := by
            have := start_div_bounds _ ftsTreeHeight hv le_rfl
            simp only [Nat.sub_self, pow_zero, zero_add] at this
            omega
          refine ⟨ftsTreeHeight, le_rfl, by rw [hheap, hroot], by rw [hstack]; trivial, ?_⟩
          rw [show position + 1 = ftsOpenings by omega, valuesFrom_last]
      rw [← htopEq]
      -- the leaf itself
      have hleafSchedule := segmentsRun_schedule f parameter index fts (leafValue values fts position)
        (by rw [leafValue_of_lt values fts _ hposition]; exact hv) top htop ftsSegments _
        (leafStart values fts position hposition r) r1
        { state with heap := 2 ^ ftsTreeHeight ||| leafValue values fts position,
                     parity := decide ((2 ^ ftsTreeHeight ||| leafValue values fts position) % 2 = 1), reads := [] }
        0 hleaf (by simp [hstart, leafValue_of_lt values fts _ hposition]) (Nat.zero_le _)
        hr1heap hchain1 (by simp [leafValue_of_lt values fts _ hposition]) hsstack rfl
        (by simp [leafValue_of_lt values fts _ hposition]) hdone
      rw [← List.range_eq_range', Nat.sub_zero] at hleafSchedule
      obtain ⟨hcheap, hcstack, hcdone⟩ := hleafSchedule
      by_cases hpush : position + 1 < ftsOpenings
      · rw [if_pos hpush] at hrest
        set climbed := (List.range top).foldl scheduleStep
          { state with heap := 2 ^ ftsTreeHeight ||| leafValue values fts position,
                       parity := decide ((2 ^ ftsTreeHeight ||| leafValue values fts position) % 2 = 1),
                       reads := [] } with hclimbed
        set closed : ScheduleState :=
          { climbed with done := climbed.done ++ [⟨false, climbed.parity, climbed.reads⟩] } with hclosed
        rw [valuesFrom_cons values fts (position + 1) hpush]
        dsimp only
        rw [← valuesFrom_cons values fts (position + 1) hpush]
        obtain ⟨hdone', hopen'⟩ := ih (position + 1) _ _ _
          { closed with stack := (closed.heap ^^^ 1) :: closed.stack } hrest (by omega) (by omega) hheap hstack
          (by simp only [hclosed, List.map_cons, hcheap, hcstack]) hcdone
        refine ⟨hdone', fun s hs hle => ?_⟩
        rcases Nat.eq_or_lt_of_le hle with heq | hlt
        · subst heq
          have hmem : (leafValue values fts position, fts.secrets ⟨position, hs⟩) ∈ r1.openings := by
            apply hopen1
            apply List.mem_append_right
            simp [pendingOpenings, leafValue_of_lt values fts _ hposition]
          -- the openings only grow along the rest of the run
          exact leavesRun_openings f parameter index values fts _ _ _ _ _ hrest _ hmem
        · exact hopen' s hs hlt
      · rw [if_neg hpush] at hrest
        have hzero : remaining = 0 := by omega
        subst hzero
        have := leavesRun_zero_eq f parameter index values fts _ _ _ _ hrest
        subst this
        rw [show position + 1 = ftsOpenings by omega, valuesFrom_last]
        dsimp only
        refine ⟨hcdone, fun s hs hle => ?_⟩
        have hs' : s = position := by omega
        subst hs'
        apply hopen1
        apply List.mem_append_right
        simp [pendingOpenings, leafValue_of_lt values fts _ hposition]

/-! ### The leaf queries -/

/-- Every consumed opening was hashed by a recorded query. -/
def OpeningsQueried (r : Run) : Prop :=
  ∀ opening ∈ r.openings, leafInput parameter index opening.1 opening.2 ∈ r.queries

theorem foldRun_queries_mono (segment : Segment) (remaining position : Nat) (r : Run) :
    ∀ x ∈ r.queries, x ∈ (foldRun f parameter index segment remaining position r).queries := by
  intro x hx
  rw [foldRun_queries]
  exact List.mem_append_left _ hx

theorem segmentsRun_openingsQueried (segments : Fin ftsSegments → Segment) (fuel : Nat) (pending : PendingHash)
    (r r' : Run) (hrun : segmentsRun f parameter index segments fuel pending r = some r')
    (hq : OpeningsQueried parameter index r) : OpeningsQueried parameter index r' := by
  induction fuel generalizing pending r with
  | zero => simp [segmentsRun] at hrun
  | succ fuel ih =>
      rw [segmentsRun] at hrun
      by_cases hsegment : r.segment < ftsSegments
      swap
      · rw [dif_neg hsegment] at hrun; simp at hrun
      rw [dif_pos hsegment] at hrun
      dsimp only at hrun
      by_cases hfolds : SegmentRejects (segments ⟨r.segment, hsegment⟩) r.heap
      · rw [if_pos hfolds] at hrun; simp at hrun
      rw [if_neg hfolds] at hrun
      set started : Run := { r.hash f (pendingInput parameter index pending r.node) with
        openings := r.openings ++ pendingOpenings pending } with hstarted
      set folded := foldRun f parameter index (segments ⟨r.segment, hsegment⟩)
        (segments ⟨r.segment, hsegment⟩).folds.val 0 started with hfoldedDef
      have hstartedQ : OpeningsQueried parameter index started := by
        intro opening hmem
        rcases List.mem_append.mp hmem with hmem | hmem
        · exact List.mem_append_left _ (hq opening hmem)
        · cases pending with
          | leaf value secret =>
              simp only [pendingOpenings, List.mem_singleton] at hmem
              subst hmem
              exact List.mem_append_right _ (List.mem_singleton_self _)
          | merge _ _ => simp [pendingOpenings] at hmem
      have hfoldedQ : OpeningsQueried parameter index folded := by
        intro opening hmem
        have hmem' : opening ∈ started.openings := by
          rw [← foldRun_openings f parameter index _ _ _ started]; exact hmem
        exact foldRun_queries_mono f parameter index _ _ _ started _ (hstartedQ opening hmem')
      by_cases hmerge : (segments ⟨r.segment, hsegment⟩).merge = true
      · rw [if_pos hmerge] at hrun
        rcases hstack : folded.stack with _ | ⟨⟨left, sibling⟩, rest⟩
        · rw [hstack] at hrun; simp at hrun
        rw [hstack] at hrun
        dsimp only at hrun
        by_cases hsibling : sibling = folded.heap
        swap
        · rw [if_neg hsibling] at hrun; simp at hrun
        rw [if_pos hsibling] at hrun
        exact ih _ _ hrun hfoldedQ
      · rw [if_neg hmerge] at hrun
        cases hrun
        exact hfoldedQ

theorem leavesRun_openingsQueried (values : SlotCode → Nat) (fts : FtsSignature) :
    ∀ (remaining position previous : Nat) (r r' : Run),
      leavesRun f parameter index values fts remaining position previous r = some r' →
      OpeningsQueried parameter index r → OpeningsQueried parameter index r' := by
  intro remaining
  induction remaining with
  | zero =>
      intro position previous r r' hrun hq
      rw [leavesRun_zero_eq f parameter index values fts _ _ _ _ hrun]
      exact hq
  | succ remaining ih =>
      intro position previous r r' hrun hq
      by_cases hposition : position < ftsOpenings
      · obtain ⟨r1, hleaf, hrest⟩ := leavesRun_succ_eq f parameter index values fts _ _ _ _ _ hposition hrun
        have h1 := segmentsRun_openingsQueried f parameter index _ _ _ _ _ hleaf hq
        apply ih _ _ _ _ hrest
        split_ifs
        · exact h1
        · exact h1
      · rw [leavesRun, dif_neg hposition] at hrun
        simp at hrun

/-- **The leaf queries of an accepted run**: every leaf's secret was hashed at the leaf's value. -/
theorem recoverRun_leafQuery (values : SlotCode → Nat) (fts : FtsSignature) (r : Run)
    (hrun : recoverRun f parameter index values fts = some r) :
    ∀ opening ∈ r.openings, leafInput parameter index opening.1 opening.2 ∈ r.queries := by
  rw [recoverRun] at hrun
  rcases hleaves : leavesRun f parameter index values fts ftsOpenings 0 0 Run.initial with _ | r'
  · rw [hleaves] at hrun
    simp at hrun
  rw [hleaves] at hrun
  dsimp only at hrun
  split_ifs at hrun
  cases hrun
  exact leavesRun_openingsQueried f parameter index values fts _ _ _ _ _ hleaves
    (fun _ h => by simp [Run.initial] at h)

/-! ### The canonical opening (E3) -/

theorem segment_ext {s t : Segment} (hfolds : s.folds = t.folds) (hmerge : s.merge = t.merge)
    (hparity : s.parity = t.parity) (hnode : ∀ i, s.node i = t.node i) : s = t := by
  cases s with
  | mk sf sm sp sn snorm =>
    cases t with
    | mk tf tm tp tn tnorm =>
      simp only at hfolds hmerge hparity
      subst hfolds hmerge hparity
      have : sn = tn := by
        funext i
        have := hnode i.val
        simpa [Segment.node, i.isLt] using this
      subst this
      rfl

theorem slotValue_castSucc (leaves : IndexGroup → FtsLeaf) (slot : IndexGroup) :
    slotValue leaves slot.castSucc = (leaves slot).val := by
  simp [slotValue]

theorem toSegment_folds_val (sseg : ScheduleSegment) (hlen : sseg.reads.length < 16) :
    sseg.folds.val = sseg.reads.length := by
  simp [ScheduleSegment.folds, Nat.mod_eq_of_lt hlen]

theorem toSegment_node (sseg : ScheduleSegment) (nodes : Fin sseg.folds.val → Digest)
    (hlen : sseg.reads.length < 16) (i : Nat) (hi : i < sseg.reads.length) :
    (sseg.toSegment nodes).node i = nodes ⟨i, by rw [toSegment_folds_val sseg hlen]; exact hi⟩ := by
  unfold ScheduleSegment.toSegment Segment.normalized Segment.node
  rw [dif_pos]

theorem toSegment_node_of_ge (sseg : ScheduleSegment) (nodes : Fin sseg.folds.val → Digest)
    (hlen : sseg.reads.length < 16) (i : Nat) (hi : ¬ i < sseg.reads.length) :
    (sseg.toSegment nodes).node i = 0 := by
  unfold ScheduleSegment.toSegment Segment.normalized Segment.node
  rw [dif_neg]
  show ¬ i < sseg.folds.val
  rw [toSegment_folds_val sseg hlen]
  exact hi

/-- **An accepted run follows the schedule**: every segment of the signature matches the honest schedule's,
and every leaf's opening was consumed at its value. -/
theorem recoverRun_schedule (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : Run)
    (hrun : recoverRun f parameter index (slotValue leaves) fts = some r) :
    (∀ j : Fin ftsSegments, SegmentMatches fts r j ((schedule (sortedLeaves leaves)).getD j.val default)) ∧
      ∀ s : Fin ftsOpenings, (leafValue (slotValue leaves) fts s.val, fts.secrets s) ∈ r.openings := by
  obtain ⟨slot, hperm, hsorted, hsegments, _, _, _⟩ := recoverRun_structure f parameter index leaves fts r hrun
  obtain ⟨_, hlt⟩ := recoverRun_order f parameter index (slotValue leaves) fts r hrun
  have hvalues : ∀ s (hs : s < ftsOpenings), slotValue leaves (fts.perm ⟨s, hs⟩) < 2 ^ ftsTreeHeight := by
    intro s hs
    have := hlt s hs
    rwa [leafValue_of_lt _ _ _ hs] at this
  have hsortedLeaves : sortedLeaves leaves = valuesFrom (slotValue leaves) fts 0 := by
    rw [sortedLeaves, hsorted, List.map_ofFn, valuesFrom, List.drop_zero]
    congr 1
    funext s
    simp only [Function.comp, leafValue_of_lt _ _ _ s.isLt, Fin.eta, hperm, slotValue_castSucc]
  rw [recoverRun] at hrun
  rcases hleaves : leavesRun f parameter index (slotValue leaves) fts ftsOpenings 0 0 Run.initial with _ | r'
  · rw [hleaves] at hrun
    simp at hrun
  rw [hleaves] at hrun
  dsimp only at hrun
  split_ifs at hrun with haccept
  cases hrun
  obtain ⟨_, hheap, hstack⟩ := haccept
  obtain ⟨hdone, hopen⟩ := leavesRun_schedule f parameter index fts (slotValue leaves) hvalues ftsOpenings 0 0
    Run.initial r ⟨[], [], 0, false, []⟩ hleaves rfl (by decide) hheap hstack rfl
    ⟨rfl, fun j hj => by simp [Run.initial, RecoverState.initial] at hj⟩
  refine ⟨fun j => ?_, fun s => hopen s.val s.isLt (Nat.zero_le _)⟩
  rw [hsortedLeaves]
  exact hdone.2 j (by rw [hsegments]; exact j.isLt)

/-- **E3, canonicity.** An accepted run that consumed only honest items (the extraction's `Consumed`) was
run on the honest opening of the digest's leaves: the sorted slots, the true secrets, and the honest
schedule's segments with the honest nodes. -/
theorem recoverRun_honest (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (secret : FtsLeaf → Digest)
    (r : Run) (hrun : recoverRun f parameter index (slotValue leaves) fts = some r)
    (hconsumed : Consumed f parameter index secret r) :
    fts = honestFts leaves secret (honestFtsNode f parameter index porsTree secret) := by
  obtain ⟨slot, hperm, hsorted, _, _, _, _⟩ := recoverRun_structure f parameter index leaves fts r hrun
  obtain ⟨hmatch, hopen⟩ := recoverRun_schedule f parameter index leaves fts r hrun
  obtain ⟨hreads, hparities, hopenings⟩ := hconsumed
  have hslotGet : ∀ s : Fin ftsOpenings, (sortedSlots leaves).getD s.val ⟨0, by decide⟩ = slot s := by
    intro s
    rw [hsorted, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  cases fts with
  | mk perm secrets segments =>
    have hperm' : ∀ s, perm s = (slot s).castSucc := hperm
    unfold honestFts
    dsimp only
    rw [FtsSignature.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · funext s
      rw [hslotGet s]
      exact hperm s
    · funext s
      rw [hslotGet s]
      have hmem := hopen s
      have := hopenings _ hmem
      simp only at this
      rw [this]
      congr 1
      rw [leafValue_of_lt _ _ _ s.isLt]
      simp only [Fin.eta, hperm', slotValue_castSucc]
      exact ftsLeafOfNat_val _
    · funext j
      obtain ⟨hfolds, hmerge, hparity, hnodes⟩ := hmatch j
      simp only at hfolds hmerge hparity hnodes
      set sseg := (schedule (sortedLeaves leaves)).getD j.val default with hsseg
      have hlen : sseg.reads.length < 16 := by
        rw [← hfolds]; exact (segments j).folds.isLt
      apply segment_ext
      · apply Fin.ext
        rw [hfolds]
        simp [ScheduleSegment.toSegment, Segment.normalized, ScheduleSegment.folds, Nat.mod_eq_of_lt hlen]
      · simp [ScheduleSegment.toSegment, Segment.normalized, hmerge]
      · simp only [ScheduleSegment.toSegment, Segment.normalized, ScheduleSegment.folds,
          Nat.mod_eq_of_lt hlen]
        by_cases hzero : (segments j).folds.val = 0
        · rw [(segments j).parity_normal hzero]
          rw [hzero] at hfolds
          simp [← hfolds]
        · obtain ⟨heap, hmem, hpar⟩ := hparity hzero
          have := hparities _ hmem
          simp only at this
          rw [this, hpar]
          have : sseg.reads.length ≠ 0 := by omega
          simp [this]
      · intro i
        have hmemOr : sseg ∈ schedule (sortedLeaves leaves) ∨ sseg = default := by
          rw [hsseg, List.getD_eq_getElem?_getD]
          cases h : (schedule (sortedLeaves leaves))[j.val]? with
          | none => exact Or.inr rfl
          | some x => exact Or.inl (List.mem_of_getElem? h)
        by_cases hi : i < sseg.reads.length
        · rw [toSegment_node sseg _ hlen i hi]
          have hmem := hnodes i hi
          have hvalue := hreads _ hmem
          simp only at hvalue
          rw [hvalue]
          simp only [List.getD_eq_getElem _ _ hi]
          have hsseg' : sseg ∈ schedule (sortedLeaves leaves) := by
            rcases hmemOr with h | h
            · exact h
            · exfalso
              rw [h] at hi
              exact Nat.not_lt_zero _ hi
          have hread := schedule_read _ (sortedLeaves_lt leaves) sseg hsseg' _ (List.getElem_mem hi)
          rw [honestFtsNode_eq_heap f parameter index porsTree secret _ _ hread.1.le hread.2]
          rfl
        · rw [toSegment_node_of_ge sseg _ hlen i hi]
          simp only [Segment.node]
          rw [dif_neg (by omega)]

end PorsMachine

end SphincsSecurity.Concrete
