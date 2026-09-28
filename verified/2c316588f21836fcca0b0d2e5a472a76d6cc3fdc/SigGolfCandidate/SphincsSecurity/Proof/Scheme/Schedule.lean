import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Arith
import SigGolfCandidate.SphincsSecurity.Scheme
/-!
# The honest schedule reads tree nodes

Every position `(height, nodeIdx)` the honest schedule of `Scheme.lean` reads is a node of the PORS tree:
`height < 14` and `nodeIdx < 2^(14 - height)`. At height `h` a leaf `v` climbs through heap index
`(2^14 + v) / 2^h = 2^(14 - h) + v / 2^h`, and the node it reads is that heap index's sibling, whose offset
in its level stays below `2^(14 - h)`. This is what lets a signer that reads the nodes off a built table
agree with the specification, which computes each node on its own.
-/

namespace SphincsSecurity.Concrete

/-- A read position is a node of the PORS tree below the root. -/
def ScheduleRead (r : Nat × Nat) : Prop := r.1 < ftsTreeHeight ∧ r.2 < 2 ^ (ftsTreeHeight - r.1)

/-- Every read of the finished segments and of the open one is a tree node. -/
def ScheduleGood (state : ScheduleState) : Prop :=
  (∀ segment ∈ state.done, ∀ r ∈ segment.reads, ScheduleRead r) ∧ ∀ r ∈ state.reads, ScheduleRead r

theorem heap_climb (v height : Nat) (hv : v < 2 ^ ftsTreeHeight) (hheight : height ≤ ftsTreeHeight) :
    (2 ^ ftsTreeHeight + v) / 2 ^ height = 2 ^ (ftsTreeHeight - height) + v / 2 ^ height
      ∧ v / 2 ^ height < 2 ^ (ftsTreeHeight - height) := by
  have hsplit : 2 ^ ftsTreeHeight = 2 ^ (ftsTreeHeight - height) * 2 ^ height := by
    rw [← pow_add, Nat.sub_add_cancel hheight]
  have hpos : 0 < 2 ^ height := Nat.two_pow_pos _
  refine ⟨?_, ?_⟩
  · rw [hsplit, Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.add_comm]
  · rw [Nat.div_lt_iff_lt_mul hpos, ← hsplit]
    exact hv

theorem scheduleStep_good (v height : Nat) (hv : v < 2 ^ ftsTreeHeight) (hheight : height < ftsTreeHeight)
    (state : ScheduleState) (hheap : state.heap = (2 ^ ftsTreeHeight + v) / 2 ^ height)
    (hgood : ScheduleGood state) :
    ScheduleGood (scheduleStep state height)
      ∧ (scheduleStep state height).heap = (2 ^ ftsTreeHeight + v) / 2 ^ (height + 1) := by
  obtain ⟨hclimb, hoffset⟩ := heap_climb v height hv hheight.le
  have heven : 2 ^ (ftsTreeHeight - height) = 2 * 2 ^ (ftsTreeHeight - height - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hhalf : (2 ^ ftsTreeHeight + v) / 2 ^ (height + 1) = state.heap / 2 := by
    rw [hheap, div_pow_succ]
  have hfold : ScheduleGood { state with
      reads := state.reads ++ [(height, (state.heap ^^^ 1) - 2 ^ (ftsTreeHeight - height))],
      heap := state.heap / 2 } := by
    refine ⟨hgood.1, fun r hr => ?_⟩
    rcases List.mem_append.mp hr with hr | hr
    · exact hgood.2 r hr
    · rw [List.mem_singleton] at hr
      subst r
      refine ⟨hheight, ?_⟩
      obtain ⟨j, hcase⟩ := index_sibling_cases state.heap
      rw [← nat_xor_eq]
      simp only
      rcases hcase with ⟨hc, hx, _⟩ | ⟨hc, hx, _⟩ <;> rw [hx] <;> omega
  unfold scheduleStep
  split
  · rename_i top rest hstack
    split
    · refine ⟨⟨fun segment hsegment => ?_, fun r hr => by simp at hr⟩, hhalf.symm⟩
      rcases List.mem_append.mp hsegment with hsegment | hsegment
      · exact hgood.1 segment hsegment
      · rw [List.mem_singleton] at hsegment
        subst segment
        exact hgood.2
    · exact ⟨hfold, hhalf.symm⟩
  · exact ⟨hfold, hhalf.symm⟩

theorem foldl_scheduleStep_good (v : Nat) (hv : v < 2 ^ ftsTreeHeight) :
    ∀ n, n ≤ ftsTreeHeight → ∀ state : ScheduleState, state.heap = 2 ^ ftsTreeHeight + v →
      ScheduleGood state →
      ScheduleGood ((List.range n).foldl scheduleStep state)
        ∧ ((List.range n).foldl scheduleStep state).heap = (2 ^ ftsTreeHeight + v) / 2 ^ n := by
  intro n
  induction n with
  | zero =>
      intro _ state hheap hgood
      simp only [List.range_zero, List.foldl_nil, pow_zero, Nat.div_one]
      exact ⟨hgood, hheap⟩
  | succ n ih =>
      intro hn state hheap hgood
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      obtain ⟨hgood', hheap'⟩ := ih (by omega) state hheap hgood
      exact scheduleStep_good v n hv (by omega) _ hheap' hgood'

theorem bitLength_xor_le (v w : Nat) (hv : v < 2 ^ ftsTreeHeight) (hw : w < 2 ^ ftsTreeHeight) :
    bitLength (v ^^^ w) ≤ ftsTreeHeight := by
  have hlt : v ^^^ w < 2 ^ ftsTreeHeight := Nat.xor_lt_two_pow hv hw
  unfold bitLength
  split
  · omega
  · rename_i hne
    have := (Nat.log2_lt hne).mpr hlt
    omega

/-- One leaf's climb through `top` heights, closed by its last segment. -/
theorem leafClimb_good (v top : Nat) (hv : v < 2 ^ ftsTreeHeight) (htop : top ≤ ftsTreeHeight)
    (state : ScheduleState) (hgood : ScheduleGood state) :
    let climbed := (List.range top).foldl scheduleStep
      { state with heap := 2 ^ ftsTreeHeight ||| v,
                   parity := decide ((2 ^ ftsTreeHeight ||| v) % 2 = 1), reads := [] }
    ScheduleGood { climbed with done := climbed.done ++ [⟨false, climbed.parity, climbed.reads⟩] } := by
  intro climbed
  have hor : 2 ^ ftsTreeHeight ||| v = 2 ^ ftsTreeHeight + v := by
    have := Nat.two_pow_add_eq_or_of_lt hv 1
    simpa using this.symm
  obtain ⟨hclimb, _⟩ := foldl_scheduleStep_good v hv top htop
    { state with heap := 2 ^ ftsTreeHeight ||| v,
                 parity := decide ((2 ^ ftsTreeHeight ||| v) % 2 = 1), reads := [] }
    hor ⟨hgood.1, fun r hr => by simp at hr⟩
  refine ⟨fun segment hsegment => ?_, hclimb.2⟩
  rcases List.mem_append.mp hsegment with hsegment | hsegment
  · exact hclimb.1 segment hsegment
  · rw [List.mem_singleton] at hsegment
    subst segment
    exact hclimb.2

theorem scheduleLeaves_good : ∀ (sorted : List Nat), (∀ v ∈ sorted, v < 2 ^ ftsTreeHeight) →
    ∀ state : ScheduleState, ScheduleGood state → ScheduleGood (scheduleLeaves sorted state) := by
  intro sorted
  induction sorted with
  | nil => intro _ state hgood; exact hgood
  | cons v rest ih =>
      intro hsorted state hgood
      have hv : v < 2 ^ ftsTreeHeight := hsorted v (List.mem_cons_self ..)
      have hrest : ∀ w ∈ rest, w < 2 ^ ftsTreeHeight := fun w hw => hsorted w (List.mem_cons_of_mem _ hw)
      cases rest with
      | nil =>
          rw [scheduleLeaves.eq_2, scheduleLeaves.eq_1]
          exact leafClimb_good v ftsTreeHeight hv le_rfl state hgood
      | cons w rest' =>
          rw [scheduleLeaves.eq_def]
          dsimp only
          apply ih hrest
          have hle := bitLength_xor_le v w hv (hrest w (List.mem_cons_self ..))
          have hclosed := leafClimb_good v (bitLength (v ^^^ w) - 1) hv (by omega) state hgood
          exact ⟨hclosed.1, hclosed.2⟩

/-- **Every read of the honest schedule is a node of the tree.** -/
theorem schedule_read (sorted : List Nat) (hsorted : ∀ v ∈ sorted, v < 2 ^ ftsTreeHeight) :
    ∀ segment ∈ schedule sorted, ∀ r ∈ segment.reads, ScheduleRead r :=
  (scheduleLeaves_good sorted hsorted ⟨[], [], 0, false, []⟩
    ⟨fun segment hsegment => by simp at hsegment, fun r hr => by simp at hr⟩).1

theorem sortedLeaves_lt (leaves : IndexGroup → FtsLeaf) :
    ∀ v ∈ sortedLeaves leaves, v < 2 ^ ftsTreeHeight := by
  intro v hv
  simp only [sortedLeaves, List.mem_map] at hv
  obtain ⟨r, _, rfl⟩ := hv
  exact (leaves r).isLt

/-- The node `i` of an honest segment read off `node` at the segment's read positions. -/
theorem honestFts_congr (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest)
    (node node' : Nat → Nat → Digest)
    (hnode : ∀ segment ∈ schedule (sortedLeaves leaves), ∀ r ∈ segment.reads,
      node r.1 r.2 = node' r.1 r.2) :
    honestFts leaves secret node = honestFts leaves secret node' := by
  unfold honestFts
  dsimp only
  rw [FtsSignature.mk.injEq]
  refine ⟨rfl, rfl, ?_⟩
  funext j
  generalize hsegment : (schedule (sortedLeaves leaves)).getD j.val default = segment
  have hmem : segment ∈ schedule (sortedLeaves leaves) ∨ segment = default := by
    rw [← hsegment, List.getD_eq_getElem?_getD]
    cases h : (schedule (sortedLeaves leaves))[j.val]? with
    | none => exact Or.inr rfl
    | some s => exact Or.inl (List.mem_of_getElem? h)
  refine congrArg (ScheduleSegment.toSegment segment) ?_
  funext i
  have hi : i.val < segment.reads.length :=
    Nat.lt_of_lt_of_le i.isLt (Nat.mod_le _ _)
  rw [List.getD_eq_getElem _ _ hi]
  rcases hmem with hmem | hdefault
  · exact hnode segment hmem _ (List.getElem_mem hi)
  · subst hdefault
    exact (Nat.not_lt_zero i.val hi).elim

/-- **The honest opening needs the tree only at the schedule's reads**, and those are tree nodes. -/
theorem honestFts_congr_tree (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest)
    (node node' : Nat → Nat → Digest)
    (hnode : ∀ level nodeIdx, level < ftsTreeHeight → nodeIdx < 2 ^ (ftsTreeHeight - level) →
      node level nodeIdx = node' level nodeIdx) :
    honestFts leaves secret node = honestFts leaves secret node' :=
  honestFts_congr leaves secret node node' fun segment hsegment r hr =>
    let hread := schedule_read _ (sortedLeaves_lt leaves) segment hsegment r hr
    hnode r.1 r.2 hread.1 hread.2

end SphincsSecurity.Concrete
