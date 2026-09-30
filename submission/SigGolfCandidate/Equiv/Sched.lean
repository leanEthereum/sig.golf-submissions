import SigGolfCandidate.Equiv.Digits
import SigGolfCandidate.SphincsSecurity.Completeness.Stack

/-!
# The honest schedule: reference vs abstract

`Ref.schedule` (segment bytes and the flat read list, `ref.schedule`) is the abstract
`Concrete.schedule` (a list of segments with their reads), and for admissible leaves the abstract
schedule has `29` segments of at most `14` reads each, all at positions inside the tree, and
`octopusSize` reads in all.
-/

namespace SigGolfCandidate.Equiv

open SphincsSecurity (IndexGroup FtsLeaf)
open SphincsSecurity.Concrete (ScheduleSegment)

/-- The reference's segment byte of an abstract schedule segment (`a | 16 merge | 32 t`, bitwise). -/
def segByte (s : ScheduleSegment) : Nat :=
  s.reads.length ||| (if s.merge then 16 else 0) ||| 32 * (if s.parity then 1 else 0)

/-! ## The simulation -/

open SphincsSecurity.Concrete (ScheduleState scheduleStep scheduleLeaves)

theorem parity_val (n : Nat) : (if decide (n % 2 = 1) = true then 1 else 0) = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem porsT_div (h : Nat) (hh : h ≤ 14) : Ref.porsT / 2 ^ h = 2 ^ (SphincsSecurity.ftsTreeHeight - h) := by
  show 2 ^ 14 / 2 ^ h = 2 ^ (14 - h)
  exact Nat.pow_div hh (by norm_num)

/-- The step relation: reference state `(st, E, cnt, t)` against the abstract state. -/
def SimR (x : Ref.SchedState × Nat × Nat × Nat) (c : ScheduleState) : Prop :=
  x.1.segs = c.done.map segByte ∧ x.1.reads = (c.done.map (·.reads)).flatten ++ c.reads ∧
    x.1.stack = c.stack ∧ x.2.1 = c.heap ∧ x.2.2.1 = c.reads.length ∧
    x.2.2.2 = (if c.parity then 1 else 0)

theorem schedStep_sim (x : Ref.SchedState × Nat × Nat × Nat) (c : ScheduleState) (h : Nat)
    (hh : h ≤ 14) (hR : SimR x c) : SimR (Ref.schedStep x h) (scheduleStep c h) := by
  obtain ⟨⟨segs, reads, stack⟩, E, cnt, t⟩ := x
  obtain ⟨done, cstack, heap, parity, creads⟩ := c
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
  simp only at h1 h2 h3 h4 h5 h6
  subst h1 h2 h3 h4 h5 h6
  have hp := porsT_div h hh
  unfold Ref.schedStep scheduleStep
  cases stack with
  | nil =>
    simp only
    refine ⟨rfl, ?_, rfl, rfl, ?_, rfl⟩
    · simp [hp]
    · simp
  | cons Q rest =>
    simp only
    by_cases hQ : Q = E
    · rw [if_pos hQ, if_pos hQ]
      refine ⟨?_, ?_, rfl, rfl, rfl, ?_⟩
      · simp [segByte]
      · simp
      · simp only [parity_val]
    · rw [if_neg hQ, if_neg hQ]
      refine ⟨rfl, ?_, rfl, rfl, ?_, rfl⟩
      · simp [hp]
      · simp

theorem foldl_schedStep_sim (l : List Nat) (hl : ∀ h ∈ l, h ≤ 14) :
    ∀ (x : Ref.SchedState × Nat × Nat × Nat) (c : ScheduleState), SimR x c →
      SimR (l.foldl Ref.schedStep x) (l.foldl scheduleStep c) := by
  induction l with
  | nil => intro x c h; exact h
  | cons h l ih =>
    intro x c hR
    exact ih (fun y hy => hl y (by simp [hy])) _ _
      (schedStep_sim x c h (hl h (by simp)) hR)

theorem bitLen_lt {v w : Nat} (hv : v < 2 ^ 14) (hw : w < 2 ^ 14) : Ref.bitLen (v ^^^ w) ≤ 14 :=
  SphincsSecurity.Completeness.bitLength_le (Nat.xor_lt_two_pow hv hw)

/-- The leaf relation: segment bytes, flat reads, stack. -/
def SimL (st : Ref.SchedState) (c : ScheduleState) : Prop :=
  st.segs = c.done.map segByte ∧ st.reads = (c.done.map (·.reads)).flatten ∧ st.stack = c.stack

theorem climb_sim (st : Ref.SchedState) (c : ScheduleState) (hR : SimL st c) (v top : Nat)
    (htop : top ≤ 14) :
    SimR ((List.range top).foldl Ref.schedStep (st, Ref.porsT ||| v, 0, (Ref.porsT ||| v) % 2))
      ((List.range' 0 top).foldl scheduleStep
        ⟨c.done, c.stack, 2 ^ SphincsSecurity.ftsTreeHeight ||| v,
          decide ((2 ^ SphincsSecurity.ftsTreeHeight ||| v) % 2 = 1), []⟩) := by
  rw [← List.range_eq_range']
  obtain ⟨h1, h2, h3⟩ := hR
  refine foldl_schedStep_sim _ (fun h hh => by rw [List.mem_range] at hh; omega) _ _ ?_
  refine ⟨h1, by simp [h2], h3, rfl, rfl, ?_⟩
  simp only [parity_val]; rfl

theorem post_sim (X : Ref.SchedState × Nat × Nat × Nat) (Y : ScheduleState) (h : SimR X Y) :
    X.1.segs ++ [X.2.2.1 ||| 32 * X.2.2.2] = (Y.done ++ [(⟨false, Y.parity, Y.reads⟩ : ScheduleSegment)]).map segByte ∧
    X.1.reads = ((Y.done ++ [(⟨false, Y.parity, Y.reads⟩ : ScheduleSegment)]).map (·.reads)).flatten := by
  obtain ⟨g1, g2, g3, g4, g5, g6⟩ := h
  refine ⟨?_, ?_⟩
  · simp [g1, segByte, g5, g6]
  · simp [g2]

theorem schedLeaves_sim (vs : List Nat) (hvs : ∀ v ∈ vs, v < 2 ^ 14) :
    ∀ (n k : Nat) (st : Ref.SchedState) (c : ScheduleState), k + n = vs.length → SimL st c →
      SimL ((List.range' k n).foldl (Ref.schedLeaf vs) st) (scheduleLeaves (vs.drop k) c) := by
  intro n
  induction n with
  | zero =>
    intro k st c hk hR
    rw [show vs.drop k = [] by simp; omega]
    exact hR
  | succ n ih =>
    intro k st c hk hR
    obtain ⟨v, rest, hdrop⟩ : ∃ v rest, vs.drop k = v :: rest := by
      cases h : vs.drop k with
      | nil => simp at h; omega
      | cons v rest => exact ⟨v, rest, rfl⟩
    have hget : ∀ i, vs.getD (k + i) 0 = (v :: rest).getD i 0 := by
      intro i
      rw [← hdrop]
      simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
    have hgetv : vs.getD k 0 = v := hget 0
    have hmem : ∀ x ∈ v :: rest, x < 2 ^ 14 := fun x hx =>
      hvs x (List.mem_of_mem_drop (by rw [hdrop]; exact hx))
    have hv : v < 2 ^ 14 := hmem v (by simp)
    have hlen : vs.length = k + 1 + rest.length := by
      have := congrArg List.length hdrop; simp at this; omega
    have hrest : vs.drop (k + 1) = rest := by
      rw [← List.drop_drop, hdrop]; rfl
    rw [List.range'_succ, List.foldl_cons, hdrop, SphincsSecurity.Completeness.scheduleLeaves_cons]
    have key : ∀ c' : ScheduleState, SimL (Ref.schedLeaf vs st k) c' →
        SimL ((List.range' (k + 1) n).foldl (Ref.schedLeaf vs) (Ref.schedLeaf vs st k))
          (scheduleLeaves rest c') := fun c' hc => by
      have := ih (k + 1) _ c' (by omega) hc
      rwa [hrest] at this
    apply key
    cases rest with
    | nil =>
      unfold Ref.schedLeaf
      simp only [SphincsSecurity.Completeness.leafTop]
      rw [if_neg (by simp at hlen; omega), if_neg (by simp at hlen; omega), hgetv]
      have hf := climb_sim st c hR v Ref.porsH (le_refl _)
      revert hf
      generalize (List.range Ref.porsH).foldl Ref.schedStep
        (st, Ref.porsT ||| v, 0, (Ref.porsT ||| v) % 2) = X
      intro hf
      obtain ⟨p1, p2⟩ := post_sim X _ hf
      obtain ⟨⟨segs, reads, stack⟩, E, cnt, t⟩ := X
      exact ⟨p1, p2, hf.2.2.1⟩
    | cons w r =>
      have hw : vs.getD (k + 1) 0 = w := hget 1
      have hwlt : w < 2 ^ 14 := hmem w (by simp)
      unfold Ref.schedLeaf
      simp only [SphincsSecurity.Completeness.leafTop]
      rw [if_pos (by simp at hlen ⊢; omega), if_pos (by simp at hlen ⊢; omega), hgetv, hw]
      have hf := climb_sim st c hR v (Ref.bitLen (v ^^^ w) - 1)
        (le_trans (Nat.sub_le _ _) (bitLen_lt hv hwlt))
      revert hf
      generalize (List.range (Ref.bitLen (v ^^^ w) - 1)).foldl Ref.schedStep
        (st, Ref.porsT ||| v, 0, (Ref.porsT ||| v) % 2) = X
      intro hf
      obtain ⟨p1, p2⟩ := post_sim X _ hf
      obtain ⟨⟨segs, reads, stack⟩, E, cnt, t⟩ := X
      exact ⟨p1, p2, congrArg₂ List.cons (congrArg (· ^^^ 1) hf.2.2.2.1) hf.2.2.1⟩

/-- **The reference schedule is the abstract schedule** (for leaf values in the tree). -/
theorem schedule_ref (vs : List Nat) (hvs : ∀ v ∈ vs, v < 2 ^ 14) :
    Ref.schedule vs = ((SphincsSecurity.Concrete.schedule vs).map segByte,
      ((SphincsSecurity.Concrete.schedule vs).map (·.reads)).flatten) := by
  have h := schedLeaves_sim vs hvs vs.length 0 ⟨[], [], []⟩ ⟨[], [], 0, false, []⟩ (by omega)
    ⟨rfl, rfl, rfl⟩
  rw [List.drop_zero] at h
  unfold Ref.schedule SphincsSecurity.Concrete.schedule
  rw [List.range_eq_range']
  exact Prod.ext h.1 h.2.1

/-! ## The schedule of admissible leaves (via `Completeness.Stack`) -/

section admissible
open SphincsSecurity.Completeness (climbSegs allSegs sibs sibPos leafTop sumTops Pending)

theorem sibs_facts (v a b : Nat) (hv : v < 2 ^ 14) (hab : a + b ≤ 14) :
    (sibs v a b).length ≤ 14 ∧ ∀ p ∈ sibs v a b, p.1 < 14 ∧ p.2 < 2 ^ (14 - p.1) := by
  refine ⟨by simp [sibs]; omega, ?_⟩
  intro p hp
  simp only [sibs, List.mem_map, List.mem_range'] at hp
  obtain ⟨y, ⟨i, hi, rfl⟩, rfl⟩ := hp
  simp only [sibPos, Nat.one_mul]
  refine ⟨by omega, ?_⟩
  have h1 : v / 2 ^ (a + i) < 2 ^ (14 - (a + i)) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add]
    exact lt_of_lt_of_le hv (Nat.pow_le_pow_right (by norm_num) (by omega))
  exact Nat.xor_lt_two_pow h1 (Nat.one_lt_two_pow (by omega))

theorem climbSegs_reads (v top : Nat) :
    ∀ (L : List Nat) (x : Nat), x ≤ top → (∀ y ∈ L, y < top) →
      ∀ s ∈ climbSegs v x L top, ∃ a b, s.reads = sibs v a b ∧ a + b ≤ top := by
  intro L
  induction L with
  | nil =>
    intro x hx _ s hs
    simp only [climbSegs, List.mem_singleton] at hs
    subst hs
    exact ⟨x, top - x, rfl, by omega⟩
  | cons y L ih =>
    intro x hx hL s hs
    simp only [climbSegs, List.mem_cons] at hs
    have hy := hL y (by simp)
    rcases hs with rfl | hs
    · exact ⟨x, y - x, rfl, by omega⟩
    · exact ih (y + 1) (by omega) (fun z hz => hL z (by simp [hz])) s hs

theorem leafTop_le (v : Nat) (rest : List Nat) (hv : v < 2 ^ 14) (hr : ∀ w ∈ rest, w < 2 ^ 14) :
    leafTop v rest ≤ 14 := by
  cases rest with
  | nil => exact le_refl _
  | cons w r =>
    simp only [leafTop]
    exact le_trans (Nat.sub_le _ _) (bitLen_lt hv (hr w (by simp)))

theorem allSegs_reads : ∀ (l L : List Nat), (∀ v ∈ l, v < 2 ^ 14) →
    ∀ s ∈ allSegs l L, s.reads.length ≤ 14 ∧ ∀ p ∈ s.reads, p.1 < 14 ∧ p.2 < 2 ^ (14 - p.1) := by
  intro l
  induction l with
  | nil => intro L _ s hs; simp [allSegs] at hs
  | cons v rest ih =>
    intro L hl s hs
    rw [SphincsSecurity.Completeness.allSegs_cons, List.mem_append] at hs
    have hv := hl v (by simp)
    rcases hs with hs | hs
    · have htop := leafTop_le v rest hv (fun w hw => hl w (by simp [hw]))
      obtain ⟨a, b, hr, hab⟩ := climbSegs_reads v _ _ 0 (Nat.zero_le _)
        (fun y hy => (SphincsSecurity.Completeness.mem_filter_lt hy).2) s hs
      rw [hr]
      exact sibs_facts v a b hv (le_trans hab htop)
    · exact ih _ (fun w hw => hl w (by simp [hw])) s hs

theorem climbSegs_total (v top : Nat) :
    ∀ (L : List Nat) (x : Nat), L.Pairwise (· < ·) → (∀ y ∈ L, x ≤ y ∧ y < top) → x ≤ top →
      ((climbSegs v x L top).map (·.reads.length)).sum + L.length = top - x := by
  intro L
  induction L with
  | nil => intro x _ _ hx; simp [climbSegs, sibs]
  | cons y L ih =>
    intro x hs hL hx
    have hy := hL y (by simp)
    have hp := List.pairwise_cons.mp hs
    have := ih (y + 1) hp.2 (fun z hz => ⟨hp.1 z hz, (hL z (by simp [hz])).2⟩) (by omega)
    simp only [climbSegs, List.map_cons, List.sum_cons, List.length_cons, sibs, List.length_map,
      List.length_range'] at this ⊢
    omega

theorem allSegs_total :
    ∀ (rest : List Nat) (v : Nat) (L : List Nat),
      (v :: rest).Pairwise (· < ·) → (∀ w ∈ v :: rest, w < 2 ^ SphincsSecurity.ftsTreeHeight) →
      Pending v L →
      ((allSegs (v :: rest) L).map (·.reads.length)).sum + L.length + rest.length =
        sumTops (v :: rest) := by
  intro rest
  induction rest with
  | nil =>
    intro v L hsorted hbound hL
    have hsplit := SphincsSecurity.Completeness.pending_split hL hsorted hbound
    have hnone : L.filter (leafTop v [] < ·) = [] :=
      SphincsSecurity.Completeness.filter_gt_nil (fun y hy => (hL.2 y hy).1)
    have hlen := congrArg List.length hsplit
    rw [hnone, List.append_nil] at hlen
    have hc := climbSegs_total v (leafTop v []) (L.filter (· < leafTop v [])) 0 (hL.1.filter _)
      (fun y hy => ⟨Nat.zero_le _, (SphincsSecurity.Completeness.mem_filter_lt hy).2⟩) (Nat.zero_le _)
    rw [SphincsSecurity.Completeness.allSegs_cons, show allSegs [] _ = [] from rfl, List.append_nil]
    simp only [sumTops, List.length_nil] at hc hlen ⊢
    omega
  | cons w rest ih =>
    intro v L hsorted hbound hL
    have hw := hbound w (by simp)
    have hvw : v < w := (List.pairwise_cons.mp hsorted).1 w (by simp)
    obtain ⟨hnext, _, _⟩ := SphincsSecurity.Completeness.pending_next hvw hw
      (rfl : leafTop v (w :: rest) = _) hL
    have hsplit := SphincsSecurity.Completeness.pending_split hL hsorted hbound
    have hlen := congrArg List.length hsplit
    rw [List.length_append] at hlen
    have hc := climbSegs_total v (leafTop v (w :: rest)) (L.filter (· < leafTop v (w :: rest))) 0
      (hL.1.filter _)
      (fun y hy => ⟨Nat.zero_le _, (SphincsSecurity.Completeness.mem_filter_lt hy).2⟩) (Nat.zero_le _)
    have hi := ih w _ (List.pairwise_cons.mp hsorted).2 (fun u hu => hbound u (by simp [hu])) hnext
    rw [SphincsSecurity.Completeness.allSegs_cons v, List.map_append, List.sum_append]
    simp only [sumTops, List.length_cons] at hc hi ⊢
    omega

end admissible

/-- **The schedule of admissible leaves**: `29` segments, each with at most `14` reads at positions
of the tree, and `octopusSize` reads in all. -/
theorem schedule_admissible (leaves : IndexGroup → FtsLeaf)
    (hadm : SphincsSecurity.Concrete.AdmissibleLeaves leaves) :
    (SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).length = 29 ∧
    (∀ s ∈ SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves),
      s.reads.length ≤ 14 ∧ ∀ p ∈ s.reads, p.1 < 14 ∧ p.2 < 2 ^ (14 - p.1)) ∧
    (((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map
        (·.reads)).flatten).length =
      SphincsSecurity.Concrete.octopusSize (SphincsSecurity.Concrete.sortedLeaves leaves) := by
  obtain ⟨hlen, hsorted, hbound⟩ := SphincsSecurity.Completeness.sortedLeaves_facts leaves hadm.1
  obtain ⟨v, rest, hvr⟩ : ∃ v rest, SphincsSecurity.Concrete.sortedLeaves leaves = v :: rest := by
    cases h : SphincsSecurity.Concrete.sortedLeaves leaves with
    | nil => rw [h] at hlen; simp [SphincsSecurity.ftsOpenings] at hlen
    | cons v rest => exact ⟨v, rest, rfl⟩
  rw [hvr] at hlen hsorted hbound ⊢
  have hrest : rest.length = 14 := by simp [SphincsSecurity.ftsOpenings] at hlen; omega
  have hsched : SphincsSecurity.Concrete.schedule (v :: rest) =
      SphincsSecurity.Completeness.allSegs (v :: rest) [] := by
    have := SphincsSecurity.Completeness.scheduleLeaves_eq rest v ⟨[], [], 0, false, []⟩ []
      hsorted hbound ⟨List.Pairwise.nil, by simp⟩ rfl
    rw [SphincsSecurity.Concrete.schedule, this.1, List.nil_append]
  rw [hsched]
  refine ⟨?_, allSegs_reads _ _ hbound, ?_⟩
  · rw [SphincsSecurity.Completeness.allSegs_length rest v [] hsorted hbound
      ⟨List.Pairwise.nil, by simp⟩, hrest]
    rfl
  · have ht := allSegs_total rest v [] hsorted hbound ⟨List.Pairwise.nil, by simp⟩
    have hsum := SphincsSecurity.Completeness.sumTops_add (v :: rest) (by simp) hsorted
    rw [List.length_flatten, List.map_map]
    rw [SphincsSecurity.Completeness.Octopus.octopusSize_eq]
    simp only [SphincsSecurity.Completeness.Octopus.octH, List.length_cons, List.length_nil] at ht hsum ⊢
    simp only [Function.comp_def]
    simp only [SphincsSecurity.ftsTreeHeight] at hsum
    omega

end SigGolfCandidate.Equiv
