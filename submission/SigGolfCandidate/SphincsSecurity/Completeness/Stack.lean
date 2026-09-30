import SigGolfCandidate.SphincsSecurity.Completeness.Uniform
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Eval
import Mathlib.Data.Nat.Bitwise

/-!
# The stack machine recovers the honest root

The PORS verifier (`Concrete.ftsRecover`, the stack machine of `ref.pors_root`) reads the sorted leaves
one by one. Each leaf climbs from its own position to the level just below where it meets the next leaf
(to the root for the last leaf); at every height it either folds with an authentication node or, when the
node on top of the stack waits for exactly the current node, merges with it. After the climb the node
reached is pushed with the heap index of its sibling. This file shows that for admissible leaves the
honest opening (`Concrete.honestFts`: the canonical `schedule`, the tree's nodes at its read positions)
makes the machine accept and return the root, under every answer function.

The argument is in two halves.

* **The schedule** (`scheduleLeaves`, pure). Before the leaf `v`, the stack holds the ancestors of `v`
  at a strictly increasing list `L` of heights, each a right child (`v`'s bit at that height is `1`):
  these are the right children of the meeting points of earlier leaves whose left child waits. The
  leaf's climb merges exactly at the heights of `L` below its top and folds everywhere else
  (`climb_eq`); its segments are `climbSegs`. The heights of `L` above the top stay, the top itself is
  never in `L` (`v`'s bit there is `0`), and the pushed sibling is the next leaf's ancestor at the top,
  so the invariant passes to the next leaf (`scheduleLeaves_eq`). The last leaf climbs to the root and
  pops everything.
* **The verifier** (under `evalWithAnswerFn f`). Along one climb the current node is the tree's node at
  the leaf's ancestor, the stack's digests are the waiting left children, and each fold and merge hashes
  the tree's own payload (`eval_foldSegment`, `eval_recoverSegments`, `eval_recoverLeaves`). The folds
  count the heights climbed minus the merges, which adds up to the octopus size.
-/

open OracleComp

namespace SphincsSecurity.Completeness

open Concrete

/-! ## Bits of leaf indices -/

/-- The heap index of the ancestor of leaf `v` at height `x`. -/
def anc (v x : Nat) : Nat := 2 ^ (ftsTreeHeight - x) + v / 2 ^ x

/-- The position `(height, index)` of the sibling of `v`'s ancestor at height `x`. -/
def sibPos (v x : Nat) : Nat × Nat := (x, (v / 2 ^ x) ^^^ 1)

/-- The sibling positions of `v`'s ancestors at the heights `x, ..., x + n - 1`. -/
def sibs (v x n : Nat) : List (Nat × Nat) := (List.range' x n).map (sibPos v)

theorem div_two_pow_lt {v : Nat} (hv : v < 2 ^ ftsTreeHeight) {x : Nat} (hx : x ≤ ftsTreeHeight) :
    v / 2 ^ x < 2 ^ (ftsTreeHeight - x) := by
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add, Nat.sub_add_cancel hx]
  exact hv

theorem div_two_pow_succ (v x : Nat) : v / 2 ^ (x + 1) = v / 2 ^ x / 2 := by
  rw [pow_succ, Nat.div_div_eq_div_mul]

theorem anc_div_two {v x : Nat} (hx : x < ftsTreeHeight) : anc v x / 2 = anc v (x + 1) := by
  unfold anc
  have hpow : 2 ^ (ftsTreeHeight - x) = 2 * 2 ^ (ftsTreeHeight - (x + 1)) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow, pow_succ, ← Nat.div_div_eq_div_mul]
  omega

theorem anc_mod_two {v x : Nat} (hx : x < ftsTreeHeight) : anc v x % 2 = v / 2 ^ x % 2 := by
  unfold anc
  have hpow : 2 ^ (ftsTreeHeight - x) = 2 * 2 ^ (ftsTreeHeight - (x + 1)) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow, Nat.add_comm, Nat.add_mul_mod_self_left]

theorem xor_one_eq (n : Nat) : n ^^^ 1 = if n % 2 = 0 then n + 1 else n - 1 := by
  split
  · exact Nat.xor_one_of_even (Nat.even_iff.mpr (by assumption))
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr (by omega))]

theorem anc_xor_one {v x : Nat} (hx : x < ftsTreeHeight) :
    anc v x ^^^ 1 = 2 ^ (ftsTreeHeight - x) + (v / 2 ^ x ^^^ 1) := by
  have hmod := anc_mod_two (v := v) hx
  rw [xor_one_eq, xor_one_eq, hmod]
  unfold anc at hmod ⊢
  have hpow : 2 ^ (ftsTreeHeight - x) = 2 * 2 ^ (ftsTreeHeight - (x + 1)) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow] at hmod ⊢
  generalize v / 2 ^ x = q at *
  generalize 2 ^ (ftsTreeHeight - (x + 1)) = A at *
  split_ifs <;> omega

theorem anc_xor_one_sub {v x : Nat} (hx : x < ftsTreeHeight) :
    (anc v x ^^^ 1) - 2 ^ (ftsTreeHeight - x) = v / 2 ^ x ^^^ 1 := by
  rw [anc_xor_one hx]; omega

theorem anc_lt {v : Nat} (hv : v < 2 ^ ftsTreeHeight) {x : Nat} (hx : x ≤ ftsTreeHeight) :
    anc v x < 2 ^ (ftsTreeHeight - x + 1) := by
  have := div_two_pow_lt hv hx
  unfold anc
  rw [pow_succ]
  omega

theorem anc_ge (v x : Nat) : 2 ^ (ftsTreeHeight - x) ≤ anc v x :=
  Nat.le_add_right _ _

/-- Ancestors at different heights have different heap indices. -/
theorem anc_injective {v : Nat} (hv : v < 2 ^ ftsTreeHeight) {x y : Nat} (hx : x ≤ ftsTreeHeight)
    (hy : y ≤ ftsTreeHeight) (h : anc v x = anc v y) : x = y := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := anc_ge v x
    have h2 := anc_lt hv hy
    have h3 : 2 ^ (ftsTreeHeight - y + 1) ≤ 2 ^ (ftsTreeHeight - x) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have h1 := anc_ge v y
    have h2 := anc_lt hv hx
    have h3 : 2 ^ (ftsTreeHeight - x + 1) ≤ 2 ^ (ftsTreeHeight - y) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem anc_zero {v : Nat} (hv : v < 2 ^ ftsTreeHeight) : anc v 0 = 2 ^ ftsTreeHeight ||| v := by
  unfold anc
  rw [Nat.pow_zero, Nat.div_one, Nat.sub_zero]
  have := Nat.two_pow_add_eq_or_of_lt hv 1
  rw [Nat.mul_one] at this
  exact this

theorem anc_top {v : Nat} (hv : v < 2 ^ ftsTreeHeight) : anc v ftsTreeHeight = 1 := by
  unfold anc
  rw [Nat.sub_self, Nat.pow_zero, Nat.div_eq_of_lt hv]

/-- The height where two leaves meet, minus one: the top of the first one's climb. -/
theorem bitLength_xor_pos {v w : Nat} (hne : v ≠ w) : 1 ≤ bitLength (v ^^^ w) := by
  unfold bitLength
  split
  · exact absurd (Nat.xor_eq_zero_iff.mp (by assumption)) hne
  · omega

theorem xor_lt_two_pow_bitLength (n : Nat) : n < 2 ^ bitLength n := by
  unfold bitLength
  split
  · subst n; simp
  · exact (Nat.log2_lt (by assumption)).mp (Nat.lt_succ_self _)

theorem bitLength_le {n k : Nat} (h : n < 2 ^ k) : bitLength n ≤ k := by
  unfold bitLength
  split
  · omega
  · have := (Nat.log2_lt (n := n) (k := k) (by assumption)).mpr h
    omega

/-- Two leaves agree above the height where they meet. -/
theorem div_eq_of_bitLength_le {v w y : Nat} (hy : bitLength (v ^^^ w) ≤ y) :
    v / 2 ^ y = w / 2 ^ y := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow]
  have hlt : v ^^^ w < 2 ^ (i + y) :=
    lt_of_lt_of_le (xor_lt_two_pow_bitLength _) (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hbit := Nat.testBit_lt_two_pow hlt
  rw [Nat.testBit_xor] at hbit
  cases hv : v.testBit (i + y) <;> cases hw : w.testBit (i + y) <;> simp_all

/-- Where `v < w` meet, `v` goes left and `w` right. -/
theorem bits_at_meet {v w : Nat} (hlt : v < w) :
    v / 2 ^ (bitLength (v ^^^ w) - 1) % 2 = 0 ∧ w / 2 ^ (bitLength (v ^^^ w) - 1) % 2 = 1 := by
  have hne : v ^^^ w ≠ 0 := fun h => by rw [Nat.xor_eq_zero_iff] at h; omega
  have htop : bitLength (v ^^^ w) - 1 = (v ^^^ w).log2 := by
    unfold bitLength; rw [if_neg hne]; omega
  have hbit := Nat.testBit_log2 hne
  rw [← htop, Nat.testBit_xor] at hbit
  have habove : ∀ j, bitLength (v ^^^ w) - 1 < j → v.testBit j = w.testBit j := by
    intro j hj
    rw [Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq,
      div_eq_of_bitLength_le (v := v) (w := w) (y := j) (by omega)]
  have hv : v.testBit (bitLength (v ^^^ w) - 1) = false := by
    by_contra hv
    have hv' : v.testBit (bitLength (v ^^^ w) - 1) = true := by simpa using hv
    have hw : w.testBit (bitLength (v ^^^ w) - 1) = false := by
      rw [hv'] at hbit; simpa using hbit
    have := Nat.lt_of_testBit _ hw hv' (fun j hj => (habove j hj).symm)
    omega
  have hw : w.testBit (bitLength (v ^^^ w) - 1) = true := by
    rw [hv] at hbit; simpa using hbit
  rw [Nat.testBit_eq_decide_div_mod_eq] at hv hw
  simp only [decide_eq_false_iff_not, decide_eq_true_eq] at hv hw
  omega

/-! ## The schedule, climb by climb -/

theorem scheduleStep_fold (state : ScheduleState) (height : Nat)
    (hne : state.stack.head? ≠ some state.heap) :
    scheduleStep state height =
      { state with reads := state.reads ++ [(height, (state.heap ^^^ 1) - 2 ^ (ftsTreeHeight - height))],
                   heap := state.heap / 2 } := by
  unfold scheduleStep
  cases hstack : state.stack with
  | nil => rfl
  | cons top rest =>
      rw [hstack] at hne
      simp only [List.head?_cons, ne_eq, Option.some.injEq] at hne
      simp [hne]

theorem scheduleStep_merge (state : ScheduleState) (height : Nat) (rest : List Nat)
    (hstack : state.stack = state.heap :: rest) :
    scheduleStep state height =
      { state with done := state.done ++ [⟨true, state.parity, state.reads⟩], stack := rest,
                   heap := state.heap / 2, parity := decide (state.heap / 2 % 2 = 1), reads := [] } := by
  unfold scheduleStep
  rw [hstack]
  simp

/-- Folding through `n` heights where no merge is due. -/
theorem foldl_scheduleStep_folds {v : Nat} :
    ∀ (n x : Nat) (state : ScheduleState), state.heap = anc v x → x + n ≤ ftsTreeHeight →
      (∀ y, x ≤ y → y < x + n → state.stack.head? ≠ some (anc v y)) →
      (List.range' x n).foldl scheduleStep state =
        { state with reads := state.reads ++ sibs v x n, heap := anc v (x + n) } := by
  intro n
  induction n with
  | zero =>
      intro x state hheap _ _
      rcases state with ⟨done, stack, heap, parity, reads⟩
      simp only at hheap
      subst hheap
      simp [sibs]
  | succ n ih =>
      intro x state hheap hbound hnomerge
      rw [List.range'_succ, List.foldl_cons,
        scheduleStep_fold state x (by rw [hheap]; exact hnomerge x le_rfl (by omega))]
      rcases state with ⟨done, stack, heap, parity, reads⟩
      simp only at hheap hnomerge
      subst hheap
      rw [ih (x + 1) ⟨done, stack, anc v x / 2, parity,
          reads ++ [(x, (anc v x ^^^ 1) - 2 ^ (ftsTreeHeight - x))]⟩
        (anc_div_two (by omega)) (by omega) (fun y hy1 hy2 => hnomerge y (by omega) (by omega))]
      simp only [sibs, List.range'_succ, List.map_cons, List.append_assoc, List.singleton_append,
        anc_xor_one_sub (show x < ftsTreeHeight by omega), sibPos,
        show x + 1 + n = x + (n + 1) by omega]

/-- The segments of one climb from a segment start at height `x`: a fold run up to each merge height
of `L`, then a fold run up to `top`, ending the leaf. -/
def climbSegs (v : Nat) : Nat → List Nat → Nat → List ScheduleSegment
  | x, [], top => [⟨false, decide (anc v x % 2 = 1), sibs v x (top - x)⟩]
  | x, y :: L, top => ⟨true, decide (anc v x % 2 = 1), sibs v x (y - x)⟩ :: climbSegs v (y + 1) L top

theorem length_le_of_pairwise {L : List Nat} (hsorted : L.Pairwise (· < ·)) :
    ∀ {a b : Nat}, (∀ y ∈ L, a ≤ y ∧ y < b) → L.length ≤ b - a := by
  induction L with
  | nil => intros; simp
  | cons z L ih =>
      intro a b hrange
      have hz := hrange z (by simp)
      have hrest := ih (List.pairwise_cons.mp hsorted).2 (a := z + 1) (b := b) (fun y hy =>
        ⟨(List.pairwise_cons.mp hsorted).1 y hy, (hrange y (by simp [hy])).2⟩)
      simp only [List.length_cons]
      omega

/-- **One climb of the schedule.** From a segment start at height `x`, with the stack holding `v`'s
ancestors at the merge heights `L` (all in `[x, top)`) above `rest` (whose top is not on the climb), the
climb emits `climbSegs` and leaves `rest` with the node at `v`'s ancestor at `top`. -/
theorem climb_eq {v : Nat} (hv : v < 2 ^ ftsTreeHeight) {top : Nat} (htop : top ≤ ftsTreeHeight)
    (rest : List Nat) :
    ∀ (L : List Nat) (x : Nat) (state : ScheduleState), L.Pairwise (· < ·) →
      (∀ y ∈ L, x ≤ y ∧ y < top) → x ≤ top →
      (∀ q ∈ rest.head?, ∀ y, x ≤ y → y < top → q ≠ anc v y) →
      state.heap = anc v x → state.reads = [] → state.parity = decide (anc v x % 2 = 1) →
      state.stack = L.map (anc v) ++ rest →
      let final := (List.range' x (top - x)).foldl scheduleStep state
      final.done ++ [⟨false, final.parity, final.reads⟩] = state.done ++ climbSegs v x L top
        ∧ final.stack = rest ∧ final.heap = anc v top := by
  intro L
  induction L with
  | nil =>
      intro x state _ _ hx hrest hheap hreads hparity hstack
      simp only [List.map_nil, List.nil_append] at hstack
      rw [foldl_scheduleStep_folds (top - x) x state hheap (by omega) (fun y hy1 hy2 => by
        rw [hstack]
        cases hr : rest.head? with
        | none => simp
        | some q =>
            have := hrest q (by simp [hr]) y hy1 (by omega)
            simp [this])]
      simp [climbSegs, hreads, hparity, hstack, show x + (top - x) = top by omega]
  | cons y L ih =>
      intro x state hsorted hrange hx hrest hheap hreads hparity hstack
      have hy := hrange y (by simp)
      have hL := (List.pairwise_cons.mp hsorted)
      have hsplit : List.range' x (top - x)
          = List.range' x (y - x) ++ y :: List.range' (y + 1) (top - (y + 1)) := by
        have h1 : top - x = (y - x) + (top - y) := by omega
        have h2 : top - y = (top - (y + 1)) + 1 := by omega
        rw [h1, ← List.range'_append_1, h2, List.range'_succ, show x + (y - x) = y by omega]
      rcases state with ⟨done, stack, heap, parity, reads⟩
      simp only at hheap hreads hparity hstack
      subst hheap hreads hparity hstack
      let st2 : ScheduleState := ⟨done ++ [⟨true, decide (anc v x % 2 = 1), sibs v x (y - x)⟩],
        L.map (anc v) ++ rest, anc v (y + 1), decide (anc v (y + 1) % 2 = 1), []⟩
      have hstep : scheduleStep ((List.range' x (y - x)).foldl scheduleStep
          ⟨done, (y :: L).map (anc v) ++ rest, anc v x, decide (anc v x % 2 = 1), []⟩) y = st2 := by
        rw [foldl_scheduleStep_folds (y - x) x _ rfl (by omega) (fun z hz1 hz2 => by
          simp only [List.map_cons, List.cons_append, List.head?_cons, ne_eq, Option.some.injEq]
          intro heq
          have := anc_injective hv (by omega) (by omega) heq
          omega)]
        rw [scheduleStep_merge _ y (L.map (anc v) ++ rest)
          (by simp [show x + (y - x) = y by omega])]
        simp [st2, show x + (y - x) = y by omega, anc_div_two (show y < ftsTreeHeight by omega)]
      simp only
      rw [hsplit, List.foldl_append, List.foldl_cons, hstep]
      have := ih (y + 1) st2 hL.2 (fun z hz => ⟨hL.1 z hz, (hrange z (by simp [hz])).2⟩) (by omega)
        (fun q hq z hz1 hz2 => hrest q hq z (by omega) hz2) rfl rfl rfl rfl
      simp only at this
      refine ⟨?_, this.2⟩
      rw [this.1]
      simp [st2, climbSegs]

/-! ## The schedule, leaf by leaf -/

/-- The top of a leaf's climb: one below the height where it meets the next leaf, or the root for the
last leaf (`scheduleLeaves`'s `top`). -/
def leafTop (v : Nat) (rest : List Nat) : Nat :=
  match rest with
  | [] => ftsTreeHeight
  | w :: _ => bitLength (v ^^^ w) - 1

/-- What the stack holds before leaf `v`: `v`'s ancestors at strictly increasing heights below the root,
each a right child. -/
def Pending (v : Nat) (L : List Nat) : Prop :=
  L.Pairwise (· < ·) ∧ ∀ y ∈ L, y < ftsTreeHeight ∧ v / 2 ^ y % 2 = 1

/-- The segments of the leaves `ws` from the stack heights `L` on: each leaf's climb merges at the
heights below its top, and the heights above it wait, under the pushed sibling, for the next leaf. -/
def allSegs : List Nat → List Nat → List ScheduleSegment
  | [], _ => []
  | v :: rest, L =>
      climbSegs v 0 (L.filter (· < leafTop v rest)) (leafTop v rest)
        ++ allSegs rest (leafTop v rest :: L.filter (leafTop v rest < ·))

/-- The sum of the climbs. -/
def sumTops : List Nat → Nat
  | [] => 0
  | v :: rest => leafTop v rest + sumTops rest

theorem split_filter {t : Nat} : ∀ {L : List Nat}, L.Pairwise (· < ·) → (∀ y ∈ L, y ≠ t) →
    L = L.filter (· < t) ++ L.filter (t < ·)
  | [], _, _ => rfl
  | a :: l, hsorted, hne => by
      have hl := List.pairwise_cons.mp hsorted
      have ih := split_filter hl.2 (fun y hy => hne y (by simp [hy]))
      have ha := hne a (by simp)
      by_cases hat : a < t
      · simp only [List.filter_cons, show decide (a < t) = true by simpa using hat,
          show decide (t < a) = false by simp; omega, if_true, Bool.false_eq_true, if_false,
          List.cons_append]
        exact congrArg (a :: ·) ih
      · have hta : t < a := by omega
        have hlo : l.filter (· < t) = [] := List.filter_eq_nil_iff.mpr (fun y hy => by
          have := hl.1 y hy; simp; omega)
        have hhi : l.filter (t < ·) = l := List.filter_eq_self.mpr (fun y hy => by
          have := hl.1 y hy; simp; omega)
        simp [List.filter_cons, hat, hta, hlo, hhi]

theorem mem_filter_lt {L : List Nat} {t y : Nat} (hy : y ∈ L.filter (· < t)) : y ∈ L ∧ y < t := by
  simpa using hy

theorem mem_filter_gt {L : List Nat} {t y : Nat} (hy : y ∈ L.filter (t < ·)) : y ∈ L ∧ t < y := by
  simpa using hy

theorem filter_gt_nil {L : List Nat} {t : Nat} (h : ∀ y ∈ L, y < t) : L.filter (t < ·) = [] :=
  List.filter_eq_nil_iff.mpr (fun y hy => by have := h y hy; simp; omega)

theorem filter_lt_length_le {L : List Nat} (hL : L.Pairwise (· < ·)) (t : Nat) :
    (L.filter (· < t)).length ≤ t := by
  have := length_le_of_pairwise (hL.filter _) (a := 0) (b := t) (fun y hy =>
    ⟨Nat.zero_le _, (mem_filter_lt hy).2⟩)
  omega

/-- Where two consecutive leaves meet: `t` is the top of the first one's climb. -/
theorem meet_facts {v w t : Nat} (hlt : v < w) (hw : w < 2 ^ ftsTreeHeight)
    (ht : t = bitLength (v ^^^ w) - 1) :
    t < ftsTreeHeight ∧ v / 2 ^ t % 2 = 0 ∧ w / 2 ^ t % 2 = 1 ∧ (v / 2 ^ t ^^^ 1) = w / 2 ^ t
      ∧ ∀ y, t < y → v / 2 ^ y = w / 2 ^ y := by
  have hpos := bitLength_xor_pos (show v ≠ w by omega)
  have hle : bitLength (v ^^^ w) ≤ ftsTreeHeight :=
    bitLength_le (Nat.xor_lt_two_pow (by omega) hw)
  obtain ⟨hv0, hw1⟩ := bits_at_meet hlt
  rw [← ht] at hv0 hw1
  have habove : ∀ y, t < y → v / 2 ^ y = w / 2 ^ y := fun y hy =>
    div_eq_of_bitLength_le (by omega)
  have hsucc := habove (t + 1) (by omega)
  rw [div_two_pow_succ, div_two_pow_succ] at hsucc
  refine ⟨by omega, hv0, hw1, ?_, habove⟩
  rw [Nat.xor_one_of_even (Nat.even_iff.mpr hv0)]
  generalize v / 2 ^ t = a at *
  generalize w / 2 ^ t = b at *
  omega

theorem anc_eq_of_div_eq {v w y : Nat} (h : v / 2 ^ y = w / 2 ^ y) : anc v y = anc w y := by
  unfold anc; rw [h]

/-- The pushed sibling and the heights above the top wait for the next leaf. -/
theorem pending_next {v w t : Nat} (hlt : v < w) (hw : w < 2 ^ ftsTreeHeight)
    (ht : t = bitLength (v ^^^ w) - 1) {L : List Nat} (hL : Pending v L) :
    Pending w (t :: L.filter (t < ·))
      ∧ anc v t ^^^ 1 = anc w t
      ∧ (L.filter (t < ·)).map (anc v) = (L.filter (t < ·)).map (anc w) := by
  obtain ⟨htl, _, hw1, hxor, habove⟩ := meet_facts hlt hw ht
  refine ⟨⟨List.pairwise_cons.mpr ⟨fun y hy => by simp at hy; exact hy.2, hL.1.filter _⟩, ?_⟩,
    ?_, ?_⟩
  · intro y hy
    simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hy
    rcases hy with rfl | ⟨hy, hty⟩
    · exact ⟨htl, hw1⟩
    · exact ⟨(hL.2 y hy).1, by rw [← habove y hty]; exact (hL.2 y hy).2⟩
  · rw [anc_xor_one htl, hxor]; rfl
  · refine List.map_congr_left fun y hy => ?_
    simp only [List.mem_filter, decide_eq_true_eq] at hy
    exact anc_eq_of_div_eq (habove y hy.2)

/-- The stack before a leaf splits at the leaf's top: the heights below it are merged on the climb, the
ones above it wait (the top itself is not pending: the leaf's bit there is `0`). -/
theorem pending_split {v : Nat} {rest : List Nat} {L : List Nat} (hL : Pending v L)
    (hsorted : (v :: rest).Pairwise (· < ·)) (hbound : ∀ w ∈ v :: rest, w < 2 ^ ftsTreeHeight) :
    L = L.filter (· < leafTop v rest) ++ L.filter (leafTop v rest < ·) := by
  refine split_filter hL.1 (fun y hy heq => ?_)
  cases rest with
  | nil => have := (hL.2 y hy).1; simp [leafTop] at heq; omega
  | cons w rest =>
      obtain ⟨_, hv0, _, _, _⟩ := meet_facts ((List.pairwise_cons.mp hsorted).1 w (by simp))
        (hbound w (by simp)) rfl
      have := (hL.2 y hy).2
      simp only [leafTop] at heq
      rw [heq] at this
      omega

/-- One leaf of the schedule, in closed form: its climb, then the push. -/
theorem scheduleLeaves_cons (v : Nat) (rest : List Nat) (state : ScheduleState) :
    scheduleLeaves (v :: rest) state =
      let climbed := (List.range' 0 (leafTop v rest)).foldl scheduleStep
        ⟨state.done, state.stack, 2 ^ ftsTreeHeight ||| v,
          decide ((2 ^ ftsTreeHeight ||| v) % 2 = 1), []⟩
      scheduleLeaves rest (match rest with
        | [] => ⟨climbed.done ++ [⟨false, climbed.parity, climbed.reads⟩], climbed.stack, climbed.heap,
            climbed.parity, climbed.reads⟩
        | _ :: _ => ⟨climbed.done ++ [⟨false, climbed.parity, climbed.reads⟩],
            (climbed.heap ^^^ 1) :: climbed.stack, climbed.heap, climbed.parity, climbed.reads⟩) := by
  simp only [scheduleLeaves, leafTop, List.range_eq_range']
  cases rest <;> rfl

theorem allSegs_cons (v : Nat) (rest L : List Nat) :
    allSegs (v :: rest) L = climbSegs v 0 (L.filter (· < leafTop v rest)) (leafTop v rest)
        ++ allSegs rest (leafTop v rest :: L.filter (leafTop v rest < ·)) := rfl

/-- **The whole schedule.** From the stack of pending heights `L` before the leaf `v`, the leaves
`v :: rest` emit `allSegs` and leave the stack empty. -/
theorem scheduleLeaves_eq :
    ∀ (rest : List Nat) (v : Nat) (state : ScheduleState) (L : List Nat),
      (v :: rest).Pairwise (· < ·) → (∀ w ∈ v :: rest, w < 2 ^ ftsTreeHeight) → Pending v L →
      state.stack = L.map (anc v) →
      (scheduleLeaves (v :: rest) state).done = state.done ++ allSegs (v :: rest) L
        ∧ (scheduleLeaves (v :: rest) state).stack = [] := by
  intro rest
  induction rest with
  | nil =>
      intro v state L hsorted hbound hL hstack
      have hv := hbound v (by simp)
      have hsplit := pending_split hL hsorted hbound
      have hnone : L.filter (leafTop v [] < ·) = [] :=
        filter_gt_nil (fun y hy => (hL.2 y hy).1)
      have hclimb := climb_eq hv (le_refl ftsTreeHeight) [] (L.filter (· < leafTop v [])) 0
        ⟨state.done, state.stack, 2 ^ ftsTreeHeight ||| v,
          decide ((2 ^ ftsTreeHeight ||| v) % 2 = 1), []⟩
        (hL.1.filter _) (fun y hy => ⟨Nat.zero_le _, (mem_filter_lt hy).2⟩)
        (Nat.zero_le _) (by simp) (anc_zero hv).symm rfl (by rw [anc_zero hv])
        (by simp only; rw [hstack, List.append_nil]; conv_lhs => rw [hsplit]
            rw [hnone, List.append_nil])
      rw [scheduleLeaves_cons]
      simp only [Nat.sub_zero] at hclimb
      simp only [scheduleLeaves]
      rw [allSegs_cons, show allSegs [] _ = [] from rfl, List.append_nil]
      exact ⟨hclimb.1, hclimb.2.1⟩
  | cons w rest ih =>
      intro v state L hsorted hbound hL hstack
      have hv := hbound v (by simp)
      have hw := hbound w (by simp)
      have hvw : v < w := (List.pairwise_cons.mp hsorted).1 w (by simp)
      have htop : leafTop v (w :: rest) = bitLength (v ^^^ w) - 1 := rfl
      obtain ⟨hnext, hpush, hmap⟩ := pending_next hvw hw htop hL
      obtain ⟨ht, _, _, _, _⟩ := meet_facts hvw hw htop
      have hsplit := pending_split hL hsorted hbound
      have hclimb := climb_eq hv ht.le ((L.filter (leafTop v (w :: rest) < ·)).map (anc v))
        (L.filter (· < leafTop v (w :: rest))) 0
        ⟨state.done, state.stack, 2 ^ ftsTreeHeight ||| v,
          decide ((2 ^ ftsTreeHeight ||| v) % 2 = 1), []⟩
        (hL.1.filter _) (fun y hy => ⟨Nat.zero_le _, (mem_filter_lt hy).2⟩)
        (Nat.zero_le _)
        (by
          intro q hq y _ hy
          cases hL' : L.filter (leafTop v (w :: rest) < ·) with
          | nil => simp [hL'] at hq
          | cons z zs =>
              simp only [hL', List.map_cons, List.head?_cons, Option.mem_def,
                Option.some.injEq] at hq
              subst hq
              have hz : z ∈ L.filter (leafTop v (w :: rest) < ·) := by rw [hL']; simp
              simp only [List.mem_filter, decide_eq_true_eq] at hz
              intro heq
              have := anc_injective hv (hL.2 z hz.1).1.le (by omega) heq
              omega)
        (anc_zero hv).symm rfl (by rw [anc_zero hv])
        (by simp only; rw [hstack, ← List.map_append, ← hsplit])
      simp only [Nat.sub_zero] at hclimb
      rw [scheduleLeaves_cons]
      generalize hF : List.foldl scheduleStep
        ⟨state.done, state.stack, 2 ^ ftsTreeHeight ||| v,
          decide ((2 ^ ftsTreeHeight ||| v) % 2 = 1), []⟩
        (List.range' 0 (leafTop v (w :: rest))) = F at hclimb ⊢
      obtain ⟨hdone, hst, hheap⟩ := hclimb
      simp only
      have := ih w ⟨F.done ++ [⟨false, F.parity, F.reads⟩], (F.heap ^^^ 1) :: F.stack, F.heap,
          F.parity, F.reads⟩ (leafTop v (w :: rest) :: L.filter (leafTop v (w :: rest) < ·))
        (List.pairwise_cons.mp hsorted).2 (fun u hu => hbound u (by simp [hu])) hnext (by
          simp only [List.map_cons]; rw [hst, hheap, hpush, hmap])
      rw [this.1]
      refine ⟨?_, this.2⟩
      rw [allSegs_cons v, ← List.append_assoc, ← hdone]

theorem climbSegs_length (v top : Nat) : ∀ (L : List Nat) (x : Nat),
    (climbSegs v x L top).length = L.length + 1
  | [], _ => rfl
  | _ :: L, _ => by simp [climbSegs, climbSegs_length v top L]

theorem allSegs_length :
    ∀ (rest : List Nat) (v : Nat) (L : List Nat),
      (v :: rest).Pairwise (· < ·) → (∀ w ∈ v :: rest, w < 2 ^ ftsTreeHeight) → Pending v L →
      (allSegs (v :: rest) L).length = L.length + 2 * rest.length + 1 := by
  intro rest
  induction rest with
  | nil =>
      intro v L hsorted hbound hL
      have hsplit := pending_split hL hsorted hbound
      have hnone : L.filter (leafTop v [] < ·) = [] :=
        filter_gt_nil (fun y hy => (hL.2 y hy).1)
      have hlen := congrArg List.length hsplit
      rw [hnone, List.append_nil] at hlen
      rw [allSegs_cons, show allSegs [] _ = [] from rfl, List.append_nil, climbSegs_length]
      simp only [List.length_nil]
      omega
  | cons w rest ih =>
      intro v L hsorted hbound hL
      have hw := hbound w (by simp)
      have hvw : v < w := (List.pairwise_cons.mp hsorted).1 w (by simp)
      obtain ⟨hnext, _, _⟩ := pending_next hvw hw (rfl : leafTop v (w :: rest) = _) hL
      have hsplit := pending_split hL hsorted hbound
      have hlen := congrArg List.length hsplit
      rw [List.length_append] at hlen
      rw [allSegs_cons v, List.length_append, climbSegs_length]
      rw [ih w _ (List.pairwise_cons.mp hsorted).2 (fun u hu => hbound u (by simp [hu])) hnext]
      simp only [List.length_cons]
      omega

/-! ## The verifier, under an answer function -/

section Verifier

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)

/-- A table of the PORS tree's nodes: every inner node `(x + 1, k)` is the hash of its children under
its heap index. -/
def HonestTable (node : Nat → Nat → Digest) : Prop :=
  ∀ x k, x < ftsTreeHeight → k < 2 ^ (ftsTreeHeight - (x + 1)) →
    node (x + 1) k = evalWithAnswerFn f (tweakableHash parameter
      (.ftsNode index porsTree (ftsHeapIndex (x + 1) k))
      (nodePayload (node x (2 * k)) (node x (2 * k + 1))) : OracleComp HashSpec Digest)

/-- The honest segments of a schedule, the table's nodes at their read positions (as in `honestFts`). -/
def honestSegments (node : Nat → Nat → Digest) (segs : List ScheduleSegment) :
    Fin ftsSegments → Segment :=
  fun j =>
    let segment := segs.getD j.val default
    segment.toSegment fun i =>
      let position := segment.reads.getD i.val (0, 0)
      node position.1 position.2

/-- The verifier's stack before leaf `v`: the waiting left children at the heights `L`, each with the
heap index of the right child it waits for. -/
def vstack (node : Nat → Nat → Digest) (v : Nat) (L : List Nat) : List (Digest × Nat) :=
  L.map fun y => (node y (v / 2 ^ y ^^^ 1), anc v y)

/-- The hash a segment performs before its folds, as a computation. -/
def pendingComp (pending : PendingHash) (current : Digest) : OracleComp HashSpec Digest :=
  match pending with
  | .leaf value secret => ftsLeafHash parameter index porsTree value secret
  | .merge heapIdx left =>
      tweakableHash parameter (.ftsNode index porsTree heapIdx) (nodePayload left current)

theorem eval_recoverSegments_end (segments : Fin ftsSegments → Segment) (fuel : Nat)
    (pending : PendingHash) (state : RecoverState) (h : state.segment < ftsSegments)
    (hfolds : ¬ ftsTreeHeight < (segments ⟨state.segment, h⟩).folds.val)
    (hparity : ¬ ((segments ⟨state.segment, h⟩).folds.val ≠ 0 ∧
      (segments ⟨state.segment, h⟩).parity ≠ decide (state.heap % 2 = 1)))
    (hmerge : (segments ⟨state.segment, h⟩).merge = false) {node : Digest} {heap : Nat}
    (hfold : evalWithAnswerFn f (foldSegment parameter index (segments ⟨state.segment, h⟩)
      (segments ⟨state.segment, h⟩).folds.val 0
      (evalWithAnswerFn f (pendingComp parameter index pending state.node)) state.heap
        : OracleComp HashSpec (Digest × Nat)) = (node, heap)) :
    evalWithAnswerFn f (recoverSegments parameter index segments (fuel + 1) pending state
        : OracleComp HashSpec _)
      = some ⟨node, heap, state.stack, state.folds + (segments ⟨state.segment, h⟩).folds.val,
          state.segment + 1⟩ := by
  rw [recoverSegments, dif_pos h, if_neg hfolds, if_neg hparity]
  cases pending <;>
    simp only [pendingComp] at hfold <;>
    simp only [evalWithAnswerFn_bind, hfold, hmerge, Bool.false_eq_true, if_false,
      evalWithAnswerFn_pure]

theorem eval_recoverSegments_merge (segments : Fin ftsSegments → Segment) (fuel : Nat)
    (pending : PendingHash) (state : RecoverState) (h : state.segment < ftsSegments)
    (hfolds : ¬ ftsTreeHeight < (segments ⟨state.segment, h⟩).folds.val)
    (hparity : ¬ ((segments ⟨state.segment, h⟩).folds.val ≠ 0 ∧
      (segments ⟨state.segment, h⟩).parity ≠ decide (state.heap % 2 = 1)))
    (hmerge : (segments ⟨state.segment, h⟩).merge = true) {node left : Digest} {heap : Nat}
    {rest : List (Digest × Nat)} (hstack : state.stack = (left, heap) :: rest)
    (hfold : evalWithAnswerFn f (foldSegment parameter index (segments ⟨state.segment, h⟩)
      (segments ⟨state.segment, h⟩).folds.val 0
      (evalWithAnswerFn f (pendingComp parameter index pending state.node)) state.heap
        : OracleComp HashSpec (Digest × Nat)) = (node, heap)) :
    evalWithAnswerFn f (recoverSegments parameter index segments (fuel + 1) pending state
        : OracleComp HashSpec _)
      = evalWithAnswerFn f (recoverSegments parameter index segments fuel (.merge (heap / 2) left)
          ⟨node, heap / 2, rest, state.folds + (segments ⟨state.segment, h⟩).folds.val,
            state.segment + 1⟩ : OracleComp HashSpec _) := by
  rw [recoverSegments, dif_pos h, if_neg hfolds, if_neg hparity]
  cases pending <;>
    simp only [pendingComp] at hfold <;>
    simp only [evalWithAnswerFn_bind, hfold, hmerge, hstack, if_pos]

variable {f parameter index}

/-- One level of the climb: hashing `v`'s ancestor at height `y` with its sibling, in the order its
bit gives, under the parent's heap index, is the parent. -/
theorem eval_parent {node : Nat → Nat → Digest} (hT : HonestTable f parameter index node) {v : Nat}
    (hv : v < 2 ^ ftsTreeHeight) {y : Nat} (hy : y < ftsTreeHeight) :
    evalWithAnswerFn f (tweakableHash parameter (.ftsNode index porsTree (anc v y / 2))
        (foldPayload (decide (v / 2 ^ y % 2 = 1)) (node y (v / 2 ^ y ^^^ 1)) (node y (v / 2 ^ y)))
        : OracleComp HashSpec Digest)
      = node (y + 1) (v / 2 ^ (y + 1)) := by
  have hk : v / 2 ^ (y + 1) < 2 ^ (ftsTreeHeight - (y + 1)) := div_two_pow_lt hv (by omega)
  rw [hT y _ hy hk, anc_div_two hy]
  have hheap : anc v (y + 1) = ftsHeapIndex (y + 1) (v / 2 ^ (y + 1)) := rfl
  rw [hheap, div_two_pow_succ]
  congr 2
  rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ y) with h0 | h1
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr h0)]
    simp only [h0, zero_ne_one, decide_false, foldPayload, Bool.false_eq_true, if_false]
    congr 2 <;> omega
  · rw [Nat.xor_one_of_odd (Nat.odd_iff.mpr h1)]
    simp only [h1, decide_true, foldPayload, if_true]
    congr 2 <;> omega

/-- Folding `n` times from `v`'s ancestor at height `x` with the honest siblings reaches its ancestor at
height `x + n`. -/
theorem eval_foldSegment {node : Nat → Nat → Digest} (hT : HonestTable f parameter index node)
    {v : Nat} (hv : v < 2 ^ ftsTreeHeight) (segment : Segment) :
    ∀ (n pos x : Nat), x + n ≤ ftsTreeHeight →
      (∀ i, i < n → segment.node (pos + i) = node (x + i) (v / 2 ^ (x + i) ^^^ 1)) →
      (pos = 0 → 0 < n → segment.parity = decide (anc v x % 2 = 1)) →
      evalWithAnswerFn f (foldSegment parameter index segment n pos (node x (v / 2 ^ x)) (anc v x)
          : OracleComp HashSpec (Digest × Nat))
        = (node (x + n) (v / 2 ^ (x + n)), anc v (x + n)) := by
  intro n
  induction n with
  | zero => intro pos x _ _ _; simp [foldSegment]
  | succ n ih =>
      intro pos x hbound hnodes hparity
      have hx : x < ftsTreeHeight := by omega
      have hright : (if pos = 0 then segment.parity else decide (anc v x % 2 = 1))
          = decide (v / 2 ^ x % 2 = 1) := by
        split
        · rw [hparity (by assumption) (by omega), anc_mod_two hx]
        · rw [anc_mod_two hx]
      simp only [foldSegment, evalWithAnswerFn_bind]
      rw [hright, show segment.node pos = node x (v / 2 ^ x ^^^ 1) by
        simpa using hnodes 0 (by omega), eval_parent hT hv hx, anc_div_two hx]
      rw [ih (pos + 1) (x + 1) (by omega) (fun i hi => by
        rw [show pos + 1 + i = pos + (i + 1) by omega, show x + 1 + i = x + (i + 1) by omega]
        exact hnodes (i + 1) (by omega)) (fun h => by omega)]
      simp only [show x + 1 + n = x + (n + 1) by omega]

/-- The segment the verifier reads at a schedule segment of `v`'s climb: its folds, merge bit, parity
and nodes. -/
theorem honestSegments_at (node : Nat → Nat → Digest) (segs : List ScheduleSegment) {j : Nat}
    (hj : j < ftsSegments) {merge parity : Bool} {v x n : Nat} (hn : n ≤ ftsTreeHeight)
    (hget : segs.getD j default = ⟨merge, parity, sibs v x n⟩) :
    (honestSegments node segs ⟨j, hj⟩).folds.val = n
      ∧ (honestSegments node segs ⟨j, hj⟩).merge = merge
      ∧ (0 < n → (honestSegments node segs ⟨j, hj⟩).parity = parity)
      ∧ ∀ i, i < n → (honestSegments node segs ⟨j, hj⟩).node i = node (x + i) (v / 2 ^ (x + i) ^^^ 1) := by
  have hlen : (sibs v x n).length % 16 = n := by
    simp only [sibs, List.length_map, List.length_range']
    exact Nat.mod_eq_of_lt (by unfold ftsTreeHeight at hn; omega)
  have hseg : honestSegments node segs ⟨j, hj⟩
      = (⟨merge, parity, sibs v x n⟩ : ScheduleSegment).toSegment fun i =>
          node ((sibs v x n).getD i.val (0, 0)).1 ((sibs v x n).getD i.val (0, 0)).2 := by
    unfold honestSegments
    dsimp only
    rw [hget]
  have hfolds : (honestSegments node segs ⟨j, hj⟩).folds.val = n := by
    rw [hseg]; exact hlen
  refine ⟨hfolds, by rw [hseg]; rfl, fun hpos => ?_, fun i hi => ?_⟩
  · rw [hseg]
    simp only [ScheduleSegment.toSegment, Segment.normalized, ScheduleSegment.folds, hlen]
    simp [show n ≠ 0 by omega]
  · have hn16 : n % 16 = n := by unfold ftsTreeHeight at hn; omega
    rw [hseg]
    simp [Segment.node, ScheduleSegment.toSegment, Segment.normalized, ScheduleSegment.folds, hn16,
      hi, sibs, List.getD_eq_getElem?_getD, sibPos, Nat.not_le.mpr hi]

theorem getD_append_length {α : Type} (pre post : List α) (a d : α) :
    (pre ++ a :: post).getD pre.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_climb {v x top : Nat} {L : List Nat} (pre post : List ScheduleSegment) :
    (pre ++ climbSegs v x L top ++ post).getD pre.length default = (climbSegs v x L top).headD default := by
  cases L <;> simp only [climbSegs, List.append_assoc, List.cons_append, List.headD_cons] <;>
    exact getD_append_length _ _ _ _

/-- **One climb of the verifier.** From a segment start at `v`'s ancestor at height `x`, with the
waiting left children of `L` on the stack above `hi`, the honest segments of the climb take the verifier
to `v`'s ancestor at `top`, with `hi` left, after `top - x - |L|` folds. -/
theorem eval_recoverSegments_climb {node : Nat → Nat → Digest}
    (hT : HonestTable f parameter index node) {v : Nat} (hv : v < 2 ^ ftsTreeHeight) {top : Nat}
    (htop : top ≤ ftsTreeHeight) (segs : List ScheduleSegment) (hi : List (Digest × Nat)) :
    ∀ (L : List Nat) (x : Nat) (pre post : List ScheduleSegment) (fuel : Nat) (pending : PendingHash)
      (state : RecoverState),
      L.Pairwise (· < ·) → (∀ y ∈ L, x ≤ y ∧ y < top ∧ v / 2 ^ y % 2 = 1) → x ≤ top →
      (∀ e ∈ hi.head?, ∀ y, x ≤ y → y < top → e.2 ≠ anc v y) →
      segs = pre ++ climbSegs v x L top ++ post → pre.length + L.length + 1 ≤ ftsSegments →
      state.heap = anc v x → state.segment = pre.length → state.stack = vstack node v L ++ hi →
      evalWithAnswerFn f (pendingComp parameter index pending state.node) = node x (v / 2 ^ x) →
      L.length + 1 ≤ fuel →
      evalWithAnswerFn f (recoverSegments parameter index (honestSegments node segs) fuel pending state
          : OracleComp HashSpec _)
        = some ⟨node top (v / 2 ^ top), anc v top, hi, state.folds + (top - x - L.length),
            pre.length + L.length + 1⟩ := by
  intro L
  induction L with
  | nil =>
      intro x pre post fuel pending state _ _ hx _ hsegs hlen hheap hseg hstack hpend hfuel
      obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
      have hj : state.segment < ftsSegments := by simp at hlen; omega
      have hget : segs.getD state.segment default
          = ⟨false, decide (anc v x % 2 = 1), sibs v x (top - x)⟩ := by
        rw [hsegs, hseg, getD_climb]; rfl
      obtain ⟨hf, hm, hp, hn⟩ := honestSegments_at node segs hj (by omega) hget
      rw [eval_recoverSegments_end f parameter index _ fuel pending state hj (by rw [hf]; omega)
        (by rintro ⟨hne, hpne⟩; exact hpne (by rw [hheap]; exact hp (by rw [hf] at hne; omega))) hm
        (node := node top (v / 2 ^ top)) (heap := anc v top) (by
          rw [hf, hpend, hheap]
          have := eval_foldSegment hT hv (honestSegments node segs ⟨state.segment, hj⟩) (top - x) 0 x
            (by omega) (fun i hi => by rw [Nat.zero_add]; exact hn i hi)
            (fun _ hpos => hp hpos)
          simpa only [show x + (top - x) = top by omega] using this)]
      rw [hf, hstack, hseg]
      simp [vstack]
  | cons y L ih =>
      intro x pre post fuel pending state hsorted hrange hx hhi hsegs hlen hheap hseg hstack hpend hfuel
      simp only [List.length_cons] at hlen hfuel ⊢
      obtain ⟨fuel, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
      have hy := hrange y (by simp)
      have hL := List.pairwise_cons.mp hsorted
      have hLlen := length_le_of_pairwise hL.2 (a := y + 1) (b := top) (fun z hz =>
        ⟨hL.1 z hz, (hrange z (by simp [hz])).2.1⟩)
      have hj : state.segment < ftsSegments := by simp at hlen; omega
      have hget : segs.getD state.segment default
          = ⟨true, decide (anc v x % 2 = 1), sibs v x (y - x)⟩ := by
        rw [hsegs, hseg, getD_climb]; rfl
      obtain ⟨hf, hm, hp, hn⟩ := honestSegments_at node segs hj (by omega) hget
      rw [eval_recoverSegments_merge f parameter index _ fuel pending state hj (by rw [hf]; omega)
        (by rintro ⟨hne, hpne⟩; exact hpne (by rw [hheap]; exact hp (by rw [hf] at hne; omega))) hm
        (node := node y (v / 2 ^ y)) (heap := anc v y) (left := node y (v / 2 ^ y ^^^ 1))
        (rest := vstack node v L ++ hi) (by simp [hstack, vstack]) (by
          rw [hf, hpend, hheap]
          have := eval_foldSegment hT hv (honestSegments node segs ⟨state.segment, hj⟩) (y - x) 0 x
            (by omega) (fun i hi => by rw [Nat.zero_add]; exact hn i hi)
            (fun _ hpos => hp hpos)
          simpa only [show x + (y - x) = y by omega] using this)]
      have hyh : y < ftsTreeHeight := by omega
      rw [ih (y + 1) (pre ++ [⟨true, decide (anc v x % 2 = 1), sibs v x (y - x)⟩]) post fuel _ _
        hL.2 (fun z hz => ⟨hL.1 z hz, (hrange z (by simp [hz])).2⟩) (by omega)
        (fun e he z hz1 hz2 => hhi e he z (by omega) hz2)
        (by rw [hsegs]; simp [climbSegs])
        (by simp only [List.length_append, List.length_singleton]; omega) (anc_div_two hyh)
        (by simp [hseg]) rfl
        (by
          simp only [pendingComp]
          have := eval_parent hT hv hyh
          rw [show decide (v / 2 ^ y % 2 = 1) = true by simpa using hy.2.2] at this
          simpa [foldPayload] using this)
        (by omega)]
      simp only [hf, List.length_append, List.length_cons, List.length_nil, Option.some.injEq,
        RecoverState.mk.injEq, true_and]
      constructor <;> omega

theorem eval_recoverLeaves_step (values : SlotCode → Nat) (fts : FtsSignature)
    (remaining position previous : Nat) (state : RecoverState) (h : position < ftsOpenings)
    (hord : ¬ (0 < position ∧ ¬ previous < values (fts.perm ⟨position, h⟩)))
    (hlast : ¬ (position + 1 = ftsOpenings ∧ ¬ values (fts.perm ⟨position, h⟩) < 2 ^ ftsTreeHeight))
    {R : RecoverState}
    (hseg : evalWithAnswerFn f (recoverSegments parameter index fts.segments ftsSegments
      (.leaf (values (fts.perm ⟨position, h⟩)) (fts.secrets ⟨position, h⟩))
      { state with heap := 2 ^ ftsTreeHeight ||| values (fts.perm ⟨position, h⟩) }
        : OracleComp HashSpec _) = some R) :
    evalWithAnswerFn f (recoverLeaves parameter index values fts (remaining + 1) position previous state
        : OracleComp HashSpec _)
      = evalWithAnswerFn f (recoverLeaves parameter index values fts remaining (position + 1)
          (values (fts.perm ⟨position, h⟩))
          (if position + 1 < ftsOpenings then { R with stack := (R.node, R.heap ^^^ 1) :: R.stack } else R)
          : OracleComp HashSpec _) := by
  rw [recoverLeaves, dif_pos h, if_neg hord, if_neg hlast]
  simp only [evalWithAnswerFn_bind, hseg]

theorem sumTops_add : ∀ (l : List Nat), l ≠ [] → l.Pairwise (· < ·) →
    sumTops l + l.length = Octopus.xorSum l + ftsTreeHeight + 1
  | [], h, _ => absurd rfl h
  | [v], _, _ => by simp [sumTops, leafTop]
  | v :: w :: t, _, hsorted => by
      have hvw : v < w := (List.pairwise_cons.mp hsorted).1 w (by simp)
      have ih := sumTops_add (w :: t) (by simp) (List.pairwise_cons.mp hsorted).2
      have hpos := bitLength_xor_pos (show v ≠ w by omega)
      rw [Octopus.xorSum_cons_cons]
      simp only [sumTops, leafTop, List.length_cons] at ih ⊢
      omega

theorem vstack_split (node : Nat → Nat → Digest) {v t : Nat} {L : List Nat}
    (hsplit : L = L.filter (· < t) ++ L.filter (t < ·)) :
    vstack node v L = vstack node v (L.filter (· < t)) ++ vstack node v (L.filter (t < ·)) := by
  conv_lhs => rw [hsplit]
  simp only [vstack, List.map_append]

/-- One leaf's climb, from the leaf hash to the top of its climb. -/
theorem eval_leaf_climb {node : Nat → Nat → Digest} (hT : HonestTable f parameter index node)
    {v : Nat} {rest L : List Nat} (hsorted : (v :: rest).Pairwise (· < ·))
    (hbound : ∀ w ∈ v :: rest, w < 2 ^ ftsTreeHeight) (hL : Pending v L)
    (segs pre post : List ScheduleSegment) (hsegs : segs = pre ++ allSegs (v :: rest) L ++ post)
    (hlen : pre.length + (allSegs (v :: rest) L).length ≤ ftsSegments) (secret : Digest)
    (hleaf : evalWithAnswerFn f (ftsLeafHash parameter index porsTree v secret : OracleComp HashSpec Digest)
      = node 0 v)
    (state : RecoverState) (hseg : state.segment = pre.length) (hstack : state.stack = vstack node v L) :
    evalWithAnswerFn f (recoverSegments parameter index (honestSegments node segs) ftsSegments
        (.leaf v secret) { state with heap := 2 ^ ftsTreeHeight ||| v } : OracleComp HashSpec _)
      = some ⟨node (leafTop v rest) (v / 2 ^ leafTop v rest), anc v (leafTop v rest),
          vstack node v (L.filter (leafTop v rest < ·)),
          state.folds + (leafTop v rest - 0 - (L.filter (· < leafTop v rest)).length),
          pre.length + (L.filter (· < leafTop v rest)).length + 1⟩ := by
  have hS : ftsSegments = 29 := rfl
  have hH : ftsTreeHeight = 14 := rfl
  have hv := hbound v (by simp)
  have htop : leafTop v rest ≤ ftsTreeHeight := by
    cases rest with
    | nil => exact le_rfl
    | cons w rest =>
        exact (meet_facts ((List.pairwise_cons.mp hsorted).1 w (by simp)) (hbound w (by simp)) rfl).1.le
  have hsplit := pending_split hL hsorted hbound
  have hlo := filter_lt_length_le hL.1 (leafTop v rest)
  have hlen' := hlen
  rw [allSegs_cons, List.length_append, climbSegs_length] at hlen'
  refine eval_recoverSegments_climb hT hv htop segs _ _ 0 pre
    (allSegs rest (leafTop v rest :: L.filter (leafTop v rest < ·)) ++ post) ftsSegments _ _
    (hL.1.filter _) (fun y hy => ⟨Nat.zero_le _, (mem_filter_lt hy).2, (hL.2 y (mem_filter_lt hy).1).2⟩)
    (Nat.zero_le _) ?_ (by rw [hsegs, allSegs_cons]; simp only [List.append_assoc]) (by omega)
    (anc_zero hv).symm hseg (by simp only; rw [hstack]; exact vstack_split node hsplit)
    (by rw [pendingComp, hleaf, Nat.pow_zero, Nat.div_one]) (by omega)
  intro e he y _ hy
  cases hL' : L.filter (leafTop v rest < ·) with
  | nil => simp [vstack, hL'] at he
  | cons z zs =>
      simp only [vstack, hL', List.map_cons, List.head?_cons, Option.mem_def,
        Option.some.injEq] at he
      subst he
      have hz : z ∈ L.filter (leafTop v rest < ·) := by rw [hL']; simp
      have hz' := mem_filter_gt hz
      intro heq
      have := anc_injective hv (hL.2 z hz'.1).1.le (by omega) heq
      omega

/-- **All leaves.** From the leaf `v` (position `pos` of the sorted leaves) with the waiting left children
of `L` on the stack, the verifier runs the remaining leaves to the root with an empty stack; its folds add
up the climbs minus the merges. -/
theorem eval_recoverLeaves_honest {node : Nat → Nat → Digest} (hT : HonestTable f parameter index node)
    (values : SlotCode → Nat) (fts : FtsSignature) (sorted : List Nat) (segs : List ScheduleSegment)
    (hsegs : fts.segments = honestSegments node segs)
    (hperm : ∀ i (h : i < ftsOpenings), values (fts.perm ⟨i, h⟩) = sorted.getD i 0)
    (hsec : ∀ i (h : i < ftsOpenings), evalWithAnswerFn f (ftsLeafHash parameter index porsTree
      (sorted.getD i 0) (fts.secrets ⟨i, h⟩) : OracleComp HashSpec Digest) = node 0 (sorted.getD i 0)) :
    ∀ (rest : List Nat) (v pos prev : Nat) (L : List Nat) (pre post : List ScheduleSegment)
      (state : RecoverState) (fuel : Nat), fuel = rest.length + 1 →
      sorted.drop pos = v :: rest → (v :: rest).Pairwise (· < ·) →
      (∀ w ∈ v :: rest, w < 2 ^ ftsTreeHeight) → pos + rest.length + 1 = ftsOpenings →
      (pos = 0 ∨ prev < v) → Pending v L → segs = pre ++ allSegs (v :: rest) L ++ post →
      pre.length + (allSegs (v :: rest) L).length ≤ ftsSegments →
      state.segment = pre.length → state.stack = vstack node v L →
      ∃ R, evalWithAnswerFn f (recoverLeaves parameter index values fts fuel pos prev state
          : OracleComp HashSpec _) = some R
        ∧ R.node = node ftsTreeHeight 0 ∧ R.heap = 1 ∧ R.stack = []
        ∧ R.folds + L.length + rest.length = state.folds + sumTops (v :: rest) := by
  have hO : ftsOpenings = 15 := rfl
  have hH : ftsTreeHeight = 14 := rfl
  intro rest
  induction rest with
  | nil =>
      intro v pos prev L pre post state fuel hfuel hdrop hsorted hbound hpos hprev hL hsegs' hlen hseg hstack
      subst hfuel
      have hv := hbound v (by simp)
      have hvpos : sorted.getD pos 0 = v := by
        rw [List.getD_eq_getElem?_getD, ← List.head?_drop, hdrop]; rfl
      have hp : pos < ftsOpenings := by simp at hpos; omega
      have hsplit := pending_split hL hsorted hbound
      have hnone : L.filter (leafTop v [] < ·) = [] := filter_gt_nil (fun y hy => (hL.2 y hy).1)
      have hlens := congrArg List.length hsplit
      rw [List.length_append, hnone, List.length_nil] at hlens
      have hclimb := eval_leaf_climb hT hsorted hbound hL segs pre post hsegs' hlen
        (fts.secrets ⟨pos, hp⟩) (by rw [← hvpos, hsec pos hp]) state hseg hstack
      rw [← hsegs] at hclimb
      refine ⟨⟨node (leafTop v []) (v / 2 ^ leafTop v []), anc v (leafTop v []),
        vstack node v (L.filter (leafTop v [] < ·)),
        state.folds + (leafTop v [] - 0 - (L.filter (· < leafTop v [])).length),
        pre.length + (L.filter (· < leafTop v [])).length + 1⟩, ?_, ?_, ?_, ?_, ?_⟩
      · rw [eval_recoverLeaves_step values fts _ pos prev state hp
          (by rw [hperm pos hp, hvpos]; rcases hprev with h | h <;> omega)
          (by rw [hperm pos hp, hvpos]; omega)
          (by rw [hperm pos hp, hvpos]; exact hclimb)]
        rw [if_neg (by simp at hpos; omega)]
        rfl
      · show node ftsTreeHeight (v / 2 ^ ftsTreeHeight) = _
        rw [Nat.div_eq_of_lt hv]
      · exact anc_top hv
      · simp [vstack, hnone]
      · have hlo := filter_lt_length_le hL.1 (leafTop v [])
        rw [show sumTops [v] = leafTop v [] + 0 from rfl, List.length_nil]
        dsimp only
        generalize (L.filter (· < leafTop v [])).length = a at hlo hlens ⊢
        generalize leafTop v [] = t at hlo hlens ⊢
        omega
  | cons w rest ih =>
      intro v pos prev L pre post state fuel hfuel hdrop hsorted hbound hpos hprev hL hsegs' hlen hseg hstack
      subst hfuel
      have hv := hbound v (by simp)
      have hw := hbound w (by simp)
      have hvw : v < w := (List.pairwise_cons.mp hsorted).1 w (by simp)
      have hvpos : sorted.getD pos 0 = v := by
        rw [List.getD_eq_getElem?_getD, ← List.head?_drop, hdrop]; rfl
      have hp : pos < ftsOpenings := by simp at hpos; omega
      have htop : leafTop v (w :: rest) = bitLength (v ^^^ w) - 1 := rfl
      obtain ⟨hnext, hpush, _⟩ := pending_next hvw hw htop hL
      obtain ⟨ht, _, _, hxor, habove⟩ := meet_facts hvw hw htop
      have hsplit := pending_split hL hsorted hbound
      have hlo := filter_lt_length_le hL.1 (leafTop v (w :: rest))
      have hlens := congrArg List.length hsplit
      rw [List.length_append] at hlens
      have hclimb := eval_leaf_climb hT hsorted hbound hL segs pre post hsegs' hlen
        (fts.secrets ⟨pos, hp⟩) (by rw [← hvpos, hsec pos hp]) state hseg hstack
      rw [← hsegs] at hclimb
      have hdrop' : sorted.drop (pos + 1) = w :: rest := by
        rw [← List.drop_drop, hdrop]; rfl
      have hlen' := hlen
      rw [allSegs_cons, List.length_append, climbSegs_length] at hlen'
      obtain ⟨R, hR, hnode, hheap, hstk, hfolds⟩ := ih w (pos + 1) v
        (leafTop v (w :: rest) :: L.filter (leafTop v (w :: rest) < ·))
        (pre ++ climbSegs v 0 (L.filter (· < leafTop v (w :: rest))) (leafTop v (w :: rest))) post
        ⟨node (leafTop v (w :: rest)) (v / 2 ^ leafTop v (w :: rest)), anc v (leafTop v (w :: rest)) ^^^ 1,
          (node (leafTop v (w :: rest)) (v / 2 ^ leafTop v (w :: rest)), anc v (leafTop v (w :: rest)) ^^^ 1) ::
            vstack node v (L.filter (leafTop v (w :: rest) < ·)),
          state.folds + (leafTop v (w :: rest) - 0 - (L.filter (· < leafTop v (w :: rest))).length),
          pre.length + (L.filter (· < leafTop v (w :: rest))).length + 1⟩ _ rfl
        hdrop' (List.pairwise_cons.mp hsorted).2 (fun u hu => hbound u (by simp [hu]))
        (by simp at hpos ⊢; omega) (Or.inr hvw) hnext
        (by rw [hsegs', allSegs_cons]; simp only [List.append_assoc])
        (by simp only [List.length_append, climbSegs_length]; omega)
        (by simp only [List.length_append, climbSegs_length]; omega)
        (by
          simp only [vstack, List.map_cons]
          rw [hpush]
          congr 1
          · congr 2
            rw [← hxor, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          · refine List.map_congr_left fun y hy => ?_
            have hy' := mem_filter_gt hy
            rw [habove y hy'.2, anc_eq_of_div_eq (habove y hy'.2)])
      refine ⟨R, ?_, hnode, hheap, hstk, ?_⟩
      · rw [eval_recoverLeaves_step values fts _ pos prev state hp
          (by rw [hperm pos hp, hvpos]; rcases hprev with h | h <;> omega)
          (by rw [hperm pos hp, hvpos]; simp at hpos; omega)
          (by rw [hperm pos hp, hvpos]; exact hclimb)]
        rw [if_pos (by simp at hpos; omega), hperm pos hp, hvpos]
        exact hR
      · rw [List.length_cons] at hfolds
        dsimp only at hfolds
        rw [List.length_cons, show sumTops (v :: w :: rest)
          = leafTop v (w :: rest) + sumTops (w :: rest) from rfl]
        generalize (L.filter (· < leafTop v (w :: rest))).length = a at hfolds hlo hlens
        generalize (L.filter (leafTop v (w :: rest) < ·)).length = b at hfolds hlo hlens
        generalize leafTop v (w :: rest) = t at hfolds hlo hlens ⊢
        omega

/-- The sorted leaves of injective leaves: `15` strictly increasing values below `2^14`. -/
theorem sortedLeaves_facts (leaves : IndexGroup → FtsLeaf) (hinj : Function.Injective leaves) :
    (sortedLeaves leaves).length = ftsOpenings ∧ (sortedLeaves leaves).Pairwise (· < ·)
      ∧ ∀ w ∈ sortedLeaves leaves, w < 2 ^ ftsTreeHeight := by
  refine ⟨by simp [sortedLeaves, sortedSlots], ?_, ?_⟩
  · rw [sortedLeaves_eq_sortLeaves]
    have hle : (Octopus.sortLeaves (Octopus.valList leaves)).Pairwise (· ≤ ·) :=
      List.pairwise_insertionSort _ _
    have hnd : (Octopus.sortLeaves (Octopus.valList leaves)).Nodup :=
      (List.perm_insertionSort _ _).nodup_iff.mpr ((Octopus.valList_nodup leaves).mpr hinj)
    exact (hle.and hnd).imp fun h => lt_of_le_of_ne h.1 h.2
  · intro w hw
    simp only [sortedLeaves, List.mem_map] at hw
    obtain ⟨r, _, rfl⟩ := hw
    exact (leaves r).isLt

theorem sortedLeaves_getD (leaves : IndexGroup → FtsLeaf) {i : Nat} (hi : i < ftsOpenings) :
    (sortedLeaves leaves).getD i 0 = (leaves ((sortedSlots leaves).getD i ⟨0, by decide⟩)).val := by
  have hlen : i < (sortedSlots leaves).length := by simpa [sortedSlots] using hi
  simp [sortedLeaves, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen]

theorem honestFts_segments (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest)
    (node : Nat → Nat → Digest) :
    (honestFts leaves secret node).segments = honestSegments node (schedule (sortedLeaves leaves)) := rfl

theorem honestFts_perm (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest)
    (node : Nat → Nat → Digest) (s : Fin ftsOpenings) :
    (honestFts leaves secret node).perm s = ((sortedSlots leaves).getD s.val ⟨0, by decide⟩).castSucc := rfl

theorem honestFts_secrets (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest)
    (node : Nat → Nat → Digest) (s : Fin ftsOpenings) :
    (honestFts leaves secret node).secrets s = secret (leaves ((sortedSlots leaves).getD s.val ⟨0, by decide⟩)) :=
  rfl

theorem slotValue_castSucc (leaves : IndexGroup → FtsLeaf) (r : IndexGroup) :
    slotValue leaves r.castSucc = (leaves r).val := by
  simp [slotValue]

/-- **The stack machine recovers the root.** For admissible leaves, the honest opening built from a
table of the tree's nodes (`honestFts`) makes `ftsRecover` accept and return the root, under every
answer function. -/
theorem eval_ftsRecover_honest {node : Nat → Nat → Digest} (hT : HonestTable f parameter index node)
    (leaves : IndexGroup → FtsLeaf) (hadm : AdmissibleLeaves leaves) (secret : FtsLeaf → Digest)
    (hleaf : ∀ j : FtsLeaf, evalWithAnswerFn f (ftsLeafHash parameter index porsTree j.val (secret j)
      : OracleComp HashSpec Digest) = node 0 j.val) :
    evalWithAnswerFn f (ftsRecover parameter index (slotValue leaves) (honestFts leaves secret node)
      : OracleComp HashSpec (Option Digest)) = some (node ftsTreeHeight 0) := by
  have hO : ftsOpenings = 15 := rfl
  obtain ⟨hlen, hsorted, hbound⟩ := sortedLeaves_facts leaves hadm.1
  obtain ⟨v, rest, hvr⟩ : ∃ v rest, sortedLeaves leaves = v :: rest := by
    cases h : sortedLeaves leaves with
    | nil => rw [h, hO] at hlen; simp at hlen
    | cons v rest => exact ⟨v, rest, rfl⟩
  rw [hvr] at hlen hsorted hbound
  have hrest : rest.length = 14 := by simp at hlen; omega
  have hsched : schedule (sortedLeaves leaves) = allSegs (v :: rest) [] := by
    have := scheduleLeaves_eq rest v ⟨[], [], 0, false, []⟩ [] hsorted hbound
      ⟨List.Pairwise.nil, by simp⟩ rfl
    rw [schedule, hvr, this.1, List.nil_append]
  have hall := allSegs_length rest v [] hsorted hbound ⟨List.Pairwise.nil, by simp⟩
  obtain ⟨R, hR, hnode, hheap, hstk, hfolds⟩ := eval_recoverLeaves_honest hT (slotValue leaves)
    (honestFts leaves secret node) (sortedLeaves leaves) (schedule (sortedLeaves leaves))
    (honestFts_segments leaves secret node)
    (fun i h => by rw [honestFts_perm, slotValue_castSucc, sortedLeaves_getD leaves h])
    (fun i h => by
      rw [honestFts_secrets, sortedLeaves_getD leaves h]
      exact hleaf _)
    rest v 0 0 [] [] [] RecoverState.initial ftsOpenings (by omega) (by rw [List.drop_zero, hvr])
    hsorted hbound (by omega) (Or.inl rfl) ⟨List.Pairwise.nil, by simp⟩ (by rw [hsched]; simp)
    (by rw [hall]; simp [ftsSegments, hO, hrest]) rfl rfl
  have hsum := sumTops_add (v :: rest) (by simp) hsorted
  have hoct := hadm.2
  rw [hvr, Octopus.octopusSize_eq] at hoct
  simp only [Octopus.octH, List.length_cons] at hoct hsum
  simp only [List.length_nil, List.length_cons] at hfolds
  have hfolds' : R.folds ≤ ftsAuthCapacity := by
    simp only [RecoverState.initial, ftsAuthCapacity, ftsTreeHeight] at hfolds hoct hsum ⊢
    omega
  simp only [ftsRecover, evalWithAnswerFn_bind, hR]
  rw [if_pos ⟨hfolds', hheap, hstk⟩, hnode]
  rfl

end Verifier

end SphincsSecurity.Completeness
