import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise
import SigGolfCandidate.Ref.Basic

/-!
# The honest PORS schedule reads exactly the octopus (`len(reads) == octopus_size(vs)`)

Pure mathematics about `ref.schedule` (`SigGolfCandidate.Ref.schedule`, no machine code).

Main result: `schedule_reads_length` (sorted distinct leaves `< 2^14`, 15 of them; general
version `schedule_reads_length_gen` for any `k ≥ 1` leaves).

Argument: every height step of leaf `s` is a read or a merge (pop); leaf `s` does `top_s` steps;
the non-last leaves push once each; the stack before leaf `s` holds, top first, the sibling
heap indices `pushQ i` of the leaves `i ∈ live s` (those whose LCA height `Lh i` exceeds every
later one), and `pushQ i` is the ancestor of leaf `s` at height `Lh i - 1`; so leaf `s` merges
exactly the entries with `Lh i < Lh s` (the last leaf: all), the final stack is empty, and
`reads = Σ top_s − (k − 1) = octopusSize vs`.
-/

namespace SigGolfCandidate.Sign.SchedMath

open SigGolfCandidate.Ref

/-! ## `bitLen` -/

theorem bitLen_le_iff (x n : Nat) : bitLen x ≤ n ↔ x < 2 ^ n := by
  unfold bitLen
  split
  · subst x; simp [Nat.two_pow_pos]
  · rename_i h; rw [← Nat.log2_lt h]; omega

theorem lt_two_pow_bitLen (x : Nat) : x < 2 ^ bitLen x := (bitLen_le_iff x _).1 le_rfl

theorem one_le_bitLen {x : Nat} (hx : x ≠ 0) : 1 ≤ bitLen x := by
  unfold bitLen; simp [hx]

theorem not_lt_two_pow_bitLen_pred {x : Nat} (hx : x ≠ 0) : ¬ x < 2 ^ (bitLen x - 1) := by
  intro h
  have h1 := (bitLen_le_iff _ _).2 h
  have h2 := one_le_bitLen hx
  omega

theorem two_pow_bitLen_pred_le {x : Nat} (hx : x ≠ 0) : 2 ^ (bitLen x - 1) ≤ x :=
  Nat.le_of_not_lt (not_lt_two_pow_bitLen_pred hx)

theorem bitLen_zero : bitLen 0 = 0 := rfl

theorem bitLen_div_two {x : Nat} (hx : x ≠ 0) : bitLen x = bitLen (x / 2) + 1 := by
  have h1 := one_le_bitLen hx
  apply Nat.le_antisymm
  · rw [bitLen_le_iff, Nat.pow_succ]
    have := lt_two_pow_bitLen (x / 2)
    omega
  · have : bitLen (x / 2) ≤ bitLen x - 1 := by
      rw [bitLen_le_iff]
      have h2 := lt_two_pow_bitLen x
      rw [show bitLen x = bitLen x - 1 + 1 by omega, Nat.pow_succ] at h2
      omega
    omega

/-! ## Bit facts -/

theorem xor_eq_zero {x y : Nat} (h : x ^^^ y = 0) : x = y := by
  have : x ^^^ (x ^^^ y) = x ^^^ 0 := by rw [h]
  rwa [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor, Nat.xor_zero, eq_comm] at this

/-- Two numbers agree above bit `h` iff their xor is below `2^h`. -/
theorem div_pow_eq_iff (a b h : Nat) : a / 2 ^ h = b / 2 ^ h ↔ a ^^^ b < 2 ^ h := by
  rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow]
  constructor
  · intro e
    have : (a ^^^ b) >>> h = 0 := by rw [Nat.shiftRight_xor_distrib, e, Nat.xor_self]
    rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_zero_iff] at this
    rcases this with h0 | h0
    · exact absurd h0 (Nat.two_pow_pos h).ne'
    · exact h0
  · intro l
    have := Nat.shiftRight_eq_zero _ _ l
    rw [Nat.shiftRight_xor_distrib] at this
    exact xor_eq_zero this

/-- The lowest common ancestor of `a < b`: with `L = bitLen (a xor b)`, the ancestors at height
`L - 1` are consecutive siblings (left `a`, right `b`). -/
theorem lca_pair {a b : Nat} (hab : a < b) :
    1 ≤ bitLen (a ^^^ b) ∧ b / 2 ^ (bitLen (a ^^^ b) - 1) = a / 2 ^ (bitLen (a ^^^ b) - 1) + 1 ∧
      a / 2 ^ (bitLen (a ^^^ b) - 1) % 2 = 0 := by
  have hx : a ^^^ b ≠ 0 := fun h => by have := xor_eq_zero h; omega
  have hL := one_le_bitLen hx
  set L := bitLen (a ^^^ b) with hLdef
  have e1 : a / 2 ^ L = b / 2 ^ L := (div_pow_eq_iff _ _ _).2 (lt_two_pow_bitLen _)
  have e2 : a / 2 ^ (L - 1) ≠ b / 2 ^ (L - 1) := fun h =>
    not_lt_two_pow_bitLen_pred hx ((div_pow_eq_iff _ _ _).1 h)
  have hp : 2 ^ L = 2 ^ (L - 1) * 2 := by rw [← Nat.pow_succ]; congr 1; omega
  rw [hp, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul] at e1
  have e3 : a / 2 ^ (L - 1) ≤ b / 2 ^ (L - 1) := Nat.div_le_div_right hab.le
  refine ⟨hL, ?_, ?_⟩ <;> omega

/-- `porsT ||| x = 2^14 + x` for `x < 2^14`. -/
theorem porsT_or {x : Nat} (hx : x < 2 ^ 14) : porsT ||| x = 2 ^ 14 + x := by
  have := Nat.two_pow_add_eq_or_of_lt hx 1
  simp only [Nat.mul_one] at this
  unfold porsT porsH; rw [← this]

/-- Heap indices of different heights differ. -/
theorem div_pow_inj {E g h : Nat} (hE1 : 2 ^ 14 ≤ E) (hE2 : E < 2 ^ 15) (hg : g ≤ 14) (hh : h ≤ 14)
    (e : E / 2 ^ g = E / 2 ^ h) : g = h := by
  have lo : ∀ g, g ≤ 14 → 2 ^ (14 - g) ≤ E / 2 ^ g := fun g hg => by
    rw [Nat.le_div_iff_mul_le (Nat.two_pow_pos _), ← Nat.pow_add, show 14 - g + g = 14 by omega]
    exact hE1
  have hi : ∀ g, g ≤ 14 → E / 2 ^ g < 2 ^ (15 - g) := fun g hg => by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 15 - g + g = 15 by omega]
    exact hE2
  rcases Nat.lt_trichotomy g h with hgh | hgh | hgh
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 15 - h ≤ 14 - g by omega)
    have := lo g hg; have := hi h hh; omega
  · exact hgh
  · have := Nat.pow_le_pow_right (show 0 < 2 by decide) (show 15 - g ≤ 14 - h by omega)
    have := lo h hh; have := hi g hg; omega

/-- `(2^14 + x) / 2^g = 2^(14 - g) + x / 2^g` for `g ≤ 14`. -/
theorem heap_div {x g : Nat} (hg : g ≤ 14) : (2 ^ 14 + x) / 2 ^ g = 2 ^ (14 - g) + x / 2 ^ g := by
  rw [show (2 : Nat) ^ 14 = 2 ^ (14 - g) * 2 ^ g by rw [← Nat.pow_add]; congr 1; omega,
    Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos _), Nat.add_comm]

/-! ## The inner loop -/

theorem length_filter_compl {α : Type} (l : List α) (p q : α → Bool) (h : ∀ x, q x = !p x) :
    (l.filter p).length + (l.filter q).length = l.length := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.filter_cons, h x, List.length_cons]
    cases p x <;> simp <;> omega

/-- The inner loop over heights `a .. a + n - 1` of a leaf whose heap index at height `a` is
`E0 / 2^a`, with a stack of entries `ls` (top first) at strictly increasing heights `g x ≥ a`,
each equal to the leaf's ancestor at its height: the entries below height `a + n` are merged,
every other step is a read. -/
theorem fold_steps {α : Type} (g q : α → Nat) (E0 : Nat) (hE1 : 2 ^ 14 ≤ E0) (hE2 : E0 < 2 ^ 15) :
    ∀ (n a : Nat) (ls : List α) (st : SchedState) (c t : Nat),
      ls.Pairwise (fun x y => g x < g y) →
      (∀ x ∈ ls, a ≤ g x ∧ g x ≤ 14 ∧ q x = E0 / 2 ^ g x) → a + n ≤ 15 →
      st.stack = ls.map q →
      ((List.range' a n).foldl schedStep (st, E0 / 2 ^ a, c, t)).1.stack =
          (ls.filter (fun x => a + n ≤ g x)).map q ∧
        ((List.range' a n).foldl schedStep (st, E0 / 2 ^ a, c, t)).1.reads.length +
          (ls.filter (fun x => g x < a + n)).length = st.reads.length + n ∧
        ((List.range' a n).foldl schedStep (st, E0 / 2 ^ a, c, t)).2.1 = E0 / 2 ^ (a + n) := by
  intro n
  induction n with
  | zero =>
    intro a ls st c t _ hls _ hst
    simp only [List.range'_zero, List.foldl_nil, Nat.add_zero]
    refine ⟨?_, ?_, by trivial⟩
    · rw [List.filter_eq_self.2 (fun x hx => by simpa using (hls x hx).1), hst]
    · rw [List.filter_eq_nil_iff.2 (fun x hx => by simpa using (hls x hx).1)]; rfl
  | succ n ih =>
    intro a ls st c t hpw hls han hst
    obtain ⟨sg, rd, sk⟩ := st
    simp only at hst
    subst hst
    have hdiv : E0 / 2 ^ a / 2 = E0 / 2 ^ (a + 1) := by
      rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    rw [List.range'_succ, List.foldl_cons]
    cases ls with
    | nil =>
      have := ih (a + 1) [] ⟨sg, rd ++ [(a, (E0 / 2 ^ a ^^^ 1) - porsT / 2 ^ a)], []⟩
        (c + 1) t List.Pairwise.nil (by simp) (by omega) rfl
      have hs : schedStep (⟨sg, rd, List.map q []⟩, E0 / 2 ^ a, c, t) a =
          (⟨sg, rd ++ [(a, (E0 / 2 ^ a ^^^ 1) - porsT / 2 ^ a)], []⟩, E0 / 2 ^ (a + 1), c + 1, t) := by
        simp only [schedStep, List.map_nil, hdiv]
      rw [hs]
      obtain ⟨t1, t2, t3⟩ := this
      refine ⟨?_, ?_, ?_⟩
      · rw [t1]; simp
      · simp only [List.length_append, List.length_singleton, List.filter_nil, List.length_nil] at t2 ⊢
        omega
      · rw [t3]; congr 2; omega
    | cons x ls' =>
      have hx := hls x List.mem_cons_self
      rw [List.pairwise_cons] at hpw
      have hls' : ∀ y ∈ ls', a + 1 ≤ g y ∧ g y ≤ 14 ∧ q y = E0 / 2 ^ g y := fun y hy => by
        have := hls y (List.mem_cons_of_mem _ hy); have := hpw.1 y hy; omega
      by_cases hxa : g x = a
      · -- merge
        have hq : q x = E0 / 2 ^ a := by rw [hx.2.2, hxa]
        have := ih (a + 1) ls' ⟨sg ++ [c ||| 16 ||| 32 * t], rd, ls'.map q⟩
          0 (E0 / 2 ^ (a + 1) % 2) hpw.2 hls' (by omega) rfl
        have hs : schedStep (⟨sg, rd, List.map q (x :: ls')⟩, E0 / 2 ^ a, c, t) a =
            (⟨sg ++ [c ||| 16 ||| 32 * t], rd, ls'.map q⟩, E0 / 2 ^ (a + 1), 0,
              E0 / 2 ^ (a + 1) % 2) := by
          simp only [schedStep, List.map_cons, hq, if_true, hdiv]
        rw [hs]
        obtain ⟨t1, t2, t3⟩ := this
        refine ⟨?_, ?_, ?_⟩
        · rw [t1, List.filter_cons, if_neg (by simp; omega)]
          congr 2; funext y; simp; omega
        · rw [List.filter_cons, if_pos (by simp; omega), List.length_cons]
          simp only at t2 ⊢
          rw [show (ls'.filter fun y => decide (g y < a + (n + 1))) =
            ls'.filter fun y => decide (g y < a + 1 + n) by congr 1; funext y; simp; omega]
          omega
        · rw [t3]; congr 2; omega
      · -- read (the stack top is at another height)
        have hne : q x ≠ E0 / 2 ^ a := by
          rw [hx.2.2]; intro e
          exact hxa (div_pow_inj hE1 hE2 hx.2.1 (by omega) e)
        have hall : ∀ y ∈ x :: ls', a + 1 ≤ g y ∧ g y ≤ 14 ∧ q y = E0 / 2 ^ g y := by
          intro y hy
          rcases List.mem_cons.1 hy with rfl | hy
          · exact ⟨by omega, hx.2.1, hx.2.2⟩
          · exact hls' y hy
        have := ih (a + 1) (x :: ls') ⟨sg, rd ++ [(a, (E0 / 2 ^ a ^^^ 1) - porsT / 2 ^ a)],
          (x :: ls').map q⟩ (c + 1) t (List.pairwise_cons.2 hpw) hall (by omega) rfl
        have hs : schedStep (⟨sg, rd, List.map q (x :: ls')⟩, E0 / 2 ^ a, c, t) a =
            (⟨sg, rd ++ [(a, (E0 / 2 ^ a ^^^ 1) - porsT / 2 ^ a)], (x :: ls').map q⟩,
              E0 / 2 ^ (a + 1), c + 1, t) := by
          simp only [schedStep, List.map_cons, hne, if_false, hdiv]
        rw [hs]
        obtain ⟨t1, t2, t3⟩ := this
        refine ⟨?_, ?_, ?_⟩
        · rw [t1]; congr 2; funext y; simp; omega
        · simp only [List.length_append, List.length_singleton] at t2 ⊢
          rw [show ((x :: ls').filter fun y => decide (g y < a + (n + 1))) =
            (x :: ls').filter fun y => decide (g y < a + 1 + n) by congr 1; funext y; simp; omega]
          omega
        · rw [t3]; congr 2; omega

/-! ## The leaves -/

section leaves
variable (vs : List Nat)

/-- LCA height of leaves `i`, `i + 1`: `bitLen (v_i xor v_{i+1})`. -/
def Lh (i : Nat) : Nat := bitLen (vs.getD i 0 ^^^ vs.getD (i + 1) 0)

/-- The number of height steps of leaf `s`. -/
def topOf (s : Nat) : Nat := if s + 1 < vs.length then Lh vs s - 1 else porsH

/-- The heap index pushed after leaf `i` (sibling of its node at height `Lh i - 1`). -/
def pushQ (i : Nat) : Nat := ((porsT ||| vs.getD i 0) / 2 ^ (Lh vs i - 1)) ^^^ 1

/-- The leaves whose pushed entry is still on the stack before leaf `s` (most recent first). -/
def live : Nat → List Nat
  | 0 => []
  | s + 1 => s :: (live s).filter (fun i => Lh vs s < Lh vs i)

variable {vs}

/-- Standing hypotheses: sorted, distinct, below `2^14`. -/
structure Good (vs : List Nat) : Prop where
  lt : ∀ i j, i < j → j < vs.length → vs.getD i 0 < vs.getD j 0
  bound : ∀ i, i < vs.length → vs.getD i 0 < 2 ^ 14

theorem good_of (hsort : vs.Pairwise (· < ·)) (hlt : ∀ v ∈ vs, v < 2 ^ 14) : Good vs := by
  refine ⟨fun i j hij hj => ?_, fun i hi => ?_⟩
  · rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj]
    exact List.pairwise_iff_getElem.1 hsort i j (by omega) hj hij
  · rw [List.getD_eq_getElem _ _ hi]; exact hlt _ (List.getElem_mem _)

theorem Lh_bounds (hg : Good vs) {i : Nat} (hi : i + 1 < vs.length) : 1 ≤ Lh vs i ∧ Lh vs i ≤ 14 := by
  have hlt := hg.lt i (i + 1) (by omega) hi
  refine ⟨(lca_pair hlt).1, ?_⟩
  unfold Lh; rw [bitLen_le_iff]
  exact Nat.xor_lt_two_pow (hg.bound i (by omega)) (hg.bound (i + 1) hi)

/-- Ultrametric: if every LCA between `i` and `s` is lower than `Lh i`, leaves `i + 1` and `s`
agree above height `Lh i - 1`. -/
theorem ultra (i : Nat) : ∀ d, i + 1 + d < vs.length →
    (∀ j, i < j → j < i + 1 + d → Lh vs j < Lh vs i) →
    vs.getD (i + 1) 0 ^^^ vs.getD (i + 1 + d) 0 < 2 ^ (Lh vs i - 1) := by
  intro d
  induction d with
  | zero => intro _ _; simp [Nat.two_pow_pos]
  | succ d ih =>
    intro hd hj
    have h1 := ih (by omega) (fun j h1 h2 => hj j h1 (by omega))
    have hjd := hj (i + 1 + d) (by omega) (by omega)
    have h2 : vs.getD (i + 1 + d) 0 ^^^ vs.getD (i + 1 + d + 1) 0 < 2 ^ (Lh vs i - 1) := by
      have := lt_two_pow_bitLen (vs.getD (i + 1 + d) 0 ^^^ vs.getD (i + 1 + d + 1) 0)
      exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by decide) (by unfold Lh at hjd ⊢; omega))
    have := Nat.xor_lt_two_pow h1 h2
    rwa [Nat.xor_assoc, ← Nat.xor_assoc (vs.getD (i + 1 + d) 0), Nat.xor_self, Nat.zero_xor,
      show i + 1 + d + 1 = i + 1 + (d + 1) by omega] at this

/-- The pushed entry of leaf `i` is the ancestor of leaf `s` at height `Lh i - 1`. -/
theorem pushQ_eq (hg : Good vs) {i s : Nat} (his : i < s) (hs : s < vs.length)
    (hj : ∀ j, i < j → j < s → Lh vs j < Lh vs i) :
    pushQ vs i = (porsT ||| vs.getD s 0) / 2 ^ (Lh vs i - 1) := by
  have hi1 : i + 1 < vs.length := by omega
  obtain ⟨hL1, hL2⟩ := Lh_bounds hg hi1
  obtain ⟨-, hB, hA⟩ := lca_pair (hg.lt i (i + 1) (by omega) hi1)
  have hu := ultra (vs := vs) i (s - (i + 1)) (by omega) (fun j h1 h2 => hj j h1 (by omega))
  rw [show i + 1 + (s - (i + 1)) = s by omega, ← div_pow_eq_iff] at hu
  unfold pushQ
  rw [porsT_or (hg.bound i (by omega)), porsT_or (hg.bound s hs), heap_div (by omega),
    heap_div (by omega), Nat.xor_one_of_even]
  · unfold Lh at hu ⊢; omega
  · rw [Nat.even_add]
    constructor <;> intro _
    · exact Nat.even_iff.2 hA
    · exact (Nat.even_pow' (by omega)).2 (by decide)

/-- An entry still on the stack is never at the LCA height of the current leaf. -/
theorem Lh_ne (hg : Good vs) {i s : Nat} (his : i < s) (hs : s + 1 < vs.length)
    (hj : ∀ j, i < j → j < s → Lh vs j < Lh vs i) : Lh vs i ≠ Lh vs s := by
  intro heq
  have hi1 : i + 1 < vs.length := by omega
  obtain ⟨-, hB, hA⟩ := lca_pair (hg.lt i (i + 1) (by omega) hi1)
  obtain ⟨-, -, hA'⟩ := lca_pair (hg.lt s (s + 1) (by omega) hs)
  have hu := ultra (vs := vs) i (s - (i + 1)) (by omega) (fun j h1 h2 => hj j h1 (by omega))
  rw [show i + 1 + (s - (i + 1)) = s by omega, ← div_pow_eq_iff] at hu
  unfold Lh at heq hu
  rw [heq] at hB hA hu
  omega

/-- Invariants of `live s`. -/
structure LiveOk (vs : List Nat) (s : Nat) : Prop where
  lt : ∀ i ∈ live vs s, i < s
  hi : ∀ i ∈ live vs s, ∀ j, i < j → j < s → Lh vs j < Lh vs i
  pw : (live vs s).Pairwise (fun a b => Lh vs a - 1 < Lh vs b - 1)

theorem liveOk_zero : LiveOk vs 0 := ⟨by simp [live], by simp [live], by simp [live]⟩

theorem liveOk_succ (hg : Good vs) {s : Nat} (hs : s + 1 < vs.length) (h : LiveOk vs s) :
    LiveOk vs (s + 1) := by
  refine ⟨fun i hi => ?_, fun i hi j h1 h2 => ?_, ?_⟩
  · simp only [live, List.mem_cons, List.mem_filter] at hi
    rcases hi with rfl | ⟨hi, -⟩
    · omega
    · have := h.lt i hi; omega
  · simp only [live, List.mem_cons, List.mem_filter, decide_eq_true_eq] at hi
    rcases hi with rfl | ⟨hi, hlt⟩
    · omega
    · by_cases hjs : j = s
      · subst hjs; exact hlt
      · exact h.hi i hi j h1 (by omega)
  · simp only [live]
    refine List.pairwise_cons.2 ⟨fun b hb => ?_, h.pw.filter _⟩
    simp only [List.mem_filter, decide_eq_true_eq] at hb
    have := (Lh_bounds hg hs).1
    omega

/-- One leaf: the stack `live s` becomes `live (s + 1)` (or empty after the last leaf); counts. -/
theorem leaf_step (hg : Good vs) {s : Nat} (hs : s < vs.length) (hl : LiveOk vs s)
    (st : SchedState) (hst : st.stack = (live vs s).map (pushQ vs)) :
    (schedLeaf vs st s).stack =
        (if s + 1 < vs.length then (live vs (s + 1)).map (pushQ vs) else []) ∧
      (schedLeaf vs st s).reads.length + st.stack.length + (if s + 1 < vs.length then 1 else 0) =
        st.reads.length + topOf vs s + (schedLeaf vs st s).stack.length := by
  set E0 := porsT ||| vs.getD s 0 with hE0
  have hE : E0 = 2 ^ 14 + vs.getD s 0 := porsT_or (hg.bound s hs)
  have hb := hg.bound s hs
  have hE1 : 2 ^ 14 ≤ E0 := by omega
  have hE2 : E0 < 2 ^ 15 := by omega
  have htop : topOf vs s ≤ 14 := by
    unfold topOf; split
    · have := (Lh_bounds hg (by assumption)).2; omega
    · unfold porsH; omega
  have hfold := fold_steps (fun i => Lh vs i - 1) (pushQ vs) E0 hE1 hE2 (topOf vs s) 0 (live vs s) st 0
    (E0 % 2) hl.pw (fun i hi => by
      have his := hl.lt i hi
      have := (Lh_bounds hg (show i + 1 < vs.length by omega))
      exact ⟨Nat.zero_le _, by omega, pushQ_eq hg his hs (hl.hi i hi)⟩) (by omega)
    (by rw [hst])
  try simp only [Nat.zero_add, Nat.pow_zero, Nat.div_one] at hfold
  have hsplit := length_filter_compl (live vs s) (fun x => decide (topOf vs s ≤ Lh vs x - 1))
    (fun x => decide (Lh vs x - 1 < topOf vs s)) (fun x => by
      by_cases h : topOf vs s ≤ Lh vs x - 1
      · simp [h]
      · simp [h]; omega)
  have hunf : schedLeaf vs st s =
      let r := (List.range (topOf vs s)).foldl schedStep (st, E0, 0, E0 % 2)
      if s + 1 < vs.length then
        (⟨r.1.segs ++ [r.2.2.1 ||| 32 * r.2.2.2], r.1.reads, (r.2.1 ^^^ 1) :: r.1.stack⟩ : SchedState)
      else ⟨r.1.segs ++ [r.2.2.1 ||| 32 * r.2.2.2], r.1.reads, r.1.stack⟩ := by
    unfold schedLeaf topOf; rfl
  rw [hunf, List.range_eq_range']
  obtain ⟨f1, f2, f3⟩ := hfold
  by_cases hlast : s + 1 < vs.length
  · simp only [hlast, if_true]
    have hrem : (live vs s).filter (fun x => decide (topOf vs s ≤ Lh vs x - 1)) =
        (live vs s).filter (fun i => Lh vs s < Lh vs i) := by
      apply List.filter_congr
      intro i hi
      have := Lh_bounds hg (show i + 1 < vs.length by have := hl.lt i hi; omega)
      have := Lh_bounds hg hlast
      have hne := Lh_ne hg (hl.lt i hi) hlast (hl.hi i hi)
      unfold topOf; simp only [hlast, if_true, decide_eq_decide]; omega
    have hpush : (E0 / 2 ^ topOf vs s) ^^^ 1 = pushQ vs s := by
      unfold pushQ topOf; simp only [hlast, if_true]; rfl
    refine ⟨?_, ?_⟩
    · rw [f1, f3, hpush, hrem]; rfl
    · simp only [List.length_cons]
      rw [f1, hst, List.length_map, List.length_map]
      omega
  · simp only [hlast, if_false]
    have hnil : (live vs s).filter (fun x => decide (topOf vs s ≤ Lh vs x - 1)) = [] := by
      apply List.filter_eq_nil_iff.2
      intro i hi
      have := Lh_bounds hg (show i + 1 < vs.length by have := hl.lt i hi; omega)
      unfold topOf porsH; simp only [hlast, if_false, decide_eq_true_eq]; omega
    refine ⟨?_, ?_⟩
    · rw [f1, hnil]; rfl
    · rw [f1, hnil, hst, List.length_map]
      rw [hnil] at hsplit
      simp only [List.length_nil, List.map_nil] at hsplit ⊢
      omega

/-- After the first `s ≤ k - 1` leaves: the stack is `live s`, and
`reads + s = Σ_{j<s} top_j + |stack|`. -/
theorem prefix_leaves (hg : Good vs) : ∀ s, s < vs.length →
    ((List.range s).foldl (schedLeaf vs) ⟨[], [], []⟩).stack = (live vs s).map (pushQ vs) ∧
      ((List.range s).foldl (schedLeaf vs) ⟨[], [], []⟩).reads.length + s =
        ((List.range s).map (topOf vs)).sum +
          ((List.range s).foldl (schedLeaf vs) ⟨[], [], []⟩).stack.length ∧
      LiveOk vs s := by
  intro s
  induction s with
  | zero => intro _; exact ⟨rfl, rfl, liveOk_zero⟩
  | succ s ih =>
    intro hs
    obtain ⟨h1, h2, h3⟩ := ih (by omega)
    obtain ⟨l1, l2⟩ := leaf_step hg (show s < vs.length by omega) h3 _ h1
    rw [if_pos hs] at l1 l2
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, List.map_append,
      List.sum_append]
    refine ⟨l1, ?_, liveOk_succ hg hs h3⟩
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

theorem zipWith_tail (f : Nat → Nat → Nat) (vs : List Nat) :
    List.zipWith f vs vs.tail =
      (List.range (vs.length - 1)).map (fun j => f (vs.getD j 0) (vs.getD (j + 1) 0)) := by
  apply List.ext_getElem
  · simp
  · intro n h1 h2
    simp only [List.length_zipWith, List.length_tail] at h1
    rw [List.getElem_zipWith, List.getElem_map, List.getElem_range, List.getElem_tail,
      List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]

theorem sum_pred (f : Nat → Nat) (n : Nat) (h : ∀ j < n, 1 ≤ f j) :
    ((List.range n).map (fun j => f j - 1)).sum + n = ((List.range n).map f).sum := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    have := ih (fun j hj => h j (by omega))
    have := h n (by omega)
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega

/-- **General version**: `k ≥ 1` sorted distinct leaves below `2^14`. -/
theorem schedule_reads_length_gen (vs : List Nat) (hk : 1 ≤ vs.length)
    (hsort : vs.Pairwise (· < ·)) (hlt : ∀ v ∈ vs, v < 2 ^ 14) :
    (schedule vs).2.length = octopusSize vs := by
  have hg := good_of hsort hlt
  set k := vs.length with hkdef
  obtain ⟨h1, h2, h3⟩ := prefix_leaves hg (k - 1) (by omega)
  obtain ⟨l1, l2⟩ := leaf_step hg (show k - 1 < vs.length by omega) h3 _ h1
  rw [if_neg (by omega)] at l1 l2
  have hsum : ((List.range (k - 1)).map (topOf vs)).sum =
      ((List.range (k - 1)).map (fun j => Lh vs j - 1)).sum := by
    congr 1; apply List.map_congr_left; intro j hj
    rw [List.mem_range] at hj; unfold topOf; rw [if_pos (by omega)]
  have hsp := sum_pred (Lh vs) (k - 1) (fun j hj => (Lh_bounds hg (by omega)).1)
  have hz : (List.zipWith (fun a b => bitLen (a ^^^ b)) vs vs.tail).sum =
      ((List.range (k - 1)).map (Lh vs)).sum := by
    rw [zipWith_tail]; rfl
  have htop : topOf vs (k - 1) = 14 := by unfold topOf porsH; rw [if_neg (by omega)]
  unfold schedule octopusSize
  simp only
  have hr : List.range vs.length = List.range (k - 1) ++ [k - 1] := by
    rw [← List.range_succ]; congr 1; omega
  rw [hr, List.foldl_append, List.foldl_cons, List.foldl_nil, hz]
  rw [l1, List.length_nil, htop] at l2
  rw [hsum] at h2
  unfold porsH
  omega

/-- **`len(reads) == octopus_size(vs)`** for the 15 sorted distinct PORS leaves. -/
theorem schedule_reads_length (vs : List Nat) (hlen : vs.length = 15)
    (hsort : vs.Pairwise (· < ·)) (hlt : ∀ v ∈ vs, v < 2 ^ 14) :
    (schedule vs).2.length = octopusSize vs :=
  schedule_reads_length_gen vs (by omega) hsort hlt

/-- Corollary: an admissible leaf set needs at most `porsM = 120` authentication nodes. -/
theorem schedule_reads_le (vs : List Nat) (hlen : vs.length = 15)
    (hsort : vs.Pairwise (· < ·)) (hlt : ∀ v ∈ vs, v < 2 ^ 14) (hoct : octopusSize vs ≤ porsM) :
    (schedule vs).2.length ≤ porsM := by
  rw [schedule_reads_length vs hlen hsort hlt]; exact hoct

end leaves

end SigGolfCandidate.Sign.SchedMath
