import SigGolfCandidate.Expand.Base
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Bitwise

/-!
# The honest schedule: counting lemmas

`ref.schedule vs` on sorted distinct leaves `vs` (all `< 2^14`) emits exactly `2 |vs| - 1`
segments and `octopusSize vs` reads, and its stack empties. We prove this with the classical
invariant of the stack machine: at the start of leaf `s`, the stack holds the ancestors
`(2^14 + v_s) / 2^g` of leaf `v_s` at a strictly increasing list of heights `g ∈ G` (top first),
each of which is a right child (`v_s / 2^g` odd).
-/

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Ref

/-! ## Number facts -/

theorem bitLen_pos {x : Nat} (hx : x ≠ 0) : bitLen x = Nat.log2 x + 1 := by
  simp [bitLen, hx]

theorem bitLen_le {x n : Nat} (hx : x < 2 ^ n) : bitLen x ≤ n := by
  unfold bitLen
  split
  · omega
  · have := (Nat.log2_lt (by assumption)).2 hx; omega

theorem div_pow_succ (a t : Nat) : a / 2 ^ t = 2 * (a / 2 ^ (t + 1)) + a / 2 ^ t % 2 := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]; omega

/-- The highest differing bit `t` of `a < b`: they agree above `t`, `a` has bit `t` clear and `b`
has it set. -/
theorem xor_top {a b : Nat} (hab : a < b) :
    a / 2 ^ (Nat.log2 (a ^^^ b) + 1) = b / 2 ^ (Nat.log2 (a ^^^ b) + 1) ∧
      a / 2 ^ Nat.log2 (a ^^^ b) % 2 = 0 ∧ b / 2 ^ Nat.log2 (a ^^^ b) % 2 = 1 := by
  have hx : a ^^^ b ≠ 0 := by
    intro h; have : a = b := Nat.eq_of_testBit_eq (fun i => by
      have := congrArg (fun x => Nat.testBit x i) h
      simp only [Nat.testBit_xor, Nat.zero_testBit] at this
      revert this; cases Nat.testBit a i <;> cases Nat.testBit b i <;> simp)
    omega
  set t := Nat.log2 (a ^^^ b)
  have h1 : a / 2 ^ (t + 1) = b / 2 ^ (t + 1) := by
    have hlt : (a ^^^ b) / 2 ^ (t + 1) = 0 := Nat.div_eq_of_lt Nat.lt_log2_self
    rw [← Nat.shiftRight_eq_div_pow, Nat.shiftRight_xor_distrib] at hlt
    rw [← Nat.shiftRight_eq_div_pow, ← Nat.shiftRight_eq_div_pow]
    exact Nat.eq_of_testBit_eq (fun i => by
      have := congrArg (fun x => Nat.testBit x i) hlt
      simp only [Nat.testBit_xor, Nat.zero_testBit] at this
      revert this; cases Nat.testBit (a >>> (t + 1)) i <;> cases Nat.testBit (b >>> (t + 1)) i <;> simp)
  have h2 : a / 2 ^ t % 2 ≠ b / 2 ^ t % 2 := by
    have := Nat.testBit_log2 hx
    rw [Nat.testBit_xor, Nat.testBit_eq_decide_div_mod_eq, Nat.testBit_eq_decide_div_mod_eq] at this
    intro h; rw [h] at this; simp at this; exact this Iff.rfl
  have ha := div_pow_succ a t
  have hb := div_pow_succ b t
  have hle : a / 2 ^ t ≤ b / 2 ^ t := Nat.div_le_div_right (by omega)
  refine ⟨h1, ?_, ?_⟩ <;> omega

/-- `2^14 ||| v = 2^14 + v` for `v < 2^14`. -/
theorem or_porsT {v : Nat} (hv : v < porsT) : porsT ||| v = porsT + v := by
  have := Nat.two_pow_add_eq_or_of_lt hv 1
  rw [Nat.mul_one] at this; exact this.symm

/-- The ancestor of leaf `v` at height `g` (heap index). -/
def anc (v g : Nat) : Nat := (porsT + v) / 2 ^ g

theorem anc_bounds {v g : Nat} (hv : v < porsT) (hg : g ≤ porsH) :
    2 ^ (porsH - g) ≤ anc v g ∧ anc v g < 2 ^ (porsH + 1 - g) := by
  unfold anc porsT at *
  have e1 : 2 ^ porsH = 2 ^ (porsH - g) * 2 ^ g := by rw [← Nat.pow_add]; congr 1; omega
  have e2 : 2 ^ (porsH + 1) = 2 ^ (porsH + 1 - g) * 2 ^ g := by rw [← Nat.pow_add]; congr 1; omega
  have hp : 0 < 2 ^ g := Nat.two_pow_pos g
  constructor
  · rw [Nat.le_div_iff_mul_le hp]; rw [e1] at *; omega
  · rw [Nat.div_lt_iff_lt_mul hp]
    have : 2 ^ (porsH + 1) = 2 * 2 ^ porsH := by rw [Nat.pow_succ]; ring
    rw [← e2]; omega

theorem anc_pos {v g : Nat} (hv : v < porsT) (hg : g ≤ porsH) : 0 < anc v g :=
  lt_of_lt_of_le (Nat.two_pow_pos _) (anc_bounds hv hg).1

theorem anc_inj {v g h : Nat} (hv : v < porsT) (hg : g ≤ porsH) (hh : h ≤ porsH)
    (he : anc v g = anc v h) : g = h := by
  obtain ⟨a1, a2⟩ := anc_bounds hv hg
  obtain ⟨b1, b2⟩ := anc_bounds hv hh
  rw [he] at a1 a2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · have : 2 ^ (porsH + 1 - h) ≤ 2 ^ (porsH - g) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have : 2 ^ (porsH + 1 - g) ≤ 2 ^ (porsH - h) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem anc_succ (v g : Nat) : anc v (g + 1) = anc v g / 2 := by
  unfold anc; rw [Nat.pow_succ, Nat.div_div_eq_div_mul]

theorem anc_zero (v : Nat) : anc v 0 = porsT + v := by simp [anc]

theorem anc_split {v g : Nat} (hg : g ≤ porsH) : anc v g = 2 ^ (porsH - g) + v / 2 ^ g := by
  unfold anc porsT
  have : 2 ^ porsH = 2 ^ (porsH - g) * 2 ^ g := by rw [← Nat.pow_add]; congr 1; omega
  rw [this, Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.two_pow_pos g), Nat.add_comm]

/-! ## The inner loop -/

theorem filter_ge_step {G : List Nat} (hG : G.Pairwise (· < ·)) (h : Nat) :
    G.filter (fun g => decide (h ≤ g)) =
      if h ∈ G then h :: G.filter (fun g => decide (h + 1 ≤ g)) else G.filter (fun g => decide (h + 1 ≤ g)) := by
  induction G with
  | nil => simp
  | cons g G ih =>
    rw [List.pairwise_cons] at hG
    have hc : ∀ h', h' ≤ g + 1 → G.filter (fun x => decide (h' ≤ x)) = G := by
      intro h' hh'
      rw [List.filter_eq_self]; intro x hx; have := hG.1 x hx; simp only [decide_eq_true_eq]; omega
    rcases Nat.lt_trichotomy g h with hlt | heq | hgt
    · rw [List.filter_cons_of_neg (by simp; omega), List.filter_cons_of_neg (by simp; omega), ih hG.2]
      have : h ∈ g :: G ↔ h ∈ G := by simp; omega
      simp only [this]
    · subst heq
      rw [if_pos List.mem_cons_self, List.filter_cons_of_pos (by simp),
        List.filter_cons_of_neg (by simp), hc g (by omega), hc (g + 1) (by omega)]
    · rw [List.filter_cons_of_pos (by simp; omega), List.filter_cons_of_pos (by simp; omega),
        hc h (by omega), hc (h + 1) (by omega)]
      have : h ∉ g :: G := by
        simp only [List.mem_cons, not_or]; exact ⟨by omega, fun hm => by have := hG.1 h hm; omega⟩
      rw [if_neg this]

/-- The inner loop of a leaf (heights `0 .. h-1`) from a stack of ancestors of `v` at the heights
`G` (strictly increasing, top first). -/
theorem inner_fold {v : Nat} (hv : v < porsT) {G : List Nat} (hG : G.Pairwise (· < ·))
    (hG14 : ∀ g ∈ G, g ≤ porsH) (st : SchedState) (hst : st.stack = G.map (anc v)) :
    ∀ h ≤ porsH,
      ((List.range h).foldl schedStep (st, porsT + v, 0, (porsT + v) % 2)).1.stack =
          (G.filter (fun g => decide (h ≤ g))).map (anc v) ∧
        ((List.range h).foldl schedStep (st, porsT + v, 0, (porsT + v) % 2)).2.1 = anc v h ∧
        ((List.range h).foldl schedStep (st, porsT + v, 0, (porsT + v) % 2)).1.reads.length + G.length =
          st.reads.length + h + (G.filter (fun g => decide (h ≤ g))).length ∧
        ((List.range h).foldl schedStep (st, porsT + v, 0, (porsT + v) % 2)).1.segs.length +
          (G.filter (fun g => decide (h ≤ g))).length = st.segs.length + G.length := by
  intro h
  induction h with
  | zero =>
    intro _
    simp only [List.range_zero, List.foldl_nil, anc_zero]
    have : G.filter (fun g => decide (0 ≤ g)) = G := by rw [List.filter_eq_self]; simp
    rw [this]; exact ⟨hst, by simp, by omega, by omega⟩
  | succ h ih =>
    intro hh
    obtain ⟨h1, h2, h3, h4⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    generalize (List.range h).foldl schedStep (st, porsT + v, 0, (porsT + v) % 2) = x at h1 h2 h3 h4 ⊢
    obtain ⟨st', E, cnt, t⟩ := x
    simp only at h1 h2 h3 h4
    have hf := filter_ge_step hG h
    by_cases hm : h ∈ G
    · rw [if_pos hm] at hf
      rw [hf, List.map_cons] at h1
      simp only [schedStep, h1, h2, ↓reduceIte]
      rw [hf] at h3 h4; simp only [List.length_cons] at h3 h4
      refine ⟨by simp, by simp [anc_succ], ?_, ?_⟩
      · omega
      · simp only [List.length_append, List.length_singleton]; omega
    · rw [if_neg hm] at hf
      rw [hf] at h1 h3 h4
      have hfold : schedStep (st', E, cnt, t) h =
          ({ st' with reads := st'.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)] }, E / 2, cnt + 1, t) := by
        simp only [schedStep]
        split
        · rename_i Q rest hQ
          rw [if_neg]
          intro hQE
          rw [h1] at hQ
          have hmem : Q ∈ (G.filter (fun g => decide (h + 1 ≤ g))).map (anc v) := by rw [hQ]; simp
          obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hmem
          rw [List.mem_filter] at hg
          have := anc_inj hv (hG14 g hg.1) (by omega) (hQE.trans h2)
          simp at hg; omega
        · rfl
      rw [hfold]
      refine ⟨h1, by rw [h2, anc_succ], ?_, h4⟩
      simp only [List.length_append, List.length_singleton]; omega

/-! ## Leaves -/

/-- The top height of leaf `s`. -/
def topOf (vs : List Nat) (s : Nat) : Nat :=
  if s + 1 < vs.length then bitLen (vs.getD s 0 ^^^ vs.getD (s + 1) 0) - 1 else porsH

/-- Stack invariant at the start of leaf `s`. -/
def LeafInv (vs : List Nat) (s : Nat) (st : SchedState) : Prop :=
  ∃ G : List Nat, G.Pairwise (· < ·) ∧ (∀ g ∈ G, g < porsH ∧ vs.getD s 0 / 2 ^ g % 2 = 1) ∧
    st.stack = G.map (anc (vs.getD s 0)) ∧
    st.reads.length + s = ((List.range s).map (topOf vs)).sum + G.length ∧
    st.segs.length + G.length = 2 * s

/-- Sorted distinct leaves below `2^14`. -/
structure Leaves (vs : List Nat) : Prop where
  sorted : vs.Pairwise (· < ·)
  lt : ∀ x ∈ vs, x < porsT

theorem Leaves.getD_lt {vs : List Nat} (h : Leaves vs) (i : Nat) : vs.getD i 0 < porsT := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : vs[i]? with
  | none => simp [porsT]
  | some x => exact h.lt x (List.mem_of_getElem? hi)

theorem Leaves.getD_mono {vs : List Nat} (h : Leaves vs) {i j : Nat} (hij : i < j) (hj : j < vs.length) :
    vs.getD i 0 < vs.getD j 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem (by omega : i < vs.length)]
  exact List.pairwise_iff_getElem.mp h.sorted i j (by omega) hj hij

theorem xor_lt_porsT {a b : Nat} (ha : a < porsT) (hb : b < porsT) : a ^^^ b < porsT :=
  Nat.xor_lt_two_pow ha hb

theorem leaf_step {vs : List Nat} (hv : Leaves vs) {s : Nat} (hs1 : s + 1 < vs.length)
    {st : SchedState} (h : LeafInv vs s st) : LeafInv vs (s + 1) (schedLeaf vs st s) := by
  obtain ⟨G, hG, hGb, hst, hr, hsg⟩ := h
  set a := vs.getD s 0 with ha
  set b := vs.getD (s + 1) 0 with hb
  have hab : a < b := hv.getD_mono (by omega) hs1
  have haT : a < porsT := hv.getD_lt s
  have hbT : b < porsT := hv.getD_lt (s + 1)
  have hx : a ^^^ b ≠ 0 := by
    intro h0; have : a = b := Nat.eq_of_testBit_eq (fun i => by
      have := congrArg (fun x => Nat.testBit x i) h0
      simp only [Nat.testBit_xor, Nat.zero_testBit] at this
      revert this; cases Nat.testBit a i <;> cases Nat.testBit b i <;> simp)
    omega
  set t := Nat.log2 (a ^^^ b) with ht
  have htop : topOf vs s = t := by
    simp only [topOf, if_pos hs1, ← ha, ← hb, bitLen_pos hx]; omega
  have ht14 : t < porsH := by
    have := bitLen_le (xor_lt_porsT haT hbT); rw [bitLen_pos hx] at this
    omega
  obtain ⟨x1, x2, x3⟩ := xor_top hab
  rw [← ht] at x1 x2 x3
  have htG : t ∉ G := fun hm => by have := (hGb t hm).2; omega
  obtain ⟨i1, i2, i3, i4⟩ := inner_fold haT hG (fun g hg => le_of_lt (hGb g hg).1) st hst t (by omega)
  -- the new stack heights
  set F := G.filter (fun g => decide (t ≤ g)) with hF
  have hFG : ∀ g ∈ F, g ∈ G ∧ t < g := by
    intro g hg; rw [List.mem_filter] at hg; simp only [decide_eq_true_eq] at hg
    exact ⟨hg.1, by rcases Nat.lt_or_eq_of_le hg.2 with h' | h'; exact h'; subst h'; exact absurd hg.1 htG⟩
  have hdiv : ∀ g, t < g → a / 2 ^ g = b / 2 ^ g := by
    intro g hg
    have e : 2 ^ g = 2 ^ (t + 1) * 2 ^ (g - (t + 1)) := by rw [← Nat.pow_add]; congr 1; omega
    rw [e, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, x1]
  unfold schedLeaf
  simp only [if_pos hs1]
  rw [or_porsT haT, show bitLen (vs.getD s 0 ^^^ vs.getD (s + 1) 0) - 1 = t by
    rw [← ha, ← hb, bitLen_pos hx]; omega]
  generalize (List.range t).foldl schedStep (st, porsT + a, 0, (porsT + a) % 2) = y at i1 i2 i3 i4 ⊢
  obtain ⟨st', E, cnt, tt⟩ := y
  simp only at i1 i2 i3 i4 ⊢
  refine ⟨t :: F, ?_, ?_, ?_, ?_, ?_⟩
  · rw [List.pairwise_cons]
    exact ⟨fun g hg => (hFG g hg).2, hG.sublist List.filter_sublist⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨ht14, x3⟩
    · obtain ⟨hgG, htg⟩ := hFG g hg
      exact ⟨(hGb g hgG).1, by rw [← hdiv g htg]; exact (hGb g hgG).2⟩
  · dsimp only
    rw [List.map_cons, i1, i2, ← hb]
    congr 1
    · rw [anc_split (by omega), anc_split (by omega)]
      have hev : (2 ^ (porsH - t) + a / 2 ^ t) % 2 = 0 := by
        have : 2 ^ (porsH - t) % 2 = 0 := by
          rw [show porsH - t = (porsH - t - 1) + 1 by omega, Nat.pow_succ]; omega
        omega
      rw [Nat.xor_one_of_even (Nat.even_iff.mpr hev)]
      have := div_pow_succ a t; have := div_pow_succ b t; omega
    · apply List.map_congr_left
      intro g hg
      rw [anc_split (by have := (hGb g (hFG g hg).1).1; omega),
        anc_split (by have := (hGb g (hFG g hg).1).1; omega), hdiv g (hFG g hg).2]
  · dsimp only
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      htop, List.length_cons]
    omega
  · dsimp only
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem leaf_iter {vs : List Nat} (hv : Leaves vs) :
    ∀ s, s + 1 ≤ vs.length → LeafInv vs s ((List.range s).foldl (schedLeaf vs) ⟨[], [], []⟩) := by
  intro s
  induction s with
  | zero => intro _; exact ⟨[], List.Pairwise.nil, by simp, rfl, by simp, by simp⟩
  | succ s ih =>
    intro hs
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact leaf_step hv (by omega) (ih (by omega))

/-- The last leaf empties the stack. -/
theorem leaf_last {vs : List Nat} (hv : Leaves vs) {s : Nat} (hs : s + 1 = vs.length)
    {st : SchedState} (h : LeafInv vs s st) :
    (schedLeaf vs st s).stack = [] ∧
      (schedLeaf vs st s).reads.length + s = ((List.range (s + 1)).map (topOf vs)).sum ∧
      (schedLeaf vs st s).segs.length = 2 * s + 1 := by
  obtain ⟨G, hG, hGb, hst, hr, hsg⟩ := h
  have haT : vs.getD s 0 < porsT := hv.getD_lt s
  obtain ⟨i1, i2, i3, i4⟩ := inner_fold haT hG (fun g hg => le_of_lt (hGb g hg).1) st hst porsH le_rfl
  have hF : G.filter (fun g => decide (porsH ≤ g)) = [] := by
    rw [List.filter_eq_nil_iff]; intro g hg; have := (hGb g hg).1; simp; omega
  rw [hF] at i1 i3 i4
  have htop : topOf vs s = porsH := by simp [topOf, show ¬ (s + 1 < vs.length) by omega]
  unfold schedLeaf
  simp only [show ¬ (s + 1 < vs.length) by omega, if_false]
  rw [or_porsT haT]
  generalize (List.range porsH).foldl schedStep (st, porsT + vs.getD s 0, 0, (porsT + vs.getD s 0) % 2) = y
    at i1 i2 i3 i4 ⊢
  obtain ⟨st', E, cnt, tt⟩ := y
  simp only [List.map_nil, List.length_nil] at i1 i2 i3 i4 ⊢
  refine ⟨i1, ?_, ?_⟩
  · rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
      htop]
    omega
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega

theorem zipWith_tail_eq (f : Nat → Nat → Nat) (l : List Nat) :
    List.zipWith f l l.tail = (List.range (l.length - 1)).map (fun j => f (l.getD j 0) (l.getD (j + 1) 0)) := by
  apply List.ext_getElem
  · simp
  · intro j h1 h2
    simp only [List.getElem_zipWith, List.getElem_map, List.getElem_range, List.getElem_tail]
    simp at h2
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      List.getElem?_eq_getElem (by omega)]
    rfl

theorem sum_sub_one (f : Nat → Nat) (n : Nat) (hf : ∀ j < n, 1 ≤ f j) :
    ((List.range n).map (fun j => f j - 1)).sum + n = ((List.range n).map f).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.sum_append, List.sum_append]
    simp only [List.map_singleton, List.sum_singleton]
    have := ih (fun j hj => hf j (by omega)); have := hf n (by omega); omega

/-- **Schedule counts**: on sorted distinct leaves below `2^14`, `schedule` emits `2 k - 1`
segments and exactly `octopusSize vs` reads. -/
theorem schedule_counts {vs : List Nat} (hv : Leaves vs) (hk : 0 < vs.length) :
    (schedule vs).2.length = octopusSize vs ∧ (schedule vs).1.length = 2 * vs.length - 1 := by
  obtain ⟨k, hk'⟩ : ∃ k, vs.length = k + 1 := ⟨vs.length - 1, by omega⟩
  have hinv := leaf_iter hv k (by omega)
  obtain ⟨l1, l2, l3⟩ := leaf_last hv hk'.symm hinv
  unfold schedule
  rw [hk', List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only
  refine ⟨?_, by rw [l3]; omega⟩
  -- the sum of the tops
  have htops : ((List.range (k + 1)).map (topOf vs)).sum =
      ((List.range k).map (fun j => bitLen (vs.getD j 0 ^^^ vs.getD (j + 1) 0) - 1)).sum + porsH := by
    rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton]
    congr 1
    · congr 1; apply List.map_congr_left; intro j hj
      rw [List.mem_range] at hj; simp [topOf, show j + 1 < vs.length by omega]
    · simp [topOf, hk']
  have hpos : ∀ j < k, 1 ≤ bitLen (vs.getD j 0 ^^^ vs.getD (j + 1) 0) := by
    intro j hj
    have hlt := hv.getD_mono (by omega : j < j + 1) (by omega : j + 1 < vs.length)
    have hx : vs.getD j 0 ^^^ vs.getD (j + 1) 0 ≠ 0 := by
      intro h0
      have : vs.getD j 0 = vs.getD (j + 1) 0 := Nat.eq_of_testBit_eq (fun i => by
        have := congrArg (fun x => Nat.testBit x i) h0
        simp only [Nat.testBit_xor, Nat.zero_testBit] at this
        revert this; cases Nat.testBit (vs.getD j 0) i <;> cases Nat.testBit (vs.getD (j + 1) 0) i <;> simp)
      omega
    rw [bitLen_pos hx]; omega
  have hs := sum_sub_one (fun j => bitLen (vs.getD j 0 ^^^ vs.getD (j + 1) 0)) k hpos
  unfold octopusSize
  rw [zipWith_tail_eq, hk', show k + 1 - 1 = k by omega]
  rw [htops] at l2
  unfold porsH at *
  omega

end SigGolfCandidate.Expand
