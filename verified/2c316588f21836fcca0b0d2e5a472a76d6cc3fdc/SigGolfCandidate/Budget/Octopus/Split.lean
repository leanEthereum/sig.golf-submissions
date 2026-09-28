import SigGolfCandidate.Budget.Octopus.Defs
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset

/-!
# PORS+FP admissibility: the octopus recursion and the generating polynomial

For a finite set `S ⊆ [0, 2^H)` let `oc H S = octH H (sort S)` (the `ref.octopus_size` formula
on the sorted list, tree height `H`). Splitting `S ⊆ [0, 2^(H+1))` by the top bit,
`S = L ∪ (R + 2^H)` with `L, R ⊆ [0, 2^H)` (`glue`), we show

* `oc (H+1) (L ∪ ∅') = oc H L + 1`, `oc (H+1) (∅ ∪ R') = oc H R + 1`,
  `oc (H+1) (L ∪ R') = oc H L + oc H R` (both nonempty)            (`oc_glue_*`)

using `H + 2 + xorSum ≥ 2 |S|` (`two_card_le_E`, so the natural subtraction in `octH` never
truncates). Hence the generating polynomial `Q y H = ∑_{∅ ≠ S ⊆ [0, 2^H)} y^(oc S) X^|S|` satisfies
`Q y 0 = X` and `Q y (H+1) = 2 y Q + Q^2` (`Q_succ`), and `(Q y H).coeff j` is the sum of
`y^(oc S)` over the `j`-subsets (`coeff_Q`).
-/

namespace SigGolfCandidate.Budget.Octopus
open Finset Polynomial

/-! ## Bits -/

theorem testBit_add_two_pow {z H : ℕ} (hz : z < 2 ^ H) (i : ℕ) :
    (z + 2 ^ H).testBit i = (decide (i = H) || z.testBit i) := by
  rw [Nat.add_comm]
  rcases lt_trichotomy i H with h | rfl | h
  · rw [Nat.testBit_two_pow_add_gt h]; simp [h.ne]
  · rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hz]; simp
  · have hH : 2 ^ (H + 1) ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) h
    have h1 : 2 ^ H + z < 2 ^ i := by rw [pow_succ] at hH; omega
    have h2 : z < 2 ^ i := by rw [pow_succ] at hH; omega
    rw [Nat.testBit_lt_two_pow h1, Nat.testBit_lt_two_pow h2]
    simp [h.ne']

theorem xor_shift_shift {x y H : ℕ} (hx : x < 2 ^ H) (hy : y < 2 ^ H) :
    (x + 2 ^ H) ^^^ (y + 2 ^ H) = x ^^^ y := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_xor, testBit_add_two_pow hx, testBit_add_two_pow hy]
  by_cases h : i = H
  · subst h; simp [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]
  · simp [h]

theorem xor_cross {x y H : ℕ} (hx : x < 2 ^ H) (hy : y < 2 ^ H) :
    x ^^^ (y + 2 ^ H) = (x ^^^ y) + 2 ^ H := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, testBit_add_two_pow hy, testBit_add_two_pow (Nat.xor_lt_two_pow hx hy),
    Nat.testBit_xor]
  by_cases h : i = H
  · subst h; simp [Nat.testBit_lt_two_pow hx, Nat.testBit_lt_two_pow hy]
  · simp [h]

theorem bitLen_add_two_pow {z H : ℕ} (hz : z < 2 ^ H) : bitLen (z + 2 ^ H) = H + 1 := by
  unfold bitLen
  have h2 : z + 2 ^ H < 2 ^ (H + 1) := by rw [pow_succ]; omega
  rw [if_neg (by positivity),
    (Nat.log2_eq_iff (n := z + 2 ^ H) (k := H) (by positivity)).2 ⟨by omega, h2⟩]

theorem bitLen_cross {x y H : ℕ} (hx : x < 2 ^ H) (hy : y < 2 ^ H) :
    bitLen (x ^^^ (y + 2 ^ H)) = H + 1 := by
  rw [xor_cross hx hy, bitLen_add_two_pow (Nat.xor_lt_two_pow hx hy)]

/-! ## `xorSum` -/

@[simp] theorem xorSum_nil : xorSum [] = 0 := rfl
@[simp] theorem xorSum_single (a : ℕ) : xorSum [a] = 0 := rfl

theorem xorSum_cons_cons (a b : ℕ) (t : List ℕ) :
    xorSum (a :: b :: t) = bitLen (a ^^^ b) + xorSum (b :: t) := by
  simp [xorSum]

theorem xorSum_append (a : List ℕ) (x y : ℕ) (b : List ℕ) :
    xorSum (a ++ x :: y :: b) = xorSum (a ++ [x]) + bitLen (x ^^^ y) + xorSum (y :: b) := by
  induction a with
  | nil => simp [xorSum_cons_cons]
  | cons c a ih =>
    cases a with
    | nil => simp [xorSum_cons_cons]; omega
    | cons d a =>
      simp only [List.cons_append] at ih ⊢
      rw [xorSum_cons_cons, ih, xorSum_cons_cons]; omega

theorem xorSum_map_shift {H : ℕ} : ∀ (l : List ℕ), (∀ z ∈ l, z < 2 ^ H) →
    xorSum (l.map (· + 2 ^ H)) = xorSum l
  | [], _ => rfl
  | [_], _ => rfl
  | a :: b :: t, h => by
    have ih := xorSum_map_shift (b :: t) (fun z hz => h z (List.mem_cons_of_mem _ hz))
    simp only [List.map_cons] at ih ⊢
    rw [xorSum_cons_cons, xorSum_cons_cons, ih,
      xor_shift_shift (h a (by simp)) (h b (by simp))]

/-! ## Splitting a set by the top bit -/

/-- `L ∪ (R + 2^H)`. -/
def glue (H : ℕ) (L R : Finset ℕ) : Finset ℕ := L ∪ R.map (addRightEmbedding (2 ^ H))

/-- The lower half. -/
def lo (H : ℕ) (S : Finset ℕ) : Finset ℕ := S.filter (· < 2 ^ H)

/-- The upper half, shifted down. -/
def hi (H : ℕ) (S : Finset ℕ) : Finset ℕ := (S.filter (2 ^ H ≤ ·)).image (· - 2 ^ H)

/-- Subsets of `[0, 2^H)`. -/
def Below (H : ℕ) (S : Finset ℕ) : Prop := ∀ x ∈ S, x < 2 ^ H

theorem below_iff (H : ℕ) (S : Finset ℕ) : Below H S ↔ S ∈ (range (2 ^ H)).powerset := by
  simp [Below, subset_iff]

theorem mem_glue {H : ℕ} {L R : Finset ℕ} {x : ℕ} :
    x ∈ glue H L R ↔ x ∈ L ∨ (2 ^ H ≤ x ∧ x - 2 ^ H ∈ R) := by
  simp only [glue, mem_union, mem_map, addRightEmbedding_apply]
  constructor
  · rintro (h | ⟨a, ha, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨by omega, by simpa using ha⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨_, h2, by omega⟩

theorem glue_below {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R) :
    Below (H + 1) (glue H L R) := by
  intro x hx
  rw [mem_glue] at hx
  rw [pow_succ]
  rcases hx with h | ⟨h1, h2⟩
  · have := hL x h; omega
  · have := hR _ h2; omega

theorem lo_below (H : ℕ) (S : Finset ℕ) : Below H (lo H S) := by
  intro x hx; simp only [lo, mem_filter] at hx; exact hx.2

theorem hi_below {H : ℕ} {S : Finset ℕ} (hS : Below (H + 1) S) : Below H (hi H S) := by
  intro x hx
  simp only [hi, mem_image, mem_filter] at hx
  obtain ⟨a, ⟨ha, h1⟩, rfl⟩ := hx
  have := hS a ha; rw [pow_succ] at this; omega

theorem glue_lo_hi {H : ℕ} {S : Finset ℕ} : glue H (lo H S) (hi H S) = S := by
  ext x
  rw [mem_glue]
  simp only [lo, hi, mem_filter, mem_image]
  constructor
  · rintro (⟨h, _⟩ | ⟨h1, a, ⟨ha, h2⟩, h3⟩)
    · exact h
    · have : a = x := by omega
      exact this ▸ ha
  · intro h
    by_cases hx : x < 2 ^ H
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨by omega, x, ⟨h, by omega⟩, rfl⟩

theorem lo_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) : lo H (glue H L R) = L := by
  ext x
  simp only [lo, mem_filter, mem_glue]
  constructor
  · rintro ⟨h | ⟨h1, _⟩, h2⟩
    · exact h
    · omega
  · intro h; exact ⟨Or.inl h, hL x h⟩

theorem hi_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) : hi H (glue H L R) = R := by
  ext x
  simp only [hi, mem_image, mem_filter, mem_glue]
  constructor
  · rintro ⟨a, ⟨h | ⟨h1, h2⟩, h3⟩, rfl⟩
    · have := hL a h; omega
    · exact h2
  · intro h
    exact ⟨x + 2 ^ H, ⟨Or.inr ⟨by omega, by simpa using h⟩, by omega⟩, by omega⟩

theorem card_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) :
    (glue H L R).card = L.card + R.card := by
  unfold glue
  rw [card_union_of_disjoint, card_map]
  rw [disjoint_left]
  intro x hx hx'
  simp only [mem_map, addRightEmbedding_apply] at hx'
  obtain ⟨a, _, rfl⟩ := hx'
  have := hL _ hx; omega

theorem glue_empty_empty (H : ℕ) : glue H ∅ ∅ = ∅ := by simp [glue]

theorem glue_ne_empty_left {H : ℕ} {L R : Finset ℕ} (h : L ≠ ∅) : glue H L R ≠ ∅ := by
  intro h'
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h
  have : x ∈ glue H L R := mem_glue.mpr (Or.inl hx)
  rw [h'] at this; simp at this

theorem glue_ne_empty_right {H : ℕ} {L R : Finset ℕ} (h : R ≠ ∅) : glue H L R ≠ ∅ := by
  intro h'
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h
  have : x + 2 ^ H ∈ glue H L R := mem_glue.mpr (Or.inr ⟨by omega, by simpa using hx⟩)
  rw [h'] at this; simp at this

/-- Sorting a glued set. -/
theorem sort_glue {H : ℕ} {L R : Finset ℕ} (hL : Below H L) :
    (glue H L R).sort = L.sort ++ R.sort.map (· + 2 ^ H) := by
  apply List.Pairwise.eq_of_mem_iff (r := (· < ·)) (sortedLT_sort _).pairwise
  · rw [List.pairwise_append, List.pairwise_map]
    refine ⟨(sortedLT_sort _).pairwise, (sortedLT_sort _).pairwise.imp (by omega), ?_⟩
    intro a ha b hb
    rw [mem_sort] at ha
    simp only [List.mem_map, mem_sort] at hb
    obtain ⟨c, _, rfl⟩ := hb
    have := hL a ha; omega
  · intro x
    simp only [mem_sort, mem_glue, List.mem_append, List.mem_map]
    constructor
    · rintro (h | ⟨h1, h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨x - 2 ^ H, h2, by omega⟩
    · rintro (h | ⟨c, hc, rfl⟩)
      · exact Or.inl h
      · exact Or.inr ⟨by omega, by simpa using hc⟩

/-! ## The octopus recursion -/

/-- `H + 2 + xorSum (sort S)`. -/
def E (H : ℕ) (S : Finset ℕ) : ℕ := H + 2 + xorSum S.sort

/-- The octopus size of a set (sorted). -/
def oc (H : ℕ) (S : Finset ℕ) : ℕ := octH H S.sort

theorem oc_eq (H : ℕ) (S : Finset ℕ) : oc H S = E H S - 2 * S.card := by
  simp [oc, octH, E, length_sort]

theorem E_glue_left {H : ℕ} {L : Finset ℕ} (hL : Below H L) :
    E (H + 1) (glue H L ∅) = E H L + 1 := by
  unfold E
  rw [sort_glue hL]
  simp; omega

theorem E_glue_right {H : ℕ} {R : Finset ℕ} (hR : Below H R) :
    E (H + 1) (glue H ∅ R) = E H R + 1 := by
  unfold E
  rw [sort_glue (by simp [Below])]
  simp only [sort_empty, List.nil_append]
  rw [xorSum_map_shift _ (fun z hz => hR z ((mem_sort _).mp hz))]; omega

theorem E_glue_both {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R)
    (hL0 : L ≠ ∅) (hR0 : R ≠ ∅) : E (H + 1) (glue H L R) = E H L + E H R := by
  unfold E
  rw [sort_glue hL]
  rcases List.eq_nil_or_concat L.sort with h | ⟨a, x, hx⟩
  · exact absurd (by simpa using congrArg List.toFinset h) hL0
  rw [List.concat_eq_append] at hx
  cases hy : R.sort with
  | nil => exact absurd (by simpa using congrArg List.toFinset hy) hR0
  | cons y b =>
    have hxL : x ∈ L := by rw [← mem_sort (r := (· ≤ ·)), hx]; simp
    have hyR : y ∈ R := by rw [← mem_sort (r := (· ≤ ·)), hy]; simp
    have hb : ∀ z ∈ y :: b, z < 2 ^ H := fun z hz => hR z (by rw [← mem_sort (r := (· ≤ ·)), hy]; exact hz)
    rw [hx, List.map_cons, List.append_assoc, List.singleton_append, xorSum_append,
      bitLen_cross (hL x hxL) (hR y hyR)]
    have := xorSum_map_shift (y :: b) hb
    rw [List.map_cons] at this
    rw [this]; omega

theorem below_zero {S : Finset ℕ} (hS : Below 0 S) (h0 : S ≠ ∅) : S = {0} := by
  obtain ⟨x, hx⟩ := nonempty_iff_ne_empty.mpr h0
  ext y
  simp only [mem_singleton]
  constructor
  · intro hy; have := hS y hy; simp at this; exact this
  · rintro rfl; have := hS x hx; simp at this; exact this ▸ hx

/-- The octopus formula never truncates: `2 |S| ≤ H + 2 + xorSum (sort S)`. -/
theorem two_card_le_E : ∀ (H : ℕ) (S : Finset ℕ), Below H S → S ≠ ∅ → 2 * S.card ≤ E H S
  | 0, S, hS, h0 => by
    rw [below_zero hS h0]; simp [E]
  | H + 1, S, hS, h0 => by
    rw [← glue_lo_hi (H := H) (S := S)] at h0 ⊢
    have hL := lo_below H S
    have hR := hi_below hS
    rw [card_glue hL]
    by_cases hL0 : lo H S = ∅
    · have hR0 : hi H S ≠ ∅ := fun h => h0 (by rw [hL0, h, glue_empty_empty])
      have := two_card_le_E H _ hR hR0
      rw [hL0, E_glue_right hR]; simp; omega
    · by_cases hR0 : hi H S = ∅
      · have := two_card_le_E H _ hL hL0
        rw [hR0, E_glue_left hL]; simp; omega
      · have h1 := two_card_le_E H _ hL hL0
        have h2 := two_card_le_E H _ hR hR0
        rw [E_glue_both hL hR hL0 hR0]; omega

theorem oc_glue_left {H : ℕ} {L : Finset ℕ} (hL : Below H L) (hL0 : L ≠ ∅) :
    oc (H + 1) (glue H L ∅) = oc H L + 1 := by
  have := two_card_le_E H L hL hL0
  rw [oc_eq, oc_eq, E_glue_left hL, card_glue hL]; simp; omega

theorem oc_glue_right {H : ℕ} {R : Finset ℕ} (hR : Below H R) (hR0 : R ≠ ∅) :
    oc (H + 1) (glue H ∅ R) = oc H R + 1 := by
  have := two_card_le_E H R hR hR0
  rw [oc_eq, oc_eq, E_glue_right hR, card_glue (by simp [Below])]; simp; omega

theorem oc_glue_both {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R)
    (hL0 : L ≠ ∅) (hR0 : R ≠ ∅) : oc (H + 1) (glue H L R) = oc H L + oc H R := by
  have h1 := two_card_le_E H L hL hL0
  have h2 := two_card_le_E H R hR hR0
  rw [oc_eq, oc_eq, oc_eq, E_glue_both hL hR hL0 hR0, card_glue hL]; omega

/-! ## Sums over subsets -/

theorem sum_powerset_succ {M : Type*} [AddCommMonoid M] (H : ℕ) (f : Finset ℕ → M) :
    ∑ S ∈ (range (2 ^ (H + 1))).powerset, f S =
      ∑ L ∈ (range (2 ^ H)).powerset, ∑ R ∈ (range (2 ^ H)).powerset, f (glue H L R) := by
  rw [← sum_product']
  refine sum_nbij' (fun S => (lo H S, hi H S)) (fun p => glue H p.1 p.2) ?_ ?_ ?_ ?_ ?_
  · intro S hS
    rw [← below_iff] at hS
    rw [mem_product, ← below_iff, ← below_iff]
    exact ⟨lo_below H S, hi_below hS⟩
  · rintro ⟨L, R⟩ h
    rw [mem_product, ← below_iff, ← below_iff] at h
    rw [← below_iff]
    exact glue_below h.1 h.2
  · intro S _; exact glue_lo_hi
  · rintro ⟨L, R⟩ h
    rw [mem_product, ← below_iff, ← below_iff] at h
    simp only [lo_glue h.1, hi_glue h.1]
  · intro S _; simp only [glue_lo_hi]

/-! ## The generating polynomial -/

/-- `y^(oc S) X^|S|` for nonempty `S`. -/
noncomputable def mono (y H : ℕ) (S : Finset ℕ) : ℕ[X] :=
  if S = ∅ then 0 else monomial S.card (y ^ oc H S)

/-- `Q y H = ∑_{∅ ≠ S ⊆ [0, 2^H)} y^(oc S) X^|S|`. -/
noncomputable def Q (y H : ℕ) : ℕ[X] := ∑ S ∈ (range (2 ^ H)).powerset, mono y H S

theorem mono_glue (y : ℕ) {H : ℕ} {L R : Finset ℕ} (hL : Below H L) (hR : Below H R) :
    mono y (H + 1) (glue H L R) =
      (if R = ∅ then C y * mono y H L else 0) + (if L = ∅ then C y * mono y H R else 0) +
        mono y H L * mono y H R := by
  by_cases hL0 : L = ∅ <;> by_cases hR0 : R = ∅
  · subst hL0; subst hR0; simp [mono, glue_empty_empty]
  · subst hL0
    rw [mono, if_neg (glue_ne_empty_right hR0), card_glue hL, oc_glue_right hR hR0]
    simp only [mono, hR0, if_true, if_false, zero_mul, add_zero, zero_add, C_mul_monomial, pow_succ,
      mul_comm, card_empty]
  · subst hR0
    rw [mono, if_neg (glue_ne_empty_left hL0), card_glue hL, oc_glue_left hL hL0]
    simp only [mono, hL0, if_true, if_false, zero_mul, add_zero, C_mul_monomial, pow_succ,
      mul_comm, card_empty]
  · rw [mono, if_neg (glue_ne_empty_left hL0), card_glue hL, oc_glue_both hL hR hL0 hR0]
    simp [mono, hL0, hR0, monomial_mul_monomial, pow_add]

theorem Q_succ (y H : ℕ) : Q y (H + 1) = C (2 * y) * Q y H + Q y H * Q y H := by
  unfold Q
  rw [sum_powerset_succ]
  have hmem : ∀ S ∈ (range (2 ^ H)).powerset, Below H S := fun S hS => (below_iff H S).mpr hS
  rw [sum_congr rfl fun L hL => sum_congr rfl fun R hR => mono_glue y (hmem L hL) (hmem R hR)]
  simp only [sum_add_distrib]
  rw [sum_mul_sum]
  congr 1
  have e1 : ∀ L ∈ (range (2 ^ H)).powerset, ∑ R ∈ (range (2 ^ H)).powerset,
      (if R = ∅ then C y * mono y H L else 0) = C y * mono y H L := by
    intro L _; rw [sum_ite_eq']; simp
  rw [sum_congr rfl e1, sum_comm]
  rw [sum_congr rfl fun R _ => sum_ite_eq' (range (2 ^ H)).powerset ∅ (fun _ => C y * mono y H R)]
  simp only [empty_mem_powerset, if_true]
  rw [← mul_sum, ← two_mul, ← mul_assoc]
  congr 1
  simp [map_mul]

theorem Q_zero (y : ℕ) : Q y 0 = X := by
  unfold Q
  have : (range (2 ^ 0)).powerset = {∅, {0}} := by decide
  rw [this, sum_pair (by decide)]
  simp [mono, oc, octH, xorSum, X]

theorem coeff_Q_succ (y H j : ℕ) : (Q y (H + 1)).coeff j =
    2 * y * (Q y H).coeff j + ∑ i ∈ range (j + 1), (Q y H).coeff i * (Q y H).coeff (j - i) := by
  rw [Q_succ, coeff_add, coeff_C_mul, coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

theorem coeff_Q (y H j : ℕ) (hj : j ≠ 0) :
    (Q y H).coeff j = ∑ S ∈ powersetCard j (range (2 ^ H)), y ^ oc H S := by
  unfold Q
  rw [finsetSum_coeff, powersetCard_eq_filter, sum_filter]
  refine sum_congr rfl fun S _ => ?_
  unfold mono
  by_cases h : S = ∅
  · subst h; simp [Ne.symm hj]
  · simp [h, coeff_monomial]

end SigGolfCandidate.Budget.Octopus
