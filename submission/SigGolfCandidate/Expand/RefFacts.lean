import SigGolfCandidate.Expand.SchedRun

/-!
# `expand`: the machine's tests against `ref.expand`

For the machine's sorted key array `A` (a strictly increasing permutation of the keys
`keyOf N r = v_r · 256 + 8 r`):

* `vsOf_eq` : the leaf values `A s / 256` are `sortLeaves (leavesOf N)`;
* `passOK_iff` : the pass test is `ref.admissible`'s (distinct leaves, octopus `≤ 120`);
* `leaves_vsOf` : then the sorted leaves are strictly increasing below `2^14` (`Leaves`);
* `idxOf_lv` : the pi byte `A s mod 256 = 8 r` is `8 · (index of v_s in the digest)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

theorem keyOf_div (N r : Nat) (hr : r < 15) : keyOf N r / 256 = leafOf N r := by
  unfold keyOf; omega

theorem keysOf_map_div (N : Nat) : (keysOf N).map (· / 256) = leavesOf N := by
  unfold keysOf leavesOf
  rw [List.map_map]
  apply List.map_congr_left
  intro r hr; exact keyOf_div N r (by simpa [porsK] using hr)

/-- The sorted key array: a permutation of the keys, strictly increasing. -/
structure SortedKeys (N : Nat) (A : Nat → Nat) : Prop where
  perm : List.Perm ((List.range 15).map A) (keysOf N)
  lt : ∀ p < 15, A p < 2 ^ 22
  sorted : ∀ p q, p < q → q < 15 → A p < A q

theorem vsOf_perm {N : Nat} {A : Nat → Nat} (h : SortedKeys N A) : List.Perm (vsOf A) (leavesOf N) := by
  rw [← keysOf_map_div]
  have := h.perm.map (· / 256)
  rw [List.map_map] at this
  exact this

theorem vsOf_pairwise_le {A : Nat → Nat} (hs : ∀ p q, p < q → q < 15 → A p < A q) :
    (vsOf A).Pairwise (· ≤ ·) := by
  unfold vsOf
  rw [List.pairwise_map]
  refine List.pairwise_iff_getElem.mpr (fun i j hi hj hij => ?_)
  simp only [List.getElem_range]
  simp at hi hj
  have := hs i j hij hj
  unfold lv; exact Nat.div_le_div_right (le_of_lt this)

theorem vsOf_eq {N : Nat} {A : Nat → Nat} (h : SortedKeys N A) : vsOf A = sortLeaves (leavesOf N) := by
  apply List.Perm.eq_of_pairwise (le := (· ≤ ·)) (fun a b _ _ h1 h2 => Nat.le_antisymm h1 h2)
    (vsOf_pairwise_le h.sorted) (List.pairwise_insertionSort _ _)
  exact (vsOf_perm h).trans (List.perm_insertionSort _ _).symm

theorem lv_mono {A : Nat → Nat} (hs : ∀ p q, p < q → q < 15 → A p < A q) {p q : Nat} (hpq : p ≤ q)
    (hq : q < 15) : lv A p ≤ lv A q := by
  rcases Nat.eq_or_lt_of_le hpq with rfl | h
  · exact le_refl _
  · unfold lv; exact Nat.div_le_div_right (le_of_lt (hs p q h hq))

theorem nodup_iff {N : Nat} {A : Nat → Nat} (h : SortedKeys N A) :
    (leavesOf N).Nodup ↔ ∀ s < 14, lv A s ≠ lv A (s + 1) := by
  rw [← (vsOf_perm h).nodup_iff]
  constructor
  · intro hn s hs heq
    have := List.nodup_iff_injective_get.mp hn
    have h1 : (vsOf A).length = 15 := by simp [vsOf]
    have := @this ⟨s, by omega⟩ ⟨s + 1, by omega⟩ (by simp [vsOf, heq])
    simp at this
  · intro hd
    unfold vsOf
    refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
    simp only [List.mem_range] at ha hb
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
    · have h1 := lv_mono h.sorted (show a + 1 ≤ b by omega) hb
      have h2 := lv_mono h.sorted (show a ≤ a by omega) (show a < 15 by omega)
      have := lv_mono h.sorted (show a ≤ a + 1 by omega) (show a + 1 < 15 by omega)
      have := hd a (by omega)
      omega
    · have h1 := lv_mono h.sorted (show b + 1 ≤ a by omega) ha
      have := lv_mono h.sorted (show b ≤ b + 1 by omega) (show b + 1 < 15 by omega)
      have := hd b (by omega)
      omega

theorem octopus_vsOf (A : Nat → Nat) : octopusSize (vsOf A) = porsH + 2 + pairSum A 14 - 30 := by
  unfold octopusSize
  rw [zipWith_tail_eq]
  have hlen : (vsOf A).length = 15 := by simp [vsOf]
  have hs : ((List.range ((vsOf A).length - 1)).map
      (fun j => bitLen ((vsOf A).getD j 0 ^^^ (vsOf A).getD (j + 1) 0))).sum = pairSum A 14 := by
    rw [hlen]; unfold pairSum
    apply congrArg
    apply List.map_congr_left
    intro j hj; simp at hj
    unfold pairBits
    rw [vsOf_getD A j (by omega), vsOf_getD A (j + 1) (by omega)]
  rw [hs, hlen]

theorem passOK_iff {N : Nat} {A : Nat → Nat} (h : SortedKeys N A) :
    PassOK A ↔ (leavesOf N).Nodup ∧ octopusSize (sortLeaves (leavesOf N)) ≤ porsM := by
  rw [← vsOf_eq h, nodup_iff h, octopus_vsOf]
  unfold PassOK porsH porsM
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

theorem leaves_vsOf {A : Nat → Nat} (hs : ∀ p q, p < q → q < 15 → A p < A q) (hlt : ∀ p < 15, A p < 2 ^ 22)
    (hd : ∀ s < 14, lv A s ≠ lv A (s + 1)) : Leaves (vsOf A) := by
  refine ⟨?_, ?_⟩
  · unfold vsOf
    rw [List.pairwise_map]
    refine List.pairwise_iff_getElem.mpr (fun i j hi hj hij => ?_)
    simp only [List.getElem_range]
    simp at hi hj
    have h1 := lv_mono hs (show i + 1 ≤ j by omega) hj
    have h2 := lv_mono hs (show i ≤ i + 1 by omega) (show i + 1 < 15 by omega)
    have := hd i (by omega)
    omega
  · intro x hx
    simp only [vsOf, List.mem_map, List.mem_range] at hx
    obtain ⟨s, hs, rfl⟩ := hx
    exact lv_lt hlt hs

/-- The digest slot of the `s`-th smallest leaf: `A s mod 256 = 8 r`, `v_r = A s / 256`. -/
theorem idxOf_lv {N : Nat} {A : Nat → Nat} (h : SortedKeys N A) (hn : (leavesOf N).Nodup) (s : Nat)
    (hs : s < 15) : A s % 256 = 8 * (leavesOf N).idxOf (lv A s) := by
  have hmem : A s ∈ keysOf N := h.perm.subset (List.mem_map.mpr ⟨s, List.mem_range.mpr hs, rfl⟩)
  obtain ⟨r, hr, hrA⟩ := List.mem_map.mp hmem
  rw [List.mem_range] at hr
  rw [← hrA, keyOf_mod N r hr]
  unfold lv; rw [← hrA, keyOf_div N r hr]
  have hlen : (leavesOf N).length = 15 := by simp [leavesOf, porsK]
  have hget : (leavesOf N)[r]'(by omega) = leafOf N r := by simp [leavesOf]
  rw [← hget, hn.idxOf_getElem]

end SigGolfCandidate.Expand
