import SigGolfCandidate.SphincsSecurity.Proof.Fts.Octopus.Count
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Perm

/-!
# PORS+FP admissibility: tuples and digests

* `card_admissibleTuples`: the number of `v : Fin 15 → Fin (2^14)` that are injective with
  `octopusSize (sortLeaves [v_0, ..., v_14]) ≤ 120` is `15! * Nadm` (every admissible set has
  exactly `15!` orderings, `card_fiber`).
* `card_admissibleDigests`: among the `N < 2^256`, exactly `2^46 * (15! * Nadm)` are
  `admissible` (the leaf indices are bits `34 .. 243` of `N`; bits `0..33` and `244..255` are
  free).
-/

namespace SphincsSecurity.Octopus
open Finset

/-- The leaf values of a tuple, as a list. -/
def valList {k n : ℕ} (v : Fin k → Fin n) : List ℕ := List.ofFn fun i => (v i : ℕ)

theorem valList_nodup {k n : ℕ} (v : Fin k → Fin n) :
    (valList v).Nodup ↔ Function.Injective v := by
  unfold valList
  rw [List.nodup_ofFn]
  exact ⟨fun h a b hab => h (by simp [hab]), fun h a b hab => h (Fin.ext hab)⟩

theorem mem_valList {k n : ℕ} (v : Fin k → Fin n) (x : ℕ) :
    x ∈ valList v ↔ ∃ i, (v i : ℕ) = x := by
  simp [valList, List.mem_ofFn]

/-- On distinct values, `sortLeaves` is `Finset.sort` of the underlying set. -/
theorem sortLeaves_eq {l : List ℕ} (hl : l.Nodup) : sortLeaves l = l.toFinset.sort := by
  unfold sortLeaves
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (List.pairwise_insertionSort _ _)
    (pairwise_sort _ _)
  refine (List.perm_insertionSort _ _).trans ?_
  rw [List.perm_ext_iff_of_nodup hl (sort_nodup _ _)]
  intro a; simp

/-- A `k`-subset of `[0, n)` has exactly `k!` injective enumerations. -/
theorem card_fiber (k n : ℕ) (S : Finset ℕ) (hS : S ∈ powersetCard k (range n)) :
    (univ.filter fun v : Fin k → Fin n =>
      Function.Injective v ∧ (valList v).toFinset = S).card = k.factorial := by
  rw [mem_powersetCard] at hS
  obtain ⟨hSn, hSk⟩ := hS
  rw [← Fintype.card_subtype]
  have mem : ∀ v : Fin k → Fin n, (valList v).toFinset = S → ∀ i, (v i : ℕ) ∈ S := by
    intro v hv i; rw [← hv, List.mem_toFinset, mem_valList]; exact ⟨i, rfl⟩
  let E : {v : Fin k → Fin n // Function.Injective v ∧ (valList v).toFinset = S} ≃ (Fin k ≃ S) :=
    { toFun := fun v => Equiv.ofBijective (fun i => ⟨(v.1 i : ℕ), mem v.1 v.2.2 i⟩)
        ⟨fun a b hab => v.2.1 (Fin.ext (by simpa using hab)), fun x => by
          have hx : (x : ℕ) ∈ (valList v.1).toFinset := by rw [v.2.2]; exact x.2
          rw [List.mem_toFinset, mem_valList] at hx
          obtain ⟨i, hi⟩ := hx
          exact ⟨i, Subtype.ext hi⟩⟩
      invFun := fun e => ⟨fun i => ⟨(e i : ℕ), mem_range.mp (hSn (e i).2)⟩, fun a b hab => by
          have : (e a : ℕ) = e b := by simpa using congrArg Fin.val hab
          exact e.injective (Subtype.ext this), by
          ext x
          rw [List.mem_toFinset, mem_valList]
          constructor
          · rintro ⟨i, rfl⟩; exact (e i).2
          · intro hx; exact ⟨e.symm ⟨x, hx⟩, by simp⟩⟩
      left_inv := fun v => Subtype.ext (funext fun i => Fin.ext rfl)
      right_inv := fun e => Equiv.ext fun i => Subtype.ext rfl }
  rw [Fintype.card_congr E]
  have e0 : Fin k ≃ S := (S.equivFinOfCardEq hSk).symm
  rw [Fintype.card_equiv e0, Fintype.card_fin]

/-- Injective tuples with a property of their value set: `k!` per `k`-subset. -/
theorem card_inj_filter (k n : ℕ) (P : Finset ℕ → Prop) [DecidablePred P] :
    (univ.filter fun v : Fin k → Fin n =>
      Function.Injective v ∧ P (valList v).toFinset).card =
      k.factorial * ((powersetCard k (range n)).filter P).card := by
  rw [card_eq_sum_card_fiberwise (f := fun v : Fin k → Fin n => (valList v).toFinset)
    (t := (powersetCard k (range n)).filter P)]
  · rw [sum_congr rfl fun S hS => ?_, sum_const, smul_eq_mul, mul_comm]
    rw [mem_filter] at hS
    rw [filter_filter, ← card_fiber k n S hS.1]
    congr 1
    refine filter_congr fun v _ => ?_
    constructor
    · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
    · rintro ⟨h1, h3⟩; exact ⟨⟨h1, h3 ▸ hS.2⟩, h3⟩
  · intro v hv
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hv
    simp only [coe_filter, mem_powersetCard, Set.mem_ofPred_eq]
    refine ⟨⟨fun x hx => ?_, ?_⟩, hv.2⟩
    · rw [List.mem_toFinset, mem_valList] at hx
      obtain ⟨i, rfl⟩ := hx
      exact mem_range.mpr (v i).2
    · rw [List.toFinset_card_of_nodup ((valList_nodup v).mpr hv.1)]
      simp [valList]

/-- **Admissible tuples**: `15! * Nadm` injective `v : Fin 15 → Fin (2^14)` with octopus size of
the sorted values `≤ 120`. -/
theorem card_admissibleTuples :
    (univ.filter fun v : Fin 15 → Fin (2 ^ 14) =>
      Function.Injective v ∧ octopusSize (sortLeaves (valList v)) ≤ 120).card =
      Nat.factorial 15 * Nadm := by
  have h := card_inj_filter 15 (2 ^ 14) (fun S => octH 14 S.sort ≤ 120)
  rw [card_admissibleSets] at h
  rw [← h]
  refine congrArg card (filter_congr fun v _ => ?_)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [octopusSize_eq, sortLeaves_eq ((valList_nodup v).mpr h1)] at h2
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    rwa [octopusSize_eq, sortLeaves_eq ((valList_nodup v).mpr h1)]

/-! ## Digests -/

/-- The 15 base-`2^14` digits of `b`. -/
def fieldsOf (b : ℕ) : List ℕ := (List.range 15).map fun r => b / 2 ^ (14 * r) % 2 ^ 14

/-- Admissibility of the leaf-index field `b = N / 2^34`. -/
def admB (b : ℕ) : Bool :=
  decide (fieldsOf b).Nodup && decide (octopusSize (sortLeaves (fieldsOf b)) ≤ 120)

theorem leavesOf_eq (N : ℕ) : leavesOf N = fieldsOf (N / 2 ^ 34) := by
  unfold leavesOf fieldsOf leafOf
  refine List.map_congr_left fun r _ => ?_
  rw [Nat.div_div_eq_div_mul, ← pow_add]

theorem admissible_eq (N : ℕ) : admissible N = admB (N / 2 ^ 34) := by
  unfold admissible admB; rw [leavesOf_eq]

theorem fieldsOf_add (c d : ℕ) : fieldsOf (c + 2 ^ 210 * d) = fieldsOf c := by
  unfold fieldsOf
  refine List.map_congr_left fun r hr => ?_
  have hr := List.mem_range.mp hr
  have e : (2 : ℕ) ^ 210 * d = 2 ^ (14 * r) * (2 ^ 14 * (2 ^ (196 - 14 * r) * d)) := by
    rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]; congr 2; omega
  rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]

theorem sum_range_mul' {M : Type*} [AddCommMonoid M] (f : ℕ → M) (A B : ℕ) :
    ∑ k ∈ range (A * B), f k = ∑ b ∈ range B, ∑ a ∈ range A, f (a + A * b) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]
    congr 1
    refine sum_congr rfl fun a _ => ?_
    rw [Nat.add_comm]

theorem count_low (A B : ℕ) (hA : 0 < A) (p : ℕ → Bool) :
    (∑ k ∈ range (A * B), if p (k / A) then 1 else 0) =
      A * ∑ b ∈ range B, if p b then 1 else 0 := by
  rw [sum_range_mul', mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [sum_congr rfl fun a ha => by
    rw [Nat.add_mul_div_left _ _ hA, Nat.div_eq_of_lt (mem_range.mp ha), Nat.zero_add]]
  simp

theorem count_high (A B : ℕ) (p : ℕ → Bool) (hp : ∀ a b, p (a + A * b) = p a) :
    (∑ k ∈ range (A * B), if p k then 1 else 0) = B * ∑ a ∈ range A, if p a then 1 else 0 := by
  rw [sum_range_mul']
  simp [hp]

theorem fieldsOf_equiv (v : Fin 15 → Fin (2 ^ 14)) :
    fieldsOf (finFunctionFinEquiv v : ℕ) = valList v := by
  unfold fieldsOf valList
  apply List.ext_getElem (by simp)
  intro r h1 _
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  have := finFunctionFinEquiv_symm_apply_val (finFunctionFinEquiv v) ⟨r, by simpa using h1⟩
  rw [Equiv.symm_apply_apply] at this
  rw [this, pow_mul]

theorem count_fields :
    (∑ c ∈ range (2 ^ 210), if admB c then 1 else 0) =
      (univ.filter fun v : Fin 15 → Fin (2 ^ 14) =>
        Function.Injective v ∧ octopusSize (sortLeaves (valList v)) ≤ 120).card := by
  have e : (2 : ℕ) ^ 210 = (2 ^ 14) ^ 15 := by rw [← pow_mul]
  rw [e, sum_range (fun c => if admB c then 1 else 0), card_filter]
  rw [← Equiv.sum_comp finFunctionFinEquiv]
  refine sum_congr rfl fun v _ => ?_
  unfold admB
  simp only [fieldsOf_equiv, valList_nodup, Bool.and_eq_true, decide_eq_true_eq]

/-- **Admissible digests**: exactly `2^46 * (15! * Nadm)` of the `N < 2^256`. -/
theorem card_admissibleDigests :
    ((range (2 ^ 256)).filter fun N => admissible N = true).card =
      2 ^ 46 * (Nat.factorial 15 * Nadm) := by
  rw [card_filter]
  have e : (2 : ℕ) ^ 256 = 2 ^ 34 * (2 ^ 210 * 2 ^ 12) := by rw [← pow_add, ← pow_add]
  rw [e, sum_congr rfl fun N _ => by rw [admissible_eq], count_low _ _ (by positivity),
    count_high _ _ _ (fun a b => by unfold admB; rw [fieldsOf_add]), count_fields,
    card_admissibleTuples, ← mul_assoc, ← pow_add]

end SphincsSecurity.Octopus
