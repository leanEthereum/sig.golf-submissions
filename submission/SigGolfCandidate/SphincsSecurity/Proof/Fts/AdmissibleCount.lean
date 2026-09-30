import SigGolfCandidate.SphincsSecurity.Scheme
import SigGolfCandidate.SphincsSecurity.Proof.Fts.Octopus.Tuples
import Mathlib.Tactic.IrreducibleDef

/-!
# The number of admissible PORS+FP leaf vectors

`AdmissibleLeaves` (distinct leaf indices, octopus of at most 120 nodes) holds for exactly
`15! · Nadm` of the `2^210` leaf vectors `IndexGroup → FtsLeaf` (`card_admissibleLeaves`; the count is a
kernel evaluation in `Octopus/Defs.lean`). The admissibility probability of a raw digest,
`p = 15! · Nadm / 2^210 ≈ 2^-9.7636`, is sealed as `admissibleProbability` with the bounds
`1/870 ≤ p ≤ 1/869`; only these bounds (and the exact count, for the uniform split of a digest) are used
elsewhere.
-/

namespace SphincsSecurity.Concrete

open Finset

private instance sortRelTotal (leaves : IndexGroup → FtsLeaf) :
    Std.Total (fun r r' : IndexGroup => (leaves r).val ≤ (leaves r').val) :=
  ⟨fun a b => le_total _ _⟩

private instance sortRelTrans (leaves : IndexGroup → FtsLeaf) :
    IsTrans IndexGroup (fun r r' : IndexGroup => (leaves r).val ≤ (leaves r').val) :=
  ⟨fun _ _ _ hab hbc => le_trans hab hbc⟩

/-- The scheme's sorted leaf values are the reference layer's sorted value list. -/
theorem sortedLeaves_eq_sortLeaves (leaves : IndexGroup → FtsLeaf) :
    sortedLeaves leaves = Octopus.sortLeaves (Octopus.valList (n := 2 ^ 14) (k := 15) leaves) := by
  unfold sortedLeaves sortedSlots Octopus.sortLeaves Octopus.valList
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · rw [List.pairwise_map]
    exact List.pairwise_insertionSort _ _
  · exact List.pairwise_insertionSort _ _
  · refine ((List.perm_insertionSort _ _).map _).trans ?_
    refine List.Perm.trans ?_ (List.perm_insertionSort _ _).symm
    rw [List.ofFn_eq_map]
    rfl

theorem octopusSize_eq_reference (sorted : List Nat) : octopusSize sorted = Octopus.octopusSize sorted := rfl

/-- **The number of admissible leaf vectors.** -/
theorem card_admissibleLeaves :
    (univ.filter AdmissibleLeaves).card = Nat.factorial 15 * Octopus.Nadm := by
  have hfilter : univ.filter AdmissibleLeaves = univ.filter fun v : IndexGroup → FtsLeaf =>
      Function.Injective v ∧ Octopus.octopusSize (Octopus.sortLeaves (Octopus.valList v)) ≤ 120 := by
    apply filter_congr
    intro leaves _
    unfold AdmissibleLeaves
    rw [sortedLeaves_eq_sortLeaves, octopusSize_eq_reference]
    rfl
  rw [hfilter]
  exact Octopus.card_admissibleTuples

theorem card_leafVectors : Fintype.card (IndexGroup → FtsLeaf) = 2 ^ 210 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, ← pow_mul]
  rfl

theorem admissibleLeafCount_bounds :
    2 ^ 210 ≤ 870 * (Nat.factorial 15 * Octopus.Nadm) ∧ 869 * (Nat.factorial 15 * Octopus.Nadm) ≤ 2 ^ 210 := by
  unfold Octopus.Nadm
  norm_num [Nat.factorial]

open ENNReal in
/-- The probability `p` that a uniform leaf vector is admissible. -/
noncomputable irreducible_def admissibleProbability : ENNReal :=
  ((univ.filter AdmissibleLeaves).card : ENNReal) / (Fintype.card (IndexGroup → FtsLeaf) : ENNReal)

open ENNReal in
theorem admissibleProbability_ge : (870 : ENNReal)⁻¹ ≤ admissibleProbability := by
  rw [admissibleProbability_def, card_admissibleLeaves, card_leafVectors]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp)), ← ENNReal.div_eq_inv_mul,
    ENNReal.div_le_iff_le_mul (Or.inl (by simp)) (Or.inl (by simp))]
  have h := admissibleLeafCount_bounds.1
  rw [mul_comm] at h
  exact_mod_cast h

open ENNReal in
theorem admissibleProbability_le : admissibleProbability ≤ (869 : ENNReal)⁻¹ := by
  rw [admissibleProbability_def, card_admissibleLeaves, card_leafVectors]
  rw [ENNReal.div_le_iff (by simp) (by simp), ← ENNReal.div_eq_inv_mul,
    ENNReal.le_div_iff_mul_le (Or.inl (by simp)) (Or.inl (by simp))]
  have h := admissibleLeafCount_bounds.2
  rw [mul_comm] at h
  exact_mod_cast h

theorem admissibleProbability_inv_le : admissibleProbability⁻¹ ≤ 870 :=
  ENNReal.inv_le_iff_inv_le.mpr admissibleProbability_ge

theorem admissibleProbability_pos : admissibleProbability ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (by simp) admissibleProbability_ge)

theorem admissibleProbability_ne_top : admissibleProbability ≠ ⊤ :=
  ne_top_of_le_ne_top (by simp) admissibleProbability_le

theorem admissibleProbability_le_one : admissibleProbability ≤ 1 :=
  admissibleProbability_le.trans (ENNReal.inv_le_one.mpr (by norm_num))

/-- The number of admissible leaf vectors, as the probability times the number of leaf vectors. -/
theorem card_admissibleLeaves_eq_mul :
    ((univ.filter AdmissibleLeaves).card : ENNReal) =
      admissibleProbability * (Fintype.card (IndexGroup → FtsLeaf) : ENNReal) := by
  rw [admissibleProbability_def, ENNReal.div_mul_cancel (by simp) (by simp)]

/-- The rate at which a fresh message query adds an admissible cached input at a given index:
`p · 2^-34`. -/
noncomputable def cachedIndexRate : ENNReal := admissibleProbability * (Fintype.card Index : ENNReal)⁻¹

theorem cachedIndexRate_ne_top : cachedIndexRate ≠ ⊤ :=
  ENNReal.mul_ne_top admissibleProbability_ne_top (by simp)

theorem cachedIndexRate_le_one : cachedIndexRate ≤ 1 :=
  (mul_le_mul' admissibleProbability_le_one (ENNReal.inv_le_one.mpr (by exact_mod_cast Fintype.card_pos))).trans_eq
    (one_mul 1)

theorem card_mul_cachedIndexRate : (Fintype.card Index : ENNReal) * cachedIndexRate = admissibleProbability := by
  rw [cachedIndexRate, mul_left_comm, ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]

end SphincsSecurity.Concrete
