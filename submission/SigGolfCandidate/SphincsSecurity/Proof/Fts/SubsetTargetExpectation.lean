import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.SubsetTargetAssignment
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeLeafAverage
/-!
# Coverage by one source, as a function of the target's leaves

A source (the view of a signed or cached digest) opens the leaves in its fifteen slots. Slot `i` of a
target on the same index is covered when the target's leaf `t_i` is one of them. As a function of the
target's leaf vector, the coverage of a coordinate set is a product of single-coordinate indicators.
-/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

/-- The leaves a source opens. -/
noncomputable def openedLeaves (source : FewTimeView) : Finset FtsLeaf := Finset.univ.image source.2

theorem mem_openedLeaves_iff {source : FewTimeView} {leaf : FtsLeaf} :
    leaf ∈ openedLeaves source ↔ leaf ∈ Set.range source.2 := by
  simp [openedLeaves]

theorem card_openedLeaves_le (source : FewTimeView) : (openedLeaves source).card ≤ ftsOpenings := by
  unfold openedLeaves
  exact Finset.card_image_le.trans (by simp)

theorem sourceSubsetMatch_leaves (index : Index) (leaves : IndexGroup → FtsLeaf) (source : FewTimeView)
    (required : Finset IndexGroup) (hne : required.Nonempty) :
    (sourceSubsetMatch (index, leaves) source required : ENNReal) =
      (if source.1 = index then 1 else 0) *
        ∏ i ∈ required, (if leaves i ∈ openedLeaves source then (1 : ENNReal) else 0) := by
  unfold sourceSubsetMatch sourceTreeMatch
  rw [Nat.cast_prod]
  by_cases hindex : source.1 = index
  · simp only [hindex, true_and, if_true, one_mul, mem_openedLeaves_iff]
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> simp
  · obtain ⟨i, hi⟩ := hne
    simp only [hindex, false_and, if_false, zero_mul, Nat.cast_zero]
    exact Finset.prod_eq_zero hi rfl

theorem sourceSubsetMatch_local (index : Index) (source : FewTimeView) (required : Finset IndexGroup) :
    LocalTo required (fun leaves : IndexGroup → FtsLeaf =>
      (sourceSubsetMatch (index, leaves) source required : ENNReal)) := by
  intro first second hagree
  dsimp only
  unfold sourceSubsetMatch sourceTreeMatch
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [hagree i hi]

end SphincsSecurity.Concrete
