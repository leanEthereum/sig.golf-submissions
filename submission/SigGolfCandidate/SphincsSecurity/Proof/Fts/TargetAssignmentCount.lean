import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeProbability
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

noncomputable def targetTreeMatchCount {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) (tree : IndexGroup) : Nat :=
  ∑ slot : Fin n, if ∃ view, views slot = some view ∧ view.1 = target.1 ∧ target.2 tree ∈ Set.range view.2 then 1 else 0

noncomputable def sourceTreeMatch (target source : FewTimeView) (tree : IndexGroup) : Nat :=
  if source.1 = target.1 ∧ target.2 tree ∈ Set.range source.2 then 1 else 0

theorem targetTreeMatchCount_pos_iff {n : Nat} (views : Fin n → Option FewTimeView) (target : FewTimeView) (tree : IndexGroup) :
    0 < targetTreeMatchCount views target tree ↔ ∃ slot view, views slot = some view ∧ view.1 = target.1 ∧ target.2 tree ∈ Set.range view.2 := by
  simp only [targetTreeMatchCount, Finset.sum_pos_iff, Finset.mem_univ, true_and]
  apply exists_congr
  intro slot
  split_ifs <;> simp_all

end SphincsSecurity.Concrete
