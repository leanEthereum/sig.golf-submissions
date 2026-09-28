import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeOperators
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeReindex
/-!
# Target-shape forecast operators with coverage rates

A signing covers a set of target coordinates (it becomes a cached source for some groups and/or opens
some remaining coordinates); an adversary query can become a cached source for some groups. The rate at
which one step covers a coordinate set `U` is a `TargetRate`, a function of `U`: for PORS+FP it depends on
the target (the signer's accepted leaf set is clustered), so the operators take a rate function. With a
constant rate they are the scalar operators of `TargetShapeOperators` (`targetShapeSigning_const`,
`targetShapeQuery_const`).
-/

namespace SphincsSecurity.Concrete

open ENNReal
attribute [local instance] Classical.propDecidable

/-- A coverage rate: for a set of target coordinates, the (normalized) rate at which one step covers all
of them. -/
abbrev TargetRate := Finset IndexGroup → ENNReal

/-- The constant rate. -/
def constRate (value : ENNReal) : TargetRate := fun _ => value

/-- The coordinates of a family of groups. -/
def groupCoordinates (groups : Finset (Finset IndexGroup)) : Finset IndexGroup := groups.biUnion id

/-- One arriving cached source covers the (nonempty) family `removed` of groups. -/
noncomputable def targetArrivalStep (arrival : TargetRate) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) : ENNReal :=
  ∑ removed ∈ groups.powerset.erase ∅, arrival (groupCoordinates removed) * f (groups \ removed) remaining

/-- One fresh signing covers the groups `removed` (as a new cached source) and the coordinates `selected`
(as an opening), not both empty. -/
noncomputable def targetFreshStep (rate : TargetRate) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) : ENNReal :=
  ∑ removed ∈ groups.powerset, ∑ selected ∈ remaining.powerset,
    if removed = ∅ ∧ selected = ∅ then 0 else
      rate (groupCoordinates removed ∪ selected) * f (groups \ removed) (remaining \ selected)

noncomputable def targetShapeQuery (arrival : TargetRate) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) : ENNReal :=
  f groups remaining + targetArrivalStep arrival f groups remaining

noncomputable def targetShapeSigning (rate : TargetRate) (reuse : ENNReal) (f : TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) : ENNReal :=
  f groups remaining + targetFreshStep rate f groups remaining + reuse * targetReuseStep f groups remaining

/-! ### Linearity -/

theorem targetArrivalStep_add (arrival : TargetRate) (f g : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetArrivalStep arrival (fun G R => f G R + g G R) groups remaining =
      targetArrivalStep arrival f groups remaining + targetArrivalStep arrival g groups remaining := by
  simp only [targetArrivalStep, mul_add, Finset.sum_add_distrib]

theorem targetArrivalStep_mul (arrival : TargetRate) (c : ENNReal) (f : TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetArrivalStep arrival (fun G R => c * f G R) groups remaining = c * targetArrivalStep arrival f groups remaining := by
  simp only [targetArrivalStep, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring

theorem targetFreshStep_add (rate : TargetRate) (f g : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetFreshStep rate (fun G R => f G R + g G R) groups remaining =
      targetFreshStep rate f groups remaining + targetFreshStep rate g groups remaining := by
  simp only [targetFreshStep, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro _ _
  apply Finset.sum_congr rfl
  intro _ _
  split_ifs
  · simp
  · rw [mul_add]

theorem targetFreshStep_mul (rate : TargetRate) (c : ENNReal) (f : TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetFreshStep rate (fun G R => c * f G R) groups remaining = c * targetFreshStep rate f groups remaining := by
  simp only [targetFreshStep, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  apply Finset.sum_congr rfl
  intro _ _
  split_ifs
  · simp
  · ring

/-! ### Constant rates are the scalar operators -/

theorem targetArrivalStep_const (value : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetArrivalStep (constRate value) f groups remaining = value * targetCacheLower f groups remaining := by
  unfold targetArrivalStep targetCacheLower constRate
  rw [← Finset.mul_sum]
  congr 1
  exact sum_nonempty_sdiff_eq_proper groups (fun kept => f kept remaining)

private theorem sum_powerset_split_empty {α : Type} [DecidableEq α] (s : Finset α) (g : Finset α → ENNReal) :
    ∑ x ∈ s.powerset, g x = g ∅ + ∑ x ∈ s.powerset.erase ∅, g x :=
  (Finset.add_sum_erase _ _ (Finset.empty_mem_powerset s)).symm

theorem targetFreshStep_const (value : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetFreshStep (constRate value) f groups remaining =
      value * (targetCacheLower f groups remaining + targetTreeLower f groups remaining +
        targetCacheLower (targetTreeLower f) groups remaining) := by
  unfold targetFreshStep constRate
  have hfirst : (∑ selected ∈ remaining.powerset,
      if (∅ : Finset (Finset IndexGroup)) = ∅ ∧ selected = ∅ then (0 : ENNReal) else
        value * f (groups \ ∅) (remaining \ selected)) = value * targetTreeLower f groups remaining := by
    rw [sum_powerset_split_empty, if_pos ⟨rfl, rfl⟩, zero_add]
    unfold targetTreeLower
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected hselected
    rw [if_neg (fun h => (Finset.mem_erase.mp hselected).1 h.2), Finset.sdiff_empty]
  have hrest : ∀ removed ∈ groups.powerset.erase ∅, (∑ selected ∈ remaining.powerset,
      if removed = ∅ ∧ selected = ∅ then (0 : ENNReal) else
        value * f (groups \ removed) (remaining \ selected)) =
      value * f (groups \ removed) remaining + value * targetTreeLower f (groups \ removed) remaining := by
    intro removed hremoved
    have hne : removed ≠ ∅ := (Finset.mem_erase.mp hremoved).1
    rw [sum_powerset_split_empty, if_neg (fun h => hne h.1), Finset.sdiff_empty]
    congr 1
    unfold targetTreeLower
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro selected _
    rw [if_neg (fun h => hne h.1)]
  rw [sum_powerset_split_empty, hfirst, Finset.sum_congr rfl hrest, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum]
  unfold targetCacheLower
  rw [sum_nonempty_sdiff_eq_proper groups (fun kept => f kept remaining),
    sum_nonempty_sdiff_eq_proper groups (fun kept => targetTreeLower f kept remaining)]
  ring

theorem targetShapeQuery_const (value : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetShapeQuery (constRate value) f groups remaining = f groups remaining + value * targetCacheLower f groups remaining := by
  rw [targetShapeQuery, targetArrivalStep_const]

theorem targetShapeSigning_const (value reuse : ENNReal) (f : TargetShapeVector) (groups : Finset (Finset IndexGroup))
    (remaining : Finset IndexGroup) :
    targetShapeSigning (constRate value) reuse f groups remaining =
      f groups remaining + value * (targetCacheLower f groups remaining + targetTreeLower f groups remaining +
        targetCacheLower (targetTreeLower f) groups remaining) + reuse * targetReuseStep f groups remaining := by
  rw [targetShapeSigning, targetFreshStep_const]

/-! ### Order -/

def TargetShapeLE (f g : TargetShapeVector) : Prop := ∀ groups remaining, TargetShapeValid groups remaining → f groups remaining ≤ g groups remaining

theorem TargetShapeLE.refl (f : TargetShapeVector) : TargetShapeLE f f := fun _ _ _ => le_rfl

theorem TargetShapeLE.trans {f g h : TargetShapeVector} (hfg : TargetShapeLE f g) (hgh : TargetShapeLE g h) : TargetShapeLE f h :=
  fun G R hv => (hfg G R hv).trans (hgh G R hv)

theorem targetCacheLower_shape_mono {f g : TargetShapeVector} (h : TargetShapeLE f g) : TargetShapeLE (targetCacheLower f) (targetCacheLower g) := by
  intro groups remaining hvalid
  exact Finset.sum_le_sum (fun kept hkept => h kept remaining
    (hvalid.subsets (Finset.mem_powerset.mp (Finset.mem_erase.mp hkept).2) (Finset.Subset.refl _)))

theorem targetTreeLower_shape_mono {f g : TargetShapeVector} (h : TargetShapeLE f g) : TargetShapeLE (targetTreeLower f) (targetTreeLower g) := by
  intro groups remaining hvalid
  exact Finset.sum_le_sum (fun _ _ => h _ _ (hvalid.subsets (Finset.Subset.refl _) Finset.sdiff_subset))

theorem targetReuseStep_shape_mono {f g : TargetShapeVector} (h : TargetShapeLE f g) : TargetShapeLE (targetReuseStep f) (targetReuseStep g) := by
  intro groups remaining hvalid
  apply Finset.sum_le_sum
  intro selected hselected
  exact h _ _ (hvalid.reuse
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
    (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2))

theorem targetArrivalStep_shape_mono (arrival : TargetRate) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE (targetArrivalStep arrival f) (targetArrivalStep arrival g) := by
  intro groups remaining hvalid
  exact Finset.sum_le_sum (fun _ _ => mul_le_mul' le_rfl
    (h _ _ (hvalid.subsets Finset.sdiff_subset (Finset.Subset.refl _))))

theorem targetFreshStep_shape_mono (rate : TargetRate) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE (targetFreshStep rate f) (targetFreshStep rate g) := by
  intro groups remaining hvalid
  apply Finset.sum_le_sum
  intro _ _
  apply Finset.sum_le_sum
  intro _ _
  split_ifs
  · exact le_rfl
  · exact mul_le_mul' le_rfl (h _ _ (hvalid.subsets Finset.sdiff_subset Finset.sdiff_subset))

theorem targetShapeQuery_mono (arrival : TargetRate) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE (targetShapeQuery arrival f) (targetShapeQuery arrival g) := by
  intro groups remaining hvalid
  exact add_le_add (h groups remaining hvalid) (targetArrivalStep_shape_mono arrival h groups remaining hvalid)

theorem targetShapeSigning_mono (rate : TargetRate) (reuse : ENNReal) {f g : TargetShapeVector} (h : TargetShapeLE f g) :
    TargetShapeLE (targetShapeSigning rate reuse f) (targetShapeSigning rate reuse g) := by
  intro groups remaining hvalid
  exact add_le_add (add_le_add (h groups remaining hvalid) (targetFreshStep_shape_mono rate h groups remaining hvalid))
    (mul_le_mul' le_rfl (targetReuseStep_shape_mono h groups remaining hvalid))

/-! ### Commutation of an arrival with a signing -/

private theorem sum_erase_empty_indicator {α : Type} [DecidableEq α] (s : Finset (Finset α)) (g : Finset α → ENNReal) :
    ∑ x ∈ s.erase ∅, g x = ∑ x ∈ s, if x = ∅ then 0 else g x := by
  rw [← Finset.filter_ne', Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x = ∅ <;> simp [hx]

/-- The arrival and fresh-signing parts commute exactly: both sides sum, over disjoint families
`arrived`, `signed` of groups and a selected coordinate set, the same coefficient. -/
theorem targetArrival_fresh_commute (arrival rate : TargetRate) (f : TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetArrivalStep arrival (targetFreshStep rate f) groups remaining =
      targetFreshStep rate (targetArrivalStep arrival f) groups remaining := by
  unfold targetArrivalStep targetFreshStep
  rw [sum_erase_empty_indicator]
  simp only [sum_erase_empty_indicator, Finset.mul_sum]
  -- left: Σ_A Σ_S Σ_sel ; right: Σ_S Σ_sel Σ_A
  have hleft : ∀ A ∈ groups.powerset,
      (if A = ∅ then 0 else ∑ S ∈ (groups \ A).powerset, ∑ sel ∈ remaining.powerset,
        arrival (groupCoordinates A) * if S = ∅ ∧ sel = ∅ then 0 else
          rate (groupCoordinates S ∪ sel) * f ((groups \ A) \ S) (remaining \ sel)) =
      ∑ S ∈ (groups \ A).powerset, ∑ sel ∈ remaining.powerset,
        (if A = ∅ ∨ (S = ∅ ∧ sel = ∅) then 0 else
          arrival (groupCoordinates A) * rate (groupCoordinates S ∪ sel) * f (groups \ (A ∪ S)) (remaining \ sel)) := by
    intro A _
    by_cases hA : A = ∅
    · simp [hA]
    · rw [if_neg hA]
      apply Finset.sum_congr rfl
      intro S _
      apply Finset.sum_congr rfl
      intro sel _
      rw [sdiff_sdiff_left, Finset.sup_eq_union]
      split_ifs <;> simp_all [mul_assoc]
  have hright : ∀ S ∈ groups.powerset, ∀ sel ∈ remaining.powerset,
      (if S = ∅ ∧ sel = ∅ then 0 else rate (groupCoordinates S ∪ sel) *
        ∑ A ∈ (groups \ S).powerset, if A = ∅ then 0 else arrival (groupCoordinates A) * f ((groups \ S) \ A) (remaining \ sel)) =
      ∑ A ∈ (groups \ S).powerset,
        (if A = ∅ ∨ (S = ∅ ∧ sel = ∅) then 0 else
          arrival (groupCoordinates A) * rate (groupCoordinates S ∪ sel) * f (groups \ (A ∪ S)) (remaining \ sel)) := by
    intro S _ sel _
    by_cases hS : S = ∅ ∧ sel = ∅
    · simp [hS]
    · rw [if_neg hS, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A _
      rw [sdiff_sdiff_left, Finset.sup_eq_union, Finset.union_comm S A]
      split_ifs <;> simp_all
      ring
  rw [Finset.sum_congr rfl hleft]
  simp only [Finset.mul_sum] at hright
  rw [Finset.sum_congr rfl (fun S hS => Finset.sum_congr rfl (fun sel hsel => hright S hS sel hsel))]
  -- reorder: Σ_A Σ_S Σ_sel = Σ_S Σ_sel Σ_A
  rw [Finset.sum_comm' (t' := groups.powerset) (s' := fun S => (groups \ S).powerset)]
  · apply Finset.sum_congr rfl
    intro S _
    exact Finset.sum_comm
  · intro A S
    simp only [Finset.mem_powerset, Finset.subset_sdiff]
    constructor
    · rintro ⟨hA, hS, hdisj⟩
      exact ⟨⟨hA, hdisj.symm⟩, hS⟩
    · rintro ⟨⟨hA, hdisj⟩, hS⟩
      exact ⟨hA, hS, hdisj.symm⟩

theorem targetArrival_reuse_le (arrival : TargetRate) (f : TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) (hvalid : TargetShapeValid groups remaining) :
    targetArrivalStep arrival (targetReuseStep f) groups remaining ≤
      targetReuseStep (targetArrivalStep arrival f) groups remaining := by
  unfold targetArrivalStep targetReuseStep
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro selected hselected
  have hnot : selected ∉ groups := hvalid.new_group
    (Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1)
    (Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2)
  have hterm : ∀ A ∈ groups.powerset.erase ∅,
      arrival (groupCoordinates A) * f (insert selected (groups \ A)) (remaining \ selected) =
        arrival (groupCoordinates A) * f (insert selected groups \ A) (remaining \ selected) := by
    intro A hA
    have hsel : selected ∉ A := fun h => hnot (Finset.mem_powerset.mp (Finset.mem_erase.mp hA).2 h)
    rw [Finset.insert_sdiff_of_notMem _ hsel]
  rw [Finset.sum_congr rfl hterm]
  apply Finset.sum_le_sum_of_subset
  intro A hA
  obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hA
  exact Finset.mem_erase.mpr ⟨hne, Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hsub).trans (Finset.subset_insert _ _))⟩

theorem targetShapeQuery_signing_le (rate : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (f : TargetShapeVector) :
    TargetShapeLE (targetShapeQuery arrival (targetShapeSigning rate reuse f)) (targetShapeSigning rate reuse (targetShapeQuery arrival f)) := by
  intro groups remaining hvalid
  have hleft : targetShapeQuery arrival (targetShapeSigning rate reuse f) groups remaining =
      f groups remaining + targetFreshStep rate f groups remaining + reuse * targetReuseStep f groups remaining +
        (targetArrivalStep arrival f groups remaining + targetArrivalStep arrival (targetFreshStep rate f) groups remaining +
          reuse * targetArrivalStep arrival (targetReuseStep f) groups remaining) := by
    unfold targetShapeQuery
    change _ + targetArrivalStep arrival
      (fun G R => (f G R + targetFreshStep rate f G R) + reuse * targetReuseStep f G R) groups remaining = _
    rw [targetArrivalStep_add, targetArrivalStep_mul, targetArrivalStep_add]
    rfl
  have hright : targetShapeSigning rate reuse (targetShapeQuery arrival f) groups remaining =
      f groups remaining + targetArrivalStep arrival f groups remaining +
        (targetFreshStep rate f groups remaining + targetFreshStep rate (targetArrivalStep arrival f) groups remaining) +
          reuse * (targetReuseStep f groups remaining + targetReuseStep (targetArrivalStep arrival f) groups remaining) := by
    unfold targetShapeSigning targetShapeQuery
    change _ + targetFreshStep rate (fun G R => f G R + targetArrivalStep arrival f G R) groups remaining +
      reuse * targetReuseStep (fun G R => f G R + targetArrivalStep arrival f G R) groups remaining = _
    rw [targetFreshStep_add, targetReuseStep_add]
  rw [hleft, hright, targetArrival_fresh_commute]
  have h := targetArrival_reuse_le arrival f groups remaining hvalid
  calc
    _ = f groups remaining + targetArrivalStep arrival f groups remaining +
        (targetFreshStep rate f groups remaining + targetFreshStep rate (targetArrivalStep arrival f) groups remaining) +
          reuse * (targetReuseStep f groups remaining + targetArrivalStep arrival (targetReuseStep f) groups remaining) := by ring
    _ ≤ _ := by gcongr

noncomputable def targetShapeEnvelope (rate : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries signings : Nat)
    (f : TargetShapeVector) : TargetShapeVector :=
  (targetShapeSigning rate reuse)^[signings] ((targetShapeQuery arrival)^[queries] f)

theorem targetShapeSigning_iterate_mono (rate : TargetRate) (reuse : ENNReal) (signings : Nat) {f g : TargetShapeVector}
    (h : TargetShapeLE f g) :
    TargetShapeLE ((targetShapeSigning rate reuse)^[signings] f) ((targetShapeSigning rate reuse)^[signings] g) := by
  induction signings with
  | zero => exact h
  | succ signings ih =>
      simp only [Function.iterate_succ_apply']
      exact targetShapeSigning_mono rate reuse ih

end SphincsSecurity.Concrete
