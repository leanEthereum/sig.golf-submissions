import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeContinuation
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeExpectation
/-!
# Averaging the target through the forecast envelope

For PORS+FP the forecast of a fixed target uses target-dependent coverage rates (the signer's accepted
leaf set is clustered, so no per-target rate is uniform). At target creation the target's leaf values
are independent and uniform, and every rate and every moment depends only on the coordinates it covers.
Because every term of the forecast operators multiplies a rate on one coordinate set with a moment on a
disjoint one, the average over the target's leaves passes through the operators: the average of the
envelope with rates `rate ℓ`, `arrival ℓ` is at most the envelope with the constant averaged rates, applied
to the averaged moments (`leafAverage_targetShapeEnvelope_le`).
-/

namespace SphincsSecurity.Concrete

open ENNReal
attribute [local instance] Classical.propDecidable
set_option linter.unusedSectionVars false

variable {L : Type} [Fintype L] [Nonempty L]

/-- `g` depends on the leaf vector only through the coordinates in `coords`. -/
def LocalTo (coords : Finset IndexGroup) (g : (IndexGroup → L) → ENNReal) : Prop :=
  ∀ first second : IndexGroup → L, (∀ i ∈ coords, first i = second i) → g first = g second

/-- The uniform average over leaf vectors. -/
noncomputable def leafAverage (g : (IndexGroup → L) → ENNReal) : ENNReal :=
  ∑ leaves : IndexGroup → L, (Fintype.card (IndexGroup → L) : ENNReal)⁻¹ * g leaves

theorem LocalTo.mono {small large : Finset IndexGroup} {g : (IndexGroup → L) → ENNReal}
    (h : LocalTo small g) (hsub : small ⊆ large) : LocalTo large g :=
  fun first second hagree => h first second (fun i hi => hagree i (hsub hi))

theorem LocalTo.const (coords : Finset IndexGroup) (value : ENNReal) :
    LocalTo (L := L) coords (fun _ => value) := fun _ _ _ => rfl

theorem LocalTo.mul {left right : Finset IndexGroup} {g h : (IndexGroup → L) → ENNReal}
    (hg : LocalTo left g) (hh : LocalTo right h) : LocalTo (left ∪ right) (fun leaves => g leaves * h leaves) := by
  intro first second hagree
  dsimp only
  rw [hg first second (fun i hi => hagree i (Finset.mem_union_left _ hi)),
    hh first second (fun i hi => hagree i (Finset.mem_union_right _ hi))]

theorem LocalTo.add {coords : Finset IndexGroup} {g h : (IndexGroup → L) → ENNReal}
    (hg : LocalTo coords g) (hh : LocalTo coords h) : LocalTo coords (fun leaves => g leaves + h leaves) := by
  intro first second hagree
  dsimp only
  rw [hg first second hagree, hh first second hagree]

theorem LocalTo.sum {ι : Type} (s : Finset ι) {coords : Finset IndexGroup} {g : ι → (IndexGroup → L) → ENNReal}
    (hg : ∀ x ∈ s, LocalTo coords (g x)) : LocalTo coords (fun leaves => ∑ x ∈ s, g x leaves) := by
  intro first second hagree
  exact Finset.sum_congr rfl (fun x hx => hg x hx first second hagree)

theorem leafAverage_add (g h : (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => g leaves + h leaves) = leafAverage g + leafAverage h := by
  simp only [leafAverage, mul_add, Finset.sum_add_distrib]

theorem leafAverage_mul_left (c : ENNReal) (g : (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => c * g leaves) = c * leafAverage g := by
  simp only [leafAverage, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring

theorem leafAverage_sum {ι : Type} (s : Finset ι) (g : ι → (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => ∑ x ∈ s, g x leaves) = ∑ x ∈ s, leafAverage (g x) := by
  simp only [leafAverage, Finset.mul_sum]
  exact Finset.sum_comm

theorem leafAverage_const (value : ENNReal) : leafAverage (L := L) (fun _ => value) = value := by
  unfold leafAverage
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
    ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _), one_mul]

theorem leafAverage_mono {g h : (IndexGroup → L) → ENNReal} (hle : ∀ leaves, g leaves ≤ h leaves) :
    leafAverage g ≤ leafAverage h :=
  Finset.sum_le_sum (fun leaves _ => mul_le_mul' le_rfl (hle leaves))

/-- Independence of disjoint coordinates under the uniform leaf vector. -/
theorem leafAverage_mul_of_disjoint {left right : Finset IndexGroup} {g h : (IndexGroup → L) → ENNReal}
    (hg : LocalTo left g) (hh : LocalTo right h) (hdisjoint : Disjoint left right) :
    leafAverage (fun leaves => g leaves * h leaves) = leafAverage g * leafAverage h := by
  let e := Equiv.piEquivPiSubtypeProd (fun i : IndexGroup => i ∈ left) (fun _ => L)
  let A := ∀ i : {i : IndexGroup // i ∈ left}, L
  let B := ∀ i : {i : IndexGroup // i ∉ left}, L
  obtain ⟨a0⟩ : Nonempty A := inferInstance
  obtain ⟨b0⟩ : Nonempty B := inferInstance
  let g' : A → ENNReal := fun a => g (e.symm (a, b0))
  let h' : B → ENNReal := fun b => h (e.symm (a0, b))
  have hge : ∀ leaves, g leaves = g' (e leaves).1 := by
    intro leaves
    apply hg
    intro i hi
    change leaves i = (e.symm ((e leaves).1, b0)) i
    simp [e, Equiv.piEquivPiSubtypeProd, hi]
  have hhe : ∀ leaves, h leaves = h' (e leaves).2 := by
    intro leaves
    apply hh
    intro i hi
    have hnot : i ∉ left := fun hl => Finset.disjoint_left.mp hdisjoint hl hi
    change leaves i = (e.symm (a0, (e leaves).2)) i
    simp [e, Equiv.piEquivPiSubtypeProd, hnot]
  let w : ENNReal := (Fintype.card (IndexGroup → L) : ENNReal)⁻¹
  have hcard : (Fintype.card (IndexGroup → L) : ENNReal) = (Fintype.card A : ENNReal) * Fintype.card B := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  have hw : w * (Fintype.card A : ENNReal) * Fintype.card B = 1 := by
    rw [mul_assoc, ← hcard]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)
  have hsum : ∀ F : A × B → ENNReal, (∑ leaves : IndexGroup → L, F (e leaves)) = ∑ ab : A × B, F ab :=
    fun F => Fintype.sum_equiv e _ _ (fun _ => rfl)
  have hgh : leafAverage (fun leaves => g leaves * h leaves) = w * ((∑ a, g' a) * ∑ b, h' b) := by
    unfold leafAverage
    rw [← Finset.mul_sum]
    congr 1
    simp only [hge, hhe]
    rw [hsum (fun ab => g' ab.1 * h' ab.2), Fintype.sum_prod_type, Finset.sum_mul_sum]
  have hgavg : leafAverage g = w * ((Fintype.card B : ENNReal) * ∑ a, g' a) := by
    unfold leafAverage
    rw [← Finset.mul_sum]
    congr 1
    simp only [hge]
    rw [hsum (fun ab => g' ab.1), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hhavg : leafAverage h = w * ((Fintype.card A : ENNReal) * ∑ b, h' b) := by
    unfold leafAverage
    rw [← Finset.mul_sum]
    congr 1
    simp only [hhe]
    rw [hsum (fun ab => h' ab.2), Fintype.sum_prod_type, Finset.sum_comm]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [hgh, hgavg, hhavg]
  calc
    w * ((∑ a, g' a) * ∑ b, h' b) = (w * (Fintype.card A : ENNReal) * Fintype.card B) * (w * ((∑ a, g' a) * ∑ b, h' b)) := by
      rw [hw, one_mul]
    _ = _ := by ring

/-- The average of a function of one coordinate. -/
theorem leafAverage_coord (i : IndexGroup) (f : L → ENNReal) :
    leafAverage (fun leaves : IndexGroup → L => f (leaves i)) =
      (Fintype.card L : ENNReal)⁻¹ * ∑ x : L, f x := by
  let e := Equiv.piSplitAt i (fun _ : IndexGroup => L)
  let R := ∀ j : {j : IndexGroup // j ≠ i}, L
  have hcard : (Fintype.card (IndexGroup → L) : ENNReal) = (Fintype.card L : ENNReal) * Fintype.card R := by
    rw [Fintype.card_congr e, Fintype.card_prod, Nat.cast_mul]
  unfold leafAverage
  rw [← Finset.mul_sum]
  have hsum : (∑ leaves : IndexGroup → L, f (leaves i)) = (Fintype.card R : ENNReal) * ∑ x : L, f x := by
    rw [← Fintype.sum_equiv e.symm (fun value : L × R => f value.1) (fun leaves => f (leaves i))
      (fun value => by simp [e, Equiv.piSplitAt])]
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [hsum, hcard, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  calc
    _ = (Fintype.card L : ENNReal)⁻¹ * (((Fintype.card R : ENNReal)⁻¹ * Fintype.card R) * ∑ x : L, f x) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel (by simp) (by simp), one_mul]

theorem LocalTo.coord (i : IndexGroup) (f : L → ENNReal) :
    LocalTo {i} (fun leaves : IndexGroup → L => f (leaves i)) := by
  intro first second hagree
  dsimp only
  rw [hagree i (Finset.mem_singleton_self i)]

theorem LocalTo.prod {ι : Type} [DecidableEq ι] (s : Finset ι) (coords : ι → Finset IndexGroup)
    {g : ι → (IndexGroup → L) → ENNReal} (hg : ∀ x ∈ s, LocalTo (coords x) (g x)) :
    LocalTo (s.biUnion coords) (fun leaves => ∏ x ∈ s, g x leaves) := by
  intro first second hagree
  apply Finset.prod_congr rfl
  intro x hx
  exact hg x hx first second (fun i hi => hagree i (Finset.mem_biUnion.mpr ⟨x, hx, hi⟩))

/-- The average of a product of functions of distinct single coordinates. -/
theorem leafAverage_prod_coord (U : Finset IndexGroup) (f : IndexGroup → L → ENNReal) :
    leafAverage (fun leaves : IndexGroup → L => ∏ i ∈ U, f i (leaves i)) =
      ∏ i ∈ U, (Fintype.card L : ENNReal)⁻¹ * ∑ x : L, f i x := by
  induction U using Finset.induction_on with
  | empty => simp [leafAverage_const]
  | @insert i U hnot ih =>
      simp only [Finset.prod_insert hnot]
      have hlocal : LocalTo U (fun leaves : IndexGroup → L => ∏ j ∈ U, f j (leaves j)) := by
        have h := LocalTo.prod (L := L) U (fun j => {j}) (g := fun j leaves => f j (leaves j))
          (fun j _ => LocalTo.coord j (f j))
        simpa using h
      rw [leafAverage_mul_of_disjoint (LocalTo.coord i (f i)) hlocal
        (Finset.disjoint_singleton_left.mpr hnot), leafAverage_coord, ih]

/-- Independence of factors on pairwise disjoint coordinate sets. -/
theorem leafAverage_prod_disjoint {ι : Type} [DecidableEq ι] (s : Finset ι) (coords : ι → Finset IndexGroup)
    {g : ι → (IndexGroup → L) → ENNReal} (hg : ∀ x ∈ s, LocalTo (coords x) (g x))
    (hdisjoint : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → Disjoint (coords x) (coords y)) :
    leafAverage (fun leaves => ∏ x ∈ s, g x leaves) = ∏ x ∈ s, leafAverage (g x) := by
  induction s using Finset.induction_on with
  | empty => simp [leafAverage_const]
  | @insert a s hnot ih =>
      simp only [Finset.prod_insert hnot]
      have hrest : LocalTo (s.biUnion coords) (fun leaves => ∏ x ∈ s, g x leaves) :=
        LocalTo.prod s coords (fun x hx => hg x (Finset.mem_insert_of_mem hx))
      have hdisj : Disjoint (coords a) (s.biUnion coords) := by
        rw [Finset.disjoint_biUnion_right]
        intro x hx
        exact hdisjoint a (Finset.mem_insert_self a s) x (Finset.mem_insert_of_mem hx)
          (fun h => hnot (h ▸ hx))
      rw [leafAverage_mul_of_disjoint (hg a (Finset.mem_insert_self a s)) hrest hdisj,
        ih (fun x hx => hg x (Finset.mem_insert_of_mem hx))
          (fun x hx y hy hxy => hdisjoint x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy)]

theorem leafAverage_tsum_plain {α : Type} (g : α → (IndexGroup → L) → ENNReal) :
    leafAverage (fun leaves => ∑' x, g x leaves) = ∑' x, leafAverage (g x) := by
  unfold leafAverage
  simp only [← ENNReal.tsum_mul_left]
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

theorem LocalTo.tsum_plain {α : Type} {coords : Finset IndexGroup} {g : α → (IndexGroup → L) → ENNReal}
    (hg : ∀ x, LocalTo coords (g x)) : LocalTo coords (fun leaves => ∑' x, g x leaves) := by
  intro first second hagree
  exact tsum_congr (fun x => hg x first second hagree)

/-! ### Locality of shapes -/

/-- Every moment `F ℓ G R` of a valid shape depends only on the coordinates of `G` and `R`. -/
def ShapeLocal (F : (IndexGroup → L) → TargetShapeVector) : Prop :=
  ∀ groups remaining, TargetShapeValid groups remaining →
    LocalTo (groupCoordinates groups ∪ remaining) (fun leaves => F leaves groups remaining)

/-- A rate function of the target whose value on `U` depends only on the coordinates in `U`. -/
def RateLocal (rate : (IndexGroup → L) → TargetRate) : Prop :=
  ∀ coords, LocalTo coords (fun leaves => rate leaves coords)

theorem groupCoordinates_mono {small large : Finset (Finset IndexGroup)} (h : small ⊆ large) :
    groupCoordinates small ⊆ groupCoordinates large :=
  Finset.biUnion_subset_biUnion_of_subset_left _ h

theorem mem_groupCoordinates {groups : Finset (Finset IndexGroup)} {i : IndexGroup} :
    i ∈ groupCoordinates groups ↔ ∃ group ∈ groups, i ∈ group := by
  simp [groupCoordinates]

theorem groupCoordinates_insert (selected : Finset IndexGroup) (groups : Finset (Finset IndexGroup)) :
    groupCoordinates (insert selected groups) = selected ∪ groupCoordinates groups := by
  simp [groupCoordinates, Finset.biUnion_insert]

/-- The coordinates removed by a step and the coordinates left are disjoint. -/
theorem TargetShapeValid.disjoint_step {groups removed : Finset (Finset IndexGroup)} {remaining selected : Finset IndexGroup}
    (hvalid : TargetShapeValid groups remaining) (hremoved : removed ⊆ groups) (hselected : selected ⊆ remaining) :
    Disjoint (groupCoordinates removed ∪ selected) (groupCoordinates (groups \ removed) ∪ (remaining \ selected)) := by
  rw [Finset.disjoint_left]
  intro i hleft hright
  rcases Finset.mem_union.mp hleft with hl | hl <;> rcases Finset.mem_union.mp hright with hr | hr
  · obtain ⟨first, hfirst, hifirst⟩ := mem_groupCoordinates.mp hl
    obtain ⟨second, hsecond, hisecond⟩ := mem_groupCoordinates.mp hr
    have hsecond' := Finset.mem_sdiff.mp hsecond
    have hne : first ≠ second := fun h => hsecond'.2 (h ▸ hfirst)
    exact Finset.disjoint_left.mp (hvalid.disjoint first (hremoved hfirst) second hsecond'.1 hne) hifirst hisecond
  · obtain ⟨first, hfirst, hifirst⟩ := mem_groupCoordinates.mp hl
    exact Finset.disjoint_left.mp (hvalid.remaining first (hremoved hfirst)) hifirst (Finset.mem_sdiff.mp hr).1
  · obtain ⟨second, hsecond, hisecond⟩ := mem_groupCoordinates.mp hr
    exact Finset.disjoint_left.mp (hvalid.remaining second (Finset.mem_sdiff.mp hsecond).1) hisecond (hselected hl)
  · exact (Finset.mem_sdiff.mp hr).2 hl

theorem step_coordinates_subset {groups removed : Finset (Finset IndexGroup)} {remaining selected : Finset IndexGroup}
    (hremoved : removed ⊆ groups) (hselected : selected ⊆ remaining) :
    (groupCoordinates removed ∪ selected) ∪ (groupCoordinates (groups \ removed) ∪ (remaining \ selected)) ⊆
      groupCoordinates groups ∪ remaining := by
  intro i hi
  simp only [Finset.mem_union] at hi ⊢
  rcases hi with (hi | hi) | (hi | hi)
  · exact Or.inl (groupCoordinates_mono hremoved hi)
  · exact Or.inr (hselected hi)
  · exact Or.inl (groupCoordinates_mono Finset.sdiff_subset hi)
  · exact Or.inr (Finset.mem_sdiff.mp hi).1

theorem TargetShapeValid.groupCoordinates_nonempty {groups removed : Finset (Finset IndexGroup)}
    {remaining : Finset IndexGroup} (hvalid : TargetShapeValid groups remaining) (hremoved : removed ⊆ groups)
    (hne : removed ≠ ∅) : (groupCoordinates removed).Nonempty := by
  obtain ⟨group, hgroup⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨i, hi⟩ := hvalid.nonempty group (hremoved hgroup)
  exact ⟨i, mem_groupCoordinates.mpr ⟨group, hgroup, hi⟩⟩

theorem reuse_coordinates_subset {groups : Finset (Finset IndexGroup)} {remaining selected : Finset IndexGroup}
    (hselected : selected ⊆ remaining) :
    groupCoordinates (insert selected groups) ∪ (remaining \ selected) ⊆ groupCoordinates groups ∪ remaining := by
  rw [groupCoordinates_insert]
  intro i hi
  simp only [Finset.mem_union] at hi ⊢
  rcases hi with (hi | hi) | hi
  · exact Or.inr (hselected hi)
  · exact Or.inl hi
  · exact Or.inr (Finset.mem_sdiff.mp hi).1

theorem shapeLocal_query {F : (IndexGroup → L) → TargetShapeVector} {arrival : (IndexGroup → L) → TargetRate}
    (hF : ShapeLocal F) (harrival : RateLocal arrival) :
    ShapeLocal (fun leaves => targetShapeQuery (arrival leaves) (F leaves)) := by
  intro groups remaining hvalid
  unfold targetShapeQuery targetArrivalStep
  apply (hF groups remaining hvalid).add
  apply LocalTo.sum
  intro removed hremoved
  have hsub : removed ⊆ groups := Finset.mem_powerset.mp (Finset.mem_erase.mp hremoved).2
  have h := (harrival (groupCoordinates removed)).mul
    (hF (groups \ removed) remaining (hvalid.subsets Finset.sdiff_subset (Finset.Subset.refl _)))
  refine h.mono ?_
  have hs := step_coordinates_subset (groups := groups) (remaining := remaining) (selected := ∅) hsub (Finset.empty_subset _)
  simpa only [Finset.union_empty, Finset.sdiff_empty] using hs

theorem shapeLocal_signing {F : (IndexGroup → L) → TargetShapeVector} {rate : (IndexGroup → L) → TargetRate}
    (reuse : ENNReal) (hF : ShapeLocal F) (hrate : RateLocal rate) :
    ShapeLocal (fun leaves => targetShapeSigning (rate leaves) reuse (F leaves)) := by
  intro groups remaining hvalid
  unfold targetShapeSigning targetFreshStep targetReuseStep
  refine ((hF groups remaining hvalid).add ?_).add ?_
  · apply LocalTo.sum
    intro removed hremoved
    apply LocalTo.sum
    intro selected hselected
    have hsubG := Finset.mem_powerset.mp hremoved
    have hsubR := Finset.mem_powerset.mp hselected
    by_cases hempty : removed = ∅ ∧ selected = ∅
    · simp only [hempty, and_self, if_true]
      exact LocalTo.const _ 0
    · simp only [hempty, if_false]
      exact ((hrate _).mul (hF _ _ (hvalid.subsets Finset.sdiff_subset Finset.sdiff_subset))).mono
        (step_coordinates_subset hsubG hsubR)
  · have hsum : LocalTo (groupCoordinates groups ∪ remaining) (fun leaves =>
        ∑ selected ∈ remaining.powerset.erase ∅, F leaves (insert selected groups) (remaining \ selected)) := by
      apply LocalTo.sum
      intro selected hselected
      have hne := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hselected).1
      have hsub := Finset.mem_powerset.mp (Finset.mem_erase.mp hselected).2
      exact (hF _ _ (hvalid.reuse hne hsub)).mono (reuse_coordinates_subset hsub)
    exact ((LocalTo.const ∅ reuse).mul hsum).mono (by rw [Finset.empty_union])

/-! ### The averaged operators -/

/-- The averaged moment vector. -/
noncomputable def averagedShape (F : (IndexGroup → L) → TargetShapeVector) : TargetShapeVector :=
  fun groups remaining => leafAverage (fun leaves => F leaves groups remaining)

theorem leafAverage_query_le {F : (IndexGroup → L) → TargetShapeVector} {arrival : (IndexGroup → L) → TargetRate}
    {average : ENNReal} (hF : ShapeLocal F) (harrival : RateLocal arrival)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => arrival leaves coords) ≤ average) :
    TargetShapeLE (averagedShape (fun leaves => targetShapeQuery (arrival leaves) (F leaves)))
      (targetShapeQuery (constRate average) (averagedShape F)) := by
  intro groups remaining hvalid
  unfold averagedShape targetShapeQuery targetArrivalStep constRate
  rw [leafAverage_add, leafAverage_sum]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro removed hremoved
  have hsub : removed ⊆ groups := Finset.mem_powerset.mp (Finset.mem_erase.mp hremoved).2
  have hdisjoint := hvalid.disjoint_step hsub (Finset.empty_subset remaining)
  simp only [Finset.union_empty, Finset.sdiff_empty] at hdisjoint
  rw [leafAverage_mul_of_disjoint (harrival _)
    (hF (groups \ removed) remaining (hvalid.subsets Finset.sdiff_subset (Finset.Subset.refl _))) hdisjoint]
  exact mul_le_mul' (haverage _ (hvalid.groupCoordinates_nonempty hsub (Finset.mem_erase.mp hremoved).1)) le_rfl

theorem leafAverage_signing_le {F : (IndexGroup → L) → TargetShapeVector} {rate : (IndexGroup → L) → TargetRate}
    (reuse : ENNReal) {average : ENNReal} (hF : ShapeLocal F) (hrate : RateLocal rate)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => rate leaves coords) ≤ average) :
    TargetShapeLE (averagedShape (fun leaves => targetShapeSigning (rate leaves) reuse (F leaves)))
      (targetShapeSigning (constRate average) reuse (averagedShape F)) := by
  intro groups remaining hvalid
  unfold averagedShape targetShapeSigning targetFreshStep constRate
  rw [leafAverage_add, leafAverage_add, leafAverage_mul_left, leafAverage_sum]
  apply add_le_add (add_le_add le_rfl _) _
  · apply Finset.sum_le_sum
    intro removed hremoved
    rw [leafAverage_sum]
    apply Finset.sum_le_sum
    intro selected hselected
    by_cases hempty : removed = ∅ ∧ selected = ∅
    · simp only [hempty, and_self, if_true]
      rw [leafAverage_const]
    · simp only [hempty, if_false]
      rw [leafAverage_mul_of_disjoint (hrate _)
        (hF _ _ (hvalid.subsets Finset.sdiff_subset Finset.sdiff_subset))
        (hvalid.disjoint_step (Finset.mem_powerset.mp hremoved) (Finset.mem_powerset.mp hselected))]
      apply mul_le_mul' (haverage _ _) le_rfl
      by_cases hr : removed = ∅
      · have hs : selected ≠ ∅ := fun h => hempty ⟨hr, h⟩
        obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hs
        exact ⟨i, Finset.mem_union_right _ hi⟩
      · obtain ⟨i, hi⟩ := hvalid.groupCoordinates_nonempty (Finset.mem_powerset.mp hremoved) hr
        exact ⟨i, Finset.mem_union_left _ hi⟩
  · unfold targetReuseStep
    rw [leafAverage_sum]

theorem leafAverage_query_iterate_le {F : (IndexGroup → L) → TargetShapeVector} {arrival : (IndexGroup → L) → TargetRate}
    {average : ENNReal} (hF : ShapeLocal F) (harrival : RateLocal arrival)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => arrival leaves coords) ≤ average) (queries : Nat) :
    ShapeLocal (fun leaves => (targetShapeQuery (arrival leaves))^[queries] (F leaves)) ∧
      TargetShapeLE (averagedShape (fun leaves => (targetShapeQuery (arrival leaves))^[queries] (F leaves)))
        ((targetShapeQuery (constRate average))^[queries] (averagedShape F)) := by
  induction queries with
  | zero => exact ⟨hF, TargetShapeLE.refl _⟩
  | succ queries ih =>
      simp only [Function.iterate_succ_apply']
      exact ⟨shapeLocal_query ih.1 harrival,
        (leafAverage_query_le ih.1 harrival haverage).trans (targetShapeQuery_mono _ ih.2)⟩

theorem leafAverage_signing_iterate_le {F : (IndexGroup → L) → TargetShapeVector} {rate : (IndexGroup → L) → TargetRate}
    (reuse : ENNReal) {average : ENNReal} (hF : ShapeLocal F) (hrate : RateLocal rate)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => rate leaves coords) ≤ average) (signings : Nat) :
    ShapeLocal (fun leaves => (targetShapeSigning (rate leaves) reuse)^[signings] (F leaves)) ∧
      TargetShapeLE (averagedShape (fun leaves => (targetShapeSigning (rate leaves) reuse)^[signings] (F leaves)))
        ((targetShapeSigning (constRate average) reuse)^[signings] (averagedShape F)) := by
  induction signings with
  | zero => exact ⟨hF, TargetShapeLE.refl _⟩
  | succ signings ih =>
      simp only [Function.iterate_succ_apply']
      exact ⟨shapeLocal_signing reuse ih.1 hrate,
        (leafAverage_signing_le reuse ih.1 hrate haverage).trans (targetShapeSigning_mono _ reuse ih.2)⟩

/-- **Fubini through the envelope.** Averaging the target's leaves through the forecast envelope with
target-dependent local rates gives at most the envelope with the averaged (constant) rates. -/
theorem leafAverage_targetShapeEnvelope_le {F : (IndexGroup → L) → TargetShapeVector}
    {rate arrival : (IndexGroup → L) → TargetRate} (reuse : ENNReal) {uniform average : ENNReal}
    (hF : ShapeLocal F) (hrate : RateLocal rate) (harrival : RateLocal arrival)
    (huniform : ∀ coords, coords.Nonempty → leafAverage (fun leaves => rate leaves coords) ≤ uniform)
    (haverage : ∀ coords, coords.Nonempty → leafAverage (fun leaves => arrival leaves coords) ≤ average)
    (queries signings : Nat) :
    TargetShapeLE (averagedShape (fun leaves => targetShapeEnvelope (rate leaves) reuse (arrival leaves) queries signings (F leaves)))
      (targetShapeEnvelope (constRate uniform) reuse (constRate average) queries signings (averagedShape F)) := by
  have hq := leafAverage_query_iterate_le hF harrival haverage queries
  have hs := leafAverage_signing_iterate_le reuse hq.1 hrate huniform signings
  exact hs.2.trans (targetShapeSigning_iterate_mono _ reuse signings hq.2)

end SphincsSecurity.Concrete
