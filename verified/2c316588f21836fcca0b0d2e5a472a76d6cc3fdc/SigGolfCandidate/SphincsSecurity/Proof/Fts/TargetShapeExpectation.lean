import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TargetShapeEnvelope
namespace SphincsSecurity.Concrete

open ENNReal

theorem targetCacheLower_tsum {α : Type} (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetCacheLower (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetCacheLower (moments result) groups remaining := by
  unfold targetCacheLower
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

theorem targetTreeLower_tsum {α : Type} (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetTreeLower (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetTreeLower (moments result) groups remaining := by
  unfold targetTreeLower
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

theorem targetReuseStep_tsum {α : Type} (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetReuseStep (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetReuseStep (moments result) groups remaining := by
  unfold targetReuseStep
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

theorem targetArrivalStep_tsum {α : Type} (arrival : TargetRate) (moments : α → TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetArrivalStep arrival (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetArrivalStep arrival (moments result) groups remaining := by
  unfold targetArrivalStep
  simp only [← ENNReal.tsum_mul_left]
  exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

theorem targetFreshStep_tsum {α : Type} (rate : TargetRate) (moments : α → TargetShapeVector)
    (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetFreshStep rate (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetFreshStep rate (moments result) groups remaining := by
  unfold targetFreshStep
  have hinner : ∀ removed selected,
      (if removed = ∅ ∧ selected = ∅ then (0 : ENNReal) else
        rate (groupCoordinates removed ∪ selected) * ∑' result, moments result (groups \ removed) (remaining \ selected)) =
      ∑' result, (if removed = ∅ ∧ selected = ∅ then (0 : ENNReal) else
        rate (groupCoordinates removed ∪ selected) * moments result (groups \ removed) (remaining \ selected)) := by
    intro removed selected
    split_ifs
    · simp
    · exact ENNReal.tsum_mul_left.symm
  simp only [hinner]
  calc
    _ = ∑ removed ∈ groups.powerset, ∑' result, ∑ selected ∈ remaining.powerset,
        (if removed = ∅ ∧ selected = ∅ then (0 : ENNReal) else
          rate (groupCoordinates removed ∪ selected) * moments result (groups \ removed) (remaining \ selected)) :=
      Finset.sum_congr rfl (fun _ _ => (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm)
    _ = _ := (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm

theorem targetShapeQuery_tsum {α : Type} (arrival : TargetRate) (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeQuery arrival (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetShapeQuery arrival (moments result) groups remaining := by
  simp only [targetShapeQuery, targetArrivalStep_tsum, ENNReal.tsum_add]

theorem targetShapeSigning_tsum {α : Type} (uniform : TargetRate) (reuse : ENNReal) (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeSigning uniform reuse (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetShapeSigning uniform reuse (moments result) groups remaining := by
  simp only [targetShapeSigning, targetFreshStep_tsum, targetReuseStep_tsum, ENNReal.tsum_mul_left, ENNReal.tsum_add]

theorem targetShapeQuery_mul (arrival : TargetRate) (scalar : ENNReal) (moments : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeQuery arrival (fun G R => scalar * moments G R) groups remaining =
      scalar * targetShapeQuery arrival moments groups remaining := by
  simp only [targetShapeQuery, targetArrivalStep_mul]
  ring

theorem targetShapeSigning_mul (uniform : TargetRate) (reuse scalar : ENNReal) (moments : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeSigning uniform reuse (fun G R => scalar * moments G R) groups remaining =
      scalar * targetShapeSigning uniform reuse moments groups remaining := by
  simp only [targetShapeSigning, targetFreshStep_mul, targetReuseStep_mul]
  ring

theorem targetShapeEnvelope_tsum {α : Type} (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries signatures : Nat)
    (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeEnvelope uniform reuse arrival queries signatures (fun G R => ∑' result, moments result G R) groups remaining =
      ∑' result, targetShapeEnvelope uniform reuse arrival queries signatures (moments result) groups remaining := by
  have hquery (count : Nat) : (targetShapeQuery arrival)^[count] (fun G R => ∑' result, moments result G R) =
      fun G R => ∑' result, (targetShapeQuery arrival)^[count] (moments result) G R := by
    induction count with
    | zero => rfl
    | succ count ih =>
        simp only [Function.iterate_succ_apply', ih]
        funext G R
        exact targetShapeQuery_tsum arrival _ G R
  unfold targetShapeEnvelope
  rw [hquery]
  induction signatures generalizing groups remaining with
  | zero => rfl
  | succ signatures ih =>
      simp only [Function.iterate_succ_apply']
      have hsign : (targetShapeSigning uniform reuse)^[signatures]
          (fun G R => ∑' result, (targetShapeQuery arrival)^[queries] (moments result) G R) =
          fun G R => ∑' result, (targetShapeSigning uniform reuse)^[signatures] ((targetShapeQuery arrival)^[queries] (moments result)) G R := by
        funext G R
        exact ih G R
      rw [hsign]
      exact targetShapeSigning_tsum uniform reuse _ groups remaining

theorem targetShapeEnvelope_mul (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (scalar : ENNReal) (queries signatures : Nat)
    (moments : TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    targetShapeEnvelope uniform reuse arrival queries signatures (fun G R => scalar * moments G R) groups remaining =
      scalar * targetShapeEnvelope uniform reuse arrival queries signatures moments groups remaining := by
  have hquery (count : Nat) : (targetShapeQuery arrival)^[count] (fun G R => scalar * moments G R) =
      fun G R => scalar * (targetShapeQuery arrival)^[count] moments G R := by
    induction count with
    | zero => rfl
    | succ count ih =>
        simp only [Function.iterate_succ_apply', ih]
        funext G R
        exact targetShapeQuery_mul arrival scalar _ G R
  unfold targetShapeEnvelope
  rw [hquery]
  induction signatures generalizing groups remaining with
  | zero => rfl
  | succ signatures ih =>
      simp only [Function.iterate_succ_apply']
      have hsign : (targetShapeSigning uniform reuse)^[signatures]
          (fun G R => scalar * (targetShapeQuery arrival)^[queries] moments G R) =
          fun G R => scalar * (targetShapeSigning uniform reuse)^[signatures] ((targetShapeQuery arrival)^[queries] moments) G R := by
        funext G R
        exact ih G R
      rw [hsign]
      exact targetShapeSigning_mul uniform reuse scalar _ groups remaining

theorem targetShapeEnvelope_expected {α : Type} (uniform : TargetRate) (reuse : ENNReal) (arrival : TargetRate) (queries signatures : Nat)
    (weight : α → ENNReal) (moments : α → TargetShapeVector) (groups : Finset (Finset IndexGroup)) (remaining : Finset IndexGroup) :
    (∑' result, weight result * targetShapeEnvelope uniform reuse arrival queries signatures (moments result) groups remaining) =
      targetShapeEnvelope uniform reuse arrival queries signatures (fun G R => ∑' result, weight result * moments result G R) groups remaining := by
  rw [targetShapeEnvelope_tsum]
  apply tsum_congr
  intro result
  exact (targetShapeEnvelope_mul uniform reuse arrival (weight result) queries signatures (moments result) groups remaining).symm

end SphincsSecurity.Concrete
