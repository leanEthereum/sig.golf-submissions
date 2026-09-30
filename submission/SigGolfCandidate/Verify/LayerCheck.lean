import SigGolfCandidate.Verify.LayerRuns

/-! Kernel check of the layer blocks (one declaration per layer). -/

namespace SigGolfCandidate.Verify

theorem layerCheck_0 : layerCheck 0 = true := by decide +kernel
theorem layerCheck_1 : layerCheck 1 = true := by decide +kernel
theorem layerCheck_2 : layerCheck 2 = true := by decide +kernel
theorem layerCheck_3 : layerCheck 3 = true := by decide +kernel
theorem layerCheck_4 : layerCheck 4 = true := by decide +kernel

theorem layerCheck_at (lay : Nat) (h : lay < 5) : layerCheck lay = true := by
  rcases (show lay = 0 ∨ lay = 1 ∨ lay = 2 ∨ lay = 3 ∨ lay = 4 by omega) with
    rfl | rfl | rfl | rfl | rfl
  exacts [layerCheck_0, layerCheck_1, layerCheck_2, layerCheck_3, layerCheck_4]

end SigGolfCandidate.Verify
