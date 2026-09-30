import SigGolfCandidate.Verify.FoldDefs

/-! Kernel check of the FORS fold levels, trees 0..4. -/

namespace SigGolfCandidate.Verify

theorem forsFoldOk_0 : forsFoldOk 0 = true := by decide +kernel
theorem forsFoldOk_1 : forsFoldOk 1 = true := by decide +kernel
theorem forsFoldOk_2 : forsFoldOk 2 = true := by decide +kernel
theorem forsFoldOk_3 : forsFoldOk 3 = true := by decide +kernel
theorem forsFoldOk_4 : forsFoldOk 4 = true := by decide +kernel

end SigGolfCandidate.Verify
