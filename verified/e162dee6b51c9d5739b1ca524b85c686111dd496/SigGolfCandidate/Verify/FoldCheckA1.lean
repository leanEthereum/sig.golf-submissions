import SigGolfCandidate.Verify.FoldCheckA0

/-! Kernel check of the FORS fold levels, trees 5..9. -/

namespace SigGolfCandidate.Verify

theorem forsFoldOk_5 : forsFoldOk 5 = true := by decide +kernel
theorem forsFoldOk_6 : forsFoldOk 6 = true := by decide +kernel
theorem forsFoldOk_7 : forsFoldOk 7 = true := by decide +kernel
theorem forsFoldOk_8 : forsFoldOk 8 = true := by decide +kernel
theorem forsFoldOk_9 : forsFoldOk 9 = true := by decide +kernel

end SigGolfCandidate.Verify
