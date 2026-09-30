import SigGolfCandidate.Verify.FoldCheckA1

/-! Kernel check of the FORS fold levels, trees 10..13. -/

namespace SigGolfCandidate.Verify

theorem forsFoldOk_10 : forsFoldOk 10 = true := by decide +kernel
theorem forsFoldOk_11 : forsFoldOk 11 = true := by decide +kernel
theorem forsFoldOk_12 : forsFoldOk 12 = true := by decide +kernel
theorem forsFoldOk_13 : forsFoldOk 13 = true := by decide +kernel

end SigGolfCandidate.Verify
