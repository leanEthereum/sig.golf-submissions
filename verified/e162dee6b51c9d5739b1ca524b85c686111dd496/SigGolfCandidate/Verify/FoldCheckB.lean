import SigGolfCandidate.Verify.FoldCheckA2

/-! Kernel check of the hypertree fold levels (one declaration per layer). -/

namespace SigGolfCandidate.Verify

theorem layFoldOk_0 : layFoldOk 0 = true := by decide +kernel
theorem layFoldOk_1 : layFoldOk 1 = true := by decide +kernel
theorem layFoldOk_2 : layFoldOk 2 = true := by decide +kernel
theorem layFoldOk_3 : layFoldOk 3 = true := by decide +kernel
theorem layFoldOk_4 : layFoldOk 4 = true := by decide +kernel

end SigGolfCandidate.Verify
