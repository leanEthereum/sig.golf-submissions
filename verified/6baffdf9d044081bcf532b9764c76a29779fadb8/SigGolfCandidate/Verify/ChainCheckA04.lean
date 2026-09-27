import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckA03

/-! Kernel check of chain blocks (layer, chain) (0, 40) .. (1, 7) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_0_40 : chainCheck 0 40 = true := by decide +kernel
theorem chainCheck_0_41 : chainCheck 0 41 = true := by decide +kernel
theorem chainCheck_1_0 : chainCheck 1 0 = true := by decide +kernel
theorem chainCheck_1_1 : chainCheck 1 1 = true := by decide +kernel
theorem chainCheck_1_2 : chainCheck 1 2 = true := by decide +kernel
theorem chainCheck_1_3 : chainCheck 1 3 = true := by decide +kernel
theorem chainCheck_1_4 : chainCheck 1 4 = true := by decide +kernel
theorem chainCheck_1_5 : chainCheck 1 5 = true := by decide +kernel
theorem chainCheck_1_6 : chainCheck 1 6 = true := by decide +kernel
theorem chainCheck_1_7 : chainCheck 1 7 = true := by decide +kernel

end SigGolfCandidate.Verify
