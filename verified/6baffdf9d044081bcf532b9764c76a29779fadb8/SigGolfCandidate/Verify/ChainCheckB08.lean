import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB07

/-! Kernel check of chain blocks (layer, chain) (5, 0) .. (5, 9) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_5_0 : chainCheck 5 0 = true := by decide +kernel
theorem chainCheck_5_1 : chainCheck 5 1 = true := by decide +kernel
theorem chainCheck_5_2 : chainCheck 5 2 = true := by decide +kernel
theorem chainCheck_5_3 : chainCheck 5 3 = true := by decide +kernel
theorem chainCheck_5_4 : chainCheck 5 4 = true := by decide +kernel
theorem chainCheck_5_5 : chainCheck 5 5 = true := by decide +kernel
theorem chainCheck_5_6 : chainCheck 5 6 = true := by decide +kernel
theorem chainCheck_5_7 : chainCheck 5 7 = true := by decide +kernel
theorem chainCheck_5_8 : chainCheck 5 8 = true := by decide +kernel
theorem chainCheck_5_9 : chainCheck 5 9 = true := by decide +kernel

end SigGolfCandidate.Verify
