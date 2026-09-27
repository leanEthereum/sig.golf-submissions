import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckA04

/-! Kernel check of chain blocks (layer, chain) (1, 8) .. (1, 17) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_1_8 : chainCheck 1 8 = true := by decide +kernel
theorem chainCheck_1_9 : chainCheck 1 9 = true := by decide +kernel
theorem chainCheck_1_10 : chainCheck 1 10 = true := by decide +kernel
theorem chainCheck_1_11 : chainCheck 1 11 = true := by decide +kernel
theorem chainCheck_1_12 : chainCheck 1 12 = true := by decide +kernel
theorem chainCheck_1_13 : chainCheck 1 13 = true := by decide +kernel
theorem chainCheck_1_14 : chainCheck 1 14 = true := by decide +kernel
theorem chainCheck_1_15 : chainCheck 1 15 = true := by decide +kernel
theorem chainCheck_1_16 : chainCheck 1 16 = true := by decide +kernel
theorem chainCheck_1_17 : chainCheck 1 17 = true := by decide +kernel

end SigGolfCandidate.Verify
