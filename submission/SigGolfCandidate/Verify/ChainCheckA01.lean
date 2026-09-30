import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckA00

/-! Kernel check of chain blocks (layer, chain) (0, 10) .. (0, 19) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_0_10 : chainCheck 0 10 = true := by decide +kernel
theorem chainCheck_0_11 : chainCheck 0 11 = true := by decide +kernel
theorem chainCheck_0_12 : chainCheck 0 12 = true := by decide +kernel
theorem chainCheck_0_13 : chainCheck 0 13 = true := by decide +kernel
theorem chainCheck_0_14 : chainCheck 0 14 = true := by decide +kernel
theorem chainCheck_0_15 : chainCheck 0 15 = true := by decide +kernel
theorem chainCheck_0_16 : chainCheck 0 16 = true := by decide +kernel
theorem chainCheck_0_17 : chainCheck 0 17 = true := by decide +kernel
theorem chainCheck_0_18 : chainCheck 0 18 = true := by decide +kernel
theorem chainCheck_0_19 : chainCheck 0 19 = true := by decide +kernel

end SigGolfCandidate.Verify
