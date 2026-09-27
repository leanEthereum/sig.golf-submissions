import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckA01

/-! Kernel check of chain blocks (layer, chain) (0, 20) .. (0, 29) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_0_20 : chainCheck 0 20 = true := by decide +kernel
theorem chainCheck_0_21 : chainCheck 0 21 = true := by decide +kernel
theorem chainCheck_0_22 : chainCheck 0 22 = true := by decide +kernel
theorem chainCheck_0_23 : chainCheck 0 23 = true := by decide +kernel
theorem chainCheck_0_24 : chainCheck 0 24 = true := by decide +kernel
theorem chainCheck_0_25 : chainCheck 0 25 = true := by decide +kernel
theorem chainCheck_0_26 : chainCheck 0 26 = true := by decide +kernel
theorem chainCheck_0_27 : chainCheck 0 27 = true := by decide +kernel
theorem chainCheck_0_28 : chainCheck 0 28 = true := by decide +kernel
theorem chainCheck_0_29 : chainCheck 0 29 = true := by decide +kernel

end SigGolfCandidate.Verify
