import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckA05

/-! Kernel check of chain blocks (layer, chain) (1, 18) .. (1, 27) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_1_18 : chainCheck 1 18 = true := by decide +kernel
theorem chainCheck_1_19 : chainCheck 1 19 = true := by decide +kernel
theorem chainCheck_1_20 : chainCheck 1 20 = true := by decide +kernel
theorem chainCheck_1_21 : chainCheck 1 21 = true := by decide +kernel
theorem chainCheck_1_22 : chainCheck 1 22 = true := by decide +kernel
theorem chainCheck_1_23 : chainCheck 1 23 = true := by decide +kernel
theorem chainCheck_1_24 : chainCheck 1 24 = true := by decide +kernel
theorem chainCheck_1_25 : chainCheck 1 25 = true := by decide +kernel
theorem chainCheck_1_26 : chainCheck 1 26 = true := by decide +kernel
theorem chainCheck_1_27 : chainCheck 1 27 = true := by decide +kernel

end SigGolfCandidate.Verify
