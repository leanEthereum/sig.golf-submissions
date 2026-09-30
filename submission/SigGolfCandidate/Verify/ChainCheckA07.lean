import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckA06

/-! Kernel check of chain blocks (layer, chain) (1, 28) .. (1, 37) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_1_28 : chainCheck 1 28 = true := by decide +kernel
theorem chainCheck_1_29 : chainCheck 1 29 = true := by decide +kernel
theorem chainCheck_1_30 : chainCheck 1 30 = true := by decide +kernel
theorem chainCheck_1_31 : chainCheck 1 31 = true := by decide +kernel
theorem chainCheck_1_32 : chainCheck 1 32 = true := by decide +kernel
theorem chainCheck_1_33 : chainCheck 1 33 = true := by decide +kernel
theorem chainCheck_1_34 : chainCheck 1 34 = true := by decide +kernel
theorem chainCheck_1_35 : chainCheck 1 35 = true := by decide +kernel
theorem chainCheck_1_36 : chainCheck 1 36 = true := by decide +kernel
theorem chainCheck_1_37 : chainCheck 1 37 = true := by decide +kernel

end SigGolfCandidate.Verify
