import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB07

/-! Kernel check of chain blocks (layer, chain) (5, 20) .. (5, 29) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_5_20 : chainCheck 5 20 = true := by decide +kernel
theorem chainCheck_5_21 : chainCheck 5 21 = true := by decide +kernel
theorem chainCheck_5_22 : chainCheck 5 22 = true := by decide +kernel
theorem chainCheck_5_23 : chainCheck 5 23 = true := by decide +kernel
theorem chainCheck_5_24 : chainCheck 5 24 = true := by decide +kernel
theorem chainCheck_5_25 : chainCheck 5 25 = true := by decide +kernel
theorem chainCheck_5_26 : chainCheck 5 26 = true := by decide +kernel
theorem chainCheck_5_27 : chainCheck 5 27 = true := by decide +kernel
theorem chainCheck_5_28 : chainCheck 5 28 = true := by decide +kernel
theorem chainCheck_5_29 : chainCheck 5 29 = true := by decide +kernel

end SigGolfCandidate.Verify
