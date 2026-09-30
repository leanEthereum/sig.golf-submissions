import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB03

/-! Kernel check of chain blocks (layer, chain) (3, 24) .. (3, 33) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_3_24 : chainCheck 3 24 = true := by decide +kernel
theorem chainCheck_3_25 : chainCheck 3 25 = true := by decide +kernel
theorem chainCheck_3_26 : chainCheck 3 26 = true := by decide +kernel
theorem chainCheck_3_27 : chainCheck 3 27 = true := by decide +kernel
theorem chainCheck_3_28 : chainCheck 3 28 = true := by decide +kernel
theorem chainCheck_3_29 : chainCheck 3 29 = true := by decide +kernel
theorem chainCheck_3_30 : chainCheck 3 30 = true := by decide +kernel
theorem chainCheck_3_31 : chainCheck 3 31 = true := by decide +kernel
theorem chainCheck_3_32 : chainCheck 3 32 = true := by decide +kernel
theorem chainCheck_3_33 : chainCheck 3 33 = true := by decide +kernel

end SigGolfCandidate.Verify
