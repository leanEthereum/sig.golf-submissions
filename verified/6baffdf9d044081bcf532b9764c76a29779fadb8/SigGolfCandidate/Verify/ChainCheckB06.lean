import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB05

/-! Kernel check of chain blocks (layer, chain) (4, 22) .. (4, 31) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_4_22 : chainCheck 4 22 = true := by decide +kernel
theorem chainCheck_4_23 : chainCheck 4 23 = true := by decide +kernel
theorem chainCheck_4_24 : chainCheck 4 24 = true := by decide +kernel
theorem chainCheck_4_25 : chainCheck 4 25 = true := by decide +kernel
theorem chainCheck_4_26 : chainCheck 4 26 = true := by decide +kernel
theorem chainCheck_4_27 : chainCheck 4 27 = true := by decide +kernel
theorem chainCheck_4_28 : chainCheck 4 28 = true := by decide +kernel
theorem chainCheck_4_29 : chainCheck 4 29 = true := by decide +kernel
theorem chainCheck_4_30 : chainCheck 4 30 = true := by decide +kernel
theorem chainCheck_4_31 : chainCheck 4 31 = true := by decide +kernel

end SigGolfCandidate.Verify
