import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB01

/-! Kernel check of chain blocks (layer, chain) (3, 4) .. (3, 13) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_3_4 : chainCheck 3 4 = true := by decide +kernel
theorem chainCheck_3_5 : chainCheck 3 5 = true := by decide +kernel
theorem chainCheck_3_6 : chainCheck 3 6 = true := by decide +kernel
theorem chainCheck_3_7 : chainCheck 3 7 = true := by decide +kernel
theorem chainCheck_3_8 : chainCheck 3 8 = true := by decide +kernel
theorem chainCheck_3_9 : chainCheck 3 9 = true := by decide +kernel
theorem chainCheck_3_10 : chainCheck 3 10 = true := by decide +kernel
theorem chainCheck_3_11 : chainCheck 3 11 = true := by decide +kernel
theorem chainCheck_3_12 : chainCheck 3 12 = true := by decide +kernel
theorem chainCheck_3_13 : chainCheck 3 13 = true := by decide +kernel

end SigGolfCandidate.Verify
