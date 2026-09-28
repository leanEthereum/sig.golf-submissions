import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckA08

/-! Kernel check of chain blocks (layer, chain) (2, 6) .. (2, 15) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_2_6 : chainCheck 2 6 = true := by decide +kernel
theorem chainCheck_2_7 : chainCheck 2 7 = true := by decide +kernel
theorem chainCheck_2_8 : chainCheck 2 8 = true := by decide +kernel
theorem chainCheck_2_9 : chainCheck 2 9 = true := by decide +kernel
theorem chainCheck_2_10 : chainCheck 2 10 = true := by decide +kernel
theorem chainCheck_2_11 : chainCheck 2 11 = true := by decide +kernel
theorem chainCheck_2_12 : chainCheck 2 12 = true := by decide +kernel
theorem chainCheck_2_13 : chainCheck 2 13 = true := by decide +kernel
theorem chainCheck_2_14 : chainCheck 2 14 = true := by decide +kernel
theorem chainCheck_2_15 : chainCheck 2 15 = true := by decide +kernel

end SigGolfCandidate.Verify
