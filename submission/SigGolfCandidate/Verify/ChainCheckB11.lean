import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB10

/-! Kernel check of chain blocks (layer, chain) (6, 8) .. (6, 17) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_6_8 : chainCheck 6 8 = true := by decide +kernel
theorem chainCheck_6_9 : chainCheck 6 9 = true := by decide +kernel
theorem chainCheck_6_10 : chainCheck 6 10 = true := by decide +kernel
theorem chainCheck_6_11 : chainCheck 6 11 = true := by decide +kernel
theorem chainCheck_6_12 : chainCheck 6 12 = true := by decide +kernel
theorem chainCheck_6_13 : chainCheck 6 13 = true := by decide +kernel
theorem chainCheck_6_14 : chainCheck 6 14 = true := by decide +kernel
theorem chainCheck_6_15 : chainCheck 6 15 = true := by decide +kernel
theorem chainCheck_6_16 : chainCheck 6 16 = true := by decide +kernel
theorem chainCheck_6_17 : chainCheck 6 17 = true := by decide +kernel

end SigGolfCandidate.Verify
