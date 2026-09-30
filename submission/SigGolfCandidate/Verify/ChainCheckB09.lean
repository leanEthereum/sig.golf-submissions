import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB08

/-! Kernel check of chain blocks (layer, chain) (5, 10) .. (5, 19) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_5_10 : chainCheck 5 10 = true := by decide +kernel
theorem chainCheck_5_11 : chainCheck 5 11 = true := by decide +kernel
theorem chainCheck_5_12 : chainCheck 5 12 = true := by decide +kernel
theorem chainCheck_5_13 : chainCheck 5 13 = true := by decide +kernel
theorem chainCheck_5_14 : chainCheck 5 14 = true := by decide +kernel
theorem chainCheck_5_15 : chainCheck 5 15 = true := by decide +kernel
theorem chainCheck_5_16 : chainCheck 5 16 = true := by decide +kernel
theorem chainCheck_5_17 : chainCheck 5 17 = true := by decide +kernel
theorem chainCheck_5_18 : chainCheck 5 18 = true := by decide +kernel
theorem chainCheck_5_19 : chainCheck 5 19 = true := by decide +kernel

end SigGolfCandidate.Verify
