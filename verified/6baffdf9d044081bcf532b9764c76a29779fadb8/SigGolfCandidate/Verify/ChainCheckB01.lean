import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB00

/-! Kernel check of chain blocks (layer, chain) (3, 14) .. (3, 23) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_3_14 : chainCheck 3 14 = true := by decide +kernel
theorem chainCheck_3_15 : chainCheck 3 15 = true := by decide +kernel
theorem chainCheck_3_16 : chainCheck 3 16 = true := by decide +kernel
theorem chainCheck_3_17 : chainCheck 3 17 = true := by decide +kernel
theorem chainCheck_3_18 : chainCheck 3 18 = true := by decide +kernel
theorem chainCheck_3_19 : chainCheck 3 19 = true := by decide +kernel
theorem chainCheck_3_20 : chainCheck 3 20 = true := by decide +kernel
theorem chainCheck_3_21 : chainCheck 3 21 = true := by decide +kernel
theorem chainCheck_3_22 : chainCheck 3 22 = true := by decide +kernel
theorem chainCheck_3_23 : chainCheck 3 23 = true := by decide +kernel

end SigGolfCandidate.Verify
