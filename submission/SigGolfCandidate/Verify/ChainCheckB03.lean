import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB02

/-! Kernel check of chain blocks (layer, chain) (4, 12) .. (4, 21) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_4_12 : chainCheck 4 12 = true := by decide +kernel
theorem chainCheck_4_13 : chainCheck 4 13 = true := by decide +kernel
theorem chainCheck_4_14 : chainCheck 4 14 = true := by decide +kernel
theorem chainCheck_4_15 : chainCheck 4 15 = true := by decide +kernel
theorem chainCheck_4_16 : chainCheck 4 16 = true := by decide +kernel
theorem chainCheck_4_17 : chainCheck 4 17 = true := by decide +kernel
theorem chainCheck_4_18 : chainCheck 4 18 = true := by decide +kernel
theorem chainCheck_4_19 : chainCheck 4 19 = true := by decide +kernel
theorem chainCheck_4_20 : chainCheck 4 20 = true := by decide +kernel
theorem chainCheck_4_21 : chainCheck 4 21 = true := by decide +kernel

end SigGolfCandidate.Verify
