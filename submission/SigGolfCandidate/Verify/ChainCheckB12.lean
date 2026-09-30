import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB11

/-! Kernel check of chain blocks (layer, chain) (6, 18) .. (6, 27) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_6_18 : chainCheck 6 18 = true := by decide +kernel
theorem chainCheck_6_19 : chainCheck 6 19 = true := by decide +kernel
theorem chainCheck_6_20 : chainCheck 6 20 = true := by decide +kernel
theorem chainCheck_6_21 : chainCheck 6 21 = true := by decide +kernel
theorem chainCheck_6_22 : chainCheck 6 22 = true := by decide +kernel
theorem chainCheck_6_23 : chainCheck 6 23 = true := by decide +kernel
theorem chainCheck_6_24 : chainCheck 6 24 = true := by decide +kernel
theorem chainCheck_6_25 : chainCheck 6 25 = true := by decide +kernel
theorem chainCheck_6_26 : chainCheck 6 26 = true := by decide +kernel
theorem chainCheck_6_27 : chainCheck 6 27 = true := by decide +kernel

end SigGolfCandidate.Verify
