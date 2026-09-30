import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckA09

/-! Kernel check of chain blocks (layer, chain) (2, 16) .. (2, 25) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_2_16 : chainCheck 2 16 = true := by decide +kernel
theorem chainCheck_2_17 : chainCheck 2 17 = true := by decide +kernel
theorem chainCheck_2_18 : chainCheck 2 18 = true := by decide +kernel
theorem chainCheck_2_19 : chainCheck 2 19 = true := by decide +kernel
theorem chainCheck_2_20 : chainCheck 2 20 = true := by decide +kernel
theorem chainCheck_2_21 : chainCheck 2 21 = true := by decide +kernel
theorem chainCheck_2_22 : chainCheck 2 22 = true := by decide +kernel
theorem chainCheck_2_23 : chainCheck 2 23 = true := by decide +kernel
theorem chainCheck_2_24 : chainCheck 2 24 = true := by decide +kernel
theorem chainCheck_2_25 : chainCheck 2 25 = true := by decide +kernel

end SigGolfCandidate.Verify
