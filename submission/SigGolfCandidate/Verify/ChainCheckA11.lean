import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckA10

/-! Kernel check of chain blocks (layer, chain) (2, 26) .. (2, 35) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_2_26 : chainCheck 2 26 = true := by decide +kernel
theorem chainCheck_2_27 : chainCheck 2 27 = true := by decide +kernel
theorem chainCheck_2_28 : chainCheck 2 28 = true := by decide +kernel
theorem chainCheck_2_29 : chainCheck 2 29 = true := by decide +kernel
theorem chainCheck_2_30 : chainCheck 2 30 = true := by decide +kernel
theorem chainCheck_2_31 : chainCheck 2 31 = true := by decide +kernel
theorem chainCheck_2_32 : chainCheck 2 32 = true := by decide +kernel
theorem chainCheck_2_33 : chainCheck 2 33 = true := by decide +kernel
theorem chainCheck_2_34 : chainCheck 2 34 = true := by decide +kernel
theorem chainCheck_2_35 : chainCheck 2 35 = true := by decide +kernel

end SigGolfCandidate.Verify
