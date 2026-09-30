import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckA07

/-! Kernel check of chain blocks (layer, chain) (1, 38) .. (2, 5) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_1_38 : chainCheck 1 38 = true := by decide +kernel
theorem chainCheck_1_39 : chainCheck 1 39 = true := by decide +kernel
theorem chainCheck_1_40 : chainCheck 1 40 = true := by decide +kernel
theorem chainCheck_1_41 : chainCheck 1 41 = true := by decide +kernel
theorem chainCheck_2_0 : chainCheck 2 0 = true := by decide +kernel
theorem chainCheck_2_1 : chainCheck 2 1 = true := by decide +kernel
theorem chainCheck_2_2 : chainCheck 2 2 = true := by decide +kernel
theorem chainCheck_2_3 : chainCheck 2 3 = true := by decide +kernel
theorem chainCheck_2_4 : chainCheck 2 4 = true := by decide +kernel
theorem chainCheck_2_5 : chainCheck 2 5 = true := by decide +kernel

end SigGolfCandidate.Verify
