import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB00

/-! Kernel check of chain blocks (layer, chain) (2, 36) .. (3, 3) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_2_36 : chainCheck 2 36 = true := by decide +kernel
theorem chainCheck_2_37 : chainCheck 2 37 = true := by decide +kernel
theorem chainCheck_2_38 : chainCheck 2 38 = true := by decide +kernel
theorem chainCheck_2_39 : chainCheck 2 39 = true := by decide +kernel
theorem chainCheck_2_40 : chainCheck 2 40 = true := by decide +kernel
theorem chainCheck_2_41 : chainCheck 2 41 = true := by decide +kernel
theorem chainCheck_3_0 : chainCheck 3 0 = true := by decide +kernel
theorem chainCheck_3_1 : chainCheck 3 1 = true := by decide +kernel
theorem chainCheck_3_2 : chainCheck 3 2 = true := by decide +kernel
theorem chainCheck_3_3 : chainCheck 3 3 = true := by decide +kernel

end SigGolfCandidate.Verify
