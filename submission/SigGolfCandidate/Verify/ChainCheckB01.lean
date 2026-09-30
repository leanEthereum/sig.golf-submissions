import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB00

/-! Kernel check of chain blocks (layer, chain) (3, 34) .. (4, 1) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_3_34 : chainCheck 3 34 = true := by decide +kernel
theorem chainCheck_3_35 : chainCheck 3 35 = true := by decide +kernel
theorem chainCheck_3_36 : chainCheck 3 36 = true := by decide +kernel
theorem chainCheck_3_37 : chainCheck 3 37 = true := by decide +kernel
theorem chainCheck_3_38 : chainCheck 3 38 = true := by decide +kernel
theorem chainCheck_3_39 : chainCheck 3 39 = true := by decide +kernel
theorem chainCheck_3_40 : chainCheck 3 40 = true := by decide +kernel
theorem chainCheck_3_41 : chainCheck 3 41 = true := by decide +kernel
theorem chainCheck_4_0 : chainCheck 4 0 = true := by decide +kernel
theorem chainCheck_4_1 : chainCheck 4 1 = true := by decide +kernel

end SigGolfCandidate.Verify
