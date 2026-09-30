import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckA02

/-! Kernel check of chain blocks (layer, chain) (0, 30) .. (0, 39) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_0_30 : chainCheck 0 30 = true := by decide +kernel
theorem chainCheck_0_31 : chainCheck 0 31 = true := by decide +kernel
theorem chainCheck_0_32 : chainCheck 0 32 = true := by decide +kernel
theorem chainCheck_0_33 : chainCheck 0 33 = true := by decide +kernel
theorem chainCheck_0_34 : chainCheck 0 34 = true := by decide +kernel
theorem chainCheck_0_35 : chainCheck 0 35 = true := by decide +kernel
theorem chainCheck_0_36 : chainCheck 0 36 = true := by decide +kernel
theorem chainCheck_0_37 : chainCheck 0 37 = true := by decide +kernel
theorem chainCheck_0_38 : chainCheck 0 38 = true := by decide +kernel
theorem chainCheck_0_39 : chainCheck 0 39 = true := by decide +kernel

end SigGolfCandidate.Verify
