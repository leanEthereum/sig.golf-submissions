import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB12

/-! Kernel check of chain blocks (layer, chain) (6, 28) .. (6, 37) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_6_28 : chainCheck 6 28 = true := by decide +kernel
theorem chainCheck_6_29 : chainCheck 6 29 = true := by decide +kernel
theorem chainCheck_6_30 : chainCheck 6 30 = true := by decide +kernel
theorem chainCheck_6_31 : chainCheck 6 31 = true := by decide +kernel
theorem chainCheck_6_32 : chainCheck 6 32 = true := by decide +kernel
theorem chainCheck_6_33 : chainCheck 6 33 = true := by decide +kernel
theorem chainCheck_6_34 : chainCheck 6 34 = true := by decide +kernel
theorem chainCheck_6_35 : chainCheck 6 35 = true := by decide +kernel
theorem chainCheck_6_36 : chainCheck 6 36 = true := by decide +kernel
theorem chainCheck_6_37 : chainCheck 6 37 = true := by decide +kernel

end SigGolfCandidate.Verify
