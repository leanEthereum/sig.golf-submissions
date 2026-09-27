import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB10

/-! Kernel check of chain blocks (layer, chain) (5, 30) .. (5, 39) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_5_30 : chainCheck 5 30 = true := by decide +kernel
theorem chainCheck_5_31 : chainCheck 5 31 = true := by decide +kernel
theorem chainCheck_5_32 : chainCheck 5 32 = true := by decide +kernel
theorem chainCheck_5_33 : chainCheck 5 33 = true := by decide +kernel
theorem chainCheck_5_34 : chainCheck 5 34 = true := by decide +kernel
theorem chainCheck_5_35 : chainCheck 5 35 = true := by decide +kernel
theorem chainCheck_5_36 : chainCheck 5 36 = true := by decide +kernel
theorem chainCheck_5_37 : chainCheck 5 37 = true := by decide +kernel
theorem chainCheck_5_38 : chainCheck 5 38 = true := by decide +kernel
theorem chainCheck_5_39 : chainCheck 5 39 = true := by decide +kernel

end SigGolfCandidate.Verify
