import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB04

/-! Kernel check of chain blocks (layer, chain) (4, 32) .. (4, 41) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_4_32 : chainCheck 4 32 = true := by decide +kernel
theorem chainCheck_4_33 : chainCheck 4 33 = true := by decide +kernel
theorem chainCheck_4_34 : chainCheck 4 34 = true := by decide +kernel
theorem chainCheck_4_35 : chainCheck 4 35 = true := by decide +kernel
theorem chainCheck_4_36 : chainCheck 4 36 = true := by decide +kernel
theorem chainCheck_4_37 : chainCheck 4 37 = true := by decide +kernel
theorem chainCheck_4_38 : chainCheck 4 38 = true := by decide +kernel
theorem chainCheck_4_39 : chainCheck 4 39 = true := by decide +kernel
theorem chainCheck_4_40 : chainCheck 4 40 = true := by decide +kernel
theorem chainCheck_4_41 : chainCheck 4 41 = true := by decide +kernel

end SigGolfCandidate.Verify
