import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB09

/-! Kernel check of chain blocks (layer, chain) (5, 40) .. (6, 7) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_5_40 : chainCheck 5 40 = true := by decide +kernel
theorem chainCheck_5_41 : chainCheck 5 41 = true := by decide +kernel
theorem chainCheck_6_0 : chainCheck 6 0 = true := by decide +kernel
theorem chainCheck_6_1 : chainCheck 6 1 = true := by decide +kernel
theorem chainCheck_6_2 : chainCheck 6 2 = true := by decide +kernel
theorem chainCheck_6_3 : chainCheck 6 3 = true := by decide +kernel
theorem chainCheck_6_4 : chainCheck 6 4 = true := by decide +kernel
theorem chainCheck_6_5 : chainCheck 6 5 = true := by decide +kernel
theorem chainCheck_6_6 : chainCheck 6 6 = true := by decide +kernel
theorem chainCheck_6_7 : chainCheck 6 7 = true := by decide +kernel

end SigGolfCandidate.Verify
