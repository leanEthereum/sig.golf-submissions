import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB05

/-! Kernel check of chain blocks (layer, chain) (4, 2) .. (4, 11) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_4_2 : chainCheck 4 2 = true := by decide +kernel
theorem chainCheck_4_3 : chainCheck 4 3 = true := by decide +kernel
theorem chainCheck_4_4 : chainCheck 4 4 = true := by decide +kernel
theorem chainCheck_4_5 : chainCheck 4 5 = true := by decide +kernel
theorem chainCheck_4_6 : chainCheck 4 6 = true := by decide +kernel
theorem chainCheck_4_7 : chainCheck 4 7 = true := by decide +kernel
theorem chainCheck_4_8 : chainCheck 4 8 = true := by decide +kernel
theorem chainCheck_4_9 : chainCheck 4 9 = true := by decide +kernel
theorem chainCheck_4_10 : chainCheck 4 10 = true := by decide +kernel
theorem chainCheck_4_11 : chainCheck 4 11 = true := by decide +kernel

end SigGolfCandidate.Verify
