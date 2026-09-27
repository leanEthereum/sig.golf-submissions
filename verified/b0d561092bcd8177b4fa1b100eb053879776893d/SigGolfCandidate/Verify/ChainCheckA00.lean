import SigGolfCandidate.Verify.ChainRuns

/-! Kernel check of chain blocks (layer, chain) (0, 0) .. (0, 9) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_0_0 : chainCheck 0 0 = true := by decide +kernel
theorem chainCheck_0_1 : chainCheck 0 1 = true := by decide +kernel
theorem chainCheck_0_2 : chainCheck 0 2 = true := by decide +kernel
theorem chainCheck_0_3 : chainCheck 0 3 = true := by decide +kernel
theorem chainCheck_0_4 : chainCheck 0 4 = true := by decide +kernel
theorem chainCheck_0_5 : chainCheck 0 5 = true := by decide +kernel
theorem chainCheck_0_6 : chainCheck 0 6 = true := by decide +kernel
theorem chainCheck_0_7 : chainCheck 0 7 = true := by decide +kernel
theorem chainCheck_0_8 : chainCheck 0 8 = true := by decide +kernel
theorem chainCheck_0_9 : chainCheck 0 9 = true := by decide +kernel

end SigGolfCandidate.Verify
