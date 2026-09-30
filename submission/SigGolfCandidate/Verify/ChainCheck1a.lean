import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheck0b

/-! Kernel check of the chain blocks 0..20 of layer 1 (one declaration per chain). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_1_0 : chainCheck 1 0 = true := by decide +kernel
theorem chainCheck_1_1 : chainCheck 1 1 = true := by decide +kernel
theorem chainCheck_1_2 : chainCheck 1 2 = true := by decide +kernel
theorem chainCheck_1_3 : chainCheck 1 3 = true := by decide +kernel
theorem chainCheck_1_4 : chainCheck 1 4 = true := by decide +kernel
theorem chainCheck_1_5 : chainCheck 1 5 = true := by decide +kernel
theorem chainCheck_1_6 : chainCheck 1 6 = true := by decide +kernel
theorem chainCheck_1_7 : chainCheck 1 7 = true := by decide +kernel
theorem chainCheck_1_8 : chainCheck 1 8 = true := by decide +kernel
theorem chainCheck_1_9 : chainCheck 1 9 = true := by decide +kernel
theorem chainCheck_1_10 : chainCheck 1 10 = true := by decide +kernel
theorem chainCheck_1_11 : chainCheck 1 11 = true := by decide +kernel
theorem chainCheck_1_12 : chainCheck 1 12 = true := by decide +kernel
theorem chainCheck_1_13 : chainCheck 1 13 = true := by decide +kernel
theorem chainCheck_1_14 : chainCheck 1 14 = true := by decide +kernel
theorem chainCheck_1_15 : chainCheck 1 15 = true := by decide +kernel
theorem chainCheck_1_16 : chainCheck 1 16 = true := by decide +kernel
theorem chainCheck_1_17 : chainCheck 1 17 = true := by decide +kernel
theorem chainCheck_1_18 : chainCheck 1 18 = true := by decide +kernel
theorem chainCheck_1_19 : chainCheck 1 19 = true := by decide +kernel
theorem chainCheck_1_20 : chainCheck 1 20 = true := by decide +kernel

end SigGolfCandidate.Verify
