import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB13

/-! Kernel check of chain blocks (layer, chain) (6, 38) .. (6, 41) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_6_38 : chainCheck 6 38 = true := by decide +kernel
theorem chainCheck_6_39 : chainCheck 6 39 = true := by decide +kernel
theorem chainCheck_6_40 : chainCheck 6 40 = true := by decide +kernel
theorem chainCheck_6_41 : chainCheck 6 41 = true := by decide +kernel

end SigGolfCandidate.Verify
