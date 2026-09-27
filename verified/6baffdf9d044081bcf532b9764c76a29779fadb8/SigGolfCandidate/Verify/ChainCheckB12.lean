import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.ChainCheckB11

/-! Kernel check of chain blocks (layer, chain) (5, 40) .. (5, 41) (one declaration per chain;
the import chain serializes this family to bound parallel build memory). -/

namespace SigGolfCandidate.Verify

theorem chainCheck_5_40 : chainCheck 5 40 = true := by decide +kernel
theorem chainCheck_5_41 : chainCheck 5 41 = true := by decide +kernel

end SigGolfCandidate.Verify
