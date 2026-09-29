import SigGolfCandidate.Verify.PorsCheckA

/-! Kernel check of the PORS code blocks: prologue and setup, leaves, dispatches, entry tails,
ladder positions, tails. -/

namespace SigGolfCandidate.Verify

theorem startCheck_ok : startCheck = true := by decide +kernel
theorem leafCheck_all : (List.range 15).all leafCheck = true := by decide +kernel
theorem dispCheck_all : (List.range 18).all dispCheck = true := by decide +kernel
theorem entCheck_ok : entCheck = true := by decide +kernel
theorem posCheck_0 : posCheck 0 = true := by decide +kernel
theorem posCheck_1 : posCheck 1 = true := by decide +kernel
theorem posCheck_2 : posCheck 2 = true := by decide +kernel
theorem tailCheck_all : (List.range 3).all tailCheck = true := by decide +kernel
theorem tailFCheck_all : (List.range 3).all tailFCheck = true := by decide +kernel

end SigGolfCandidate.Verify
