import SigGolfCandidate.Verify.ForsRuns

/-! Kernel check of the prologue, digest, FORS tree prefixes and roots blocks. -/

namespace SigGolfCandidate.Verify

theorem treeCheck_1 : treeCheck 1 = true := by decide +kernel
theorem treeCheck_2 : treeCheck 2 = true := by decide +kernel
theorem treeCheck_3 : treeCheck 3 = true := by decide +kernel
theorem treeCheck_4 : treeCheck 4 = true := by decide +kernel
theorem treeCheck_5 : treeCheck 5 = true := by decide +kernel
theorem treeCheck_6 : treeCheck 6 = true := by decide +kernel
theorem treeCheck_7 : treeCheck 7 = true := by decide +kernel
theorem treeCheck_8 : treeCheck 8 = true := by decide +kernel
theorem treeCheck_9 : treeCheck 9 = true := by decide +kernel
theorem treeCheck_10 : treeCheck 10 = true := by decide +kernel
theorem treeCheck_11 : treeCheck 11 = true := by decide +kernel
theorem treeCheck_12 : treeCheck 12 = true := by decide +kernel
theorem treeCheck_13 : treeCheck 13 = true := by decide +kernel
theorem rootsCheck_ok : rootsCheck = true := by decide +kernel
theorem topCheck_ok : topCheck = true := by decide +kernel

theorem treeCheck_at (k : Nat) (h1 : 1 ≤ k) (hk : k < 14) : treeCheck k = true := by
  interval_cases k
  · exact treeCheck_1
  · exact treeCheck_2
  · exact treeCheck_3
  · exact treeCheck_4
  · exact treeCheck_5
  · exact treeCheck_6
  · exact treeCheck_7
  · exact treeCheck_8
  · exact treeCheck_9
  · exact treeCheck_10
  · exact treeCheck_11
  · exact treeCheck_12
  · exact treeCheck_13

end SigGolfCandidate.Verify
