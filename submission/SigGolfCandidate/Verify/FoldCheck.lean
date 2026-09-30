import SigGolfCandidate.Verify.FoldCheckB

/-! All Merkle fold levels. -/

namespace SigGolfCandidate.Verify

theorem forsFoldOk_at (k : Nat) (hk : k < 14) : forsFoldOk k = true := by
  interval_cases k
  · exact forsFoldOk_0
  · exact forsFoldOk_1
  · exact forsFoldOk_2
  · exact forsFoldOk_3
  · exact forsFoldOk_4
  · exact forsFoldOk_5
  · exact forsFoldOk_6
  · exact forsFoldOk_7
  · exact forsFoldOk_8
  · exact forsFoldOk_9
  · exact forsFoldOk_10
  · exact forsFoldOk_11
  · exact forsFoldOk_12
  · exact forsFoldOk_13

theorem layFoldOk_at (k : Nat) (hk : k < 6) : layFoldOk k = true := by
  interval_cases k
  · exact layFoldOk_0
  · exact layFoldOk_1
  · exact layFoldOk_2
  · exact layFoldOk_3
  · exact layFoldOk_4
  · exact layFoldOk_5

end SigGolfCandidate.Verify
