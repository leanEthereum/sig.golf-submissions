import SigGolfCandidate.Verify.FoldCheckB

/-! All Merkle fold levels. -/

namespace SigGolfCandidate.Verify

theorem layFoldOk_at (k : Nat) (hk : k < 5) : layFoldOk k = true := by
  interval_cases k
  · exact layFoldOk_0
  · exact layFoldOk_1
  · exact layFoldOk_2
  · exact layFoldOk_3
  · exact layFoldOk_4

end SigGolfCandidate.Verify
