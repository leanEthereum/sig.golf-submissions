import SigGolfCandidate.Verify.FoldCheckA
import SigGolfCandidate.Verify.FoldCheckB

/-! All 174 Merkle fold levels. -/

namespace SigGolfCandidate.Verify

theorem forsFoldOk_all : ((List.range 14).all forsFoldOk) = true := by
  rw [List.all_eq_true]; intro k hk; simp only [List.mem_range] at hk
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

theorem layFoldOk_all : ((List.range 7).all layFoldOk) = true := by
  rw [List.all_eq_true]; intro k hk; simp only [List.mem_range] at hk
  interval_cases k
  · exact layFoldOk_0
  · exact layFoldOk_1
  · exact layFoldOk_2
  · exact layFoldOk_3
  · exact layFoldOk_4
  · exact layFoldOk_5
  · exact layFoldOk_6

end SigGolfCandidate.Verify
