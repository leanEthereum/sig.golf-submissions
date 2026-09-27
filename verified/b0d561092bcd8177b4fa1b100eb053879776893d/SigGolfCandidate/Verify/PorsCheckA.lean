import SigGolfCandidate.Verify.PorsRuns

/-! Kernel check of the PORS dispatch tables (both tables, 256 entries each). -/

namespace SigGolfCandidate.Verify

theorem tabCheck_N0 : tabCheck 0 0 128 = true := by decide +kernel
theorem tabCheck_N1 : tabCheck 0 128 128 = true := by decide +kernel
theorem tabCheck_L0 : tabCheck 1 0 128 = true := by decide +kernel
theorem tabCheck_L1 : tabCheck 1 128 128 = true := by decide +kernel

theorem tabCheck1_ok (tb b : Nat) (htb : tb < 2) (hb : b < 256) : tabCheck1 tb b = true := by
  have h : ∀ lo, tabCheck tb lo 128 = true → lo ≤ b → b < lo + 128 → tabCheck1 tb b = true := by
    intro lo hc h1 h2
    simp only [tabCheck, List.all_eq_true, List.mem_range'] at hc
    obtain ⟨i, hi, rfl⟩ : ∃ i, i < 128 ∧ b = lo + 1 * i := ⟨b - lo, by omega, by omega⟩
    exact hc _ ⟨i, hi, rfl⟩
  rcases (show tb = 0 ∨ tb = 1 by omega) with rfl | rfl
  · by_cases hb' : b < 128
    · exact h 0 tabCheck_N0 (by omega) (by omega)
    · exact h 128 tabCheck_N1 (by omega) (by omega)
  · by_cases hb' : b < 128
    · exact h 0 tabCheck_L0 (by omega) (by omega)
    · exact h 128 tabCheck_L1 (by omega) (by omega)

end SigGolfCandidate.Verify
