import SigGolfCandidate.SphincsSecurity.Proof.Base.RomQueryCharge
import SigGolfCandidate.SphincsSecurity.Proof.Reference.QueryBound
/-!
# Potentials truncated at a hash-call budget

If every hash call raises a cache potential by at most `rate` in expectation, then the potential
counted only on paths that stay within `r` hash calls, plus `rate` for every call still left, is a
supermartingale. So its expectation is at most the initial potential plus `rate * r`, whatever the
computation does after the budget runs out.
-/
namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

noncomputable def truncatedPotential (potential : QueryCache HashSpec → ℝ≥0∞) (rate : ℝ≥0∞) (budget count : Nat)
    (cache : QueryCache HashSpec) : ℝ≥0∞ :=
  if count ≤ budget then potential cache + rate * ((budget - count : Nat) : ℝ≥0∞) else 0

theorem expected_truncatedPotential_le {α : Type}
    (potential : QueryCache HashSpec → ℝ≥0∞) (rate : ℝ≥0∞)
    (hstep : ∀ (query : OracleWorld.Domain) (cache : QueryCache HashSpec), Finite cache →
      (∑' result, Pr[= result | (romImpl query).run cache] * potential result.2) ≤
        potential cache + (if query matches .inr _ then rate else 0))
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (hfinite : Finite cache) (budget : Nat) :
    (∑' result, Pr[= result | (simulateQ romImpl (countHashQueries computation)).run cache] *
      truncatedPotential potential rate budget result.1.2 result.2) ≤ potential cache + rate * budget := by
  induction computation using OracleComp.inductionOn generalizing cache budget with
  | pure value =>
      simp only [countHashQueries_pure, simulateQ_pure, StateT.run_pure, tsum_probOutput_pure_mul, truncatedPotential,
        zero_le, if_true, Nat.sub_zero, le_refl]
  | query_bind query next ih =>
      rw [countHashQueries_query_bind, simulateQ_bind, simulateQ_spec_query, StateT.run_bind, tsum_probOutput_bind_mul]
      simp only [bind_pure_comp, simulateQ_map, StateT.run_map, tsum_probOutput_map_mul]
      have hmass := romImpl_query_mass query cache
      cases query with
      | inl sample =>
          simp only [Bool.false_eq_true, if_false, zero_add]
          calc
            _ ≤ ∑' result, Pr[= result | (romImpl (.inl sample)).run cache] * (potential result.2 + rate * budget) := by
              apply ENNReal.tsum_le_tsum
              intro result
              by_cases hresult : result ∈ support ((romImpl (.inl sample)).run cache)
              · exact mul_le_mul' le_rfl (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hresult) budget)
              · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
            _ = (∑' result, Pr[= result | (romImpl (.inl sample)).run cache] * potential result.2) + rate * budget := by
              simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
            _ ≤ _ := by
              have h := hstep (.inl sample) cache hfinite
              simp only [Bool.false_eq_true, if_false, add_zero] at h
              exact add_le_add h le_rfl
      | inr input =>
          simp only [if_true]
          cases budget with
          | zero =>
              refine le_trans (le_of_eq ?_) zero_le
              apply ENNReal.tsum_eq_zero.mpr
              intro result
              apply mul_eq_zero_of_right
              apply ENNReal.tsum_eq_zero.mpr
              intro inner
              apply mul_eq_zero_of_right
              simp [truncatedPotential]
          | succ remaining =>
              calc
                _ ≤ ∑' result, Pr[= result | (romImpl (.inr input)).run cache] * (potential result.2 + rate * remaining) := by
                  apply ENNReal.tsum_le_tsum
                  intro result
                  by_cases hresult : result ∈ support ((romImpl (.inr input)).run cache)
                  · apply mul_le_mul' le_rfl
                    refine le_trans (le_of_eq ?_) (ih result.1 result.2 (finite_of_mem_support_romImpl hfinite hresult) remaining)
                    apply tsum_congr
                    intro inner
                    congr 1
                    unfold truncatedPotential
                    by_cases hk : inner.1.2 ≤ remaining
                    · rw [if_pos (by omega), if_pos hk]
                      congr 3
                      omega
                    · rw [if_neg (by omega), if_neg hk]
                  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul, zero_mul]
                _ = (∑' result, Pr[= result | (romImpl (.inr input)).run cache] * potential result.2) + rate * remaining := by
                  simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, hmass, one_mul]
                _ ≤ (potential cache + rate) + rate * remaining := add_le_add (by simpa using hstep (.inr input) cache hfinite) le_rfl
                _ = _ := by push_cast; ring

end SphincsSecurity
