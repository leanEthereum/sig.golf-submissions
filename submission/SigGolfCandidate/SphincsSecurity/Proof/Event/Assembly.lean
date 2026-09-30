import SigGolfCandidate.SphincsSecurity.Proof.Event.Transfer
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualEventLarge
import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.SmallEvent
/-!
# Assembly of the event form

The ideal (independent) scheme's event-form bound splits at `budgetSplit`: above it the large-budget
chain (`RetainedResidualEventLarge`), below it the small-budget chain.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security

theorem independentEventStatement : IndependentEventStatement := by
  intro q _ adversary
  have hcast : ((2 ^ 127 : Nat) : ℝ≥0∞) = (2 : ℝ≥0∞) ^ 127 := by norm_num
  rw [hcast]
  by_cases h : q + 1 ≤ Concrete.budgetSplit
  · exact Concrete.EventSmall.security127_event_of_small_budget q h adversary
  · exact Concrete.security127_event_of_large_budget q (by omega) adversary

/-- **The event form of the 127-bit bound**, for every adversary, with no query bound. -/
theorem security127_event : ∀ q : Nat, 1 ≤ q → ∀ adversary : Security.Adversary,
    Pr[fun result => result.1 = true ∧ result.2 ≤ q | Security.experiment adversary] ≤
      (q : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
  fun q hq adversary => security127_event_of_independent independentEventStatement q hq adversary

end SphincsSecurity.Security
