import SigGolfCandidate.SphincsSecurity.Proof.Event.Deterministic
import SigGolfCandidate.SphincsSecurity.Proof.Adversary.Embedding
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Security
/-!
# From the independent scheme to the statement, in event form

Everything but the ideal bound itself: the event-form statement for the experiment of `Statement.lean`,
given the event-form bound for the table-secret scheme.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Security

set_option backward.isDefEq.respectTransparency false

/-- The event-form claim for the scheme of the ideal proof. -/
def IndependentEventStatement : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary : SphincsSecurity.Adversary,
    Concrete.forgeEventAdvantage Concrete.scheme adversary q ≤ q / ((2 ^ 127 : Nat) : ℝ≥0∞)

theorem forgeEventAdvantage_mono {Key : Type} (scheme : SphincsSecurity.Scheme Key) (adversary : SphincsSecurity.Adversary)
    {q r : Nat} (h : q ≤ r) :
    Concrete.forgeEventAdvantage scheme adversary q ≤ Concrete.forgeEventAdvantage scheme adversary r :=
  probEvent_mono fun _ _ hresult => ⟨hresult.1, hresult.2.trans h⟩

theorem experiment_event_eq (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q | experiment adversary] =
      Concrete.forgeEventAdvantage Seeded.scheme (embed adversary) q := by
  rw [Concrete.forgeEventAdvantage, experiment_embed]
  rfl

theorem security127_event_of_independent (hideal : IndependentEventStatement) (q : Nat) (hq : 1 ≤ q)
    (adversary : Adversary) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q | experiment adversary] ≤ q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  rw [experiment_event_eq]
  by_cases hsmall : q < 2 ^ 127
  · refine (Seeded.forgeEventAdvantage_scheme_le_independent (embed adversary) q).trans ?_
    by_cases hone : q = 1
    · subst q
      have h := (forgeEventAdvantage_mono Concrete.scheme (Seeded.memoAdversary (embed adversary)) (Nat.zero_le 1)).trans
        (hideal 1 le_rfl (Seeded.memoAdversary (embed adversary)))
      simpa only [Nat.sub_self, Nat.cast_zero, ENNReal.zero_div, add_zero] using h
    · exact (add_le_add (hideal (q - 1) (by omega) _) le_rfl).trans (Seeded.seed_loss_absorbed q hq hsmall)
  · have hlarge : 2 ^ 127 ≤ q := Nat.le_of_not_gt hsmall
    calc
      _ ≤ 1 := probEvent_le_one
      _ = ((2 ^ 127 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) :=
        (ENNReal.div_self (by norm_num) (ENNReal.natCast_ne_top _)).symm
      _ ≤ _ := ENNReal.div_le_div (by exact_mod_cast hlarge) le_rfl

theorem probEvent_win_le_event (experimentLaw : ProbComp (Bool × Nat)) (q : Nat)
    (hbound : ∀ result ∈ support experimentLaw, result.2 ≤ q) :
    Pr[fun result => result.1 = true | experimentLaw] ≤ Pr[fun result => result.1 = true ∧ result.2 ≤ q | experimentLaw] :=
  probEvent_mono fun result hresult hwin => ⟨hwin, hbound result hresult⟩

/-- Under a pointwise query bound the budget event is the whole winning event. -/
theorem hasClassicalSecurityBits_of_event (bits : Nat)
    (hevent : ∀ q, 1 ≤ q → ∀ adversary : Adversary,
      Pr[fun result => result.1 = true ∧ result.2 ≤ q | experiment adversary] ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)) :
    HasClassicalSecurityBits bits := by
  intro q hq adversary hbound
  exact (probEvent_win_le_event (experiment adversary) q hbound).trans (hevent q hq adversary)

end SphincsSecurity.Security
