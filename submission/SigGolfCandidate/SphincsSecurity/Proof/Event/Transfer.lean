import SigGolfCandidate.SphincsSecurity.Proof.Event.Deterministic
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.MacElimination
/-!
# From the independent scheme to the statement, in event form

Everything but the ideal bound itself: the event-form statement for the experiment of `Statement.lean`,
given the event-form bound for the table-secret scheme.

1. `experiment_event_le_cachedTable`: the seed is erased (every derivation, masks and MAC answers
   included, is presampled), at one query less and one 256-bit seed guess per query.
2. `cachedTable_le_simulated`: the cache's masks and MAC are eliminated. The masked region is uniform and
   independent of the tree, so the simulating adversary publishes a uniform region and tag itself and
   answers every request with another cache by `none`; a request with another cache that passes the MAC
   check costs `2^-256`, and a winning run has at most `2^32` requests.
3. Memoizing the signing requests turns the table game into the independent scheme's game.
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

open Seeded in
attribute [local irreducible] cachedTableGameAfterSecrets tableGameAfterSecrets sampleSecretOutputs
  sampleRandomizerOutputs sampleMaskOutputs sampleMacOutputs in
/-- The experiment against the independent scheme, in event form. -/
theorem experiment_event_le_independent (adversary : Adversary) (q : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q | experiment adversary] ≤
      Concrete.forgeEventAdvantage Concrete.scheme (memoAdversary (simAdversary adversary)) (q - 1) +
        (2 ^ 32 : ℝ≥0∞) / 2 ^ 256 + ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  refine (experiment_event_le_cachedTable adversary q).trans (add_le_add ?_ le_rfl)
  calc
    _ ≤ Pr[fun result => result.1 = true ∧ result.2 ≤ q - 1 | do
          let outputs ← sampleSecretOutputs
          let randomizers ← sampleRandomizerOutputs
          (simulateQ romImpl (countHashQueries
            (tableGameAfterSecrets (simAdversary adversary) outputs randomizers))).run' ∅] +
          (2 ^ 32 : ℝ≥0∞) / 2 ^ 256 := by
      apply probEvent_bind_congr_le_add
      intro outputs _
      apply probEvent_bind_congr_le_add
      intro randomizers _
      exact cachedTable_le_simulated adversary outputs randomizers (q - 1)
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      unfold Concrete.forgeEventAdvantage
      rw [← simulateQ_countHashQueries]
      refine le_trans (probEvent_bind_mono fun outputs _ => probEvent_bind_mono fun randomizers _ =>
        probEvent_tableGameAfterSecrets_memo_counted (simAdversary adversary) outputs randomizers ∅ (q - 1))
        (le_of_eq ?_)
      exact probEvent_of_evalSPMF_eq (evalDist_independentTable_memo_counted (simAdversary adversary)) _

/-- The losses of the transfer fit in the slack between `q - 1` and `q` queries. -/
theorem transfer_loss_absorbed (q : Nat) (hq : 2 ≤ q) (hsmall : q < 2 ^ 127) :
    ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 127 : Nat) : ℝ≥0∞) + (2 ^ 32 : ℝ≥0∞) / 2 ^ 256 +
      ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) ≤ q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  have hq' : ((q - 1 : Nat) : ℝ) + 1 = q := by
    have : q - 1 + 1 = q := by omega
    exact_mod_cast this
  have hlt : ((q - 1 : Nat) : ℝ) < 2 ^ 127 := by
    have : q - 1 < 2 ^ 127 := by omega
    exact_mod_cast this
  have hnonneg : (0 : ℝ) ≤ ((q - 1 : Nat) : ℝ) := by positivity
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
    ENNReal.toReal_pow, ENNReal.toReal_ofNat, Nat.cast_pow, Nat.cast_ofNat]
  rw [← hq']
  have h1 : ((q - 1 : Nat) : ℝ) / 2 ^ 256 ≤ 1 / 2 ^ 129 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have h2 : (2 : ℝ) ^ 32 / 2 ^ 256 ≤ 1 / 2 ^ 129 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    norm_num
  have h3 : (1 : ℝ) / 2 ^ 129 + 1 / 2 ^ 129 ≤ 1 / 2 ^ 127 := by norm_num
  rw [add_div]
  linarith

theorem security127_event_of_independent (hideal : IndependentEventStatement)
    (hzero : ∀ adversary : SphincsSecurity.Adversary, Concrete.forgeEventAdvantage Concrete.scheme adversary 0 = 0)
    (q : Nat) (hq : 1 ≤ q) (adversary : Adversary) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q | experiment adversary] ≤ q / ((2 ^ 127 : Nat) : ℝ≥0∞) := by
  by_cases hsmall : q < 2 ^ 127
  · refine (experiment_event_le_independent adversary q).trans ?_
    by_cases hone : q = 1
    · subst q
      rw [Nat.sub_self, hzero, Nat.cast_zero, ENNReal.zero_div, add_zero, zero_add]
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      simp only [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofNat, ENNReal.toReal_natCast,
        Nat.cast_one, Nat.cast_pow, Nat.cast_ofNat]
      norm_num
    · exact (add_le_add (add_le_add (hideal (q - 1) (by omega) _) le_rfl) le_rfl).trans
        (transfer_loss_absorbed q (by omega) hsmall)
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
