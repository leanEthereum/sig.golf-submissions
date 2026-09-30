import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.TableToReference
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.GameComparison

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

attribute [local irreducible] Concrete.gameAfterSecrets

theorem evalDist_secrets_continuation {α : Type} (next : Secrets → ProbComp α) :
    𝒮[do let outputs ← sampleSecretOutputs; next (tableOts outputs, tableFts outputs)] =
      𝒮[do let secret ← sampleSecrets; next secret] := by
  rw [evalSPMF_bind, evalDist_secretOutputs_from_halves, ← evalSPMF_bind]
  simp only [bind_assoc, pure_bind, tableOts_from_halves, tableFts_from_halves]
  apply evalSPMF_bind_congr'
  intro secret
  apply evalSPMF_ext
  intro value
  simp

theorem evalDist_referenceOutputs (adversary : Adversary) :
    𝒮[do
      let outputs ← sampleSecretOutputs
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary 0
        (tableOts outputs) (tableFts outputs))).run' ∅] =
      𝒮[(simulateQ romImpl (gameCore Concrete.scheme adversary)).run' ∅] := by
  rw [gameCore_independent_eq, run'_lift_sample_bind]
  exact evalDist_secrets_continuation fun secret =>
    (simulateQ romImpl (Concrete.gameAfterSecrets adversary 0 secret.1 secret.2)).run' ∅

theorem worldHandler_randomOracle : worldHandler randomOracle = romImpl := rfl

theorem evalDist_independentTableGame_memo (adversary : Adversary) :
    𝒮[independentTableGame (memoAdversary adversary)] =
      𝒮[(simulateQ romImpl (gameCore Concrete.scheme (memoAdversary adversary))).run' ∅] := by
  rw [← evalDist_referenceOutputs]
  unfold independentTableGame drawSigningMaterial
  simp only [bind_assoc, pure_bind]
  apply evalSPMF_bind_congr'
  intro outputs
  have h := evalDist_tableGameAfterSecrets_memo randomOracle adversary outputs ∅
  rw [worldHandler_randomOracle] at h
  have heq := congrArg (fun distribution => Prod.fst <$> distribution) h
  simpa only [StateT.run'_eq, evalSPMF_map, evalSPMF_bind, map_bind] using heq

theorem forgeAdvantage_deterministic_le_reference (adversary : Adversary) (q : Nat)
    (hbound : HasTableBudget adversary q) :
    forgeAdvantage scheme adversary ≤ forgeAdvantage Concrete.scheme (memoAdversary adversary) +
      q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hmemo := prob_independentTableGame_le_memo adversary
  rw [probOutput_congr rfl (evalDist_independentTableGame_memo adversary)] at hmemo
  exact (forgeAdvantage_deterministic_le_table adversary q hbound).trans (add_le_add hmemo le_rfl)

end SphincsSecurity.Seeded
