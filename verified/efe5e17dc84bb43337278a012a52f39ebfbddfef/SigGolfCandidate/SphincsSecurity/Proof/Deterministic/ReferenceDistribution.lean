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
  rw [evalSPMF_bind, evalDist_secretOutputs, ← evalSPMF_bind]
  simp only [bind_map_left, tableOts_secretTables, tableFts_secretTables]

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

end SphincsSecurity.Seeded
