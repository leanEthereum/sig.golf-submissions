import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.RequestSampling
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.ReferenceSource
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.MemoTable
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.CostState

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {State : Type}

attribute [local irreducible] tableSign

theorem evalDist_tableGameAfterSecrets_memo (hash : QueryImpl HashSpec (StateT State ProbComp))
    (adversary : Adversary) (outputs : SecretOutputs) (state : State) :
    𝒮[do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ (worldHandler hash) (tableGameAfterSecrets (memoAdversary adversary) outputs randomizers)).run state] =
      𝒮[(simulateQ (worldHandler hash) (Concrete.gameAfterSecrets (memoAdversary adversary)
        0 (tableOts outputs) (tableFts outputs))).run state] := by
  unfold tableGameAfterSecrets Concrete.gameAfterSecrets
  simp only [simulateQ_bind, StateT.run_bind]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro result
  change _ = 𝒮[(simulateQ (worldHandler hash) (gameRest Concrete.scheme (memoAdversary adversary)
    ⟨result.1 (layerHeight topLayer) 0, 0⟩ (tableKey 0 result.1 outputs))).run result.2]
  have hleft (randomizers) := runSigning_sourceGame randomizers (tableKey 0 result.1 outputs)
    ⟨result.1 (layerHeight topLayer) 0, 0⟩ (memoAdversary adversary)
  simp_rw [← hleft]
  rw [← runWorldSigning_sourceGame, simulateQ_runWorldSigning]
  exact evalDist_tableRequests hash (tableKey 0 result.1 outputs)
    (sourceGame ⟨result.1 (layerHeight topLayer) 0, 0⟩ (memoAdversary adversary))
    (freshRequests_sourceGame_memo _ _) result.2

end SphincsSecurity.Seeded
