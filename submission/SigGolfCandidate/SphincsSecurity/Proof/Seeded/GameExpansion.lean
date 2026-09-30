import SigGolfCandidate.SphincsSecurity.Proof.Seeded.GameErasure
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Presampling
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.TableSampling

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem run'_lift_hash_bind {A B : Type} (computation : OracleComp HashSpec A)
    (next : A → OracleComp OracleWorld B) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld A) >>= next)).run' cache =
      ((simulateQ randomOracle computation).run cache >>= fun result =>
        (simulateQ romImpl (next result.1)).run' result.2) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld A) =
      simulateQ randomOracle computation :=
    QueryImpl.simulateQ_add_liftM_right _ _ computation
  rw [h, map_bind]
  rfl

theorem run'_lift_sample_bind {A B : Type} (computation : ProbComp A)
    (next : A → OracleComp OracleWorld B) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld A) >>= next)).run' cache =
      (computation >>= fun result => (simulateQ romImpl (next result)).run' cache) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld A) =
      simulateQ (unifFwdImpl HashSpec) computation :=
    QueryImpl.simulateQ_add_liftM_left _ _ computation
  rw [h, unifFwdImpl.simulateQ_run]
  simp only [bind_map_left, map_bind]
  rfl

theorem evalDist_gameAfterSeed_prepared (adversary : Adversary) (seed : MasterSeed) :
    𝒮[(simulateQ romImpl (gameAfterSeed adversary seed)).run' ∅] =
      𝒮[do
        let outputs ← sampleSecretOutputs
        (simulateQ romImpl (Concrete.gameAfterSecrets adversary 0
          (tableOts outputs) (tableFts outputs))).run' (derivationCache seed outputs)] := by
  rw [evalDist_presample_computation _
    (liftM (prepareSecrets seed) : OracleComp OracleWorld SecretOutputs)]
  rw [show simulateQ romImpl (liftM (prepareSecrets seed) : OracleComp OracleWorld SecretOutputs) =
      simulateQ randomOracle (prepareSecrets seed) from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalSPMF_bind, evalDist_prepareSecrets, ← evalSPMF_bind, bind_map_left]
  apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
  intro outputs
  rw [StateT.run'_eq, StateT.run'_eq, evalSPMF_map, evalSPMF_map]
  rw [(erases_gameAfterSeed (derivationCache_secret seed outputs) adversary).evalDist_run _ le_rfl]

/-- The seeded game with every derivation presampled into the cache: the secrets are the low halves
of the derivation answers and the high halves only sit in the cache. -/
noncomputable def programmedGame (adversary : Adversary) : ProbComp Bool := do
  let seed ← sampleMasterSeed
  let secret ← sampleSecrets
  let secretHigh ← sampleSecrets
  (simulateQ romImpl (Concrete.gameAfterSecrets adversary 0 secret.1 secret.2)).run'
    (programmedCache seed secret secretHigh)

theorem evalDist_gameCore_eq_programmed (adversary : Adversary) :
    𝒮[(simulateQ romImpl (gameCore randomizedScheme adversary)).run' ∅] = 𝒮[programmedGame adversary] := by
  rw [gameCore_seeded_eq, run'_lift_sample_bind]
  unfold programmedGame
  apply OracleComp.DeferredSampling.evalSPMF_bind_congr_left
  intro seed
  rw [evalDist_gameAfterSeed_prepared, evalSPMF_bind, evalDist_secretOutputs_from_halves, ← evalSPMF_bind]
  simp only [bind_assoc, pure_bind, tableOts_from_halves, tableFts_from_halves, programmedCache]

end SphincsSecurity.Seeded
