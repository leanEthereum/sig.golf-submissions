import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.TableSigner
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.GameExpansion

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The deterministic seeded game once the seed is sampled: build the top tree from the seed, then play. -/
noncomputable def deterministicGameAfterSeed (adversary : Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld Bool := do
  let root ← liftM (keygenTree (otsSecret 0 seed topLayer Concrete.rootTree))
  gameRest scheme adversary ⟨root, 0⟩ ⟨seed, 0, root⟩

/-- The game from secret and randomizer tables: build the top tree from the table, then play
against the table signer. -/
noncomputable def tableGameAfterSecrets (adversary : Adversary) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) : OracleComp OracleWorld Bool := do
  let root ← liftM
    (Concrete.keygenRoot 0 (tableOts outputs topLayer Concrete.rootTree) : OracleComp HashSpec Digest)
  gameRest (tableScheme randomizers) adversary ⟨root, 0⟩ (tableKey 0 root outputs)

theorem gameCore_deterministic_eq (adversary : Adversary) :
    gameCore scheme adversary =
      ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>= deterministicGameAfterSeed adversary) := by
  have hkeygen : scheme.keygen = keygen := rfl
  unfold deterministicGameAfterSeed keygenTree
  simp only [gameCore, hkeygen, keygen, keygenFromSeed, bind_assoc, liftM_bind, liftM_pure, pure_bind]

theorem erases_deterministicGameRest (known : QueryCache HashSpec) (parameter : PublicParameter)
    (seed : MasterSeed) (root : Digest) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (hsecrets : ∀ position, known (secretInputs parameter seed position) = some (outputs position))
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (adversary : Adversary) :
    Erases (worldKnown known)
      (gameRest scheme adversary ⟨root, parameter⟩ ⟨seed, parameter, root⟩)
      (gameRest (tableScheme randomizers) adversary ⟨root, parameter⟩ (tableKey parameter root outputs)) := by
  unfold gameRest
  apply Erases.bind _ _ _ (fun _ => Erases.refl (worldKnown known) _)
  apply Erases.simulateQ_writer
  intro input
  cases input with
  | inl input =>
      simp only [QueryImpl.add_apply_inl]
      exact .refl _ _
  | inr request =>
      simp only [QueryImpl.add_apply_inr, signingOracle, QueryImpl.run_withLogging_apply, bind_pure_comp]
      exact (erases_deterministicSign known parameter seed root outputs randomizers
        hsecrets hrandomizers request).lift_hash.map _

theorem erases_deterministicGameAfterSeed (known : QueryCache HashSpec)
    (seed : MasterSeed) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (hsecrets : ∀ position, known (secretInputs 0 seed position) = some (outputs position))
    (hrandomizers : ∀ position, known (randomizerInputs 0 seed position) = some (randomizers position))
    (adversary : Adversary) :
    Erases (worldKnown known) (deterministicGameAfterSeed adversary seed)
      (tableGameAfterSecrets adversary outputs randomizers) := by
  unfold deterministicGameAfterSeed tableGameAfterSecrets
  exact Erases.keygen_bind hsecrets fun root =>
    erases_deterministicGameRest known 0 seed root outputs randomizers hsecrets hrandomizers adversary

attribute [local irreducible] deterministicGameAfterSeed tableGameAfterSecrets signingDerivationCache

theorem evalDist_deterministicGameAfterSeed_prepared (adversary : Adversary) (seed : MasterSeed) :
    𝒮[(simulateQ romImpl (deterministicGameAfterSeed adversary seed)).run' ∅] =
      𝒮[do
        let outputs ← sampleSecretOutputs
        let randomizers ← sampleRandomizerOutputs
        (simulateQ romImpl (tableGameAfterSecrets adversary outputs randomizers)).run'
          (signingDerivationCache seed outputs randomizers)] := by
  rw [evalDist_presample_computation _
    (liftM (prepareSecrets seed) : OracleComp OracleWorld SecretOutputs)]
  rw [show simulateQ romImpl (liftM (prepareSecrets seed) : OracleComp OracleWorld SecretOutputs) =
      simulateQ randomOracle (prepareSecrets seed)
      from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalSPMF_bind, evalDist_prepareSecrets, ← evalSPMF_bind, bind_map_left]
  apply evalSPMF_bind_congr'
  intro outputs
  rw [evalDist_presample_computation _
    (liftM (prepareRandomizers seed) : OracleComp OracleWorld RandomizerOutputs)]
  rw [show simulateQ romImpl (liftM (prepareRandomizers seed) : OracleComp OracleWorld RandomizerOutputs) =
      simulateQ randomOracle (prepareRandomizers seed)
      from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalSPMF_bind, evalDist_prepareRandomizers, ← evalSPMF_bind, bind_map_left]
  apply evalSPMF_bind_congr'
  intro randomizers
  rw [StateT.run'_eq, StateT.run'_eq, evalSPMF_map, evalSPMF_map]
  exact congrArg _ ((erases_deterministicGameAfterSeed _ seed outputs randomizers
    (signingDerivationCache_secret seed outputs randomizers)
    (signingDerivationCache_randomizer seed outputs randomizers) adversary).evalDist_run _ le_rfl)

/-- The deterministic game with every derivation presampled into the cache. -/
noncomputable def programmedDeterministicGame (adversary : Adversary) : ProbComp Bool := do
  let seed ← sampleMasterSeed
  let outputs ← sampleSecretOutputs
  let randomizers ← sampleRandomizerOutputs
  (simulateQ romImpl (tableGameAfterSecrets adversary outputs randomizers)).run'
    (signingDerivationCache seed outputs randomizers)

theorem evalDist_gameCore_deterministic_programmed (adversary : Adversary) :
    𝒮[(simulateQ romImpl (gameCore scheme adversary)).run' ∅] =
      𝒮[programmedDeterministicGame adversary] := by
  rw [gameCore_deterministic_eq, run'_lift_sample_bind]
  unfold programmedDeterministicGame
  apply evalSPMF_bind_congr'
  intro seed
  exact evalDist_deterministicGameAfterSeed_prepared adversary seed

end SphincsSecurity.Seeded
