import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.GameExpansion

/-!
# The deterministic table game runs within one query less

Key generation's first query derives the top tree's first secret. With every derivation
presampled, the table game reads that secret from its table and saves the query, so a budget of `q`
for the deterministic game leaves `q - 1` for the table game.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem gameCore_deterministic_split (adversary : Adversary) :
    gameCore scheme adversary = ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>=
      deterministicGameAfterSeed adversary) := gameCore_deterministic_eq adversary

/-- The first hash query after the seed is the derivation of the top tree's first secret. -/
theorem deterministicAfterSeed_first_query (adversary : Adversary) (seed : MasterSeed) :
    deterministicGameAfterSeed adversary seed = (do
      let output ← liftM (OracleWorld.query (.inr (secretInputs 0 seed firstSecretPosition)))
      let root ← liftM (keygenTree (withFirst (otsSecret 0 seed topLayer Concrete.rootTree)
        (truncateHash output)))
      gameRest scheme adversary ⟨root, 0⟩ ⟨seed, 0, root⟩) := by
  unfold deterministicGameAfterSeed
  exact keygenTree_first_query seed _

attribute [local irreducible] sampleMasterSeed derivationCache signingDerivationCache prepareSecrets
  prepareRandomizers sampleSecretOutputs sampleRandomizerOutputs

theorem mem_support_signingSecretOutputs (outputs : SecretOutputs) : outputs ∈ support sampleSecretOutputs := by
  rw [mem_support_iff]
  unfold sampleSecretOutputs
  rw [probOutput_uniformSample]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem hashQueryBound_after_signing_derivation (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) (seed : MasterSeed)
    (outputs : SecretOutputs) (randomizers : RandomizerOutputs) :
    1 ≤ q ∧ HashQueryBound (tableGameAfterSecrets adversary outputs randomizers)
      (signingDerivationCache seed outputs randomizers) (q - 1) := by
  rw [hasHashQueryBound_iff, gameCore_deterministic_split] at hbound
  have hs : seed ∈ support sampleMasterSeed := by
    rw [mem_support_iff]
    unfold sampleMasterSeed
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hseed : HashQueryBound (deterministicGameAfterSeed adversary seed) ∅ q :=
    hashQueryBound_of_sampling_bind sampleMasterSeed (deterministicGameAfterSeed adversary) ∅ q hbound seed hs
  have houtputs : (outputs, derivationCache seed outputs) ∈
      support ((simulateQ romImpl (liftM (prepareSecrets seed) : OracleComp OracleWorld _)).run ∅) := by
    rw [romImpl, QueryImpl.simulateQ_add_liftM_right,
      mem_support_iff_of_evalSPMF_eq (evalDist_prepareSecrets seed), support_map]
    exact ⟨outputs, mem_support_signingSecretOutputs outputs, rfl⟩
  have hprepared := hashQueryBound_after_preparation _ _ _ _ hseed _ houtputs
  have hrandomizers : (randomizers, signingDerivationCache seed outputs randomizers) ∈
      support ((simulateQ romImpl (liftM (prepareRandomizers seed) :
        OracleComp OracleWorld _)).run (derivationCache seed outputs)) := by
    rw [romImpl, QueryImpl.simulateQ_add_liftM_right,
      mem_support_iff_of_evalSPMF_eq (evalDist_prepareRandomizers seed outputs), support_map]
    refine ⟨randomizers, ?_, rfl⟩
    rw [mem_support_iff]
    unfold sampleRandomizerOutputs
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hfullyPrepared := hashQueryBound_after_preparation _ _ _ _ hprepared _ hrandomizers
  unfold deterministicGameAfterSeed at hfullyPrepared
  unfold tableGameAfterSecrets
  exact hashQueryBound_keygen_erased (signingDerivationCache_secret seed outputs randomizers) _ le_rfl
    (fun root => erases_deterministicGameRest _ 0 seed root outputs randomizers
      (signingDerivationCache_secret seed outputs randomizers)
      (signingDerivationCache_randomizer seed outputs randomizers) adversary) q hfullyPrepared

def HasTableBudget (adversary : Adversary) (q : Nat) : Prop :=
  ∀ (outputs : SecretOutputs) (randomizers : RandomizerOutputs),
    HashQueryBound (tableGameAfterSecrets adversary outputs randomizers) ∅ q

theorem tableBudget_from_deterministic (adversary : Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : HasHashQueryBound scheme adversary q) :
    HasTableBudget adversary (q - 1) := by
  intro outputs randomizers
  exact hashQueryBound_of_seed_caches _ (q - 1) []
    (fun seed => signingDerivationCache seed outputs randomizers) ∅
    (by simpa using lt_of_le_of_lt (Nat.sub_le q 1) hsmall)
    (fun seed _ => signingDerivationCache_agreeOutside seed outputs randomizers)
    (fun seed _ => (hashQueryBound_after_signing_derivation adversary q hbound seed outputs randomizers).2)

end SphincsSecurity.Seeded
