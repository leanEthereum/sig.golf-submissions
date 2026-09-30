import SigGolfCandidate.SphincsSecurity.Proof.Seeded.GameExpansion

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-!
# The table game runs within one query less

Key generation's first query derives the top tree's first secret. The table game reads that secret
from its table, so it saves the query: a seeded budget of `q` leaves the table game `q - 1`.
-/

theorem gameCore_seeded_split (adversary : Adversary) :
    gameCore randomizedScheme adversary = ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>=
      gameAfterSeed adversary) := gameCore_seeded_eq adversary

attribute [local irreducible] sampleMasterSeed Concrete.gameAfterSecrets derivationCache prepareSecrets
  sampleSecretOutputs

theorem mem_support_secretOutputs (outputs : SecretOutputs) : outputs ∈ support sampleSecretOutputs := by
  rw [mem_support_iff]
  unfold sampleSecretOutputs
  rw [probOutput_uniformSample]
  exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

theorem hashQueryBound_after_derivation (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound randomizedScheme adversary q) (seed : MasterSeed)
    (outputs : SecretOutputs) :
    1 ≤ q ∧ HashQueryBound
      (Concrete.gameAfterSecrets adversary 0 (tableOts outputs) (tableFts outputs))
      (derivationCache seed outputs) (q - 1) := by
  rw [hasHashQueryBound_iff, gameCore_seeded_split] at hbound
  have hs : seed ∈ support sampleMasterSeed := by
    rw [mem_support_iff]
    unfold sampleMasterSeed
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  have hseed : HashQueryBound (gameAfterSeed adversary seed) ∅ q :=
    hashQueryBound_of_sampling_bind sampleMasterSeed (gameAfterSeed adversary) ∅ q hbound seed hs
  have houtputs : (outputs, derivationCache seed outputs) ∈
      support ((simulateQ romImpl (liftM (prepareSecrets seed) : OracleComp OracleWorld _)).run ∅) := by
    rw [romImpl, QueryImpl.simulateQ_add_liftM_right,
      mem_support_iff_of_evalSPMF_eq (evalDist_prepareSecrets seed), support_map]
    exact ⟨outputs, mem_support_secretOutputs outputs, rfl⟩
  have hprepared := hashQueryBound_after_preparation _ _ _ _ hseed _ houtputs
  unfold gameAfterSeed at hprepared
  unfold Concrete.gameAfterSecrets
  exact hashQueryBound_keygen_erased (derivationCache_secret seed outputs) _ le_rfl
    (fun root => erases_gameRest _ 0 seed outputs (derivationCache_secret seed outputs) adversary root) q
    hprepared

theorem hashQueryBound_programmed_from_seeded (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound randomizedScheme adversary q) (seed : MasterSeed)
    (secret secretHigh : Secrets) :
    HashQueryBound (Concrete.gameAfterSecrets adversary 0 secret.1 secret.2)
      (programmedCache seed secret secretHigh) (q - 1) := by
  have h := (hashQueryBound_after_derivation adversary q hbound seed
    (secretHalves.symm (secret, secretHigh))).2
  simpa only [programmedCache, tableOts_from_halves, tableFts_from_halves] using h

theorem programmedCache_agreeOutside (seed : MasterSeed) (secret secretHigh : Secrets) :
    AgreeOutside (fun input => SeedHit input seed) (programmedCache seed secret secretHigh) ∅ :=
  derivationCache_agreeOutside seed _

theorem hashQueryBound_independent_from_seeded (adversary : Adversary) (q : Nat)
    (hsmall : q < 2 ^ 256) (hbound : HasHashQueryBound randomizedScheme adversary q) :
    HasHashQueryBound Concrete.scheme adversary (q - 1) := by
  rw [hasHashQueryBound_iff, Concrete.gameCore_eq_secrets]
  have htail (parameter : PublicParameter) (hparameter : parameter ∈ support Concrete.sampleParameter)
      (ots : OtsSecrets) (fts : FtsSecrets) :
      HashQueryBound (Concrete.gameAfterSecrets adversary parameter ots fts) ∅ (q - 1) := by
    rw [sampleParameter_eq_zero, support_pure, Set.mem_singleton_iff] at hparameter
    subst parameter
    let high : Secrets := (fun _ _ _ _ => 0, fun _ _ _ => 0)
    exact hashQueryBound_of_seed_caches _ (q - 1) []
      (fun seed => programmedCache seed (ots, fts) high) ∅
      (by simpa using lt_of_le_of_lt (Nat.sub_le q 1) hsmall)
      (fun seed _ => programmedCache_agreeOutside seed _ _)
      (fun seed _ => hashQueryBound_programmed_from_seeded adversary q hbound seed (ots, fts) high)
  intro result hresult
  simp only [countHashQueries_bind, countHashQueries_lift_prob, simulateQ_bind,
    simulateQ_map, StateT.run'_eq, StateT.run_bind, StateT.run_map,
    romImpl, QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run,
    bind_map_left, map_bind, Nat.zero_add, bind_pure_comp, Functor.map_map,
    support_bind, Set.mem_iUnion, support_map] at hresult
  obtain ⟨parameter, hparameter, ots, _, fts, _, record, hrecord, rfl⟩ := hresult
  apply htail parameter hparameter ots fts record.1
  rw [StateT.run'_eq, support_map]
  exact ⟨record, hrecord, rfl⟩

end SphincsSecurity.Seeded
