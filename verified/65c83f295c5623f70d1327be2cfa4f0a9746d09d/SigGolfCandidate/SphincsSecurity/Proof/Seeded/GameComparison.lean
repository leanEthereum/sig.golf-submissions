import SigGolfCandidate.SphincsSecurity.Proof.Seeded.KeygenBudget

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The secrets and the high halves of their derivation answers. -/
abbrev KeyMaterial := Secrets × Secrets

noncomputable def drawKeyMaterial : ProbComp KeyMaterial := do
  let secret ← sampleSecrets
  let secretHigh ← sampleSecrets
  return (secret, secretHigh)

noncomputable def materialCache (seed : MasterSeed) (material : KeyMaterial) : QueryCache HashSpec :=
  programmedCache seed material.1 material.2

theorem evalDist_programmedGame_seed_last (adversary : Adversary) :
    𝒮[programmedGame adversary] = 𝒮[do
      let material ← drawKeyMaterial
      let seed ← sampleMasterSeed
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary 0 material.1.1 material.1.2)).run'
        (materialCache seed material)] := by
  have heq : programmedGame adversary = (do
      let seed ← sampleMasterSeed
      let material ← drawKeyMaterial
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary 0 material.1.1 material.1.2)).run'
        (materialCache seed material)) := by
    simp only [programmedGame, drawKeyMaterial, materialCache, bind_assoc, pure_bind]
  rw [heq, evalSPMF_bind_bind_swap]

theorem gameCore_independent_eq (adversary : Adversary) :
    gameCore Concrete.scheme adversary = (do
      let secret ← liftM sampleSecrets
      Concrete.gameAfterSecrets adversary 0 secret.1 secret.2) := by
  rw [Concrete.gameCore_eq_secrets, sampleParameter_eq_zero]
  simp only [sampleSecrets, liftM_bind, liftM_pure, bind_assoc, pure_bind]

theorem evalDist_independentGame_material (adversary : Adversary) :
    𝒮[(simulateQ romImpl (gameCore Concrete.scheme adversary)).run' ∅] = 𝒮[do
      let material ← drawKeyMaterial
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary 0 material.1.1 material.1.2)).run' ∅] := by
  rw [gameCore_independent_eq, run'_lift_sample_bind]
  unfold drawKeyMaterial
  simp only [bind_assoc, pure_bind]
  apply evalSPMF_bind_congr'
  intro secret
  apply evalSPMF_ext
  intro value
  simp

theorem hashQueryBound_gameAfterSecrets (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound Concrete.scheme adversary q)
    (secret : Secrets) :
    HashQueryBound (Concrete.gameAfterSecrets adversary 0 secret.1 secret.2) ∅ q := by
  apply Concrete.hashQueryBound_gameAfterSecrets adversary q hbound
  · rw [sampleParameter_eq_zero]
    simp
  · rw [mem_support_iff]
    unfold Concrete.sampleOtsSecrets
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)
  · rw [mem_support_iff]
    unfold Concrete.sampleFtsSecrets
    rw [probOutput_uniformSample]
    exact ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top _)

/-- The seeded game differs from the independent game by at most one 256-bit guess per hash call. -/
theorem forgeAdvantage_seeded_le_of_independent_budget (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound Concrete.scheme adversary q) :
    forgeAdvantage randomizedScheme adversary ≤ forgeAdvantage Concrete.scheme adversary +
      q / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  classical
  unfold forgeAdvantage
  simp only [probOutput_def, evalDist_gameCore_eq_programmed,
    evalDist_programmedGame_seed_last, evalDist_independentGame_material]
  change Pr[= true | drawKeyMaterial >>= fun material => sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary 0 material.1.1 material.1.2)).run'
        (materialCache seed material)] ≤
    Pr[= true | drawKeyMaterial >>= fun material =>
      (simulateQ romImpl (Concrete.gameAfterSecrets adversary 0 material.1.1 material.1.2)).run' ∅] + _
  rw [← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput]
  apply probEvent_bind_congr_le_add
  intro material _
  exact probEvent_random_cache_change_le _ (fun seed => materialCache seed material) ∅
    (fun seed => programmedCache_agreeOutside seed _ _) q
    (hashQueryBound_gameAfterSecrets adversary q hbound _) (fun value => value = true)

end SphincsSecurity.Seeded
