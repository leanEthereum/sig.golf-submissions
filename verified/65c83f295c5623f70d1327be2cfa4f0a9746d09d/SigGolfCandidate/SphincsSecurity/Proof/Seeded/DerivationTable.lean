import SigGolfCandidate.SphincsSecurity.Proof.Seeded.FiniteTable
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.KeyDerivation
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.SeedGuessing
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.CacheCoupling

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

abbrev OtsPosition := Layer × TreeIndex × LeafIndex × ChainIndex
abbrev FtsPosition := Index × FtsTree × FtsLeaf
abbrev SecretPosition := OtsPosition ⊕ FtsPosition
abbrev SecretOutputs := SecretPosition → HashOutput
abbrev SecretValues := SecretPosition → Digest

noncomputable opaque secretOutputsSampleableType : SampleableType SecretOutputs :=
  SampleableType.ofFintype SecretOutputs

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType

noncomputable def sampleSecretOutputs : ProbComp SecretOutputs := $ᵗ SecretOutputs

def secretDomain : SecretPosition → KeygenDomain
  | .inl (lay, tree, leaf, chain) => .ots lay tree leaf chain
  | .inr (index, tree, leaf) => .fts index tree leaf

theorem secretDomain_injective : Function.Injective secretDomain := by
  intro left right h
  cases left with
  | inl left =>
      rcases left with ⟨lay, tree, leaf, chain⟩
      cases right <;> simp_all [secretDomain]
  | inr left =>
      rcases left with ⟨index, tree, leaf⟩
      cases right <;> simp_all [secretDomain]

def secretInputs (parameter : PublicParameter) (seed : MasterSeed) (position : SecretPosition) : HashInput :=
  keygenHashInput parameter (secretDomain position) seed

theorem secretInputs_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (secretInputs parameter seed) := by
  intro left right h
  exact secretDomain_injective (keygenHashInput_injective h).2.1

/-- Every secret derivation of the seed, answered by `outputs`. There is no parameter derivation:
the parameter is `P = 0`, so the table holds the secrets alone. -/
noncomputable def derivationCache (seed : MasterSeed) (outputs : SecretOutputs) : QueryCache HashSpec :=
  cacheTable ∅ (secretInputs 0 seed) outputs

theorem derivationCache_secret (seed : MasterSeed) (outputs : SecretOutputs) (position : SecretPosition) :
    derivationCache seed outputs (secretInputs 0 seed position) = some (outputs position) :=
  cacheTable_apply _ _ (secretInputs_injective _ seed) outputs position

theorem derivationCache_agreeOutside (seed : MasterSeed) (outputs : SecretOutputs) :
    AgreeOutside (fun input => SeedHit input seed) (derivationCache seed outputs) ∅ := by
  intro input hinput
  unfold derivationCache
  rw [cacheTable_apply_of_not_mem]
  intro position heq
  exact hinput (heq.symm ▸ derivationSeedHit_keygen 0 (secretDomain position) seed)

noncomputable def prepareSecrets (seed : MasterSeed) : OracleComp HashSpec SecretOutputs :=
  queryTable (secretInputs 0 seed)

theorem evalDist_prepareSecrets (seed : MasterSeed) :
    𝒮[(simulateQ randomOracle (prepareSecrets seed)).run ∅] =
        𝒮[(fun outputs => (outputs, derivationCache seed outputs)) <$> sampleSecretOutputs] :=
  evalDist_queryTable_fresh _ (secretInputs_injective _ seed) _ (fun _ => QueryCache.empty_apply _)

end SphincsSecurity.Seeded
