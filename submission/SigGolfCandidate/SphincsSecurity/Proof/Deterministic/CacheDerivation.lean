import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.DerivationTable
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Inputs

/-!
# The cache's derivations: masks and MAC answers

Key generation masks the top tree's nodes with `mask(l, j)`, a seed derivation of domain tag `13`, and
authenticates the masked region with the MAC `H(tw_mac || P || S || region)` of tag `14`, keyed by the
master seed. Both families are derivations of the seed, like the one-time secrets and the randomizers:
their inputs carry the seed in bytes `32` through `63`, so an adversary query that hits one is a seed
guess. This file adds them to the derivation cache: the masks as one more keygen family, and the MAC
answers as a table over every possible region, like the randomizers are a table over every message.
-/

open OracleComp OracleSpec

namespace SphincsSecurity

set_option backward.isDefEq.respectTransparency false

/-! ## The inputs -/

theorem length_flatten_ofFn_eq {α : Type} {n : Nat} (f g : Fin n → List α)
    (hlen : ∀ i, (f i).length = (g i).length) (h : (List.ofFn f).flatten = (List.ofFn g).flatten) : f = g := by
  induction n with
  | zero => funext i; exact i.elim0
  | succ n ih =>
      rw [List.ofFn_succ, List.ofFn_succ, List.flatten_cons, List.flatten_cons] at h
      obtain ⟨hhead, htail⟩ := List.append_inj h (hlen 0)
      have htail' := ih (fun i => f i.succ) (fun i => g i.succ) (fun i => hlen i.succ) htail
      funext i
      cases i using Fin.cases with
      | zero => exact hhead
      | succ i => exact congrFun htail' i

theorem flatMap_bytesLE_ofFn_injective {n k : Nat} {f g : Fin n → BitVec (8 * k)}
    (h : (List.ofFn f).flatMap (bytesLE k) = (List.ofFn g).flatMap (bytesLE k)) : f = g := by
  rw [List.flatMap_def, List.flatMap_def, List.map_ofFn, List.map_ofFn] at h
  have hfun := length_flatten_ofFn_eq (fun i => bytesLE k (f i)) (fun i => bytesLE k (g i))
    (fun i => by simp [bytesLE_length]) h
  funext i
  exact bytesLE_injective (congrFun hfun i)

theorem regionBytes_injective : Function.Injective regionBytes := by
  intro left right h
  unfold regionBytes at h
  have hlevels := length_flatten_ofFn_eq _ _ (fun level => by
    simp [List.length_flatMap, bytesLE_length, Function.comp_def]) h
  funext level
  exact flatMap_bytesLE_ofFn_injective (congrFun hlevels level)

theorem macHashInput_injective {p₁ p₂ : PublicParameter} {s₁ s₂ : MasterSeed} {r₁ r₂ : TopRegion}
    (h : macHashInput p₁ s₁ r₁ = macHashInput p₂ s₂ r₂) : p₁ = p₂ ∧ s₁ = s₂ ∧ r₁ = r₂ := by
  unfold macHashInput at h
  obtain ⟨hprefix, hregion⟩ := List.append_inj h (by simp [fieldBytes, bytesLE_length])
  obtain ⟨hprefix, hs⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  obtain ⟨_, hp⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  exact ⟨bytesLE_injective hp, bytesLE_injective hs, regionBytes_injective hregion⟩

/-- The MAC's tweak tag `14` separates it from every other hash input of the scheme. -/
theorem macHashInput_tag (parameter : PublicParameter) (seed : MasterSeed) (region : TopRegion) :
    (macHashInput parameter seed region).take 2 = [protocolDomainSep, 14] := by
  simp [macHashInput, fieldBytes, bytesLE]

theorem macHashInput_ne_keygenHashInput (p₁ p₂ : PublicParameter) (s₁ s₂ : MasterSeed) (region : TopRegion)
    (domain : KeygenDomain) : macHashInput p₁ s₁ region ≠ keygenHashInput p₂ domain s₂ := by
  intro h
  have h2 := congrArg (List.take 2) h
  rw [macHashInput_tag] at h2
  cases domain <;> simp [keygenHashInput, keygenDomainFields, tweakFields, fieldBytes, bytesLE] at h2 <;>
    exact absurd h2 (by decide)

theorem macHashInput_ne_randomizerHashInput (p₁ p₂ : PublicParameter) (s₁ s₂ : MasterSeed)
    (region : TopRegion) (message : Message) (trial : BitVec 32) :
    macHashInput p₁ s₁ region ≠ randomizerHashInput p₂ s₂ message trial := by
  intro h
  have h2 := congrArg (List.take 2) h
  rw [macHashInput_tag] at h2
  simp [randomizerHashInput, fieldBytes, bytesLE] at h2
  exact absurd h2 (by decide)

theorem macHashInput_ne_tweakableHashInput (p₁ p₂ : PublicParameter) (seed : MasterSeed)
    (region : TopRegion) (domain : HashDomain) (payload : HashInput) :
    macHashInput p₁ seed region ≠ tweakableHashInput p₂ domain payload := by
  intro h
  have h2 := congrArg (List.take 2) h
  rw [macHashInput_tag] at h2
  cases domain <;> simp [tweakableHashInput, tweakBytes, hashDomainFields, tweakFields, fieldBytes, bytesLE] at h2 <;>
    exact absurd h2 (by decide)

theorem derivationSeedHit_mac (parameter : PublicParameter) (seed : MasterSeed) (region : TopRegion) :
    DerivationSeedHit (macHashInput parameter seed region) seed := by
  simp [DerivationSeedHit, macHashInput, fieldBytes, bytesLE]

namespace Seeded

/-! ## The mask table -/

/-- A mask position: a level below the root and a node index. Positions outside the region hold masks
nothing reads. -/
abbrev MaskPosition := Fin maxLayerHeight × Fin (2 ^ maxLayerHeight)
abbrev MaskOutputs := MaskPosition → HashOutput

noncomputable opaque maskOutputsSampleableType : SampleableType MaskOutputs :=
  SampleableType.ofFintype MaskOutputs

noncomputable instance : SampleableType MaskOutputs := maskOutputsSampleableType

noncomputable def sampleMaskOutputs : ProbComp MaskOutputs := $ᵗ MaskOutputs

/-- The position `maskDomain level nodeIdx` derives. -/
def maskPosition (level nodeIdx : Nat) : MaskPosition :=
  (⟨level % maxLayerHeight, Nat.mod_lt _ (by decide)⟩, ⟨nodeIdx % 2 ^ maxLayerHeight, Nat.mod_lt _ (by decide)⟩)

def maskInputs (parameter : PublicParameter) (seed : MasterSeed) (position : MaskPosition) : HashInput :=
  keygenHashInput parameter (.mask position.1 position.2) seed

theorem maskInputs_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (maskInputs parameter seed) := by
  intro left right h
  have hdomain := (keygenHashInput_injective h).2.1
  simp only [KeygenDomain.mask.injEq] at hdomain
  exact Prod.ext hdomain.1 hdomain.2

theorem maskSecret_input (parameter : PublicParameter) (seed : MasterSeed) (level nodeIdx : Nat) :
    keygenHashInput parameter (maskDomain level nodeIdx) seed = maskInputs parameter seed (maskPosition level nodeIdx) :=
  rfl

/-- The mask the table assigns to node `(l, j)`. -/
def maskValue (masks : MaskOutputs) (level nodeIdx : Nat) : Digest :=
  truncateHash (masks (maskPosition level nodeIdx))

/-! ## The MAC table -/

abbrev MacOutputs := TopRegion → HashOutput

noncomputable opaque macOutputsSampleableType : SampleableType MacOutputs :=
  SampleableType.ofFintype MacOutputs

noncomputable instance : SampleableType MacOutputs := macOutputsSampleableType

noncomputable def sampleMacOutputs : ProbComp MacOutputs := $ᵗ MacOutputs

def macInputs (parameter : PublicParameter) (seed : MasterSeed) (region : TopRegion) : HashInput :=
  macHashInput parameter seed region

theorem macInputs_injective (parameter : PublicParameter) (seed : MasterSeed) :
    Function.Injective (macInputs parameter seed) :=
  fun _ _ h => (macHashInput_injective h).2.2

/-! ## The full derivation cache -/

/-- The secrets, the randomizers and the masks. -/
noncomputable def maskedDerivationCache (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) : QueryCache HashSpec :=
  cacheTable (signingDerivationCache seed outputs randomizers) (maskInputs 0 seed) masks

/-- Every derivation of the seed: secrets, randomizers, masks and MAC answers. -/
noncomputable def cachedDerivationCache (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) : QueryCache HashSpec :=
  cacheTable (maskedDerivationCache seed outputs randomizers masks) (macInputs 0 seed) macs

theorem signingDerivationCache_mask_fresh (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (position : MaskPosition) :
    signingDerivationCache seed outputs randomizers (maskInputs 0 seed position) = none := by
  unfold signingDerivationCache derivationCache
  rw [cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem]
  · rfl
  · intro secret h
    have := (keygenHashInput_injective h).2.1
    cases secret <;> simp [secretDomain] at this
  · intro randomizer h
    exact randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ _ h.symm

theorem maskedDerivationCache_mac_fresh (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (region : TopRegion) :
    maskedDerivationCache seed outputs randomizers masks (macInputs 0 seed region) = none := by
  unfold maskedDerivationCache signingDerivationCache derivationCache
  rw [cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem]
  · rfl
  · intro secret
    exact macHashInput_ne_keygenHashInput _ _ _ _ _ _
  · intro randomizer
    exact macHashInput_ne_randomizerHashInput _ _ _ _ _ _ _
  · intro position
    exact macHashInput_ne_keygenHashInput _ _ _ _ _ _

theorem cachedDerivationCache_mac (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) (region : TopRegion) :
    cachedDerivationCache seed outputs randomizers masks macs (macInputs 0 seed region) = some (macs region) :=
  cacheTable_apply _ _ (macInputs_injective _ _) _ _

theorem cachedDerivationCache_mask (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) (position : MaskPosition) :
    cachedDerivationCache seed outputs randomizers masks macs (maskInputs 0 seed position) =
      some (masks position) := by
  unfold cachedDerivationCache
  rw [cacheTable_apply_of_not_mem]
  · exact cacheTable_apply _ _ (maskInputs_injective _ _) _ _
  · intro region h
    exact macHashInput_ne_keygenHashInput _ _ _ _ _ _ h.symm

theorem cachedDerivationCache_randomizer (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) (position : RandomizerPosition) :
    cachedDerivationCache seed outputs randomizers masks macs (randomizerInputs 0 seed position) =
      some (randomizers position) := by
  unfold cachedDerivationCache maskedDerivationCache
  rw [cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem]
  · exact signingDerivationCache_randomizer _ _ _ _
  · intro mask h
    exact randomizerHashInput_ne_keygenHashInput _ _ _ _ _ _ _ h
  · intro region h
    exact macHashInput_ne_randomizerHashInput _ _ _ _ _ _ _ h.symm

theorem cachedDerivationCache_secret (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) (position : SecretPosition) :
    cachedDerivationCache seed outputs randomizers masks macs (secretInputs 0 seed position) =
      some (outputs position) := by
  unfold cachedDerivationCache maskedDerivationCache
  rw [cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem]
  · exact signingDerivationCache_secret _ _ _ _
  · intro mask h
    have := (keygenHashInput_injective h).2.1
    cases position <;> simp [secretDomain] at this
  · intro region h
    exact macHashInput_ne_keygenHashInput _ _ _ _ _ _ h.symm

theorem cachedDerivationCache_agreeOutside (seed : MasterSeed) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) :
    AgreeOutside (fun input => SeedHit input seed) (cachedDerivationCache seed outputs randomizers masks macs) ∅ := by
  intro input hinput
  unfold cachedDerivationCache maskedDerivationCache
  rw [cacheTable_apply_of_not_mem, cacheTable_apply_of_not_mem]
  · exact signingDerivationCache_agreeOutside seed outputs randomizers input hinput
  · intro position heq
    exact hinput (heq.symm ▸ derivationSeedHit_keygen 0 _ seed)
  · intro region heq
    exact hinput (heq.symm ▸ derivationSeedHit_mac 0 seed region)

noncomputable def prepareMasks (seed : MasterSeed) : OracleComp HashSpec MaskOutputs :=
  queryTable (maskInputs 0 seed)

theorem evalDist_prepareMasks (seed : MasterSeed) (outputs : SecretOutputs) (randomizers : RandomizerOutputs) :
    𝒮[(simulateQ randomOracle (prepareMasks seed)).run (signingDerivationCache seed outputs randomizers)] =
        𝒮[(fun masks => (masks, maskedDerivationCache seed outputs randomizers masks)) <$> sampleMaskOutputs] :=
  evalDist_queryTable_fresh _ (maskInputs_injective _ seed) _
    (signingDerivationCache_mask_fresh seed outputs randomizers)

noncomputable def prepareMacs (seed : MasterSeed) : OracleComp HashSpec MacOutputs :=
  queryTable (macInputs 0 seed)

theorem evalDist_prepareMacs (seed : MasterSeed) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (masks : MaskOutputs) :
    𝒮[(simulateQ randomOracle (prepareMacs seed)).run (maskedDerivationCache seed outputs randomizers masks)] =
        𝒮[(fun macs => (macs, cachedDerivationCache seed outputs randomizers masks macs)) <$> sampleMacOutputs] :=
  evalDist_queryTable_fresh _ (macInputs_injective _ seed) _
    (maskedDerivationCache_mac_fresh seed outputs randomizers masks)

end Seeded

end SphincsSecurity
