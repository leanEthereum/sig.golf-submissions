import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.CacheDerivation
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.AlgorithmErasure

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

open Concrete
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def tableDigestLoop (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (message : Message) : Nat → Nat → m (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := truncateHash (randomizers (message, BitVec.ofNat 32 trial))
      match ← Concrete.signAttempt secretKey message randomness with
      | some (index, leaves) => return some (randomness, index, leaves)
      | none => tableDigestLoop randomizers secretKey message attempts (trial + 1)

/-- The deterministic signer from tables: the randomizers from `randomizers`, then the table signer
after the digest loop. -/
def tableSign (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (message : Message) : OracleComp HashSpec (Option Signature) := do
  match ← tableDigestLoop randomizers secretKey message digestAttemptLimit 0 with
  | none => return none
  | some (randomness, index, leaves) => Concrete.signAfterDigest secretKey randomness index leaves

noncomputable def tableScheme (randomizers : RandomizerOutputs) : Scheme SphincsSecurity.SecretKey where
  keygen := Concrete.scheme.keygen
  sign := fun sk message => liftM (tableSign randomizers sk message : OracleComp HashSpec _)
  verify := Concrete.scheme.verify

theorem erases_deterministicDigestLoop (known : QueryCache HashSpec) (parameter : PublicParameter)
    (seed : MasterSeed) (top : Nat → Nat → Digest) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (hknown : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (message : Message) (attempts trial : Nat) :
    Erases known (signDigestLoop ⟨seed, parameter, top (layerHeight topLayer) 0⟩ message attempts trial :
        OracleComp HashSpec _)
      (tableDigestLoop randomizers (tableKey parameter top outputs) message attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
      unfold signDigestLoop tableDigestLoop deriveRandomizer Concrete.oracleHash
      simp only [bind_assoc, pure_bind]
      apply Erases.skip _ _ (hknown (message, BitVec.ofNat 32 trial))
      change Erases known (Concrete.signAttempt (tableKey parameter top outputs) message
        (truncateHash (randomizers (message, BitVec.ofNat 32 trial))) >>= _)
          (Concrete.signAttempt (tableKey parameter top outputs) message
            (truncateHash (randomizers (message, BitVec.ofNat 32 trial))) >>= _)
      apply (Erases.refl known _).bind
      intro attempt
      cases attempt with
      | none => exact ih _
      | some result => exact .pure _

/-! ## The cached signer from tables

The table version of `Seeded.sign`: the MAC check reads the MAC table, the masks come from the mask
table, and everything else is the table signer's. -/

/-- `maskRegion` with the mask derivation as an argument. -/
def maskRegionWith {m : Type → Type} [Monad m] (getMask : Nat → Nat → m Digest) (table : Nat → Nat → Digest) :
    m TopRegion := do
  let rows ← Concrete.sequenceFin fun level : Fin maxLayerHeight => do
    let row ← Concrete.sequenceFin fun nodeIdx : Fin (2 ^ (maxLayerHeight - level.val)) => do
      let mask ← getMask level.val nodeIdx.val
      return table level.val nodeIdx.val ^^^ mask
    return fun nodeIdx : Nat => if h : nodeIdx < 2 ^ (maxLayerHeight - level.val) then row ⟨nodeIdx, h⟩ else 0
  return fun level nodeIdx => rows level nodeIdx.val

theorem maskRegion_eq_with {m : Type → Type} [Monad m] [HasQuery HashSpec m] (parameter : PublicParameter)
    (seed : MasterSeed) (table : Nat → Nat → Digest) :
    (maskRegion parameter seed table : m TopRegion) = maskRegionWith (maskSecret parameter seed) table := rfl

/-- The masked region the tables produce. -/
def tableRegion (table : Nat → Nat → Digest) (masks : MaskOutputs) : TopRegion :=
  fun level nodeIdx => table level.val nodeIdx.val ^^^ maskValue masks level.val nodeIdx.val

theorem maskRegionWith_pure {m : Type → Type} [Monad m] [LawfulMonad m] (table : Nat → Nat → Digest)
    (masks : MaskOutputs) :
    maskRegionWith (m := m) (fun level nodeIdx => pure (maskValue masks level nodeIdx)) table =
      pure (tableRegion table masks) := by
  unfold maskRegionWith
  simp only [pure_bind, sequenceFin_pure]
  congr 1
  funext level nodeIdx
  simp [tableRegion, nodeIdx.isLt]

/-- The table signer after its MAC check, with the top layer's path read from `cache` and unmasked
with the mask table. -/
def cachedTableSignChecked (randomizers : RandomizerOutputs) (masks : MaskOutputs)
    (secretKey : SphincsSecurity.SecretKey) (cache : TopCache) (message : Message) :
    OracleComp HashSpec (Option Signature) := do
  match ← tableDigestLoop randomizers secretKey message digestAttemptLimit 0 with
  | none => return none
  | some (randomness, index, leaves) =>
      Concrete.signFrom secretKey.parameter index (fun tree leaf => pure (secretKey.ftsSecret index tree leaf))
        (fun lay tree leaf chainIdx => pure (secretKey.otsSecret lay tree leaf chainIdx))
        (fun level nodeIdx => pure (cache.node level nodeIdx ^^^ maskValue masks level nodeIdx)) randomness leaves

/-- `Seeded.sign` from tables: the MAC check against the MAC table, then the checked signer. -/
def cachedTableSign (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs)
    (secretKey : SphincsSecurity.SecretKey) (cache : TopCache) (message : Message) :
    OracleComp HashSpec (Option Signature) :=
  if macs cache.region = cache.tag then cachedTableSignChecked randomizers masks secretKey cache message
  else pure none

section Cached

variable (known : QueryCache HashSpec) (parameter : PublicParameter) (seed : MasterSeed)
  (top : Nat → Nat → Digest) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
  (masks : MaskOutputs) (macs : MacOutputs)

theorem erases_maskSecret
    (hmasks : ∀ position, known (maskInputs parameter seed position) = some (masks position))
    (level nodeIdx : Nat) :
    Erases known (maskSecret parameter seed level nodeIdx : OracleComp HashSpec Digest)
      (pure (maskValue masks level nodeIdx)) := by
  unfold maskSecret deriveKey Concrete.oracleHash
  exact Erases.skip _ _ (hmasks (maskPosition level nodeIdx)) _ _ (.pure _)

theorem erases_cachedTopNode
    (hmasks : ∀ position, known (maskInputs parameter seed position) = some (masks position))
    (cache : TopCache) (level nodeIdx : Nat) :
    Erases known (cachedTopNode parameter seed cache level nodeIdx : OracleComp HashSpec Digest)
      (pure (cache.node level nodeIdx ^^^ maskValue masks level nodeIdx)) := by
  unfold cachedTopNode maskSecret deriveKey Concrete.oracleHash
  simp only [bind_assoc, pure_bind]
  exact Erases.skip _ _ (hmasks (maskPosition level nodeIdx)) _ _ (.pure _)

theorem erases_maskRegion
    (hmasks : ∀ position, known (maskInputs parameter seed position) = some (masks position))
    (table : Nat → Nat → Digest) :
    Erases known (maskRegion parameter seed table : OracleComp HashSpec TopRegion)
      (pure (tableRegion table masks)) := by
  rw [maskRegion_eq_with, ← maskRegionWith_pure]
  unfold maskRegionWith
  apply (Erases.sequenceFin known _ _ fun level =>
    (Erases.sequenceFin known _ _ fun nodeIdx =>
      (erases_maskSecret known parameter seed masks hmasks _ _).bind _ _ fun _ => .pure _).bind _ _
        fun _ => .pure _).bind
  intro _
  exact .pure _

theorem erases_signChecked
    (hsecrets : ∀ position, known (secretInputs parameter seed position) = some (outputs position))
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (hmasks : ∀ position, known (maskInputs parameter seed position) = some (masks position))
    (cache : TopCache) (message : Message) :
    Erases known (signChecked ⟨seed, parameter, top (layerHeight topLayer) 0⟩ cache message :
        OracleComp HashSpec _)
      (cachedTableSignChecked randomizers masks (tableKey parameter top outputs) cache message) := by
  unfold signChecked cachedTableSignChecked
  apply (erases_deterministicDigestLoop known parameter seed top outputs randomizers hrandomizers message _ _).bind
  intro attempt
  rcases attempt with _ | ⟨randomness, index, leaves⟩
  · exact .pure _
  · exact erases_signFrom parameter index
      (fun tree leaf => erases_ftsSecret known parameter seed outputs hsecrets index tree leaf)
      (fun lay tree leaf chainIdx => erases_otsSecret known parameter seed outputs hsecrets lay tree leaf chainIdx)
      (fun level nodeIdx => erases_cachedTopNode known parameter seed masks hmasks cache level nodeIdx)
      randomness leaves

theorem erases_cachedSign
    (hsecrets : ∀ position, known (secretInputs parameter seed position) = some (outputs position))
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (hmasks : ∀ position, known (maskInputs parameter seed position) = some (masks position))
    (hmacs : ∀ region, known (macInputs parameter seed region) = some (macs region))
    (cache : TopCache) (message : Message) :
    Erases known (sign ⟨seed, parameter, top (layerHeight topLayer) 0⟩ cache message : OracleComp HashSpec _)
      (cachedTableSign randomizers masks macs (tableKey parameter top outputs) cache message) := by
  unfold sign cachedTableSign Concrete.oracleHash
  apply Erases.skip _ _ (hmacs cache.region)
  change Erases known (if macs cache.region = cache.tag then _ else _) _
  split
  · exact erases_signChecked known parameter seed top outputs randomizers masks hsecrets hrandomizers hmasks
      cache message
  · exact .pure _

end Cached

end SphincsSecurity.Seeded
