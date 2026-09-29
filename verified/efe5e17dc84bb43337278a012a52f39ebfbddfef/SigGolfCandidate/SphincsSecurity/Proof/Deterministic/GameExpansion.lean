import SigGolfCandidate.SphincsSecurity.Proof.Seeded.GameErasure
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.GameExpansion

/-!
# The experiment's games after the seed

`cachedGameRest` is everything the experiment does after key generation, with the signer as a
parameter: the adversary gets the public key and the cache, signing requests carry a cache, and the
final forgery is checked against the request log. With the seeded key generation and signer it is the
experiment after the seed (`deterministicGameAfterSeed`); with every derivation read from tables it is
`cachedTableGameAfterSecrets`, which the seeded game erases to once the tables are in the cache.
`tableGameAfterSecrets` is the proof's table game for message-only adversaries, whose signer reads the
top layer's path from the key's node table.
-/

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

open Concrete

/-- Everything the experiment does after key generation, with the signer as a parameter. -/
noncomputable def cachedGameRest (signer : TopCache → Message → OracleComp HashSpec (Option Signature))
    (adversary : Security.Adversary) (pk : PublicKey) (cache : TopCache) : OracleComp OracleWorld Bool := do
  let ((forgery, log) : Forgery × QueryLog RequestSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog RequestSpec) (OracleComp OracleWorld)) +
      QueryImpl.withLogging fun request : SigningRequest =>
        (liftM (signer request.cache request.message) : OracleComp OracleWorld (Option Signature)))
      (adversary.main pk cache)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (RequestTranscript.Valid log ∧ ¬RequestTranscript.Contains log forgery) && verified

/-- The experiment once the seed is sampled: seeded key generation, then play against the seeded signer. -/
noncomputable def deterministicGameAfterSeed (adversary : Security.Adversary) (seed : MasterSeed) :
    OracleComp OracleWorld Bool :=
  (liftM (keygenCachedWith (otsSecret 0 seed topLayer rootTree) (maskSecret 0 seed)
      (fun region => oracleHash (macHashInput 0 seed region))) : OracleComp OracleWorld _) >>= fun result =>
    cachedGameRest (fun cache message => sign ⟨seed, 0, result.1 (layerHeight topLayer) 0⟩ cache message)
      adversary ⟨result.1 (layerHeight topLayer) 0, 0⟩ result.2

/-- The experiment from derivation tables: key generation and the signer read every derivation (one-time
and few-time secrets, masks, MAC answers, randomizers) from the tables. -/
noncomputable def cachedTableGameAfterSecrets (adversary : Security.Adversary) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (masks : MaskOutputs) (macs : MacOutputs) : OracleComp OracleWorld Bool :=
  (liftM (keygenCachedWith (fun leaf pair => pure (pairOf (tableOts outputs topLayer rootTree leaf) pair))
      (fun level nodeIdx => pure (maskValue masks level nodeIdx)) (fun region => pure (macs region))) :
      OracleComp OracleWorld _) >>= fun result =>
    cachedGameRest (cachedTableSign randomizers masks macs (tableKey 0 result.1 outputs))
      adversary ⟨result.1 (layerHeight topLayer) 0, 0⟩ result.2

/-- The proof's table game: build the top tree from the table, then play a message-only adversary against
the table signer. -/
noncomputable def tableGameAfterSecrets (adversary : Adversary) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) : OracleComp OracleWorld Bool := do
  let top ← liftM
    (Concrete.keygenTable 0 (tableOts outputs topLayer Concrete.rootTree) : OracleComp HashSpec (Nat → Nat → Digest))
  gameRest (tableScheme randomizers) adversary ⟨top (layerHeight topLayer) 0, 0⟩ (tableKey 0 top outputs)

theorem gameCore_deterministic_eq (adversary : Security.Adversary) :
    Security.gameCore adversary =
      ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>= deterministicGameAfterSeed adversary) := by
  unfold Security.gameCore
  refine bind_congr fun seed => ?_
  unfold deterministicGameAfterSeed
  rw [keygenFromSeed_eq, liftM_map, bind_map_left]
  refine bind_congr fun result => ?_
  rfl

theorem erases_cachedGameRest (known : QueryCache HashSpec)
    {left right : TopCache → Message → OracleComp HashSpec (Option Signature)}
    (h : ∀ cache message, Erases known (left cache message) (right cache message))
    (adversary : Security.Adversary) (pk : PublicKey) (cache : TopCache) :
    Erases (worldKnown known) (cachedGameRest left adversary pk cache) (cachedGameRest right adversary pk cache) := by
  unfold cachedGameRest
  apply Erases.bind _ _ _ (fun _ => Erases.refl (worldKnown known) _)
  apply Erases.simulateQ_writer
  intro input
  cases input with
  | inl input =>
      simp only [QueryImpl.add_apply_inl]
      exact .refl _ _
  | inr request =>
      simp only [QueryImpl.add_apply_inr, QueryImpl.run_withLogging_apply, bind_pure_comp]
      exact (h request.cache request.message).lift_hash.map _

section Erasure

variable {known : QueryCache HashSpec} {seed : MasterSeed} {outputs : SecretOutputs}
  {randomizers : RandomizerOutputs} {masks : MaskOutputs} {macs : MacOutputs}
  (hsecrets : ∀ position, known (secretInputs 0 seed position) = some (outputs position))
  (hrandomizers : ∀ position, known (randomizerInputs 0 seed position) = some (randomizers position))
  (hmasks : ∀ position, known (maskInputs 0 seed position) = some (masks position))
  (hmacs : ∀ region, known (macInputs 0 seed region) = some (macs region))

include hsecrets hrandomizers hmasks hmacs

theorem erases_deterministicGameRest (adversary : Security.Adversary) (top : Nat → Nat → Digest)
    (cache : TopCache) :
    Erases (worldKnown known)
      (cachedGameRest (fun cache message => sign ⟨seed, 0, top (layerHeight topLayer) 0⟩ cache message)
        adversary ⟨top (layerHeight topLayer) 0, 0⟩ cache)
      (cachedGameRest (cachedTableSign randomizers masks macs (tableKey 0 top outputs))
        adversary ⟨top (layerHeight topLayer) 0, 0⟩ cache) :=
  erases_cachedGameRest known (fun cache message =>
    erases_cachedSign known 0 seed top outputs randomizers masks macs hsecrets hrandomizers hmasks hmacs
      cache message) adversary _ cache

theorem erases_deterministicGameAfterSeed (adversary : Security.Adversary) :
    Erases (worldKnown known) (deterministicGameAfterSeed adversary seed)
      (cachedTableGameAfterSecrets adversary outputs randomizers masks macs) := by
  unfold deterministicGameAfterSeed cachedTableGameAfterSecrets
  exact (erases_keygen hsecrets hmasks hmacs).lift_hash.bind _ _ fun result =>
    erases_deterministicGameRest hsecrets hrandomizers hmasks hmacs adversary result.1 result.2

/-- The same, after key generation's first query (the derivation of the top tree's first secret) has
been answered with the table's value. -/
theorem erases_deterministicGameAfterSeed_first (adversary : Security.Adversary) :
    Erases (worldKnown known)
      ((liftM (keygenCachedWith (withFirstPair (otsSecret 0 seed topLayer rootTree)
          (splitSecrets (outputs firstSecretPosition))) (maskSecret 0 seed)
          (fun region => oracleHash (macHashInput 0 seed region))) : OracleComp OracleWorld _) >>= fun result =>
        cachedGameRest (fun cache message => sign ⟨seed, 0, result.1 (layerHeight topLayer) 0⟩ cache message)
          adversary ⟨result.1 (layerHeight topLayer) 0, 0⟩ result.2)
      (cachedTableGameAfterSecrets adversary outputs randomizers masks macs) := by
  unfold cachedTableGameAfterSecrets
  exact (erases_keygen_first hsecrets hmasks hmacs).lift_hash.bind _ _ fun result =>
    erases_deterministicGameRest hsecrets hrandomizers hmasks hmacs adversary result.1 result.2

end Erasure

/-- The first hash query after the seed is the derivation of the top tree's first secret. -/
theorem deterministicAfterSeed_first_query (adversary : Security.Adversary) (seed : MasterSeed) :
    deterministicGameAfterSeed adversary seed = (do
      let output ← liftM (OracleWorld.query (.inr (secretInputs 0 seed firstSecretPosition)))
      (liftM (keygenCachedWith (withFirstPair (otsSecret 0 seed topLayer rootTree) (splitSecrets output))
          (maskSecret 0 seed) (fun region => oracleHash (macHashInput 0 seed region))) :
          OracleComp OracleWorld _) >>= fun result =>
        cachedGameRest (fun cache message => sign ⟨seed, 0, result.1 (layerHeight topLayer) 0⟩ cache message)
          adversary ⟨result.1 (layerHeight topLayer) 0, 0⟩ result.2) := by
  unfold deterministicGameAfterSeed
  rw [keygenCachedWith_first, otsSecret_first]
  simp only [map_eq_bind_pure_comp, liftM_bind, bind_assoc, liftM_pure, pure_bind, Function.comp_apply]
  rfl

end SphincsSecurity.Seeded
