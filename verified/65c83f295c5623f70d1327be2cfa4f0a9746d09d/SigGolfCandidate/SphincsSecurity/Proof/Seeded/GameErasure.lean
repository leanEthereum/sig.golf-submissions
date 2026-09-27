import SigGolfCandidate.SphincsSecurity.Proof.Seeded.AlgorithmErasure
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Secrets

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem Erases.simulateQ_writer {ι κ : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    {α : Type} (known : QueryCache target)
    (left right : QueryImpl source (WriterT (QueryLog SigningSpec) (OracleComp target)))
    (h : ∀ input, Erases known (left input).run (right input).run)
    (computation : OracleComp source α) :
    Erases known (simulateQ left computation).run (simulateQ right computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure _
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, WriterT.run_bind]
      apply (h input).bind
      intro result
      exact (ih result.1).map _

/-- Layer `0`'s tree built with the getter `secret`: the root key generation publishes. -/
def keygenTree (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) :
    OracleComp HashSpec Digest := do
  let (_, _, root) ← Concrete.buildLayerTree 0 topLayer Concrete.rootTree secret
    ⟨0, Nat.two_pow_pos _⟩ Concrete.zeroEncoding
  return root

theorem keygenRoot_eq_keygenTree (secret : LeafIndex → ChainIndex → Digest) :
    (Concrete.keygenRoot 0 secret : OracleComp HashSpec Digest) =
      keygenTree fun leaf chainIdx => pure (secret leaf chainIdx) := by
  rw [Concrete.keygenRoot]
  rfl

/-- The seeded game once the seed is sampled: build the top tree from the seed, then play. -/
noncomputable def gameAfterSeed (adversary : Adversary) (seed : MasterSeed) : OracleComp OracleWorld Bool := do
  let root ← liftM (keygenTree (otsSecret 0 seed topLayer Concrete.rootTree))
  gameRest randomizedScheme adversary ⟨root, 0⟩ ⟨seed, 0, root⟩

theorem gameCore_seeded_eq (adversary : Adversary) :
    gameCore randomizedScheme adversary =
      ((liftM sampleMasterSeed : OracleComp OracleWorld _) >>= gameAfterSeed adversary) := by
  have hkeygen : randomizedScheme.keygen = keygen := rfl
  unfold gameAfterSeed keygenTree
  simp only [gameCore, hkeygen, keygen, keygenFromSeed, bind_assoc, liftM_bind, liftM_pure, pure_bind]

/-- Key generation's first query: the derivation of the top tree's first secret. -/
def firstSecretPosition : SecretPosition :=
  .inl (topLayer, Concrete.rootTree, Concrete.leafOfNat 0, ⟨0, by decide⟩)

theorem keygenTree_first_query (seed : MasterSeed) {β : Type} (next : Digest → OracleComp OracleWorld β) :
    (liftM (keygenTree (otsSecret 0 seed topLayer Concrete.rootTree)) : OracleComp OracleWorld Digest) >>= next =
      (liftM (OracleWorld.query (.inr (secretInputs 0 seed firstSecretPosition))) >>= fun output =>
        (liftM (keygenTree (withFirst (otsSecret 0 seed topLayer Concrete.rootTree) (truncateHash output))) :
          OracleComp OracleWorld Digest) >>= next) := by
  unfold keygenTree
  rw [buildLayerTree_split_first]
  simp only [otsSecret, deriveKey, Concrete.oracleHash, liftM_bind, bind_assoc, liftM_pure, pure_bind]
  rfl

section Keygen

variable {known : QueryCache HashSpec} {seed : MasterSeed} {outputs : SecretOutputs}
  (hknown : ∀ position, known (secretInputs 0 seed position) = some (outputs position))

include hknown

theorem erases_keygenTree :
    Erases known (keygenTree (otsSecret 0 seed topLayer Concrete.rootTree))
      (Concrete.keygenRoot 0 (tableOts outputs topLayer Concrete.rootTree)) := by
  rw [keygenRoot_eq_keygenTree]
  unfold keygenTree
  exact (erases_buildLayerTree 0 _ _ (fun leaf chainIdx =>
    erases_otsSecret known 0 seed outputs hknown _ _ leaf chainIdx) _ _).bind _ _ fun _ => .refl _ _

/-- With the first secret already known, the rest of key generation also erases. -/
theorem erases_keygenTree_first :
    Erases known
      (keygenTree (withFirst (otsSecret 0 seed topLayer Concrete.rootTree)
        (truncateHash (outputs firstSecretPosition))))
      (Concrete.keygenRoot 0 (tableOts outputs topLayer Concrete.rootTree)) := by
  rw [keygenRoot_eq_keygenTree]
  unfold keygenTree
  refine (erases_buildLayerTree 0 _ _ (fun leaf chainIdx => ?_) _ _).bind _ _ fun _ => .refl _ _
  unfold withFirst
  split
  · next hfirst =>
      have hleaf : leaf = Concrete.leafOfNat 0 := Fin.ext (by simp [hfirst.1, Concrete.leafOfNat])
      have hchain : chainIdx = ⟨0, by decide⟩ := Fin.ext hfirst.2
      subst hleaf hchain
      exact .pure _
  · exact erases_otsSecret known 0 seed outputs hknown _ _ leaf chainIdx

theorem Erases.keygen_bind {β : Type} {nextLeft nextRight : Digest → OracleComp OracleWorld β}
    (hnext : ∀ root, Erases (worldKnown known) (nextLeft root) (nextRight root)) :
    Erases (worldKnown known)
      ((liftM (keygenTree (otsSecret 0 seed topLayer Concrete.rootTree)) : OracleComp OracleWorld Digest) >>= nextLeft)
      ((liftM (Concrete.keygenRoot 0 (tableOts outputs topLayer Concrete.rootTree) : OracleComp HashSpec Digest) :
        OracleComp OracleWorld Digest) >>= nextRight) :=
  (erases_keygenTree hknown).lift_hash.bind _ _ hnext

/-- The erased game saves at least the first query of key generation: its answer is known. -/
theorem hashQueryBound_keygen_erased (cache : QueryCache HashSpec) (hcache : known ≤ cache) {β : Type}
    {nextLeft nextRight : Digest → OracleComp OracleWorld β}
    (hnext : ∀ root, Erases (worldKnown known) (nextLeft root) (nextRight root)) (q : Nat)
    (hbound : HashQueryBound
      ((liftM (keygenTree (otsSecret 0 seed topLayer Concrete.rootTree)) : OracleComp OracleWorld Digest) >>= nextLeft)
      cache q) :
    1 ≤ q ∧ HashQueryBound
      ((liftM (Concrete.keygenRoot 0 (tableOts outputs topLayer Concrete.rootTree) : OracleComp HashSpec Digest) :
        OracleComp OracleWorld Digest) >>= nextRight) cache (q - 1) := by
  rw [keygenTree_first_query] at hbound
  have hc : cache (secretInputs 0 seed firstSecretPosition) = some (outputs firstSecretPosition) :=
    hcache (hknown _)
  have hstep : (outputs firstSecretPosition, cache) ∈
      support ((romImpl (.inr (secretInputs 0 seed firstSecretPosition))).run cache) := by
    change _ ∈ support ((randomOracle (spec := HashSpec) _).run cache)
    rw [QueryImpl.withCaching_run_some _ hc]
    simp
  have h := hashQueryBound_query_bind _ _ cache q hbound _ hstep
  exact ⟨h.1, ((erases_keygenTree_first hknown).lift_hash.bind _ _ hnext).hashQueryBound cache hcache _ h.2⟩

end Keygen

section Game

variable (known : QueryCache HashSpec) (parameter : PublicParameter) (seed : MasterSeed)
  (outputs : SecretOutputs)
  (hknown : ∀ position, known (secretInputs parameter seed position) = some (outputs position))

include hknown

theorem erases_gameRest (adversary : Adversary) (root : Digest) :
    Erases (worldKnown known)
      (gameRest randomizedScheme adversary ⟨root, parameter⟩ ⟨seed, parameter, root⟩)
      (SphincsSecurity.gameRest Concrete.scheme adversary ⟨root, parameter⟩ (tableKey parameter root outputs)) := by
  unfold gameRest SphincsSecurity.gameRest
  apply Erases.bind _ _ _ (fun _ => Erases.refl (worldKnown known) _)
  apply Erases.simulateQ_writer
  intro input
  cases input with
  | inl input =>
      simp only [QueryImpl.add_apply_inl]
      exact .refl _ _
  | inr request =>
      simp only [QueryImpl.add_apply_inr, signingOracle, QueryImpl.run_withLogging_apply, bind_pure_comp]
      exact (erases_sign known parameter seed outputs hknown root request).map _

end Game

theorem erases_gameAfterSeed {known : QueryCache HashSpec} {seed : MasterSeed} {outputs : SecretOutputs}
    (hknown : ∀ position, known (secretInputs 0 seed position) = some (outputs position))
    (adversary : Adversary) :
    Erases (worldKnown known) (gameAfterSeed adversary seed)
      (Concrete.gameAfterSecrets adversary 0 (tableOts outputs) (tableFts outputs)) := by
  unfold gameAfterSeed Concrete.gameAfterSecrets
  exact Erases.keygen_bind hknown fun root => erases_gameRest known 0 seed outputs hknown adversary root

end SphincsSecurity.Seeded
