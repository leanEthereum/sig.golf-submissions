import SigGolfCandidate.SphincsSecurity.Completeness
import SigGolfCandidate.SphincsSecurity.Completeness.Recovery
import SigGolfCandidate.Equiv.Honest
import SigGolfCandidate.Equiv.Expand

/-!
# The abstract honest game over the hash oracle alone

`game seed m` is `Completeness.seededGameCore seed m` without the lift into `OracleWorld`:
generate the key from the seed, sign, verify. `seededExperiment_eq` runs it against the lazy random
oracle; `hq_game`: all its queries are `Honest`.

`gameX seed m` is the organizer's honest pipeline in abstract form: it also expands the compressed
signature (`Equiv.aExpand`, one digest query) and verifies the decoded witness. Under every answer
function it computes what `game` computes (`eval_gameX`): the expansion's digest query of `rho` returns
the digest the signer accepted, so (relation R4, `Equiv.expandOf_honest`) the witness decodes to the
signature itself.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Final
open SphincsSecurity

/-- The honest abstract run from a fixed seed, over the hash oracle alone. -/
def game (seed : MasterSeed) (message : Message) : OracleComp SphincsSecurity.HashSpec Bool := do
  let (pk, cache, sk) ← Seeded.keygenFromSeed seed
  let some signature ←
      (Seeded.sign sk cache message : OracleComp SphincsSecurity.HashSpec (Option Signature))
    | return false
  (Concrete.verify pk message signature : OracleComp SphincsSecurity.HashSpec Bool)

/-- The honest abstract run with the expansion: key generation, signing, the expansion of the
compressed signature, verification of the decoded witness. -/
def gameX (seed : MasterSeed) (message : Message) : OracleComp SphincsSecurity.HashSpec Bool := do
  let (pk, cache, sk) ← Seeded.keygenFromSeed seed
  let some signature ←
      (Seeded.sign sk cache message : OracleComp SphincsSecurity.HashSpec (Option Signature))
    | return false
  let some witness ← Equiv.aExpand message pk (Equiv.compress signature) | return false
  (Concrete.verify pk message (Equiv.witDec witness) : OracleComp SphincsSecurity.HashSpec Bool)

theorem seededGameCore_eq (seed : MasterSeed) (message : Message) :
    Completeness.seededGameCore seed message =
      (liftM (game seed message) : OracleComp OracleWorld Bool) := by
  unfold Completeness.seededGameCore game
  simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_bind]
  refine bind_congr fun kp => ?_
  rcases kp with ⟨pk, cache, sk⟩
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · simp
  · rfl

theorem seededExperiment_eq (seed : MasterSeed) (message : Message) :
    Completeness.seededExperiment seed message =
      (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec
        (StateT (QueryCache SphincsSecurity.HashSpec) ProbComp)) (game seed message)).run' ∅ := by
  unfold Completeness.seededExperiment Completeness.romImpl
  rw [seededGameCore_eq, QueryImpl.simulateQ_add_liftM_right]

theorem hq_game (seed : MasterSeed) (message : Message) : Equiv.HQ (game seed message) := by
  unfold game Seeded.keygenFromSeed Seeded.maskRegion
  simp only [bind_assoc, pure_bind]
  refine Equiv.hq_bind (Equiv.hq_buildLayerTablePaired _ rfl _ _ _ (fun _ _ => Equiv.hq_otsSecret _ _ _ _ _ _) _ _)
    fun t => ?_
  refine Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ => Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ =>
    Equiv.hq_bind (Equiv.hq_maskSecret _ _ _ _) fun _ => Equiv.hq_pure _) fun _ => Equiv.hq_pure _)
    fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_mac _ _ _) fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_sign _ rfl _ _) fun s => ?_
  rcases s with _ | σ
  · exact Equiv.hq_pure _
  · exact Equiv.hq_verify _ rfl _ _

theorem hq_gameX (seed : MasterSeed) (message : Message) : Equiv.HQ (gameX seed message) := by
  unfold gameX Seeded.keygenFromSeed Seeded.maskRegion
  simp only [bind_assoc, pure_bind]
  refine Equiv.hq_bind (Equiv.hq_buildLayerTablePaired _ rfl _ _ _ (fun _ _ => Equiv.hq_otsSecret _ _ _ _ _ _) _ _)
    fun t => ?_
  refine Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ => Equiv.hq_bind (Equiv.hq_sequenceFin _ fun _ =>
    Equiv.hq_bind (Equiv.hq_maskSecret _ _ _ _) fun _ => Equiv.hq_pure _) fun _ => Equiv.hq_pure _)
    fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_mac _ _ _) fun _ => ?_
  refine Equiv.hq_bind (Equiv.hq_sign _ rfl _ _) fun s => ?_
  rcases s with _ | σ
  · exact Equiv.hq_pure _
  · refine Equiv.hq_bind (Equiv.hq_aExpand _ _ _) fun w => ?_
    rcases w with _ | w
    · exact Equiv.hq_pure _
    · exact Equiv.hq_verify _ rfl _ _

/-! ## The expansion under a fixed answer function -/

section eval

variable (f : QueryImpl SphincsSecurity.HashSpec Id)

-- Both values stand for a whole tree build under `f`; unfolding them runs it.
attribute [local irreducible] Completeness.keygenTableValue Completeness.keygenRegionValue

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

theorem ofList_sigRho_compress (σ : Signature) :
    Ref.ofList 16 (Ref.sigRho (Ref.toList (Equiv.compress σ))) = σ.randomness := by
  rw [Equiv.toList_compress]
  unfold Ref.sigRho Equiv.compressList
  simp only [List.append_assoc]
  rw [Equiv.slice_append_left _ _ _ _ (by simp), Equiv.slice_full _ _ (Equiv.length_dv _)]
  exact Ref.ofList_toList (n := 16) _

/-- A signature signed with the key and cache of key generation is the honest opening of the admissible
digest of its randomness. -/
theorem sign_shape (seed : MasterSeed) (message : Message) {pk : PublicKey} {cache : TopCache}
    {sk : Seeded.SecretKey} {S : Signature}
    (hkeys : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (pk, cache, sk))
    (hsign : evalWithAnswerFn f (Seeded.sign sk cache message
      : OracleComp SphincsSecurity.HashSpec (Option Signature)) = some S) :
    pk = ⟨sk.root, 0⟩ ∧ sk.parameter = 0 ∧
    Concrete.Admissible (Completeness.digestValue f sk message S.randomness) ∧
    ∃ (secret : FtsLeaf → Digest) (node : Nat → Nat → Digest),
      S = ⟨S.randomness, Concrete.honestFts
        (Concrete.digestLeaves (Completeness.digestValue f sk message S.randomness)) secret node,
        S.layers⟩ := by
  rw [Completeness.eval_keygenFromSeed] at hkeys
  simp only [Prod.mk.injEq] at hkeys
  obtain ⟨rfl, rfl, rfl⟩ := hkeys
  refine ⟨rfl, rfl, ?_⟩
  obtain ⟨hadm, hsig⟩ := Completeness.signChecked_spec f _ _ (Completeness.keygen_cacheHonest f seed _)
    message (Completeness.signChecked_of_sign f _ _ message hsign)
  refine ⟨hadm, ?_⟩
  unfold Concrete.signatureValue at hsig
  cases hparts : SphincsSecurity.Concrete.sequenceFin (m := Option) (fun lay =>
      evalWithAnswerFn f (Concrete.signLayer (Completeness.tableKey f
        ⟨seed, 0, Completeness.keygenTableValue f seed (layerHeight topLayer) 0⟩)
        (Concrete.digestIndex (Completeness.digestValue f _ message S.randomness)) lay)) with
  | none => rw [hparts] at hsig; simp at hsig
  | some parts =>
    rw [hparts] at hsig
    simp only [Option.map_some, Option.some.injEq] at hsig
    rw [Concrete.eval_ftsOpen] at hsig
    rcases S with ⟨r, fts, layers⟩
    simp only [Signature.mk.injEq] at hsig
    obtain ⟨-, hfts, -⟩ := hsig
    subst hfts
    exact ⟨_, _, rfl⟩

/-- Under a fixed answer function, the expansion of an honestly produced signature succeeds with a
witness decoding to the signature. -/
theorem eval_aExpand_sign (seed : MasterSeed) (message : Message) {pk : PublicKey} {cache : TopCache}
    {sk : Seeded.SecretKey} {S : Signature}
    (hkeys : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (pk, cache, sk))
    (hsign : evalWithAnswerFn f (Seeded.sign sk cache message
      : OracleComp SphincsSecurity.HashSpec (Option Signature)) = some S) :
    ∃ w, evalWithAnswerFn f (Equiv.aExpand message pk (Equiv.compress S)) = some w ∧
      Equiv.witDec w = S := by
  obtain ⟨hpk, hP, hadm, secret, node, hS⟩ := sign_shape f seed message hkeys hsign
  set d := Completeness.digestValue f sk message S.randomness with hd
  obtain ⟨wl, hlen, hexp, hwit⟩ := Equiv.expandOf_honest (Concrete.digestLeaves d) hadm d.toNat
    (fun r => Equiv.leafOf_eq d r) S.randomness secret node S.layers
  refine ⟨Ref.ofList 6348 wl, ?_, ?_⟩
  · unfold Equiv.aExpand
    rw [ofList_sigRho_compress, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
    have e1 : evalWithAnswerFn f (Concrete.messageDigest (m := Equiv.AComp) 0 pk.root message S.randomness)
        = d := by
      rw [hd, Completeness.digestValue, hP]
      rfl
    rw [e1, Equiv.toList_compress]
    conv_lhs => rw [hS]
    rw [hexp]
    rfl
  · unfold Equiv.witDec
    rw [Ref.toList_ofList _ _ hlen, hwit, ← hS]

/-- **The expansion does not change the honest game** under any answer function. -/
theorem eval_gameX (seed : MasterSeed) (message : Message) :
    evalWithAnswerFn f (gameX seed message) = evalWithAnswerFn f (game seed message) := by
  unfold gameX game
  simp only [evalWithAnswerFn_bind]
  generalize hk : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = kp
  obtain ⟨pk, cache, sk⟩ := kp
  dsimp only
  generalize hs : evalWithAnswerFn f (Seeded.sign sk cache message
    : OracleComp SphincsSecurity.HashSpec (Option Signature)) = s
  cases s with
  | none => rfl
  | some S =>
    obtain ⟨w, hw, hwS⟩ := eval_aExpand_sign f seed message hk hs
    simp only [evalWithAnswerFn_bind, hw, hwS]

end eval

end SigGolfCandidate.Final
