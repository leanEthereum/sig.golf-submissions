import SigGolfCandidate.Bridge.Setup

/-!
# Convenience constructors for the bridge assumptions

* `seedOf_id_dist`: the organizer secret key *is* a master seed (both are 32 uniform bytes).
* `Assumptions.ofZeroPad`: build the oracle relabelling (C) from a zero-padding map that is
  injective on honest inputs, all of which start with byte `1`; adversary queries outside the
  honest image are sent to the abstract oracle as `0 :: qEnc y`.
-/

open OracleSpec OracleComp SigGolf

namespace SigGolfCandidate.Bridge

/-- With `seedOf = id`, the seed distribution hypothesis holds: both samplers are uniform on
`BitVec 256`. -/
theorem seedOf_id_dist (seed : SphincsSecurity.MasterSeed) :
    Pr[= seed | (id : SecretKey → SphincsSecurity.MasterSeed) <$> sampleSecretKey] =
      Pr[= seed | SphincsSecurity.sampleMasterSeed] := by
  rw [id_map]
  unfold sampleSecretKey SphincsSecurity.sampleMasterSeed
  rw [probOutput_uniformSample, probOutput_uniformSample]

section relabelCongr

variable {ι ι' : Type} {R : Type}

lemma relabel_congr_of_allQ (P : ι → Prop) {f g : ι → ι'} (hfg : ∀ x, P x → f x = g x)
    {α : Type} {oa : OracleComp (ι →ₒ R) α} (hq : AllQ P oa) : relabel f oa = relabel g oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rw [allQ_query_bind] at hq
    rw [relabel_bind, relabel_bind, relabel_query, relabel_query, hfg t hq.1]
    exact bind_congr fun u => ih u (hq.2 u)

end relabelCongr

/-- An injective encoding of organizer queries as byte lists (unary in the `Encodable` code:
only injectivity matters, since it is used only inside the proof's relabelling). -/
noncomputable def defaultQEnc (y : Query) : List UInt8 :=
  List.replicate (@Encodable.encode _ (Encodable.ofCountable Query) y) 0

lemma defaultQEnc_injective : Function.Injective defaultQEnc := by
  intro x y h
  have := congrArg List.length h
  simp only [defaultQEnc, List.length_replicate] at this
  exact @Encodable.encode_injective _ (Encodable.ofCountable Query) _ _ this

section zeroPad

variable (padZ : List UInt8 → Query) (Honest : List UInt8 → Prop) (qEnc : Query → List UInt8)

open Classical in
/-- Abstract name of an organizer query: its honest preimage under `padZ` if there is one,
otherwise the tagged encoding `0 :: qEnc y`. -/
noncomputable def zpUnpad (y : Query) : List UInt8 :=
  if h : ∃ x, Honest x ∧ padZ x = y then Classical.choose h else 0 :: qEnc y

open Classical in
/-- Organizer query of an abstract input: `padZ` on honest inputs, decoding of the tag otherwise. -/
noncomputable def zpPad (x : List UInt8) : Query :=
  if Honest x then padZ x
  else if h : ∃ y, x = 0 :: qEnc y then Classical.choose h else padZ x

variable {padZ Honest qEnc}

lemma zpPad_zpUnpad (hfirst : ∀ x, Honest x → x.head? = some 1) (hq : Function.Injective qEnc)
    (y : Query) : zpPad padZ Honest qEnc (zpUnpad padZ Honest qEnc y) = y := by
  unfold zpUnpad
  split_ifs with h
  · have hs := Classical.choose_spec h
    simp [zpPad, hs.1, hs.2]
  · have hnot : ¬ Honest (0 :: qEnc y) := fun hh => by simpa using hfirst _ hh
    have hex : ∃ y', (0 :: qEnc y : List UInt8) = 0 :: qEnc y' := ⟨y, rfl⟩
    simp only [zpPad, hnot, if_false, dif_pos hex]
    have := Classical.choose_spec hex
    exact (hq (List.cons_injective this)).symm

lemma zpUnpad_zpPad (hinj : Set.InjOn padZ Honest) (x : List UInt8) (hx : Honest x) :
    zpUnpad padZ Honest qEnc (zpPad padZ Honest qEnc x) = x := by
  have hpad : zpPad padZ Honest qEnc x = padZ x := by simp [zpPad, hx]
  rw [hpad]
  unfold zpUnpad
  have h : ∃ x', Honest x' ∧ padZ x' = padZ x := ⟨x, hx, rfl⟩
  rw [dif_pos h]
  have hs := Classical.choose_spec h
  exact hinj hs.1 hx hs.2

end zeroPad

/-- `Assumptions` with the oracle relabelling (C) given in zero-padding form: `pad` is injective on
honest inputs, every honest input starts with byte `1`, and `qEnc` is any injective byte
encoding of organizer queries (e.g. `defaultQEnc`). -/
structure ZeroPadAssumptions (sub : SigGolf.Submission) where
  /-- (A) abstract event-form security. -/
  security : EventSecurity
  /-- The abstract signing budget covers the organizer lifetime. -/
  lifetime_le : SigGolf.LIFETIME ≤ SphincsSecurity.signatureLimit
  /-- Organizer secret keys become abstract master seeds, with the right distribution. -/
  seedOf : SigGolf.SecretKey → SphincsSecurity.MasterSeed
  seedOf_dist : ∀ seed, Pr[= seed | seedOf <$> SigGolf.sampleSecretKey] =
    Pr[= seed | SphincsSecurity.sampleMasterSeed]
  /-- (B) messages. -/
  msgOf : SigGolf.Message → SphincsSecurity.Message
  msgOf_injective : Function.Injective msgOf
  /-- (B) signatures: an exact byte codec. -/
  sigCodec : SigGolf.Bytes sub.sizes.signature ≃ SphincsSecurity.Signature
  /-- (B) the expansion map and the witness decoder, with `witDec ∘ expandFn = sigCodec`. -/
  expandFn : SigGolf.Bytes sub.sizes.signature → SigGolf.Bytes sub.sizes.witness
  witDec : SigGolf.Bytes sub.sizes.witness → SphincsSecurity.Signature
  witDec_expandFn : ∀ b, witDec (expandFn b) = sigCodec b
  /-- (B) public keys and the published cache. -/
  pkEnc : SphincsSecurity.PublicKey → SigGolf.PublicKey
  cacheOf : SphincsSecurity.PublicKey → SigGolf.Cache
  /-- (C) zero padding, injective on honest inputs, which all start with byte `1`. -/
  pad : List UInt8 → SigGolf.Query
  Honest : List UInt8 → Prop
  pad_injOn : Set.InjOn pad Honest
  honest_head : ∀ x, Honest x → x.head? = some 1
  qEnc : SigGolf.Query → List UInt8
  qEnc_injective : Function.Injective qEnc
  /-- (D) key generation. -/
  keygen_eq : ∀ sk, (fun r => (r.value, r.hashCalls)) <$> sub.run .keygen sk =
    (fun p => (some (pkEnc p.1.1, cacheOf p.1.1), p.2)) <$>
      countCalls (relabel pad (aKeygen (seedOf sk)))
  keygen_honest : ∀ seed, AllQ Honest (aKeygen seed)
  /-- (D) signing, for the abstract secret key produced by key generation. -/
  sign_eq : ∀ sk pk sk', (pk, sk') ∈ support (aKeygen (seedOf sk)) →
    ∀ cache message,
      (fun r => (r.value, r.hashCalls)) <$> sub.run .sign (sk, cache, message) =
        (fun p => (p.1.map sigCodec.symm, p.2)) <$>
          countCalls (relabel pad
            (aSign sk' (msgOf message)))
  sign_honest : ∀ seed pk sk', (pk, sk') ∈ support (aKeygen seed) →
    ∀ message, AllQ Honest (aSign sk' message)
  /-- (D) expansion: no hash calls. -/
  expand_eq : ∀ message pk signature,
    (fun r => (r.value, r.hashCalls)) <$> sub.run .expand (message, pk, signature) =
      pure (some (expandFn signature), 0)
  /-- (D) verification, for public keys produced by key generation. -/
  verify_eq : ∀ seed pk sk', (pk, sk') ∈ support (aKeygen seed) →
    ∀ message witness,
      (fun r => (r.value, r.hashCalls)) <$> sub.run .verify (message, pkEnc pk, witness) =
        (fun p => (if p.1 then some () else none, p.2)) <$>
          countCalls (relabel pad
            (aVerify pk (msgOf message) (witDec witness)))
  verify_honest : ∀ seed pk sk', (pk, sk') ∈ support (aKeygen seed) →
    ∀ message signature,
      AllQ Honest (aVerify pk message signature)


namespace ZeroPadAssumptions

variable {sub : SigGolf.Submission} (Z : ZeroPadAssumptions sub)

lemma zpPad_eq {x : List UInt8} (hx : Z.Honest x) : zpPad Z.pad Z.Honest Z.qEnc x = Z.pad x := by
  simp [zpPad, hx]

lemma relabel_zp {α : Type} {X : OracleComp AHash α} (hX : AllQ Z.Honest X) :
    relabel (zpPad Z.pad Z.Honest Z.qEnc) X = relabel Z.pad X :=
  relabel_congr_of_allQ Z.Honest (fun _ hx => Z.zpPad_eq hx) hX

/-- Convert the zero-padding form of (C) into the bridge's `pad`/`unpad` form. -/
noncomputable def toAssumptions : Assumptions sub where
  security := Z.security
  lifetime_le := Z.lifetime_le
  seedOf := Z.seedOf
  seedOf_dist := Z.seedOf_dist
  msgOf := Z.msgOf
  msgOf_injective := Z.msgOf_injective
  sigCodec := Z.sigCodec
  expandFn := Z.expandFn
  witDec := Z.witDec
  witDec_expandFn := Z.witDec_expandFn
  pkEnc := Z.pkEnc
  cacheOf := Z.cacheOf
  pad := zpPad Z.pad Z.Honest Z.qEnc
  unpad := zpUnpad Z.pad Z.Honest Z.qEnc
  Honest := Z.Honest
  pad_unpad := zpPad_zpUnpad Z.honest_head Z.qEnc_injective
  unpad_pad := zpUnpad_zpPad Z.pad_injOn
  keygen_eq sk := by rw [Z.keygen_eq, Z.relabel_zp (Z.keygen_honest _)]
  keygen_honest := Z.keygen_honest
  sign_eq sk pk sk' h cache m := by
    rw [Z.sign_eq sk pk sk' h, Z.relabel_zp (Z.sign_honest _ pk sk' h _)]
  sign_honest := Z.sign_honest
  expand_eq := Z.expand_eq
  verify_eq seed pk sk' h m w := by
    rw [Z.verify_eq seed pk sk' h, Z.relabel_zp (Z.verify_honest _ pk sk' h _ _)]
  verify_honest := Z.verify_honest

end ZeroPadAssumptions

end SigGolfCandidate.Bridge
