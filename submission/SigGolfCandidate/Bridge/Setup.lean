import SigGolfCandidate.Bridge.Basic
import SigGolf.Security
import SigGolfCandidate.SphincsSecurity.Statement

/-!
# Bridge assumptions

`Assumptions submission` collects everything the bridge needs about a submission: the abstract
event-form security claim, encodings between organizer bytes and abstract objects, the oracle
relabelling, and the implementation equations for the four programs.
-/

open OracleSpec OracleComp ENNReal

namespace SigGolfCandidate.Bridge

/-- The abstract hash oracle `List UInt8 →ₒ BitVec 256` (definitionally
`SphincsSecurity.HashSpec`, spelled with the literal output width). -/
abbrev AHash := List UInt8 →ₒ BitVec 256

/-- The abstract world `unifSpec + (List UInt8 →ₒ BitVec 256)`. -/
abbrev AW := unifSpec + AHash

/-- Abstract key generation, typed over `AHash`. -/
def aKeygen (seed : SphincsSecurity.MasterSeed) :
    OracleComp AHash (SphincsSecurity.PublicKey × SphincsSecurity.Seeded.SecretKey) :=
  SphincsSecurity.Seeded.keygenFromSeed seed

/-- Abstract signing, typed over `AHash`. -/
def aSign (sk : SphincsSecurity.Seeded.SecretKey) (message : SphincsSecurity.Message) :
    OracleComp AHash (Option SphincsSecurity.Signature) :=
  SphincsSecurity.Seeded.sign (m := OracleComp SphincsSecurity.HashSpec) sk message

/-- Abstract verification, typed over `AHash`. -/
def aVerify (pk : SphincsSecurity.PublicKey) (message : SphincsSecurity.Message)
    (signature : SphincsSecurity.Signature) : OracleComp AHash Bool :=
  SphincsSecurity.Concrete.verify (m := OracleComp SphincsSecurity.HashSpec) pk message signature

/-- Abstract event-form security: every adversary wins *and* uses at most `q` hash calls with
probability at most `q / 2^127`. -/
def EventSecurity : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ adversary : SphincsSecurity.Security.Adversary,
    Pr[fun result => result.1 = true ∧ result.2 ≤ q |
      SphincsSecurity.Security.experiment adversary] ≤ (q : ℝ≥0∞) / 2 ^ 127

/-- Everything the bridge assumes about a submission. -/
structure Assumptions (submission : SigGolf.Submission) where
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
  sigCodec : SigGolf.Bytes submission.sizes.signature ≃ SphincsSecurity.Signature
  /-- (B) the expansion map and the witness decoder, with `witDec ∘ expandFn = sigCodec`. -/
  expandFn : SigGolf.Bytes submission.sizes.signature → SigGolf.Bytes submission.sizes.witness
  witDec : SigGolf.Bytes submission.sizes.witness → SphincsSecurity.Signature
  witDec_expandFn : ∀ b, witDec (expandFn b) = sigCodec b
  /-- (B) public keys and the published cache. -/
  pkEnc : SphincsSecurity.PublicKey → SigGolf.PublicKey
  cacheOf : SphincsSecurity.PublicKey → SigGolf.Cache
  /-- (C) oracle relabelling: `pad` maps abstract inputs to organizer queries, and is
  inverted by `unpad` on every organizer query and on every honest abstract input. -/
  pad : List UInt8 → SigGolf.Query
  unpad : SigGolf.Query → List UInt8
  Honest : List UInt8 → Prop
  pad_unpad : ∀ y, pad (unpad y) = y
  unpad_pad : ∀ x, Honest x → unpad (pad x) = x
  /-- (D) key generation. -/
  keygen_eq : ∀ sk, (fun r => (r.value, r.hashCalls)) <$> submission.run .keygen sk =
    (fun p => (some (pkEnc p.1.1, cacheOf p.1.1), p.2)) <$>
      countCalls (relabel pad (aKeygen (seedOf sk)))
  keygen_honest : ∀ seed, AllQ Honest (aKeygen seed)
  /-- (D) signing, for the abstract secret key produced by key generation. -/
  sign_eq : ∀ sk pk sk', (pk, sk') ∈ support (aKeygen (seedOf sk)) →
    ∀ cache message,
      (fun r => (r.value, r.hashCalls)) <$> submission.run .sign (sk, cache, message) =
        (fun p => (p.1.map sigCodec.symm, p.2)) <$>
          countCalls (relabel pad
            (aSign sk' (msgOf message)))
  sign_honest : ∀ seed pk sk', (pk, sk') ∈ support (aKeygen seed) →
    ∀ message, AllQ Honest (aSign sk' message)
  /-- (D) expansion: no hash calls. -/
  expand_eq : ∀ message pk signature,
    (fun r => (r.value, r.hashCalls)) <$> submission.run .expand (message, pk, signature) =
      pure (some (expandFn signature), 0)
  /-- (D) verification, for public keys produced by key generation. -/
  verify_eq : ∀ seed pk sk', (pk, sk') ∈ support (aKeygen seed) →
    ∀ message witness,
      (fun r => (r.value, r.hashCalls)) <$> submission.run .verify (message, pkEnc pk, witness) =
        (fun p => (if p.1 then some () else none, p.2)) <$>
          countCalls (relabel pad
            (aVerify pk (msgOf message) (witDec witness)))
  verify_honest : ∀ seed pk sk', (pk, sk') ∈ support (aKeygen seed) →
    ∀ message signature,
      AllQ Honest (aVerify pk message signature)

end SigGolfCandidate.Bridge
