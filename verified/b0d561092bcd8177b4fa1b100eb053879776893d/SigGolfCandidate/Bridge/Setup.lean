import SigGolfCandidate.Bridge.Basic
import SigGolf.Security
import SigGolfCandidate.SphincsSecurity.Statement

/-!
# Bridge assumptions

`Assumptions submission` collects everything the bridge needs about a submission: the abstract
event-form security claim, encodings (including the cache codec) between organizer bytes and abstract objects, the oracle
relabelling, and the implementation equations for the four programs.
-/

open OracleSpec OracleComp ENNReal

namespace SigGolfCandidate.Bridge

/-- The abstract hash oracle `List UInt8 →ₒ BitVec 256` (definitionally
`SphincsSecurity.HashSpec`, spelled with the literal output width). -/
abbrev AHash := List UInt8 →ₒ BitVec 256

/-- The abstract world `unifSpec + (List UInt8 →ₒ BitVec 256)`. -/
abbrev AW := unifSpec + AHash

/-- Abstract key generation, typed over `AHash`: the public key, the published cache, and the
secret key. -/
def aKeygen (seed : SphincsSecurity.MasterSeed) :
    OracleComp AHash
      (SphincsSecurity.PublicKey × SphincsSecurity.TopCache × SphincsSecurity.Seeded.SecretKey) :=
  SphincsSecurity.Seeded.keygenFromSeed seed

/-- Abstract signing with a caller-supplied cache, typed over `AHash`. It first checks the cache's
MAC (one query) and fails on a mismatch. -/
def aSign (sk : SphincsSecurity.Seeded.SecretKey) (cache : SphincsSecurity.TopCache)
    (message : SphincsSecurity.Message) : OracleComp AHash (Option SphincsSecurity.Signature) :=
  SphincsSecurity.Seeded.sign (m := OracleComp SphincsSecurity.HashSpec) sk cache message

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

/-- The abstract signing budget covers the organizer lifetime (both are `2^32`). -/
theorem lifetime_le : SigGolf.LIFETIME ≤ SphincsSecurity.signatureLimit := le_of_eq rfl

/-- Everything the bridge assumes about a submission.

The abstract signature is witness-shaped: the signer outputs `compress Σ`, expansion
(`aExpand`, which may query the oracle and fail) recovers a witness `w` with
`compress (witDec w) = σ`, and verification checks `witDec w` at the abstract level. -/
structure Assumptions (submission : SigGolf.Submission) where
  /-- (A) abstract event-form security. -/
  security : EventSecurity
  /-- Organizer secret keys become abstract master seeds, with the right distribution. -/
  seedOf : SigGolf.SecretKey → SphincsSecurity.MasterSeed
  seedOf_dist : ∀ seed, Pr[= seed | seedOf <$> SigGolf.sampleSecretKey] =
    Pr[= seed | SphincsSecurity.sampleMasterSeed]
  /-- (B) messages. -/
  msgOf : SigGolf.Message → SphincsSecurity.Message
  msgOf_injective : Function.Injective msgOf
  /-- (B) signatures. The abstract signature is witness-shaped: `compress` gives the compact
  signature bytes the signer outputs, and `witDec` parses a witness into an abstract signature.
  No codec law is assumed; the only link is `expand_compress` below. -/
  compress : SphincsSecurity.Signature → SigGolf.Bytes submission.sizes.signature
  witDec : SigGolf.Bytes submission.sizes.witness → SphincsSecurity.Signature
  /-- (B) public keys. -/
  pkEnc : SphincsSecurity.PublicKey → SigGolf.PublicKey
  /-- (B) caches: `cacheEnc` gives the bytes key generation publishes, `cacheDec` the abstract
  cache the signer reads from arbitrary bytes. No law relating them is needed for security. -/
  cacheEnc : SphincsSecurity.TopCache → SigGolf.Bytes submission.sizes.cache
  cacheDec : SigGolf.Bytes submission.sizes.cache → SphincsSecurity.TopCache
  /-- (C) oracle relabelling: `pad` maps abstract inputs to organizer queries, and is
  inverted by `unpad` on every organizer query and on every honest abstract input. -/
  pad : List UInt8 → SigGolf.Query
  unpad : SigGolf.Query → List UInt8
  Honest : List UInt8 → Prop
  pad_unpad : ∀ y, pad (unpad y) = y
  unpad_pad : ∀ x, Honest x → unpad (pad x) = x
  /-- (B) the abstract expansion: it may query the oracle and may fail. -/
  aExpand : SphincsSecurity.Message → SphincsSecurity.PublicKey →
    SigGolf.Bytes submission.sizes.signature →
      OracleComp AHash (Option (SigGolf.Bytes submission.sizes.witness))
  /-- (D) key generation. -/
  keygen_eq : ∀ sk, (fun r => (r.value, r.hashCalls)) <$> submission.run .keygen sk =
    (fun p => (some (pkEnc p.1.1, cacheEnc p.1.2.1), p.2)) <$>
      countCalls (relabel pad (aKeygen (seedOf sk)))
  keygen_honest : ∀ seed, AllQ Honest (aKeygen seed)
  /-- (D) signing, for the abstract secret key produced by key generation and *any* cache bytes,
  which the signer decodes with `cacheDec` (the MAC-mismatch path included). -/
  sign_eq : ∀ sk pk cache' sk', (pk, cache', sk') ∈ support (aKeygen (seedOf sk)) →
    ∀ cache message,
      (fun r => (r.value, r.hashCalls)) <$> submission.run .sign (sk, cache, message) =
        (fun p => (p.1.map compress, p.2)) <$>
          countCalls (relabel pad
            (aSign sk' (cacheDec cache) (msgOf message)))
  sign_honest : ∀ seed pk cache' sk', (pk, cache', sk') ∈ support (aKeygen seed) →
    ∀ cache message, AllQ Honest (aSign sk' cache message)
  /-- (D) expansion, for public keys produced by key generation. -/
  expand_eq : ∀ seed pk cache' sk', (pk, cache', sk') ∈ support (aKeygen seed) →
    ∀ message signature,
      (fun r => (r.value, r.hashCalls)) <$> submission.run .expand (message, pkEnc pk, signature) =
        countCalls (relabel pad (aExpand (msgOf message) pk signature))
  expand_honest : ∀ seed pk cache' sk', (pk, cache', sk') ∈ support (aKeygen seed) →
    ∀ message signature, AllQ Honest (aExpand message pk signature)
  /-- (B) `compress ∘ witDec` inverts expansion: on every successful run (for any oracle
  answers), the expanded witness compresses back to the input signature. -/
  expand_compress : ∀ seed pk cache' sk', (pk, cache', sk') ∈ support (aKeygen seed) →
    ∀ message signature witness, some witness ∈ support (aExpand message pk signature) →
      compress (witDec witness) = signature
  /-- (D) verification, for public keys produced by key generation. -/
  verify_eq : ∀ seed pk cache' sk', (pk, cache', sk') ∈ support (aKeygen seed) →
    ∀ message witness,
      (fun r => (r.value, r.hashCalls)) <$> submission.run .verify (message, pkEnc pk, witness) =
        (fun p => (if p.1 then some () else none, p.2)) <$>
          countCalls (relabel pad
            (aVerify pk (msgOf message) (witDec witness)))
  verify_honest : ∀ seed pk cache' sk', (pk, cache', sk') ∈ support (aKeygen seed) →
    ∀ message signature,
      AllQ Honest (aVerify pk message signature)

end SigGolfCandidate.Bridge
