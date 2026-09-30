import SigGolfCandidate.SphincsSecurity.Scheme
import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# SPHINCS+ security statement

Strong unforgeability under chosen-message attacks (SUF-CMA) in the classical random-oracle model, with a 127-bit security target for the scheme in `Scheme.lean`.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

/-! ## The security experiment -/

/-- A claimed forgery: a message and a signature. -/
structure Forgery where
  message : Message
  signature : Signature
deriving DecidableEq

/-- A signing request of the proof's ideal games is a message alone, and the answer is a signature or `none` if the signer fails. -/
abbrev SigningSpec := Message →ₒ Option Signature

/-- A signing request of the experiment: a message and a cache, both chosen by the adversary. The signer
checks the cache's MAC and reads the top layer's path from it. -/
structure SigningRequest where
  message : Message
  cache : TopCache
deriving DecidableEq

/-- The experiment's signing oracle: a request is answered by a signature or `none` if the signer fails
(including a cache that fails its MAC check). -/
abbrev RequestSpec := SigningRequest →ₒ Option Signature

namespace SigningTranscript

/-- A signing transcript is valid exactly when the key signed at most `q_s` messages. Repeated messages receive the same signature or failure. -/
def Valid (log : QueryLog SigningSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog SigningSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

/-- The signer returned the claimed forgery exactly when the transcript contains the same message answered by the same signature. A different signature for a signed message is therefore a valid strong forgery. -/
def Contains (log : QueryLog SigningSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog SigningSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1 = forgery.message ∧ entry.2 = some forgery.signature))

end SigningTranscript

namespace RequestTranscript

/-- A transcript is valid exactly when the key answered at most `q_s` requests, failed ones included. -/
def Valid (log : QueryLog RequestSpec) : Prop := log.length ≤ signatureLimit

instance (log : QueryLog RequestSpec) : Decidable (Valid log) :=
  inferInstanceAs (Decidable (log.length ≤ signatureLimit))

/-- The signer returned the claimed forgery exactly when some request for the same message, with any
cache, was answered by the same signature. A different signature for a signed message is a valid strong
forgery. -/
def Contains (log : QueryLog RequestSpec) (forgery : Forgery) : Prop :=
  ∃ entry ∈ log, entry.1.message = forgery.message ∧ entry.2 = some forgery.signature

instance (log : QueryLog RequestSpec) (forgery : Forgery) : Decidable (Contains log forgery) :=
  inferInstanceAs
    (Decidable (∃ entry ∈ log, entry.1.message = forgery.message ∧ entry.2 = some forgery.signature))

end RequestTranscript

namespace Security

/-- A probabilistic adaptive adversary with private randomness and access to hashing and signing. It
receives the public key and the published cache, and chooses the cache of every signing request. -/
structure Adversary where
  main : PublicKey → TopCache → OracleComp (OracleWorld + RequestSpec) Forgery

/-- Record each signing request and its answer. -/
def signingOracle (sk : Seeded.SecretKey) :
    QueryImpl RequestSpec (WriterT (QueryLog RequestSpec) (OracleComp OracleWorld)) :=
  QueryImpl.withLogging fun request =>
    liftM (Seeded.sign sk request.cache request.message : OracleComp HashSpec _)

/-- Sample the master seed, then run all parties with one shared hash oracle. -/
noncomputable def gameCore (adversary : Adversary) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, cache, sk) ← liftM (Seeded.keygenFromSeed seed)
  let ((forgery, log) : Forgery × QueryLog RequestSpec) ←
    (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog RequestSpec) (OracleComp OracleWorld)) + signingOracle sk) (adversary.main pk cache)).run
  let verified ← liftM (Concrete.verify pk forgery.message forgery.signature : OracleComp HashSpec Bool)
  return decide (RequestTranscript.Valid log ∧ ¬RequestTranscript.Contains log forgery) && verified

/-- Forward private sampling for free; answer hash queries consistently and count every call, including cache hits. -/
noncomputable def countedOracle :=
  (unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))).withAddCost
    (fun | .inl _ => (0 : Nat) | .inr _ => 1)

/-- Run the game from an empty random-oracle cache, recording success and the total number of hash calls. -/
noncomputable def experiment (adversary : Adversary) : ProbComp (Bool × Nat) :=
  (simulateQ countedOracle (gameCore adversary)).run.run' ∅

/-- The probability of a successful forgery. -/
noncomputable def forgeAdvantage (adversary : Adversary) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true | experiment adversary]

/-- Every execution uses at most `q` hash calls, including key generation, signing, and verification. -/
def HasHashQueryBound (adversary : Adversary) (q : Nat) : Prop :=
  ∀ result ∈ support (experiment adversary), result.2 ≤ q

/-- Every adversary with nonzero query budget `q` wins with probability at most `q / 2^bits`. -/
def HasClassicalSecurityBits (bits : Nat) : Prop :=
  ∀ q, 1 ≤ q → ∀ adversary, HasHashQueryBound adversary q →
    forgeAdvantage adversary ≤ q / ((2 ^ bits : Nat) : ℝ≥0∞)

end Security

/-- The security claim. -/
abbrev SphincsSecurityStatement : Prop := Security.HasClassicalSecurityBits 127

end SphincsSecurity
