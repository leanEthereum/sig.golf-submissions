import SigGolfCandidate.SphincsSecurity.Scheme

/-!
# SPHINCS: correctness and completeness

`Statement.lean` states unforgeability. This file states what makes the scheme usable: a signature the
signer produces verifies (`doc/sphincs/main.tex` §sec:ver), and the signer almost never fails to produce
one (§sec:completeness), for a random master seed and for every fixed one. The theorems are in `SphincsSecurity.lean`, the proofs under `Completeness/`.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

/-- **Correctness**, for every hash function, not only a random oracle: if the signer produces a
signature for a generated key, the verifier accepts it. `evalWithAnswerFn hash` runs a computation with
every hash query answered by `hash`. -/
abbrev SphincsCorrectnessStatement : Prop :=
  ∀ (hash : QueryImpl HashSpec Id) (seed : MasterSeed) (publicKey : PublicKey)
    (secretKey : Seeded.SecretKey) (message : Message) (signature : Signature),
    evalWithAnswerFn hash (Seeded.keygenFromSeed seed) = (publicKey, secretKey) →
    evalWithAnswerFn hash (Seeded.sign secretKey message : OracleComp HashSpec (Option Signature))
      = some signature →
    evalWithAnswerFn hash (Concrete.verify publicKey message signature : OracleComp HashSpec Bool)
      = true

namespace Completeness

/-- The honest run: sample the master seed, generate a key, sign, and verify. -/
noncomputable def gameCore (message : Message) : OracleComp OracleWorld Bool := do
  let seed ← liftM sampleMasterSeed
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let some signature ← liftM (Seeded.sign sk message : OracleComp HashSpec (Option Signature))
    | return false
  liftM (Concrete.verify pk message signature : OracleComp HashSpec Bool)

/-- The security game's random oracle, without its query counter. -/
noncomputable def romImpl : QueryImpl OracleWorld (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + (randomOracle : QueryImpl HashSpec (StateT (QueryCache HashSpec) ProbComp))

noncomputable def experiment (message : Message) : ProbComp Bool :=
  (simulateQ romImpl (gameCore message)).run' ∅

/-- The honest run from a fixed master seed: generate the key, sign, and verify. -/
noncomputable def seededGameCore (seed : MasterSeed) (message : Message) :
    OracleComp OracleWorld Bool := do
  let (pk, sk) ← liftM (Seeded.keygenFromSeed seed)
  let some signature ← liftM (Seeded.sign sk message : OracleComp HashSpec (Option Signature))
    | return false
  liftM (Concrete.verify pk message signature : OracleComp HashSpec Bool)

noncomputable def seededExperiment (seed : MasterSeed) (message : Message) : ProbComp Bool :=
  (simulateQ romImpl (seededGameCore seed message)).run' ∅

end Completeness

/-- **Completeness**, in the random-oracle model: the sum over all messages of the probability that
the honest run fails, because the signer returned no signature or the verifier rejected it, is at
most `2⁻²⁵⁶`. By a union bound, this also bounds the probability that any message fails under one
key and random oracle. -/
abbrev SphincsCompletenessStatement : Prop :=
  ∑' message : Message, Pr[= false | Completeness.experiment message]
    ≤ ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹

/-- **Per-seed completeness**, in the random-oracle model: for every master seed, not only on average
over a random one, the sum over all messages of the probability that the honest run from that seed
fails is at most `2⁻²⁵⁶`. The only randomness is the random oracle. -/
abbrev SphincsSeededCompletenessStatement : Prop :=
  ∀ seed : MasterSeed, ∑' message : Message, Pr[= false | Completeness.seededExperiment seed message]
    ≤ ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹

end SphincsSecurity
