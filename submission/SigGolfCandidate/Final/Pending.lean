import SigGolfCandidate.Submission
import SigGolfCandidate.Final.Params
import SigGolfCandidate.Ref
import SigGolfCandidate.Sign.Sim
import SigGolfCandidate.Bridge.Setup

/-!
# Pending component statements

The certificate (`SigGolfCandidate.Final.certificate_of`) is proved from the statements below.
Each is a `def … : Prop`; the agents working on sign, verify and abstract security must prove them
(as `theorem`s), after which `Solution.lean` plugs them in.

Everything else (the expand refinement, the reference/abstract equivalence, the bridge,
compression bounds, per-seed completeness) is already proved.

| statement | owner | used for |
|---|---|---|
| `KeygenRefinementStatement` | keygen | completeness, compression bounds, security |
| `KeygenTerminationStatement` | keygen | termination |
| `SignRefinementStatement` | sign | completeness, compression bounds, security |
| `SignTerminationStatement` | sign | termination |
| `VerifyRefinementStatement` | verify | completeness, security |
| `VerifyTerminationStatement` | verify | termination |
| `VerifyCyclesStatement` | verify | verification bound `claimedC` |
| `EventSecurityStatement` | abstract security | security |

Plugging in: `Discharge.lean` proves each statement from the component theorems and defines
`certificate := certificate_of ⟨…⟩` (field order of `Pending`).

Shapes: `KeygenRefinementStatement` is `Sign.Sim.run_eq`-style with `F = some` (the program outputs
the reference's `(pk, cache)`); `SignRefinementStatement` is `Sign.Sim.run_eq` with `F = id`; `SignTerminationStatement`
follows from `Sign.Sim.runWith` (`W + 1 < CYCLE_LIMIT`); `VerifyRefinementStatement` is exactly
`Equiv.Refinements.verify`; `EventSecurityStatement` is `Bridge.EventSecurity` unfolded (so any
proof of `Bridge.EventSecurity` is one of it).
-/

namespace SigGolfCandidate.Final
open SigGolf

/-- **Keygen refinement** (keygen agent). For every secret key, the keygen program outputs the
reference's `(pk, cache) = Ref.keygenRef sk`, with its joint call / compression counter. -/
def KeygenRefinementStatement : Prop :=
  ∀ sk : SecretKey,
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .keygen sk =
      (fun p => (some p.1, p.2.1, p.2.2)) <$> Sign.countBoth (Ref.keygenRef sk)

/-- **Keygen termination** (keygen agent). Under every fixed oracle, keygen finishes within the
cycle limit. -/
def KeygenTerminationStatement : Prop :=
  ∀ (hash : Hash) (sk : SecretKey),
    (submission.runWith hash .keygen sk).finished = true ∧
      (submission.runWith hash .keygen sk).cycles < CYCLE_LIMIT

/-- **Sign refinement** (sign agent). For every input, the sign program's value, hash-call count
and compression count are distributed as the reference signer `Ref.signRef sk cache m` with its
joint call / compression counter (`Sign.countBoth`). This is `Sign.Sim.run_eq` with `F = id`. The
cache is arbitrary (the reference checks its MAC first). -/
def SignRefinementStatement : Prop :=
  ∀ (sk : SecretKey) (cache : Cache) (m : Message),
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$>
        submission.run .sign (sk, cache, m) =
      Sign.countBoth (Ref.signRef sk cache m)

/-- **Sign termination** (sign agent). Under every fixed oracle and every input, the sign program
finishes within the cycle limit (`Sign.Sim.runWith`). -/
def SignTerminationStatement : Prop :=
  ∀ (hash : Hash) (sk : SecretKey) (cache : Cache) (m : Message),
    (submission.runWith hash .sign (sk, cache, m)).finished = true ∧
      (submission.runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT

/-- **Verify refinement** (verify agent). For every input (arbitrary public key and witness), the
verify program accepts exactly when the reference verifier `Ref.verifyRef m pk w` returns `true`,
with the same hash calls. This is `Equiv.Refinements.verify`. -/
def VerifyRefinementStatement : Prop :=
  ∀ (m : Message) (pk : PublicKey) (w : Bytes submission.sizes.witness),
    (fun r => (r.value, r.hashCalls)) <$> submission.run .verify (m, pk, w) =
      (fun p => (if p.1 then some () else none, p.2)) <$> Ref.countCalls (Ref.verifyRef m pk w)

/-- **Verify termination** (verify agent). Under every fixed oracle and every input, the verify
program finishes within the cycle limit. -/
def VerifyTerminationStatement : Prop :=
  ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes submission.sizes.witness),
    (submission.runWith hash .verify (m, pk, w)).finished = true ∧
      (submission.runWith hash .verify (m, pk, w)).cycles < CYCLE_LIMIT

/-- **Verify cycles** (verify agent). Under every fixed oracle, every *accepting* verify run takes
at most `verifyCycleBound` cycles (`claimedC = verifyCycleBound + witnessCharge`). -/
def VerifyCyclesStatement : Prop :=
  ∀ (hash : Hash) (m : Message) (pk : PublicKey) (w : Bytes submission.sizes.witness),
    (submission.runWith hash .verify (m, pk, w)).value.isSome = true →
      (submission.runWith hash .verify (m, pk, w)).cycles ≤ verifyCycleBound

/-- **(A) Abstract event-form security** (security agent): every adversary against the abstract
SUF-CMA experiment wins *and* uses at most `q` hash calls with probability at most `q / 2^127`.
This is `Bridge.EventSecurity`, unfolded. -/
def EventSecurityStatement : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ adversary : SphincsSecurity.Security.Adversary,
    Pr[fun result => result.1 = true ∧ result.2 ≤ q |
      SphincsSecurity.Security.experiment adversary] ≤ (q : ENNReal) / 2 ^ 127

theorem eventSecurity_of (h : EventSecurityStatement) : Bridge.EventSecurity := h

/-- All pending statements. -/
structure Pending : Prop where
  keygenRefinement : KeygenRefinementStatement
  keygenTermination : KeygenTerminationStatement
  signRefinement : SignRefinementStatement
  signTermination : SignTerminationStatement
  verifyRefinement : VerifyRefinementStatement
  verifyTermination : VerifyTerminationStatement
  verifyCycles : VerifyCyclesStatement
  eventSecurity : EventSecurityStatement

end SigGolfCandidate.Final
