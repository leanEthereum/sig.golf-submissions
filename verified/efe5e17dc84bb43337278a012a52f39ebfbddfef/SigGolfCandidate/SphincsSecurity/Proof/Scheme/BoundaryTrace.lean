import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Base.RomQueryCharge
import SigGolfCandidate.SphincsSecurity.Proof.Fts.JointProbeMessageReserve
/-!
# The signing boundary trace

What the boundary between the adversary and the signer records of each hash call: nothing but the call
itself, and the input and answer of message-digest calls. (Split out of `Fts/SigningProposalRecord` so
that the hash-cost evaluation does not import the proposal-word machinery.)
-/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

abbrev SigningBoundaryTrace := FreeMonoid (Option (HashInput × HashOutput))

noncomputable def signingBoundaryTrace (parameter : PublicParameter) :
    (input : OracleWorld.Domain) → OracleWorld.Range input → SigningBoundaryTrace
  | .inl _, _ => 1
  | .inr input, output => FreeMonoid.of
      (if FtsProbeSimulation.MessageHashInput parameter input then some (input, output) else none)

def SigningBoundaryTrace.hashCalls (trace : SigningBoundaryTrace) : Nat := trace.toList.length

def SigningBoundaryTrace.messageCalls (trace : SigningBoundaryTrace) : List (HashInput × HashOutput) :=
  trace.toList.filterMap id

theorem signingBoundaryTrace_nonmessage (parameter : PublicParameter) (input : HashInput) (output : HashOutput)
    (hinput : ¬ FtsProbeSimulation.MessageHashInput parameter input) :
    signingBoundaryTrace parameter (.inr input) output = FreeMonoid.of none := by
  simp only [signingBoundaryTrace, if_neg hinput]

end SphincsSecurity.Concrete
