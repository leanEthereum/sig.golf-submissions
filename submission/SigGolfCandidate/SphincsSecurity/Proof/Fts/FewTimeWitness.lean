import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Replay
/-!
# Finite witnesses for the few-time leak

A leak chooses one successful signing entry for each of the fourteen opened trees.  Keeping the
range of that choice as a finset exposes the number of distinct signatures used by the opening.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

abbrev SigningEntry := (request : Message) × SigningSpec.Range request

end SphincsSecurity.Concrete
