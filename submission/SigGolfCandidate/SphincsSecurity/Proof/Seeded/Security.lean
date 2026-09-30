import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Transfer
import SigGolfCandidate.SphincsSecurity.Proof

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

theorem randomizedScheme_has_127_bits_of_classical_security : HasClassicalSecurityBits randomizedScheme 127 :=
  randomizedScheme_security_of_independent Concrete.security127

end SphincsSecurity.Seeded
