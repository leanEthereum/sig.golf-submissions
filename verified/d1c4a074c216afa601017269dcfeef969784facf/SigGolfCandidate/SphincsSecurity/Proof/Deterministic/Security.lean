import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Transfer
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Security

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

theorem scheme_has_127_bits_of_classical_security :
    HasClassicalSecurityBits scheme 127 :=
  scheme_security_of_independent Concrete.security127

end SphincsSecurity.Seeded
