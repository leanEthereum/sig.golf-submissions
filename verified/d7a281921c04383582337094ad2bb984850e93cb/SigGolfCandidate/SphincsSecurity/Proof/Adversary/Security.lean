import SigGolfCandidate.SphincsSecurity.Proof.Adversary.Transfer
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Security

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity.Security

/-- The embedding preserves both the winning event and the complete hash-query budget. -/
theorem security127 : HasClassicalSecurityBits 127 :=
  security127_of_independent Concrete.security127

end SphincsSecurity.Security
