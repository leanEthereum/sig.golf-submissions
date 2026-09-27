import SigGolfCandidate.SphincsSecurity.Proof.Adversary.Embedding
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.Transfer

open OracleComp OracleSpec ENNReal
namespace SphincsSecurity.Security

set_option backward.isDefEq.respectTransparency false

/-- The embedding preserves both the winning event and the complete hash-query budget, so the
statement follows from the independent scheme's bound. -/
theorem security127_of_independent (hideal : IndependentSecurityStatement) :
    HasClassicalSecurityBits 127 := by
  intro q hq adversary hbound
  rw [← advantage_embed]
  apply Seeded.scheme_security_of_independent hideal q hq
  change ∀ result ∈ support ((simulateQ countedRomImpl
    (SphincsSecurity.gameCore Seeded.scheme (embed adversary))).run.run' ∅), result.2 ≤ q
  rw [experiment_embed]
  exact hbound

end SphincsSecurity.Security
