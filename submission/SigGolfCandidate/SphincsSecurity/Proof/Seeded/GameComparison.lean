import SigGolfCandidate.SphincsSecurity.Proof.Seeded.GameExpansion

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem gameCore_independent_eq (adversary : Adversary) :
    gameCore Concrete.scheme adversary = (do
      let secret ← liftM sampleSecrets
      Concrete.gameAfterSecrets adversary 0 secret.1 secret.2) := by
  rw [Concrete.gameCore_eq_secrets, sampleParameter_eq_zero]
  simp only [sampleSecrets, liftM_bind, liftM_pure, bind_assoc, pure_bind]

end SphincsSecurity.Seeded
