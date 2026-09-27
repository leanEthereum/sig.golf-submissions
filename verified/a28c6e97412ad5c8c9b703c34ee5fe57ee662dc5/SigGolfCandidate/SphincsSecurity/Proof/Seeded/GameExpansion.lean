import SigGolfCandidate.SphincsSecurity.Proof.Seeded.GameErasure
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Presampling
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.TableSampling

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem run'_lift_hash_bind {A B : Type} (computation : OracleComp HashSpec A)
    (next : A → OracleComp OracleWorld B) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld A) >>= next)).run' cache =
      ((simulateQ randomOracle computation).run cache >>= fun result =>
        (simulateQ romImpl (next result.1)).run' result.2) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld A) =
      simulateQ randomOracle computation :=
    QueryImpl.simulateQ_add_liftM_right _ _ computation
  rw [h, map_bind]
  rfl

theorem run'_lift_sample_bind {A B : Type} (computation : ProbComp A)
    (next : A → OracleComp OracleWorld B) (cache : QueryCache HashSpec) :
    (simulateQ romImpl ((liftM computation : OracleComp OracleWorld A) >>= next)).run' cache =
      (computation >>= fun result => (simulateQ romImpl (next result)).run' cache) := by
  rw [simulateQ_bind, StateT.run'_eq, StateT.run_bind]
  have h : simulateQ romImpl (liftM computation : OracleComp OracleWorld A) =
      simulateQ (unifFwdImpl HashSpec) computation :=
    QueryImpl.simulateQ_add_liftM_left _ _ computation
  rw [h, unifFwdImpl.simulateQ_run]
  simp only [bind_map_left, map_bind]
  rfl

end SphincsSecurity.Seeded
