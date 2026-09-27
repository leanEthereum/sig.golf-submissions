import SigGolfCandidate.SphincsSecurity.Completeness
import SigGolfCandidate.Equiv.Honest

/-!
# The abstract honest game over the hash oracle alone

`game seed m` is `Completeness.seededGameCore seed m` without the lift into `OracleWorld`:
generate the key from the seed, sign, verify. `seededExperiment_eq` runs it against the lazy random
oracle; `hq_game`: all its queries are `Honest`.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Final
open SphincsSecurity

/-- The honest abstract run from a fixed seed, over the hash oracle alone. -/
def game (seed : MasterSeed) (message : Message) : OracleComp SphincsSecurity.HashSpec Bool := do
  let (pk, sk) ← Seeded.keygenFromSeed seed
  let some signature ← (Seeded.sign sk message : OracleComp SphincsSecurity.HashSpec (Option Signature))
    | return false
  (Concrete.verify pk message signature : OracleComp SphincsSecurity.HashSpec Bool)

theorem seededGameCore_eq (seed : MasterSeed) (message : Message) :
    Completeness.seededGameCore seed message =
      (liftM (game seed message) : OracleComp OracleWorld Bool) := by
  unfold Completeness.seededGameCore game
  simp only [← OracleComp.liftComp_eq_liftM, OracleComp.liftComp_bind]
  refine bind_congr fun kp => ?_
  rcases kp with ⟨pk, sk⟩
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · simp
  · rfl

theorem seededExperiment_eq (seed : MasterSeed) (message : Message) :
    Completeness.seededExperiment seed message =
      (simulateQ (randomOracle : QueryImpl SphincsSecurity.HashSpec
        (StateT (QueryCache SphincsSecurity.HashSpec) ProbComp)) (game seed message)).run' ∅ := by
  unfold Completeness.seededExperiment Completeness.romImpl
  rw [seededGameCore_eq, QueryImpl.simulateQ_add_liftM_right]

theorem hq_game (seed : MasterSeed) (message : Message) : Equiv.HQ (game seed message) := by
  unfold game
  refine Equiv.hq_bind (Equiv.hq_keygen seed) fun kp => ?_
  refine Equiv.hq_bind (Equiv.hq_sign _ _) fun s => ?_
  rcases s with _ | σ
  · exact Equiv.hq_pure _
  · exact Equiv.hq_verify _ _ _

end SigGolfCandidate.Final
