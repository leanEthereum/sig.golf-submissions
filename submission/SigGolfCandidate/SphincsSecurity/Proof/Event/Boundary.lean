import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.FrontierRandomOracle
import SigGolfCandidate.SphincsSecurity.Proof.Reference.BoundaryHashCost
/-!
# The budget event at the boundary game

The event form of the security bound is about the joint law of the verdict and the total number of
hash calls. `boundaryGameCore` records that count as the length of its trace, so the event carries
over to it exactly.
-/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The probability of winning with at most `q` hash calls in the whole experiment. -/
noncomputable def forgeEventAdvantage {Key : Type} (scheme : Scheme Key) (adversary : Adversary) (q : Nat) : ℝ≥0∞ :=
  Pr[fun result => result.1 = true ∧ result.2 ≤ q |
    (simulateQ countedRomImpl (gameCore scheme adversary)).run.run' ∅]

theorem forgeAdvantage_le_forgeEventAdvantage {Key : Type} (scheme : Scheme Key) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) :
    forgeAdvantage scheme adversary ≤ forgeEventAdvantage scheme adversary q := by
  have hforget := congrArg (fun computation : OracleComp OracleWorld Bool => (simulateQ romImpl computation).run' ∅)
    (QueryCap.counted_forget (fun input : OracleWorld.Domain => input matches .inr _) (gameCore scheme adversary))
  simp only [simulateQ_map, StateT.run'_map'] at hforget
  rw [forgeAdvantage, ← hforget, ← probEvent_eq_eq_probOutput, probEvent_map, forgeEventAdvantage,
    ← simulateQ_countHashQueries]
  apply probEvent_mono
  intro result hresult hwin
  refine ⟨hwin, hbound result ?_⟩
  change result ∈ support ((simulateQ romImpl (countHashQueries (gameCore scheme adversary))).run' ∅) at hresult
  rwa [simulateQ_countHashQueries] at hresult

theorem romRun_countHashQueries_lift_bind {α β : Type} (sample : ProbComp α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (countHashQueries ((liftM sample : OracleComp OracleWorld α) >>= next))).run' cache =
      sample >>= fun value => (simulateQ romImpl (countHashQueries (next value))).run' cache := by
  rw [countHashQueries_bind, countHashQueries_lift_prob, bind_map_left]
  simp only [zero_add, Prod.mk.eta, bind_pure]
  exact simulateQ_romImpl_liftM_bind_run' sample _ cache

theorem romRun_boundaryComputation_count {α : Type} (parameter : PublicParameter)
    (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (fun result => (result.1, result.2.hashCalls)) <$>
        (simulateQ romImpl (boundaryComputation parameter computation)).run' cache =
      (simulateQ romImpl (countHashQueries computation)).run' cache := by
  rw [← boundaryRun_fst_eq_boundaryComputation, StateT.run'_eq, ← boundaryRun_count, Functor.map_map,
    Functor.map_map]

theorem countedGame_eq_boundaryGameCore (adversary : Adversary) :
    (simulateQ countedRomImpl (gameCore scheme adversary)).run.run' ∅ =
      (fun result => (result.1, result.2.hashCalls)) <$> (simulateQ romImpl (boundaryGameCore adversary)).run' ∅ := by
  rw [← simulateQ_countHashQueries, gameCore_eq_secrets, boundaryGameCore, romRun_countHashQueries_lift_bind,
    simulateQ_romImpl_liftM_bind_run', map_bind]
  refine bind_congr fun parameter => ?_
  rw [romRun_countHashQueries_lift_bind, simulateQ_romImpl_liftM_bind_run', map_bind]
  refine bind_congr fun otsSecret => ?_
  rw [romRun_countHashQueries_lift_bind, simulateQ_romImpl_liftM_bind_run', map_bind]
  refine bind_congr fun ftsSecret => ?_
  exact (romRun_boundaryComputation_count parameter _ ∅).symm

theorem forgeEventAdvantage_eq_boundary (adversary : Adversary) (q : Nat) :
    forgeEventAdvantage scheme adversary q =
      Pr[fun result => result.1 = true ∧ result.2.hashCalls ≤ q |
        (simulateQ romImpl (boundaryGameCore adversary)).run' ∅] := by
  rw [forgeEventAdvantage, countedGame_eq_boundaryGameCore, probEvent_map]
  rfl

end SphincsSecurity.Concrete
