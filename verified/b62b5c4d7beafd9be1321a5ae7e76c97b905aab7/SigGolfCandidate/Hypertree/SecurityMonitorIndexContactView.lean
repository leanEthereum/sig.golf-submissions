import SigGolfCandidate.Hypertree.SecurityMonitorIndexContactState
import SigGolfCandidate.Hypertree.SecurityMonitorGraphStoppedView
import SigGolfCandidate.Hypertree.SecurityMonitorViewBounds

namespace SigGolfCandidate.Hypertree.SecurityMonitorIndexContact
open SigGolf OracleComp OracleComp.EvalDist OracleSpec Reference SecurityGraphFactor SecurityGraphPassive
  SecurityGraphMonitorProgram SecurityGraphMonitorSign SecurityGraphMonitorPublicCoupling
  SecurityMonitorView SecurityMonitorIndexState SecurityMonitorGraphView SecurityMonitorGraphState
  SecurityMonitorGraphStoppedView
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

/-- The complete adaptive stopped execution carries actual cache provenance,
including repeated signing requests and the verifier's own public H5 query. -/
theorem execute_tracked {α : Type} (factors : Factors) (view : View α)
    (remaining : Nat) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (history : History) (tracked : Tracked factors.2.1 cache history)
    (result : Result α)
    (member : some result ∈ support (execute factors view remaining exposed cache history)) :
    Tracked factors.2.1 result.residual result.history := by
  induction view generalizing remaining exposed cache history result with
  | done value =>
    simp only [execute, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
    cases member
    exact tracked
  | coin n next ih =>
    simp only [execute, mem_support_bind_iff] at member
    obtain ⟨answer, _, member⟩ := member
    exact ih answer remaining exposed cache history tracked result member
  | hash query next ih =>
    cases remaining with
    | zero =>
      simp only [execute, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
      cases member
      exact tracked
    | succ remaining =>
      rw [execute] at member
      split at member
      · simp only [support_pure, Set.mem_singleton_iff, Option.some_ne_none] at member
      · rw [mem_support_bind_iff] at member
        obtain ⟨answer, queried, member⟩ := member
        split at member
        · simp only [support_pure, Set.mem_singleton_iff, Option.some_ne_none] at member
        · exact ih answer.1 remaining _ answer.2 _
            (tracked.public_oracle _ _ query answer.1 answer.2 queried) result member
  | sign message next ih =>
    rw [execute] at member
    split at member
    · rw [mem_support_bind_iff] at member
      obtain ⟨answer, queried, member⟩ := member
      exact ih _ (remaining - 117508) _ answer.2 _
        (tracked.sign_random message answer.1 answer.2 queried) result member
    · simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
      cases member
      exact tracked

/-- Operational compiler lifting uses exact stopped-distribution equality, not
an inference from matching terminal values. -/
theorem compile_tracked {α : Type} (factors : Factors) (view : View α)
    (remaining : Nat) (exposed : QueryCache PointSpec)
    (cache : QueryCache HashSpec) (history : History)
    (ready : Ready factors history exposed cache) (tracked : Tracked factors.2.1 cache history)
    (result : Result α)
    (member : some result ∈ support (stopped factors.1 exposed
      (compile factors.2.1 factors.2.2 view remaining exposed cache history))) :
    Tracked factors.2.1 result.residual result.history := by
  apply execute_tracked factors view remaining exposed cache history tracked result
  exact (mem_support_iff_of_evalSPMF_eq
    (stopped_compile factors view remaining exposed cache history ready) (some result)).mp member

 theorem start_tracked {α : Type} (factors : Factors) (view : View α)
    (budget : Nat) (result : Result α)
    (member : some result ∈ support (stopped factors.1 ∅
      (start factors.2.1 factors.2.2 view budget))) :
    Tracked factors.2.1 result.residual result.history := by
  rw [start] at member
  split at member
  · rw [SecurityGraphMonitorSetup.setup, SecurityGraphMonitorMetadata.stopped_disclose] at member
    exact compile_tracked factors view (budget - 739) _ ∅ _ (setup_ready factors)
      (tracked_empty factors.2.1).keygen result member
  · simp only [stopped, support_pure, Set.mem_singleton_iff, Option.some.injEq] at member
    cases member
    exact tracked_empty factors.2.1

/-- The actual passive execution, on a non-contact outcome, retains the full
index provenance needed by the forgery extraction bridge. -/
theorem run_start_tracked {α : Type} (factors : Factors) (view : View α)
    (budget : Nat) (result : Outcome (Result α))
    (member : result ∈ support (run factors.1 ∅ (start factors.2.1 factors.2.2 view budget)))
    (clean : result.bad = false) : Tracked factors.2.1 result.value.residual result.value.history := by
  apply start_tracked factors view budget result.value
  apply (mem_support_iff_of_evalSPMF_eq (stopped_eq factors.1 ∅ _) (some result.value)).mpr
  rw [support_map]
  exact ⟨result, member, by simp only [keep, clean, Bool.false_eq_true, if_false]⟩

/-- info: 'SigGolfCandidate.Hypertree.SecurityMonitorIndexContact.run_start_tracked' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms run_start_tracked
end SigGolfCandidate.Hypertree.SecurityMonitorIndexContact
