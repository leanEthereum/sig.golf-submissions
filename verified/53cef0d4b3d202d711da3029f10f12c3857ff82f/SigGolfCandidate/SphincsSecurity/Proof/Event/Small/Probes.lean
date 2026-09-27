import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.CrudeCap
import SigGolfCandidate.SphincsSecurity.Proof.Forced.FtsGuessBudget
/-!
# Probes of the capped adversary

In the forced-guess world a probe is a hash query of the adversary or of the verifier; signing
requests make none. The capped adversary makes at most `budget - keygenHashCost` hash queries and the
verifier at most `verifyHashBound < keygenHashCost`, so every run makes at most `budget` probes.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem weightBound_writer_simulate {α : Type}
    (impl : QueryImpl (OracleWorld + SigningSpec) (WriterT (QueryLog SigningSpec) (OracleComp (OracleWorld + SigningSpec))))
    (hstep : ∀ input, WeightBound (impl input).run (visWeight input))
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : Nat) (h : WeightBound computation budget) :
    WeightBound (simulateQ impl computation).run budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => exact weightBound_pure _ _
  | query_bind input next ih =>
      rw [weightBound_query_bind_iff] at h
      rw [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind']
      refine (weightBound_bind (hstep input) fun step =>
        weightBound_map _ (ih step.1 (budget - visWeight input) (h.2 step.1))).mono ?_
      have := h.1
      omega

theorem weightBound_logged {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : Nat)
    (h : WeightBound computation budget) : WeightBound (OtsPrefix.logged computation) budget := by
  apply weightBound_writer_simulate _ _ computation budget h
  intro input
  change WeightBound (liftM ((OracleWorld + SigningSpec).query input) >>= fun answer =>
    (pure (answer, signingLogFragment input answer) : OracleComp (OracleWorld + SigningSpec) _)) (visWeight input)
  exact (weightBound_query_bind_iff _ _ _).mpr ⟨le_rfl, fun _ => weightBound_pure _ _⟩


section Forced

open FtsGuessHash
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (State Environment fixedRun runWith)

variable {Memory : Type}

private theorem map_nonzero' {First Result : Type} (function : First → Result) (law : SPMF First) (result : Result) :
    (function <$> law) result ≠ 0 ↔ ∃ first, law first ≠ 0 ∧ result = function first := by
  simp only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not]

theorem fixed_adversaryImpl_probes_weight (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (labels : CanonicalGraphLabels) {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (budget : Nat) (h : WeightBound computation budget)
    (state : State Coordinate Digest Memory)
    (result : ((Result × SigningBoundaryTrace) × OtsContactTrace.Trace) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets ((simulateQ (adversaryImpl parameter labels) computation).run).run state result ≠ 0) :
    result.2.probes ≤ state.probes + budget := by
  induction computation using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
      simp only [simulateQ_pure, WriterT.run_pure, fixedRun, SecretGuessObservation.runWith_pure,
        ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact Nat.le_add_right _ _
  | query_bind input next ih =>
      rw [weightBound_query_bind_iff] at h
      simp only [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind, WriterT.run_map,
        fixedRun, runWith_bind, runWith_map, RetainedObservation.bind_nonzero, map_nonzero'] at hr
      obtain ⟨middle, hm, outer, ⟨tail, ht, rfl⟩, rfl⟩ := hr
      have htail := ih middle.1.1.1 (budget - visWeight input) (h.2 _) middle.2 tail ht
      have hhead : middle.2.probes ≤ state.probes + visWeight input := by
        cases input with
        | inl input =>
            simp only [adversaryImpl, WriterT.run_mk, runWith_map, map_nonzero'] at hm
            obtain ⟨answer, ha, rfl⟩ := hm
            have hp := fixed_worldProgram_probes environment secrets parameter labels input state answer ha
            rw [signingBoundaryTrace_hashCalls_eq] at hp
            cases input <;> simpa only [visWeight, Bool.false_eq_true, if_false, if_true] using hp
        | inr message =>
            simp only [adversaryImpl, WriterT.run_mk, runWith_map, map_nonzero'] at hm
            obtain ⟨record, hrec, rfl⟩ := hm
            rw [fixed_signingProgram_probes environment secrets message state record hrec]
            exact Nat.le_add_right _ _
      have := h.1
      change tail.2.probes ≤ state.probes + budget
      omega

theorem fixed_adversaryRun_probes_weight (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (labels : CanonicalGraphLabels) {Result : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (budget : Nat) (h : WeightBound computation budget)
    (state : State Coordinate Digest Memory)
    (result : (((Result × QueryLog SigningSpec) × SigningBoundaryTrace) × OtsContactTrace.Trace) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (adversaryRun parameter labels computation) state result ≠ 0) :
    result.2.probes ≤ state.probes + budget :=
  fixed_adversaryImpl_probes_weight environment secrets parameter labels _ budget (weightBound_logged computation budget h)
    state result hr



private theorem traced_map' {First Result : Type} (function : First → Result) (computation : OracleComp OracleWorld First) :
    QueryPause.traced hashObservationTrace (function <$> computation) =
      (fun result => (function result.1, result.2)) <$> QueryPause.traced hashObservationTrace computation := by
  simp only [QueryPause.traced, simulateQ_map, WriterT.run_map]

theorem fixed_tracedBoundary_probes_bound (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (labels : CanonicalGraphLabels) {Result : Type}
    (computation : OracleComp OracleWorld Result) (budget : Nat)
    (hbudget : computation.IsQueryBoundP (fun input : OracleWorld.Domain => input matches .inr _) budget)
    (state : State Coordinate Digest Memory)
    (result : ((Result × SigningBoundaryTrace) × OtsContactTrace.Trace) × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (simulateQ (worldProgram parameter labels)
      (QueryPause.traced hashObservationTrace (boundaryComputation parameter computation))) state result ≠ 0) :
    result.2.probes ≤ state.probes + budget := by
  induction computation using OracleComp.inductionOn generalizing budget state result with
  | pure value =>
      simp only [boundaryComputation, simulateQ_pure, WriterT.run_pure, QueryPause.traced_pure,
        fixedRun, SecretGuessObservation.runWith_pure, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
      subst result
      exact Nat.le_add_right _ _
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbudget
      simp only [ResidualByteFrontend.boundaryComputation_query_bind, QueryPause.traced_query_bind, traced_map',
        simulateQ_bind, simulateQ_spec_query, simulateQ_map, fixedRun, runWith_bind, runWith_map,
        RetainedObservation.bind_nonzero, map_nonzero'] at hr
      obtain ⟨middle, hm, outer, ⟨tail, ht, rfl⟩, rfl⟩ := hr
      have hhead := fixed_worldProgram_probes environment secrets parameter labels input state middle hm
      rw [signingBoundaryTrace_hashCalls_eq] at hhead
      have htail := ih middle.1 _ (hbudget.2 middle.1) middle.2 tail ht
      change tail.2.probes ≤ state.probes + budget
      cases input with
      | inl input =>
          simp only [Bool.false_eq_true, if_false, not_false_eq_true, true_or, Nat.add_zero] at hhead hbudget htail ⊢
          omega
      | inr input =>
          simp only [if_true, not_true_eq_false, false_or] at hhead hbudget htail ⊢
          omega

theorem isQueryBoundP_liftM_of_evenBound {α : Type} (computation : OracleComp HashSpec α) (budget : Nat)
    (h : EvenBound computation budget) :
    (liftM computation : OracleComp OracleWorld α).IsQueryBoundP (fun input : OracleWorld.Domain => input matches .inr _) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => exact isQueryBoundP_pure _ _ _
  | query_bind input next ih =>
      rw [evenBound_query_bind_iff] at h
      rw [liftM_bind]
      change (liftM (OracleWorld.query (.inr input)) >>= fun answer => liftM (next answer) : OracleComp OracleWorld α).IsQueryBoundP _ budget
      rw [isQueryBoundP_query_bind_iff]
      exact ⟨Or.inr h.1.2, fun answer => by simpa only [if_true] using ih answer _ (h.2 answer)⟩

theorem fixed_completedRun_probes_visAdversary (environment : Environment Auxiliary Coordinate Digest Memory)
    (secrets : Coordinate → Digest) (parameter : PublicParameter) (root : Digest) (labels : CanonicalGraphLabels)
    (adversary : Adversary) (budget : Nat) (hbudget : keygenHashCost + 1 ≤ budget)
    (state : State Coordinate Digest Memory) (result : Completed × State Coordinate Digest Memory)
    (hr : fixedRun environment secrets (completedRun parameter root labels (visAdversary adversary budget)) state result ≠ 0) :
    result.2.probes ≤ state.probes + budget := by
  simp only [completedRun, fixedRun, runWith_bind, SecretGuessObservation.runWith_pure,
    RetainedObservation.bind_nonzero, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hr
  obtain ⟨before, hb, checked, hc, rfl⟩ := hr
  have hbefore := fixed_adversaryRun_probes_weight environment secrets parameter labels _ _
    (visAdversary_weightBound adversary budget ⟨root, parameter⟩ hbudget) state before hb
  have hchecked := fixed_tracedBoundary_probes_bound environment secrets parameter labels _ verifyHashBound
    (isQueryBoundP_liftM_of_evenBound _ _ (evenBound_verify _ _ _)) before.2 checked hc
  have hK := verifyHashBound_lt_keygen
  change checked.2.probes ≤ state.probes + budget
  omega



theorem probeBudget_visAdversary (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : keygenHashCost + 1 ≤ budget) : ProbeBudget dummy (visAdversary adversary budget) budget := by
  intro parameter _ otsSecret labels auxiliary _ result hr
  rw [← SecretGuessObservation.run_erasure _ _ _ (fun _ => Finset.univ_nonempty), RetainedObservation.bind_nonzero] at hr
  obtain ⟨secrets, _, hr⟩ := hr
  have h := fixed_completedRun_probes_visAdversary _ secrets parameter (canonicalGraphRoot labels) labels adversary budget hbudget
    (SecretGuessObservation.initialState PUnit.unit) result hr
  simpa only [SecretGuessObservation.initialState, Nat.zero_add] using h

end Forced

end SphincsSecurity.Concrete.EventSmall
