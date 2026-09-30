import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.ChainGlue
/-!
# Reading the marker from a trace

The marker is the last message call of odd length in a trace: every other message-class input the
signer or the verifier hashes has an even payload. Its payload length `2 * count + 1` gives back the
number of nonmessage hash queries the capped adversary made.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec

def oddEntry (entry : HashInput × HashOutput) : Bool := entry.1.length % 2 == 1

/-- The count recorded by the last odd-length message call of the trace. -/
def markerValue (trace : SigningBoundaryTrace) : Nat :=
  match (trace.messageCalls.filter oddEntry).getLast? with
  | some entry => (entry.1.length - 33) / 2
  | none => 0

theorem markerValue_mul_even (first second : SigningBoundaryTrace)
    (hsecond : ∀ entry ∈ second.messageCalls, entry.1.length % 2 = 0) :
    markerValue (first * second) = markerValue first := by
  have hfilter : second.messageCalls.filter oddEntry = [] := by
    rw [List.filter_eq_nil_iff]
    intro entry hentry
    simp [oddEntry, hsecond entry hentry]
  simp only [markerValue, SigningBoundaryTrace.messageCalls_mul, List.filter_append, hfilter, List.append_nil]

theorem markerValue_pow_none_mul (cost : Nat) (trace : SigningBoundaryTrace) :
    markerValue ((FreeMonoid.of none) ^ cost * trace) = markerValue trace := by
  simp only [markerValue, SigningBoundaryTrace.messageCalls_mul, SigningBoundaryTrace.messageCalls_pow_none,
    List.nil_append]

theorem length_markerInput (parameter : PublicParameter) (count : Nat) :
    (markerInput parameter count).length = 2 * count + 33 := by
  rw [markerInput, length_tweakableHashInput, List.length_replicate]
  omega

theorem messageHashInput_markerInput (parameter : PublicParameter) (count : Nat) :
    FtsProbeSimulation.MessageHashInput parameter (markerInput parameter count) :=
  ⟨_, rfl⟩

theorem markerValue_mul_marker (trace : SigningBoundaryTrace) (parameter : PublicParameter) (count : Nat)
    (answer : HashOutput) :
    markerValue (trace * signingBoundaryTrace parameter (.inr (markerInput parameter count)) answer) = count := by
  have hmsg : (signingBoundaryTrace parameter (.inr (markerInput parameter count)) answer).messageCalls =
      [(markerInput parameter count, answer)] := by
    simp only [signingBoundaryTrace, if_pos (messageHashInput_markerInput parameter count),
      SigningBoundaryTrace.messageCalls, FreeMonoid.toList_of, List.filterMap_cons, List.filterMap_nil, id]
  have hodd : oddEntry (markerInput parameter count, answer) = true := by
    simp only [oddEntry, length_markerInput, beq_iff_eq]
    omega
  simp only [markerValue, SigningBoundaryTrace.messageCalls_mul, hmsg, List.filter_append, List.filter_cons, hodd,
    if_true, List.filter_nil, List.getLast?_append, List.getLast?_singleton, Option.some_or, length_markerInput]
  omega

theorem isMessageInput_iff (parameter : PublicParameter) (input : HashInput) :
    isMessageInput parameter input = true ↔ FtsProbeSimulation.MessageHashInput parameter input := by
  rw [isMessageInput, List.isPrefixOf_iff_prefix]
  constructor
  · rintro ⟨payload, hpayload⟩
    exact ⟨payload, by rw [← hpayload, tweakableHashInput, messagePrefix, List.append_assoc]⟩
  · rintro ⟨payload, rfl⟩
    exact ⟨payload, by rw [tweakableHashInput, messagePrefix, List.append_assoc]⟩


/-! ### The marker in the causal frontier program -/

section Causal

variable (parameter : PublicParameter) (root : Digest) (external : QueryImpl HashSpec Id)
  (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)

private theorem logged_query_bind' {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) :
    OtsPrefix.logged (liftM ((OracleWorld + SigningSpec).query input) >>= next) =
      liftM ((OracleWorld + SigningSpec).query input) >>= fun answer =>
        (fun tail => (tail.1, signingLogFragment input answer ++ tail.2)) <$> OtsPrefix.logged (next answer) := by
  simp only [OtsPrefix.logged, OtsProbeSimulation.simulateQ_withTraceAppend_run_eq_signingTraceComputation,
    simulateQ_id', OtsProbeSimulation.signingTraceComputation_query_bind]

theorem causalAdversaryRun_pure {Result : Type} (value : Result) :
    CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier (pure value) = pure ((value, []), 1) := by
  simp only [CausalFrontierProgram.adversaryRun, OtsPrefix.logged, simulateQ_pure, WriterT.run_pure]
  rfl

theorem causalAdversaryRun_query_bind {Result : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) Result) :
    CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier
      (liftM ((OracleWorld + SigningSpec).query input) >>= next) = (do
      let head ← (CausalFrontierProgram.adversaryImpl parameter root external ftsSecret words frontier input).run
      let tail ← CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier (next head.1)
      pure ((tail.1.1, signingLogFragment input head.1 ++ tail.1.2), head.2 * tail.2)) := by
  simp only [CausalFrontierProgram.adversaryRun, logged_query_bind', simulateQ_bind, simulateQ_spec_query, simulateQ_map,
    WriterT.run_bind, WriterT.run_map, Functor.map_map, bind_pure_comp]

theorem causalAdversaryRun_map {Result Next : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (g : Result → Next) :
    CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier (g <$> computation) =
      (fun result => ((g result.1.1, result.1.2), result.2)) <$>
        CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier computation := by
  simp only [CausalFrontierProgram.adversaryRun, OtsPrefix.logged, simulateQ_map, WriterT.run_map']
  rfl

theorem causalAdversaryImpl_world_run (world : OracleWorld.Domain) :
    (CausalFrontierProgram.adversaryImpl parameter root external ftsSecret words frontier (.inl world)).run =
      (fun answer => (answer, signingBoundaryTrace parameter world answer)) <$>
        (liftM (OracleWorld.query world) : OracleComp OracleWorld _) := by
  simp [CausalFrontierProgram.adversaryImpl, QueryImpl.withTrace_apply, WriterT.run_bind, WriterT.run_tell]

theorem causalAdversaryImpl_world_count (world : OracleWorld.Domain) (head : _)
    (hhead : head ∈ support (QueryCap.counted (CausalFrontierProgram.NonmessageHash parameter)
      (CausalFrontierProgram.adversaryImpl parameter root external ftsSecret words frontier (.inl world)).run)) :
    head.2 = if NonmessageQuery parameter (.inl world) then 1 else 0 := by
  rw [causalAdversaryImpl_world_run, QueryCap.counted_map, QueryCap.counted_query, support_map, support_map] at hhead
  obtain ⟨_, ⟨answer, _, rfl⟩, rfl⟩ := hhead
  cases world with
  | inl sample => simp [CausalFrontierProgram.NonmessageHash, NonmessageQuery]
  | inr bytes =>
      simp only [CausalFrontierProgram.NonmessageHash, NonmessageQuery]
      have h := isMessageInput_iff parameter bytes
      by_cases hm : FtsProbeSimulation.MessageHashInput parameter bytes
      · have hb : isMessageInput parameter bytes = true := h.mpr hm
        simp [hm, hb]
      · have hb : isMessageInput parameter bytes = false := by
          cases hb' : isMessageInput parameter bytes
          · rfl
          · exact absurd (h.mp hb') hm
        simp [hm, hb]

theorem causalAdversaryImpl_sign_count (message : Message) (head : _)
    (hhead : head ∈ support (QueryCap.counted (CausalFrontierProgram.NonmessageHash parameter)
      (CausalFrontierProgram.adversaryImpl parameter root external ftsSecret words frontier (.inr message)).run)) :
    head.2 = 0 := by
  rw [CausalFrontierProgram.adversaryImpl_signing, WriterT.run_mk] at hhead
  have hzero := QueryCap.counted_le_of_queryBound _ _ 0
    (CausalFrontierProgram.TraceCharge.lift_prob_queryBound (CausalFrontierProgram.nonmessageTraceCharge parameter) _)
    head hhead
  omega

theorem causalAdversaryRun_counted_marker {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (result : _)
    (hresult : result ∈ support (QueryCap.counted (CausalFrontierProgram.NonmessageHash parameter)
      (CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier
        (QueryCap.counted (NonmessageQuery parameter) computation)))) :
    result.2 = result.1.1.1.2 := by
  induction computation using OracleComp.inductionOn generalizing result with
  | pure value =>
      rw [QueryCap.counted_pure, causalAdversaryRun_pure, QueryCap.counted_pure, mem_support_pure_iff] at hresult
      subst result
      rfl
  | query_bind input next ih =>
      rw [QueryCap.counted_query_bind] at hresult
      simp only [bind_pure_comp] at hresult
      rw [causalAdversaryRun_query_bind] at hresult
      simp only [causalAdversaryRun_map, QueryCap.counted_bind, QueryCap.counted_pure, QueryCap.counted_map, bind_map_left,
        pure_bind, mem_support_bind_iff, support_map, mem_support_pure_iff, Set.mem_image] at hresult
      obtain ⟨head, hhead, tail', ⟨tail, htail, rfl⟩, rfl⟩ := hresult
      have hrest := ih _ tail htail
      have hstep : head.2 = if NonmessageQuery parameter input then 1 else 0 := by
        cases input with
        | inl world => exact causalAdversaryImpl_world_count parameter root external ftsSecret words frontier world head hhead
        | inr message =>
            rw [causalAdversaryImpl_sign_count parameter root external ftsSecret words frontier message head hhead]
            rfl
      simp only [hstep, hrest]
      omega

theorem causalAdversaryRun_bind {Result Next : Type} (first : OracleComp (OracleWorld + SigningSpec) Result)
    (next : Result → OracleComp (OracleWorld + SigningSpec) Next) :
    CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier (first >>= next) =
      CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier first >>= fun result =>
        (fun tail => ((tail.1.1, result.1.2 ++ tail.1.2), result.2 * tail.2)) <$>
          CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier (next result.1.1) := by
  induction first using OracleComp.inductionOn with
  | pure value =>
      rw [pure_bind, causalAdversaryRun_pure, pure_bind]
      simp only [List.nil_append, one_mul]
      exact (id_map _).symm
  | query_bind input continuation ih =>
      rw [bind_assoc, causalAdversaryRun_query_bind, causalAdversaryRun_query_bind]
      simp only [bind_assoc, pure_bind, ih, map_bind, bind_map_left, bind_pure_comp, Functor.map_map,
        List.append_assoc, mul_assoc]

theorem isMessageInput_markerInput (count : Nat) : isMessageInput parameter (markerInput parameter count) = true :=
  (isMessageInput_iff parameter _).mpr (messageHashInput_markerInput parameter count)

theorem causalAdversaryRun_marker_step {Result : Type} (count : Nat) (value : Result) (result : _)
    (hresult : result ∈ support (QueryCap.counted (CausalFrontierProgram.NonmessageHash parameter)
      (CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier
        (liftM ((OracleWorld + SigningSpec).query (.inl (.inr (markerInput parameter count)))) >>= fun _ => pure value)))) :
    result.2 = 0 ∧ ∃ answer, result.1.2 = signingBoundaryTrace parameter (.inr (markerInput parameter count)) answer := by
  rw [causalAdversaryRun_query_bind] at hresult
  simp only [causalAdversaryRun_pure, QueryCap.counted_bind, QueryCap.counted_pure, pure_bind, mem_support_bind_iff,
    mem_support_pure_iff] at hresult
  obtain ⟨head, hhead, rfl⟩ := hresult
  have hmarker := causalAdversaryImpl_world_count parameter root external ftsSecret words frontier _ head hhead
  simp only [NonmessageQuery, isMessageInput_markerInput, Bool.true_eq_false, if_false] at hmarker
  rw [causalAdversaryImpl_world_run, QueryCap.counted_map, QueryCap.counted_query, support_map, support_map] at hhead
  obtain ⟨_, ⟨answer, _, rfl⟩, rfl⟩ := hhead
  exact ⟨by simpa using hmarker, answer, by simp⟩

/-- In the causal frontier program the capped adversary's nonmessage hash queries are exactly what
its marker records. -/
theorem causalAdversaryRun_visAdversary_marker (adversary : Adversary) (budget : Nat) (root' : Digest) (result : _)
    (hresult : result ∈ support (QueryCap.counted (CausalFrontierProgram.NonmessageHash parameter)
      (CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier
        ((visAdversary adversary budget).main ⟨root', parameter⟩)))) :
    result.2 = markerValue result.1.2 := by
  simp only [visAdversary] at hresult
  rw [causalAdversaryRun_bind] at hresult
  simp only [QueryCap.counted_bind, QueryCap.counted_pure, QueryCap.counted_map, bind_map_left, mem_support_bind_iff,
    support_map, mem_support_pure_iff, Set.mem_image] at hresult
  obtain ⟨first, hfirst, second, hsecond, rfl⟩ := hresult
  have hcount := causalAdversaryRun_counted_marker parameter root external ftsSecret words frontier _ first hfirst
  obtain ⟨hzero, answer, htrace⟩ := causalAdversaryRun_marker_step parameter root external ftsSecret words frontier _ _ second hsecond
  change first.2 + second.2 = markerValue (first.1.2 * second.1.2)
  rw [hzero, htrace, markerValue_mul_marker, hcount]
  rfl

theorem boundaryComputation_even {α : Type} (computation : OracleComp HashSpec α) (bound : Nat)
    (h : EvenBound computation bound) (result : α × SigningBoundaryTrace)
    (hresult : result ∈ support (boundaryComputation parameter (liftM computation : OracleComp OracleWorld α))) :
    ∀ entry ∈ result.2.messageCalls, entry.1.length % 2 = 0 := by
  induction computation using OracleComp.inductionOn generalizing bound result with
  | pure value =>
      simp only [liftM_pure, boundaryComputation, simulateQ_pure, WriterT.run_pure, support_pure,
        Set.mem_singleton_iff] at hresult
      subst result
      intro entry hentry
      simp [SigningBoundaryTrace.messageCalls] at hentry
  | query_bind input next ih =>
      rw [evenBound_query_bind_iff] at h
      rw [liftM_bind] at hresult
      change result ∈ support (boundaryComputation parameter (liftM (OracleWorld.query (.inr input)) >>= fun answer =>
        (liftM (next answer) : OracleComp OracleWorld α))) at hresult
      rw [ResidualByteFrontend.boundaryComputation_query_bind, mem_support_bind_iff] at hresult
      obtain ⟨answer, _, hresult⟩ := hresult
      rw [support_map] at hresult
      obtain ⟨tail, htail, rfl⟩ := hresult
      intro entry hentry
      rw [SigningBoundaryTrace.messageCalls_mul, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · by_cases hm : FtsProbeSimulation.MessageHashInput parameter input
        · simp only [signingBoundaryTrace, if_pos hm, SigningBoundaryTrace.messageCalls, FreeMonoid.toList_of,
            List.filterMap_cons, List.filterMap_nil, id, List.mem_singleton] at hentry
          subst entry
          exact Nat.even_iff.mp h.1.1
        · simp [signingBoundaryTrace, if_neg hm, SigningBoundaryTrace.messageCalls] at hentry
      · exact ih answer _ (h.2 answer) tail htail entry hentry

theorem causalGame_nonmessage_marker (adversary : Adversary) (budget : Nat) (result : _)
    (hresult : result ∈ support (QueryCap.counted (CausalFrontierProgram.NonmessageHash parameter)
      (CausalFrontierProgram.game parameter external ftsSecret words frontier (visAdversary adversary budget)))) :
    result.2 ≤ markerValue result.1.2 + verifyHashBound := by
  rw [CausalFrontierProgram.game, QueryCap.counted_map, support_map] at hresult
  obtain ⟨original, horiginal, rfl⟩ := hresult
  rw [CausalFrontierProgram.gameRest] at horiginal
  simp only [QueryCap.counted_bind, QueryCap.counted_pure, pure_bind, mem_support_bind_iff, mem_support_pure_iff] at horiginal
  obtain ⟨first, hfirst, _, ⟨second, hsecond, rfl⟩, rfl⟩ := horiginal
  have hadv := causalAdversaryRun_visAdversary_marker parameter _ external ftsSecret words frontier adversary budget _ first hfirst
  have hbound : (boundaryComputation parameter (liftM (verify ⟨frontierRoot parameter (maskOtsPrefixes parameter words external)
      words frontier, parameter⟩ first.1.1.1.message first.1.1.1.signature : OracleComp HashSpec Bool))).IsQueryBoundP
      (CausalFrontierProgram.NonmessageHash parameter) verifyHashBound := by
    rw [← isQueryBoundP_map_iff _ Prod.fst, boundaryComputation_fst]
    refine (isQueryBoundP_liftM_of_evenBound _ _ (evenBound_verify _ _ _)).of_imp ?_
    intro input hinput
    cases input with
    | inl _ => exact hinput.elim
    | inr _ => trivial
  have hcount := QueryCap.counted_le_of_queryBound _ _ _ hbound second hsecond
  have hmarker : markerValue ((FreeMonoid.of none) ^ keygenHashCost * (first.1.2 * second.1.2)) = markerValue first.1.2 := by
    rw [markerValue_pow_none_mul, markerValue_mul_even]
    have hsupport : second.1 ∈ support (boundaryComputation parameter (liftM (verify ⟨frontierRoot parameter
        (maskOtsPrefixes parameter words external) words frontier, parameter⟩ first.1.1.1.message first.1.1.1.signature :
        OracleComp HashSpec Bool))) := by
      have h := QueryCap.counted_forget (CausalFrontierProgram.NonmessageHash parameter) (boundaryComputation parameter
        (liftM (verify ⟨frontierRoot parameter (maskOtsPrefixes parameter words external) words frontier, parameter⟩
          first.1.1.1.message first.1.1.1.signature : OracleComp HashSpec Bool)))
      rw [← h, support_map]
      exact ⟨second, hsecond, rfl⟩
    exact boundaryComputation_even parameter _ _ (evenBound_verify _ _ _) _ hsupport
  change first.2 + (second.2 + 0) ≤ markerValue ((FreeMonoid.of none) ^ keygenHashCost * (first.1.2 * second.1.2)) + verifyHashBound
  rw [hmarker, ← hadv]
  omega

end Causal

end SphincsSecurity.Concrete.EventSmall
