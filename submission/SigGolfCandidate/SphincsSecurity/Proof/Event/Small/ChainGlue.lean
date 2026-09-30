import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.NearMass
import SigGolfCandidate.SphincsSecurity.Proof.Reference.ReferencePrimitiveBound
/-!
# Chain budgets of the capped adversary

In the causal frontier program the signer makes no hash queries of the world: the adversary's hash
queries and the verifier's are the only ones. The capped adversary makes at most
`budget - keygenHashCost` of them and the verifier at most `verifyHashBound < keygenHashCost`, so every
path of the program makes at most `budget` hash queries. This bounds the prefix queries of every seed
game and the observed queries of every contact run, structurally.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem isQueryBoundP_writer_simulate {ι ι' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'} {ω : Type} [Monoid ω]
    {α : Type} (weight : ι → Nat) (selected : ι' → Prop) [DecidablePred selected]
    (impl : QueryImpl spec (WriterT ω (OracleComp spec')))
    (hstep : ∀ input, (impl input).run.IsQueryBoundP selected (weight input))
    (computation : OracleComp spec α) (budget : Nat)
    (h : computation.IsQueryBound budget (fun input remaining => weight input ≤ remaining)
      (fun input remaining => remaining - weight input)) :
    (simulateQ impl computation).run.IsQueryBoundP selected budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => exact isQueryBoundP_pure _ _ _
  | query_bind input next ih =>
      rw [isQueryBound_query_bind_iff] at h
      rw [simulateQ_bind, simulateQ_spec_query, WriterT.run_bind]
      have hbind := isQueryBoundP_bind (ob := fun step => (fun final => (final.1, step.2 * final.2)) <$>
          (simulateQ impl (next step.1)).run) (hstep input) (fun step _ =>
        (isQueryBoundP_map_iff _ _ _).mpr (ih step.1 (budget - weight input) (h.2 step.1)))
      refine hbind.mono ?_
      have := h.1
      omega

/-- On every path of the causal frontier program the capped adversary and the verifier make at most
`budget` hash queries. -/
theorem causalGame_queryBound (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (budget : Nat) (hbudget : keygenHashCost + 1 ≤ budget) :
    (CausalFrontierProgram.game parameter external ftsSecret words frontier (visAdversary adversary budget)).IsQueryBoundP
      CausalFrontierProgram.IsHash budget := by
  rw [CausalFrontierProgram.game, isQueryBoundP_map_iff, CausalFrontierProgram.gameRest]
  have hadversary : ∀ root : Digest, (CausalFrontierProgram.adversaryRun parameter root external ftsSecret words frontier
      ((visAdversary adversary budget).main ⟨root, parameter⟩)).IsQueryBoundP CausalFrontierProgram.IsHash
      (budget - keygenHashCost) := by
    intro root
    apply isQueryBoundP_writer_simulate visWeight
    · intro input
      rcases input with (input | input) | message
      · change ((fun answer => (answer, signingBoundaryTrace parameter (.inl input) answer)) <$>
          (liftM (OracleWorld.query (.inl input)) : OracleComp OracleWorld _)).IsQueryBoundP _ _
        rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        intro h
        cases h
      · change ((fun answer => (answer, signingBoundaryTrace parameter (.inr input) answer)) <$>
          (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld _)).IsQueryBoundP _ _
        rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        intro _
        exact Nat.one_pos
      · rw [CausalFrontierProgram.adversaryImpl_signing, WriterT.run_mk]
        exact (CausalFrontierProgram.TraceCharge.lift_prob_queryBound (CausalFrontierProgram.hashTraceCharge parameter) _).mono
          (Nat.zero_le _)
    · exact weightBound_logged _ _ (visAdversary_weightBound adversary budget _ hbudget)
  have hverify : ∀ (root : Digest) (forgery : Forgery),
      (boundaryComputation parameter (liftM (verify ⟨root, parameter⟩ forgery.message forgery.signature :
        OracleComp HashSpec Bool))).IsQueryBoundP CausalFrontierProgram.IsHash verifyHashBound := by
    intro root forgery
    rw [← isQueryBoundP_map_iff _ Prod.fst, boundaryComputation_fst]
    exact isQueryBoundP_liftM_of_evenBound _ _ (evenBound_verify _ _ _)
  refine IsQueryBoundP.mono (n := budget - keygenHashCost + (verifyHashBound + 0)) ?_
    (by have := verifyHashBound_lt_keygen; omega)
  exact isQueryBoundP_bind (hadversary _) (fun result _ =>
    isQueryBoundP_bind (hverify _ result.1.1) (fun _ _ => isQueryBoundP_pure _ _ 0))


theorem visibleWorldImpl_queryBound (segment : OtsPrefix) (high : segment.Query → OtsPrefix.High) (input : OracleWorld.Domain) :
    (segment.visibleWorldImpl high input).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery
      (if input matches .inr _ then 1 else 0) := by
  cases input with
  | inl input =>
      simp only [OtsPrefix.visibleWorldImpl, isQueryBoundP_query_iff, PartialChainEndpoint.IsPrefixQuery, false_implies]
  | inr bytes =>
      change (segment.visibleHashImpl high bytes).IsQueryBoundP _ 1
      unfold OtsPrefix.visibleHashImpl
      split
      · simp only [isQueryBoundP_query_iff, PartialChainEndpoint.IsPrefixQuery, false_implies]
      · rw [isQueryBoundP_map_iff, isQueryBoundP_query_iff]
        intro _
        exact Nat.one_pos

theorem worldImpl_hash_bound (segment : OtsPrefix) (high : segment.Query → OtsPrefix.High) (outside : QueryImpl HashSpec Id)
    (input : OracleWorld.Domain) (hinput : CausalFrontierProgram.IsHash input) :
    (segment.worldImpl high outside input).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery 1 := by
  have h := segment.worldImpl_queryBound high outside input
  cases input with
  | inl _ => exact absurd hinput (by simp [CausalFrontierProgram.IsHash])
  | inr _ => simpa only [if_true] using h

theorem worldImpl_nonhash_bound (segment : OtsPrefix) (high : segment.Query → OtsPrefix.High) (outside : QueryImpl HashSpec Id)
    (input : OracleWorld.Domain) (hinput : ¬ CausalFrontierProgram.IsHash input) :
    (segment.worldImpl high outside input).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery 0 := by
  have h := segment.worldImpl_queryBound high outside input
  cases input with
  | inl _ => simpa only [Bool.false_eq_true, if_false] using h
  | inr _ => exact absurd hinput (by simp [CausalFrontierProgram.IsHash])

theorem visibleWorldImpl_hash_bound (segment : OtsPrefix) (high : segment.Query → OtsPrefix.High)
    (input : OracleWorld.Domain) (hinput : CausalFrontierProgram.IsHash input) :
    (segment.visibleWorldImpl high input).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery 1 := by
  have h := visibleWorldImpl_queryBound segment high input
  cases input with
  | inl _ => exact absurd hinput (by simp [CausalFrontierProgram.IsHash])
  | inr _ => simpa only [if_true] using h

theorem visibleWorldImpl_nonhash_bound (segment : OtsPrefix) (high : segment.Query → OtsPrefix.High)
    (input : OracleWorld.Domain) (hinput : ¬ CausalFrontierProgram.IsHash input) :
    (segment.visibleWorldImpl high input).IsQueryBoundP PartialChainEndpoint.IsPrefixQuery 0 := by
  have h := visibleWorldImpl_queryBound segment high input
  cases input with
  | inl _ => simpa only [Bool.false_eq_true, if_false] using h
  | inr _ => exact absurd hinput (by simp [CausalFrontierProgram.IsHash])

theorem prefixBudget_visAdversary (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : keygenHashCost + 1 ≤ budget) : PrefixBudget dummy (visAdversary adversary budget) budget := by
  intro parameter _ ftsSecret address selections _ other auxiliary _
  refine ⟨fun _ => budget, ?_, ?_, fun _ _ => le_rfl⟩
  · intro endpoint result hresult
    refine QueryCap.counted_le_of_queryBound _ _ budget ?_ result hresult
    rw [OtsPrefix.seedGame, ← CausalFrontierProgram.prefix_game]
    exact IsQueryBoundP.simulateQ_of_step (p := CausalFrontierProgram.IsHash)
      (causalGame_queryBound _ _ _ _ _ adversary budget hbudget)
      (fun input hinput => worldImpl_hash_bound _ _ _ input hinput)
      (fun input hinput => worldImpl_nonhash_bound _ _ _ input hinput)
  · intro endpoint result hresult
    refine QueryCap.counted_le_of_queryBound _ _ budget ?_ result hresult
    rw [OtsPrefix.visibleSeedGame, OtsPrefix.visibleGame]
    exact IsQueryBoundP.simulateQ_of_step (p := CausalFrontierProgram.IsHash)
      (causalGame_queryBound _ _ _ _ _ adversary budget hbudget)
      (fun input hinput => visibleWorldImpl_hash_bound _ _ input hinput)
      (fun input hinput => visibleWorldImpl_nonhash_bound _ _ input hinput)


theorem contactObserver_length_le (parameter : PublicParameter) (external : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (adversary : Adversary) (budget : Nat) (hbudget : keygenHashCost + 1 ≤ budget) (result : ContactResult)
    (hresult : result ∈ support (contactObserver parameter words frontier
      (CausalFrontierProgram.game parameter external ftsSecret words frontier (visAdversary adversary budget)))) :
    (result.before * result.after).toList.length ≤ budget := by
  rw [contactObserver, support_map] at hresult
  obtain ⟨split, hsplit, rfl⟩ := hresult
  have htraced : (split.2.1, split.1 * split.2.2) ∈ support (QueryPause.traced hashObservationTrace
      (CausalFrontierProgram.game parameter external ftsSecret words frontier (visAdversary adversary budget))) := by
    rw [← OtsContactTrace.splitRun_trace parameter words frontier, support_map]
    exact ⟨split, hsplit, rfl⟩
  have hcounted : (split.2.1, (split.1 * split.2.2).toList.length) ∈ support (QueryCap.counted CausalFrontierProgram.IsHash
      (CausalFrontierProgram.game parameter external ftsSecret words frontier (visAdversary adversary budget))) := by
    rw [← OtsContactTrace.traced_hash_counted, support_map]
    exact ⟨_, htraced, rfl⟩
  exact QueryCap.counted_le_of_queryBound _ _ budget (causalGame_queryBound _ _ _ _ _ adversary budget hbudget) _ hcounted

theorem contactBudget_visAdversary (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : keygenHashCost + 1 ≤ budget) : ContactBudget dummy (visAdversary adversary budget) budget := by
  intro result hresult
  simp only [referenceContactGame, referenceInstrumentedGame, mem_support_bind_iff] at hresult
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, reference, _, output, houtput, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  have hsyntax := (mem_support_iff_of_evalSPMF_eq (mx := referenceInstrumentedRest contactObserver _ _ _ _ dummy _)
    (mx' := 𝒮[referenceInstrumentedRest contactObserver _ _ _ _ dummy _]) rfl output).mpr houtput
  exact contactObserver_length_le _ _ _ _ _ adversary budget hbudget output (QueryCap.simulate_oracle_mem_support _ _ output hsyntax)

end SphincsSecurity.Concrete.EventSmall
