import SigGolfCandidate.SphincsSecurity.Proof.Event.Boundary
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualGameTransfer
/-!
# Carrying the budget event into the source game

The coupling between the original game and the stopped source game already runs both on one
execution. The source memory counts the hash calls, keygen included, and a path that stops early
has counted only a prefix of the calls the original path makes, so the event "at most `q` hash
calls" transfers along the coupling.
-/
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (withSigningLog)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
  signDigestLoop sequenceFin chainWalk gameInputs
set_option backward.isDefEq.respectTransparency false

private theorem fixedCounted_sign_bind {Result : Type} (key : SecretKey) (oracle : QueryImpl HashSpec Id)
    (message : Message) (next : Option Signature → OracleComp OracleWorld Result) :
    simulateQ (fixedHashWorld oracle) (countHashQueries (scheme.sign key message >>= next)) =
      fixedBoundaryRun key.parameter oracle (signWithView key message) >>= fun record =>
        (fun tail => (tail.1, record.2.hashCalls + tail.2)) <$>
          simulateQ (fixedHashWorld oracle) (countHashQueries (next record.1.1)) := by
  rw [show scheme.sign key message = sign key message from rfl, ← signWithView_fst key message, bind_map_left,
    countHashQueries_bind, simulateQ_bind, ← fixedBoundaryRun_count key.parameter oracle (signWithView key message),
    bind_map_left]
  simp only [bind_pure_comp, simulateQ_map]

theorem prob_originalSource_le_stopped_counted {Result : Type} {inputs : Finset HashInput} (context : Context inputs)
    (computation : OracleComp (OracleWorld + SigningSpec) Result) (memory : Memory)
    (event : Result → QueryLog SigningSpec → Prop) (budget : Nat) :
    Pr[fun result => event result.1.1 result.1.2 ∧ result.2 ≤ budget |
      simulateQ (fixedHashWorld context.oracle)
        (countHashQueries (simulateQ (expandedAdversaryImpl context.key) (withSigningLog computation memory.log)))] ≤
      Pr[fun result => StoppedOr event result ∧ result.2.external.hashCalls ≤ memory.external.hashCalls + budget |
        fixedSourceRun context computation memory] := by
  induction computation using OracleComp.inductionOn generalizing memory budget with
  | pure value =>
      simp only [FtsProbeSimulation.withSigningLog_pure, simulateQ_pure, countHashQueries_pure, fixedSourceRun_pure,
        probEvent_pure, StoppedOr, Option.elim_some, zero_le, and_true, le_add_iff_nonneg_right]
      exact le_rfl
  | query_bind input next ih =>
      rw [FtsProbeSimulation.withSigningLog_query_bind, fixedSourceRun_query_bind]
      cases input with
      | inl input =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inl, countHashQueries_query_bind, simulateQ_bind,
            simulateQ_spec_query]
          simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, fixedByteRun, simulateQ_spec_query,
            signingLogFragment, List.append_nil, bind_pure_comp, simulateQ_map]
          cases input with
          | inl input =>
              simp only [fixedHashWorld, fixedByteImpl, OptionT.run_mk, StateT.run_mk, bind_assoc, pure_bind,
                Option.elim_some, probEvent_bind_eq_tsum, probOutput_query, SPMF.probOutput_liftM,
                PMF.probOutput_eq_apply, PMF.uniformOfFintype_apply, probEvent_map]
              apply ENNReal.tsum_le_tsum
              intro answer
              apply mul_le_mul' le_rfl
              refine le_trans (le_of_eq ?_) (ih answer memory budget)
              apply probEvent_ext
              intro result _
              simp
          | inr input =>
              simp only [fixedHashWorld, fixedByteImpl, OptionT.run_mk, StateT.run_mk, pure_bind, probEvent_map]
              rcases fixedHashStep_answer context input memory with hstop | hlive
              · rw [hstop, Option.elim_none]
                simp only [probEvent_pure, StoppedOr, Option.elim_none, true_and, fixedHashStep_hashCalls, if_true]
                split_ifs with hb
                · exact probEvent_le_one
                · refine (le_of_eq (probEvent_eq_zero ?_)).trans zero_le
                  intro result _ hresult
                  simp only [Function.comp_apply] at hresult
                  omega
              · rw [hlive, Option.elim_some]
                have h := ih (context.oracle input)
                  (fixedHashStep context.key.parameter context.words context.auxiliary.selections memory.routing context.actual
                    context.oracle input memory).2 (budget - 1)
                rw [fixedHashStep_log, fixedHashStep_hashCalls] at h
                by_cases hb : 1 ≤ budget
                · refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
                  · apply probEvent_ext
                    intro result _
                    simp only [Function.comp_apply, if_true]
                    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
                  · apply probEvent_ext
                    intro result _
                    constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
                · refine (le_of_eq (probEvent_eq_zero ?_)).trans zero_le
                  intro result _ hresult
                  simp only [Function.comp_apply, if_true] at hresult
                  omega
      | inr message =>
          rw [simulateQ_expandedAdversaryImpl_query_bind_inr, fixedCounted_sign_bind]
          simp only [fixedSourceImpl, OptionT.run_mk, StateT.run_mk, bind_map_left, Option.elim_some,
            probEvent_bind_eq_tsum, probEvent_map]
          apply ENNReal.tsum_le_tsum
          intro record
          apply mul_le_mul'
          · simp only [probOutput_def, SPMF.evalSPMF_def, le_refl]
          · have h := ih record.1.1 ((memory.applyBoundary record.2).recordSigning message record) (budget - record.2.hashCalls)
            have hlog : ((memory.applyBoundary record.2).recordSigning message record).log =
                memory.log ++ signingLogFragment (.inr message) record.1.1 := rfl
            rw [hlog, applyBoundary_recordSigning_hashCalls] at h
            by_cases hb : record.2.hashCalls ≤ budget
            · refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
              · apply probEvent_ext
                intro result _
                simp only [Function.comp_apply]
                constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
              · apply probEvent_ext
                intro result _
                constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
            · refine (le_of_eq (probEvent_eq_zero ?_)).trans zero_le
              intro result _ hresult
              simp only [Function.comp_apply] at hresult
              omega

theorem gameRest_eq_verdict (key : SecretKey) (adversary : Adversary) :
    gameRest scheme adversary ⟨key.root, key.parameter⟩ key =
      (fun result => sourceVerdict result.1 result.2) <$>
        simulateQ (expandedAdversaryImpl key)
          (withSigningLog (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) []) := by
  rw [← FtsProbeSimulation.simulateQ_expanded_tracedGameRestComputation,
    ← FtsProbeSimulation.retainedGameRestComputation_verdict_projection,
    FtsProbeSimulation.retainedGameRestComputation_eq_signingTrace]
  simp only [simulateQ_map, Functor.map_map, withSigningLog, List.nil_append]
  rfl

theorem prob_gameRest_le_stopped_counted {inputs : Finset HashInput} (context : Context inputs)
    (adversary : Adversary) (memory : Memory) (hlog : memory.log = []) (budget : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ budget |
      simulateQ (fixedHashWorld context.oracle)
        (countHashQueries (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key))] ≤
      Pr[fun result => StoppedOr (fun result log => sourceVerdict result log = true) result ∧
          result.2.external.hashCalls ≤ memory.external.hashCalls + budget |
        fixedSourceRun context
          (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩) memory] := by
  rw [gameRest_eq_verdict, countHashQueries_map, simulateQ_map, probEvent_map]
  have h := prob_originalSource_le_stopped_counted context
    (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)
    memory (fun result log => sourceVerdict result log = true) budget
  rw [hlog] at h
  exact h

theorem prob_gameRest_le_observed_counted {inputs : Finset HashInput} (context : Context inputs)
    (adversary : Adversary)
    (hinputs : sourceInputs context.key
      (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩) ⊆ inputs)
    (state : State inputs) (hcovered : ResidualByteFrontend.RowsCovered inputs (project state))
    (hcompatible : Compatible context state.memory) (hlog : state.memory.log = []) (budget : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ budget |
      simulateQ (fixedHashWorld context.oracle)
        (countHashQueries (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key))] ≤
      Pr[fun result => StoppedOr (fun value log => sourceVerdict value log = true) (forgetState result) ∧
          result.2.memory.external.hashCalls ≤ state.memory.external.hashCalls + budget |
        observedRun context.environment context.actual context.auxiliary.seed
          (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections)
            (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩)) state] := by
  have h := prob_gameRest_le_stopped_counted context adversary state.memory hlog budget
  rw [← observedRun_source_memory context _ hinputs state hcovered hcompatible, probEvent_map] at h
  exact h

theorem Context.frontierGame_original_counted {inputs : Finset HashInput} (context : Context inputs)
    (adversary : Adversary) (hroot : context.key.root = canonicalGraphRoot context.graph) :
    (fun result => (result.1, result.2.hashCalls)) <$> referenceFamilyFrontierRest context.key context.oracle context.graph
        context.auxiliary.selections context.dummy adversary =
      (fun result => (result.1, keygenHashCost + result.2)) <$> simulateQ (fixedHashWorld context.oracle)
        (countHashQueries (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩ context.key)) := by
  have hselection : referenceTableSelection context.key context.oracle = context.auxiliary.selections :=
    referenceTableSelection_prefix context.key inputs context.encoding context.graph context.auxiliary context.auxiliary_valid
  have hgraph : canonicalGraphLabels context.key.parameter context.key.otsSecret context.key.ftsSecret context.oracle =
      context.graph := canonicalGraphLabels_programmedHash _ _ _ _ _
  have hfrontier : referenceFamilyFrontierRest context.key context.oracle context.graph
      context.auxiliary.selections context.dummy adversary =
      fixedBoundaryRun context.key.parameter context.oracle
        (gameAfterSecrets adversary context.key.parameter context.key.otsSecret context.key.ftsSecret) := by
    rw [← hselection, referenceFamilyFrontierRest_selected, ← hgraph, graphFrontierGameRest_canonical]
  rw [hfrontier, gameAfterSecrets, fixedBoundaryRun_bind, context.keygen_record hroot, pure_bind, Functor.map_map]
  have hkey : (⟨context.key.parameter, context.key.root, context.key.otsSecret, context.key.ftsSecret⟩ : SecretKey) = context.key := by
    cases context.key
    rfl
  change (fun result => (result.1, SigningBoundaryTrace.hashCalls ((FreeMonoid.of none) ^ keygenHashCost * result.2))) <$>
    fixedBoundaryRun context.key.parameter context.oracle
      (gameRest scheme adversary ⟨context.key.root, context.key.parameter⟩
        ⟨context.key.parameter, context.key.root, context.key.otsSecret, context.key.ftsSecret⟩) = _
  rw [hkey, ← fixedBoundaryRun_count context.key.parameter, Functor.map_map]
  simp only [SigningBoundaryTrace.hashCalls_mul, SigningBoundaryTrace.hashCalls_pow_none]

private theorem probEvent_denotation {Result : Type} (computation : ProbComp Result) (event : Result → Prop) :
    Pr[event | 𝒮[computation]] = Pr[event | computation] := rfl

theorem forgeEventAdvantage_eq_retainedPrefixPrior (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) :
    forgeEventAdvantage scheme adversary q =
      Pr[fun result => result.2.1 = true ∧ result.2.2.hashCalls ≤ q | referencePrefixJointPriorGame (gameInputs adversary)
        (canonicalEncodingInputs_subset_retainedGameInputs adversary) dummy adversary] := by
  rw [forgeEventAdvantage_eq_boundary, ← probEvent_denotation, boundaryGameCore_eq_retainedPrefixPrior, probEvent_map]
  rfl

theorem observedInitialSource_success_counted (parameter : PublicParameter) (inputs : Finset HashInput)
    (hcanonical : canonicalEncodingInputs parameter ⊆ inputs)
    (encoding : ReferenceEncodingAuxiliary) (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (seed : inputs → HashOutput) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (labels : Labels)
    (hlabels : UniformTableCompletion.complete (initialAllowed (referenceFamilyWords encoding.selections dummy) exposed) labels ≠ 0)
    (adversary : Adversary)
    (hinputs : ∀ key : SecretKey, sourceInputs key
      (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) ⊆ inputs) (q : Nat) :
    Pr[fun result => result.1 = true ∧ result.2.hashCalls ≤ q |
      referenceFamilyFrontierRest ⟨parameter, 0, coordinateOtsSecrets labels, coordinateFtsSecrets labels⟩
        (programmedHash parameter (coordinateOtsSecrets labels) (coordinateFtsSecrets labels) (coordinateGraphLabels labels high)
          (finiteHashAnswer ∅ inputs (canonicalPrefixResidual parameter inputs hcanonical (coordinateGraphLabels labels high)
            encoding.selections encoding.rows seed)))
        (coordinateGraphLabels labels high) encoding.selections dummy adversary] ≤
      Pr[fun result => StoppedOr (fun value log => sourceVerdict value log = true) (forgetState result) ∧
          result.2.memory.external.hashCalls ≤ q |
        observedRun
          (environment parameter inputs hcanonical (referenceFamilyWords encoding.selections dummy)
            (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
            encoding.selections encoding.rows)
          labels seed
          (simulateQ (adversaryImpl inputs parameter (knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
            (referenceFamilyWords encoding.selections dummy) encoding.selections)
            (FtsProbeSimulation.unloggedRetainedRestComputation adversary
              ⟨knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed), parameter⟩))
          (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed)] := by
  let auxiliary : ReferenceAuxiliary inputs := ⟨encoding.selections, encoding.rows, seed⟩
  have hauxiliary := referenceEncodingAuxiliary_support_seed inputs encoding hencoding seed
  let context := initialContext parameter inputs hcanonical auxiliary hauxiliary dummy exposed high labels
  have hroot : context.key.root = canonicalGraphRoot context.graph :=
    initialKnown_root (referenceFamilyWords encoding.selections dummy) exposed labels hlabels high
  have hcompatible : Compatible context (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed).memory := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · simpa only [context, auxiliary, Context.words, Context.actual, initialContext, coordinateGraphLabels_value,
        initialState, initialMemory] using initialKnown_agrees (referenceFamilyWords encoding.selections dummy) exposed labels hlabels
    · exact initialKnown_graphReplies (referenceFamilyWords encoding.selections dummy) exposed labels hlabels high
    · intro input answer hanswer; cases hanswer
    · intro input answer hanswer; cases hanswer
    · intro input answer hanswer; cases hanswer
  have h := prob_gameRest_le_observed_counted context adversary (hinputs context.key)
    (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed) (initialState_rowsCovered _ _ exposed)
    hcompatible rfl (q - keygenHashCost)
  have hframe := congrArg (fun law : ProbComp (Bool × Nat) => Pr[fun result => result.1 = true ∧ result.2 ≤ q | law])
    (context.frontierGame_original_counted adversary hroot)
  simp only [probEvent_map] at hframe
  have hstart : (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed).memory.external.hashCalls =
      keygenHashCost := rfl
  rw [hstart] at h
  have hmain : Pr[fun result => result.1 = true ∧ result.2.hashCalls ≤ q |
      referenceFamilyFrontierRest context.key context.oracle context.graph context.auxiliary.selections context.dummy adversary] ≤
      Pr[fun result => StoppedOr (fun value log => sourceVerdict value log = true) (forgetState result) ∧
          result.2.memory.external.hashCalls ≤ q |
        observedRun context.environment context.actual context.auxiliary.seed
          (simulateQ (adversaryImpl inputs context.key.parameter context.key.root context.words context.auxiliary.selections)
            (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨context.key.root, context.key.parameter⟩))
          (initialState inputs (referenceFamilyWords encoding.selections dummy) exposed)] := by
    change Pr[(fun result => result.1 = true ∧ result.2 ≤ q) ∘ (fun result => (result.1, result.2.hashCalls)) |
      referenceFamilyFrontierRest context.key context.oracle context.graph context.auxiliary.selections context.dummy adversary] ≤ _
    rw [hframe]
    by_cases hq : keygenHashCost ≤ q
    · have heq : keygenHashCost + (q - keygenHashCost) = q := by omega
      rw [heq] at h
      refine le_trans (le_of_eq ?_) h
      apply probEvent_ext
      intro result _
      simp only [Function.comp_apply]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
    · refine le_trans (le_of_eq ?_) zero_le
      apply probEvent_eq_zero
      intro result _ hresult
      simp only [Function.comp_apply] at hresult
      omega
  simpa only [context, auxiliary, Context.words, Context.actual, Context.oracle, Context.environment, initialContext,
    coordinateGraphLabels_value, referenceFamilyFrontierRest, Function.comp_def] using hmain

private theorem probEvent_bind_compare {A B C : Type} (law : SPMF A)
    (left : A → SPMF B) (right : A → SPMF C) (before : B → Prop) (after : C → Prop)
    (h : ∀ value, law value ≠ 0 → Pr[before | left value] ≤ Pr[after | right value]) :
    Pr[before | law >>= left] ≤ Pr[after | law >>= right] := by
  simp only [probEvent_bind_eq_tsum, SPMF.probOutput_eq_apply]
  apply ENNReal.tsum_le_tsum
  intro value
  by_cases hvalue : law value = 0
  · simp only [hvalue, zero_mul, le_refl]
  exact mul_le_mul' le_rfl (h value hvalue)

/-- The event form of `forgeAdvantage_le_sourceGame`: a win within `q` calls is a stopped or winning
source run whose memory has counted at most `q` calls. -/
theorem forgeEventAdvantage_le_sourceGame (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) :
    forgeEventAdvantage scheme adversary q ≤
      Pr[fun result => StoppedOr (fun value log => sourceVerdict value log = true) (forgetState result) ∧
          result.2.memory.external.hashCalls ≤ q |
        sourceGame dummy adversary] := by
  rw [forgeEventAdvantage_eq_retainedPrefixPrior dummy adversary]
  rw [referencePrefixJointPriorGame, sourceGame]
  apply probEvent_bind_compare
  intro parameter _
  apply probEvent_bind_compare
  intro encoding hencoding
  have hencoding' : encoding ∈ referenceEncodingAuxiliarySample.support := by
    apply (PMF.mem_support_iff _ _).mpr
    simpa only [PMF.evalSPMF_eq, SPMF.liftM_apply] using hencoding
  apply probEvent_bind_compare
  intro high _
  apply probEvent_bind_compare
  intro exposed _
  rw [← run_erasure _ _ (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed)
    (initialAllowed_nonempty _ exposed)]
  apply probEvent_bind_compare
  intro labels hlabels
  apply probEvent_bind_compare
  intro seed _
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, probEvent_denotation]
  exact observedInitialSource_success_counted parameter (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary parameter) encoding hencoding' seed dummy exposed high labels
    hlabels adversary (sourceInputs_unlogged_subset_gameInputs adversary) q

theorem forgeEventAdvantage_le_source_stop_add_win (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) :
    forgeEventAdvantage scheme adversary q ≤
      Pr[fun result => result.1 = none ∧ result.2.memory.external.hashCalls ≤ q | sourceGame dummy adversary] +
        Pr[fun result => (∃ value, result.1 = some value ∧ sourceVerdict value result.2.memory.log = true) ∧
          result.2.memory.external.hashCalls ≤ q | sourceGame dummy adversary] := by
  apply (forgeEventAdvantage_le_sourceGame dummy adversary q).trans
  apply le_trans _ (probEvent_or_le (sourceGame dummy adversary) _ _)
  apply probEvent_mono
  rintro ⟨result, state⟩ _ ⟨hresult, hcalls⟩
  cases result with
  | none => exact Or.inl ⟨rfl, hcalls⟩
  | some value => exact Or.inr ⟨⟨value, rfl, hresult⟩, hcalls⟩

end SphincsSecurity.Concrete.RetainedResidual
