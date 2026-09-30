import SigGolfCandidate.SphincsSecurity.Proof.Residual.Security127LargeBudget
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualEventTransfer
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualEventCoverage
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualEventCache
/-!
# The large-budget bound in event form

The chain of `RetainedResidualCacheTail`, with the event "at most `q` hash calls" carried along instead
of a query bound on the adversary.
-/
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs gameInputs
  certificateCacheExceptionWeight
set_option backward.isDefEq.respectTransparency false

theorem initialMonitoredSource_event_stop_add_strong_le (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf))
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support)
    (hroot : key.root = knownRoot (initialKnown (referenceFamilyWords encoding.selections dummy) exposed))
    (hbudget : budget ≤ 2 ^ 127) :
    Pr[fun result => result.1 = none ∧ result.2.1.memory.external.hashCalls ≤ budget |
      initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped] +
      Pr[fun result => MonitoredStrongWin result ∧ result.2.1.memory.external.hashCalls ≤ budget |
        initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped] ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * fullCertificateExcessRate +
        Pr[fun result => MonitoredStrongException result ∧ result.2.1.memory.external.hashCalls ≤ budget |
          initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped] := by
  let law := initialMonitoredSource key adversary encoding dummy exposed high budget Finset.univ (proposalStop stopAfter) stopped
  have hcount : Pr[fun result => MonitoredStrongWin result ∧ result.2.2.stopped = false | law] ≤
      ∑' result, Pr[= result | law] * certificateBankCount result.2.2.bank := by
    apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
    rintro ⟨answer, after⟩ hsupport ⟨⟨⟨forgery, checked⟩, hanswer, hwin⟩, halive⟩
    simp only [sourceVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
    obtain ⟨⟨_, hnew⟩, rfl⟩ := hwin
    dsimp only at hanswer halive hnew ⊢
    subst answer
    have hresult := probOutput_ne_zero_of_mem_support hsupport
    rw [SPMF.probOutput_eq_apply] at hresult
    exact initialMonitoredSource_strong_count key adversary encoding hencoding dummy hdummy exposed high hroot
      budget (proposalStop stopAfter) stopped forgery after hresult hnew halive
  have hsplit : Pr[fun result => MonitoredStrongWin result ∧ result.2.1.memory.external.hashCalls ≤ budget | law] ≤
      Pr[fun result => MonitoredStrongWin result ∧ result.2.2.stopped = false | law] +
        Pr[fun result => MonitoredStrongException result ∧ result.2.1.memory.external.hashCalls ≤ budget | law] := by
    apply le_trans ?_ (probEvent_or_le law _ _)
    apply probEvent_mono
    intro result _ ⟨hwin, hcalls⟩
    cases hstop : result.2.2.stopped with
    | false => exact Or.inl ⟨hwin, rfl⟩
    | true => exact Or.inr ⟨⟨hwin, hstop⟩, hcalls⟩
  have hcoverage := expected_initialMonitoredSource_full_unit_count_le_mass key adversary encoding dummy exposed high budget
    stopAfter stopped hbudget
  have hprimitive := initialMonitoredSource_event_primitive key budget adversary encoding dummy exposed high Finset.univ
    (proposalStop stopAfter) stopped hencoding hbudget
  change Pr[_ | law] + Pr[_ | law] ≤ _
  change Pr[_ | law] + (∑' result, Pr[= result | law] * result.2.2.creationMass) / 2 ^ digestBits ≤ _ at hprimitive
  change (∑' result, Pr[= result | law] * _) ≤ (2 ^ 128 : ENNReal)⁻¹ * (∑' result, Pr[= result | law] * _) + _ at hcoverage
  calc
    _ ≤ Pr[fun result => result.1 = none ∧ result.2.1.memory.external.hashCalls ≤ budget | law] +
        (((2 ^ 128 : ENNReal)⁻¹ * (∑' result, Pr[= result | law] * result.2.2.creationMass) +
          (budget : ENNReal) * fullCertificateExcessRate) +
          Pr[fun result => MonitoredStrongException result ∧ result.2.1.memory.external.hashCalls ≤ budget | law]) :=
      add_le_add le_rfl (hsplit.trans (add_le_add (hcount.trans hcoverage) le_rfl))
    _ = (Pr[fun result => result.1 = none ∧ result.2.1.memory.external.hashCalls ≤ budget | law] +
          (∑' result, Pr[= result | law] * result.2.2.creationMass) / 2 ^ digestBits) +
        (budget : ENNReal) * fullCertificateExcessRate +
        Pr[fun result => MonitoredStrongException result ∧ result.2.1.memory.external.hashCalls ≤ budget | law] := by
      simp only [div_eq_mul_inv, digestBits]
      ring
    _ ≤ _ := add_le_add (add_le_add hprimitive le_rfl) le_rfl

private theorem probEvent_bind_add_le_const_add {A B : Type} (law : SPMF A) (next : A → SPMF B)
    (left right exception : B → Prop) (bound : ENNReal)
    (h : ∀ value, law value ≠ 0 → Pr[left | next value] + Pr[right | next value] ≤ bound + Pr[exception | next value]) :
    Pr[left | law >>= next] + Pr[right | law >>= next] ≤ bound + Pr[exception | law >>= next] := by
  simp only [probEvent_bind_eq_tsum, ← ENNReal.tsum_add, ← mul_add]
  calc
    _ ≤ ∑' value, Pr[= value | law] * (bound + Pr[exception | next value]) := by
      apply ENNReal.tsum_le_tsum
      intro value
      by_cases hvalue : law value = 0
      · simp only [SPMF.probOutput_eq_apply, hvalue, zero_mul, le_refl]
      exact mul_le_mul' le_rfl (h value hvalue)
    _ = (∑' value, Pr[= value | law]) * bound + ∑' value, Pr[= value | law] * Pr[exception | next value] := by
      simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
    _ ≤ _ := add_le_add (mul_le_of_le_one_left' tsum_probOutput_le_one) le_rfl

theorem monitoredSourceGame_event_stop_add_strong_le (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf)) (adversary : Adversary)
    (budget : Nat) (stopAfter : CertificateStopRule) (hbudget : budget ≤ 2 ^ 127) :
    Pr[fun result => result.1 = none ∧ result.2.1.memory.external.hashCalls ≤ budget |
      monitoredSourceGame dummy adversary budget stopAfter] +
      Pr[fun result => MonitoredStrongWin result ∧ result.2.1.memory.external.hashCalls ≤ budget |
        monitoredSourceGame dummy adversary budget stopAfter] ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * fullCertificateExcessRate +
        Pr[fun result => MonitoredStrongException result ∧ result.2.1.memory.external.hashCalls ≤ budget |
          monitoredSourceGame dummy adversary budget stopAfter] := by
  unfold monitoredSourceGame
  apply probEvent_bind_add_le_const_add
  intro parameter _
  apply probEvent_bind_add_le_const_add
  intro encoding hencoding
  have hencoding' : encoding ∈ referenceEncodingAuxiliarySample.support := by
    apply (PMF.mem_support_iff _ _).mpr
    simpa only [PMF.evalSPMF_eq, SPMF.liftM_apply] using hencoding
  apply probEvent_bind_add_le_const_add
  intro high _
  apply probEvent_bind_add_le_const_add
  intro exposed _
  unfold initialMonitoredPrior
  apply probEvent_bind_add_le_const_add
  intro labels _
  exact initialMonitoredSource_event_stop_add_strong_le _ adversary encoding dummy hdummy exposed high budget stopAfter false
    hencoding' rfl hbudget

theorem forgeEventAdvantage_le_monitored_bound_add_exception (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf)) (adversary : Adversary)
    (budget : Nat) (stopAfter : CertificateStopRule) (hbudget : budget ≤ 2 ^ 127) :
    forgeEventAdvantage scheme adversary budget ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * fullCertificateExcessRate +
        Pr[fun result => MonitoredStrongException result ∧ result.2.1.memory.external.hashCalls ≤ budget |
          monitoredSourceGame dummy adversary budget stopAfter] := by
  have h := forgeEventAdvantage_le_source_stop_add_win dummy adversary budget
  rw [← monitoredSourceGame_erasure dummy adversary budget stopAfter, probEvent_map, probEvent_map] at h
  exact h.trans (monitoredSourceGame_event_stop_add_strong_le dummy hdummy adversary budget stopAfter hbudget)

theorem initialExceptionHistorySource_event_exception (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) (hbudget : budget ≤ 2 ^ 127)
    (result : Option (Forgery × Bool) × ExceptionHistoryState (gameInputs adversary))
    (hresult : initialExceptionHistorySource key adversary encoding dummy exposed high budget result ≠ 0)
    (hexception : MonitoredStrongException (result.1, result.2.1))
    (hbound : result.2.1.1.memory.external.hashCalls ≤ budget) :
    result.2.2.1 = true ∨ result.2.2.2 = true := by
  by_contra hflags
  have hclean : result.2.2 = (false, false) := by
    rcases hf : result.2.2 with ⟨cache, proposals⟩
    cases cache <;> cases proposals <;> simp_all only [Bool.false_eq_true, or_self, not_false_eq_true, not_true_eq_false,
      or_true, true_or]
  obtain ⟨⟨value, hvalue, hwin⟩, hstop⟩ := hexception
  have hlive : result.1 ≠ none := by rw [hvalue]; exact Option.some_ne_none _
  have hlog : result.2.1.1.memory.log.length ≤ signatureLimit := by
    simp only [sourceVerdict, Bool.and_eq_true, decide_eq_true_eq] at hwin
    exact hwin.1.1
  have halive := exceptionHistoryRun_unstopped key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget Finset.univ _ _
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_unlogged_subset_gameInputs adversary key) (fun _ => rfl)
    (monitoredBankComplete_initial key (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) Finset.univ exposed keygenHashCost false)
    (show CacheSizeBound (initialMemory (referenceFamilyWords encoding.selections dummy) exposed) from by
      change QueryCache.enncard (∅ : QueryCache HashSpec) ≤ (keygenHashCost : ENNReal)
      rw [QueryCache.enncard_empty]
      exact zero_le)
    (by intro entry hentry; cases hentry) rfl hbudget result hresult hlive hbound hlog hclean
  simp only [halive, Bool.false_eq_true] at hstop

theorem initialExceptionHistorySource_event_cache_le (key : SecretKey) (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (budget : Nat) :
    Pr[fun result => result.2.2.1 = true ∧ result.2.1.1.memory.external.hashCalls ≤ budget |
      initialExceptionHistorySource key adversary encoding dummy exposed high budget] ≤
      (budget : ENNReal) * certificateCacheExceptionRate := by
  have hrun := expected_exceptionHistoryRun_eventCache_le key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget Finset.univ (proposalStop (fun _ _ _ _ => false))
    (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)
    ((initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
      initialCertificateMonitor keygenHashCost false), (false, false))
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_unlogged_subset_gameInputs adversary key)
    (show CacheSizeBound (initialMemory (referenceFamilyWords encoding.selections dummy) exposed) from by
      change QueryCache.enncard (∅ : QueryCache HashSpec) ≤ (keygenHashCost : ENNReal)
      rw [QueryCache.enncard_empty]
      exact zero_le) budget
  refine le_trans ?_ (hrun.trans ?_)
  · apply probEvent_le_tsum_probOutput_mul_cost_of_mem_support
    intro result _ ⟨hflag, hcalls⟩
    unfold eventCacheHistory cacheHistoryWeight
    rw [if_pos hcalls, if_pos hflag]
    exact le_self_add
  · unfold eventCacheHistory cacheHistoryWeight
    change (if keygenHashCost ≤ budget then (if false = true then 1 else certificateCacheExceptionWeight key ∅) +
      certificateCacheExceptionRate * ((budget - keygenHashCost : Nat) : ℝ≥0∞) else 0) ≤ _
    simp only [Bool.false_eq_true, if_false]
    split_ifs
    · rw [certificateCacheExceptionWeight_initial key ∅ (fun _ _ => rfl), zero_add, mul_comm]
      exact mul_le_mul' (Nat.cast_le.mpr (Nat.sub_le _ _)) le_rfl
    · exact zero_le

theorem exceptionHistorySourceGame_event_exception (dummy : OtsReferenceWords) (adversary : Adversary)
    (budget : Nat) (hbudget : budget ≤ 2 ^ 127)
    (result : Option (Forgery × Bool) × ExceptionHistoryState (gameInputs adversary))
    (hresult : exceptionHistorySourceGame dummy adversary budget result ≠ 0)
    (hexception : MonitoredStrongException (result.1, result.2.1))
    (hbound : result.2.1.1.memory.external.hashCalls ≤ budget) :
    result.2.2.1 = true ∨ result.2.2.2 = true := by
  rw [exceptionHistorySourceGame, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨parameter, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨encoding, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨high, _, hresult⟩ := hresult
  rw [RetainedObservation.bind_nonzero] at hresult
  obtain ⟨exposed, _, hresult⟩ := hresult
  rw [initialExceptionHistoryPrior, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨labels, _, hresult⟩ := hresult
  exact initialExceptionHistorySource_event_exception _ adversary encoding dummy exposed high budget
    hbudget result hresult hexception hbound

theorem monitoredSourceGame_event_exception_le_history (dummy : OtsReferenceWords) (adversary : Adversary)
    (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    Pr[fun result => MonitoredStrongException result ∧ result.2.1.memory.external.hashCalls ≤ budget |
        monitoredSourceGame dummy adversary budget (fun _ _ _ _ => false)] ≤
      Pr[fun result => result.2.2.1 = true ∧ result.2.1.1.memory.external.hashCalls ≤ budget |
          exceptionHistorySourceGame dummy adversary budget] +
      Pr[fun result => result.2.2.2 = true | exceptionHistorySourceGame dummy adversary budget] := by
  rw [← exceptionHistorySourceGame_erasure dummy adversary budget, probEvent_map]
  apply le_trans ?_ (probEvent_or_le _ _ _)
  apply probEvent_mono
  intro result hsupport ⟨hexception, hbound⟩
  have hresult := probOutput_ne_zero_of_mem_support hsupport
  rw [SPMF.probOutput_eq_apply] at hresult
  rcases exceptionHistorySourceGame_event_exception dummy adversary budget hbudget result hresult hexception hbound with h | h
  · exact Or.inl ⟨h, hbound⟩
  · exact Or.inr h

theorem exceptionHistorySourceGame_event_cache_le (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat) :
    Pr[fun result => result.2.2.1 = true ∧ result.2.1.1.memory.external.hashCalls ≤ budget |
      exceptionHistorySourceGame dummy adversary budget] ≤ (budget : ENNReal) * certificateCacheExceptionRate := by
  unfold exceptionHistorySourceGame
  apply probEvent_bind_le_of_forall_le
  intro parameter _
  apply probEvent_bind_le_of_forall_le
  intro encoding _
  apply probEvent_bind_le_of_forall_le
  intro high _
  apply probEvent_bind_le_of_forall_le
  intro exposed _
  unfold initialExceptionHistoryPrior
  apply probEvent_bind_le_of_forall_le
  intro labels _
  exact initialExceptionHistorySource_event_cache_le _ adversary encoding dummy exposed high budget

theorem forgeEventAdvantage_le_native_bound (dummy : OtsReferenceWords)
    (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf)) (adversary : Adversary)
    (budget : Nat) (hbudget : budget ≤ 2 ^ 127) :
    forgeEventAdvantage scheme adversary budget ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) +
        (budget : ENNReal) * fullCertificateExcessRate +
        ((budget : ENNReal) * certificateCacheExceptionRate + proposalPrefixExceptionBound) :=
  (forgeEventAdvantage_le_monitored_bound_add_exception dummy hdummy adversary budget (fun _ _ _ _ => false) hbudget).trans
    (add_le_add le_rfl ((monitoredSourceGame_event_exception_le_history dummy adversary budget hbudget).trans
      (add_le_add (exceptionHistorySourceGame_event_cache_le dummy adversary budget)
        (exceptionHistorySourceGame_prefix_le dummy adversary budget))))

end SphincsSecurity.Concrete.RetainedResidual

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

theorem security127_event_of_large_budget (q : Nat) (hlarge : budgetSplit ≤ q) (adversary : Adversary) :
    forgeEventAdvantage scheme adversary q ≤ (q : ENNReal) / 2 ^ 127 := by
  by_cases hsmall : q ≤ 2 ^ 127
  · exact (RetainedResidual.forgeEventAdvantage_le_native_bound fixedReferenceDummy
      (fun _ _ _ => fixedReferenceDummyWord_valid) adversary q hsmall).trans
        (native_bound_le_security127 q hlarge hsmall)
  · apply probEvent_le_one.trans
    calc
      (1 : ENNReal) = (2 ^ 127 : ENNReal) / 2 ^ 127 := (ENNReal.div_self (by positivity) (by finiteness)).symm
      _ ≤ _ := ENNReal.div_le_div_right (by exact_mod_cast (show 2 ^ 127 ≤ q by omega)) _

end SphincsSecurity.Concrete
