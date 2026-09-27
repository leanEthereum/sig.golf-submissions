import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualResources
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateCreationBudget
/-!
# Structural creation-mass bound on the monitored run

On every path of the monitored run the creation mass is at most the monitor budget, whatever the
number of hash calls.
-/
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
set_option backward.isDefEq.respectTransparency false

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)

attribute [local irreducible] lazyRun environment ResidualByteFrontend.jointSigningProgram
  certificateMonitorUpdate monitoredSigningResult

theorem monitoredStep_creationBudget (input : (OracleWorld + SigningSpec).Domain)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : requestInputs key input ⊆ inputs) (hbefore : CreationBudget budget state.2)
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    CreationBudget budget result.2.2 := by
  cases input with
  | inl input =>
      rw [monitoredStep, map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      cases hr : raw.1 with
      | none =>
          simp only [monitoredWorldResult, hr, Option.elim_none]
          exact creationBudget_stop budget _ hbefore
      | some answer =>
          simp only [monitoredWorldResult, hr, Option.elim_some]
          apply creationBudget_update key budget required stopAfter (.inl input) (monitorView state) 0 _ hbefore
          simp only [proposalOfWorldResult, signingBoundaryTrace_hashCalls_eq, targetCreationMultiplier, monitorView]
          cases input with
          | inl sample => exact le_rfl
          | inr input =>
              simp only [freshWorldTargetHashCost]
              split_ifs <;> norm_num
  | inr message =>
      rw [monitoredStep, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨annotation, _, hresult⟩ := hresult
      rw [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨raw, hraw, hresult⟩ := hresult
      simp only [Function.comp_def, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      have hin := digestInputs_of_request key inputs words selections message state.1.memory.routing.known hinputs
      obtain ⟨record, hr, hm⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies selections rows
        state.1.memory.routing key.root message (by simpa only [publicDigestLoop_eq] using hin) state.1 hvalid.1 hvalid.2 raw hraw
      obtain ⟨other, ho, hmin⟩ := lazyRun_jointSigningProgram_hashCalls_min key inputs hencoding words publicReplies selections rows
        state.1.memory.routing message hin state.1 hvalid.1 hvalid.2 raw hraw
      have heq : other = record := Option.some.inj (ho.symm.trans hr)
      subst other
      have heq : raw = (some record, raw.2) := Prod.ext hr rfl
      rw [heq]
      simp only [monitoredSigningResult]
      apply creationBudget_update key budget required stopAfter (.inr message) (monitorView state) annotation.1 _ hbefore
      change targetCreationMultiplier key state.1.memory.external.cache (.inr message) ≤ record.2.hashCalls
      have hp := mul_le_mul' (le_refl (((2 ^ ftsTreeHeight : Nat) : ENNReal)))
        (freshDigestSelectionProbability_le_one key message state.1.memory.external.cache)
      calc
        _ ≤ ((2 ^ ftsTreeHeight : Nat) : ENNReal) := by simpa only [targetCreationMultiplier, mul_one] using hp
        _ ≤ (ftsOpenHashCost : ENNReal) := Nat.cast_le.mpr two_pow_ftsTreeHeight_le_ftsOpenHashCost
        _ ≤ record.2.hashCalls := Nat.cast_le.mpr hmin

theorem monitoredRun_creationBudget {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state)
    (hinputs : sourceInputs key computation ⊆ inputs) (hbefore : CreationBudget budget state.2)
    (result : Option Result × MonitoredState inputs)
    (hresult : monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state result ≠ 0) :
    CreationBudget budget result.2.2 := by
  induction computation using OracleComp.inductionOn generalizing state result with
  | pure value =>
      rw [monitoredRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact hbefore
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨⟨answer, after⟩, hstep, hresult⟩ := hresult
      have hafter := monitoredStep_creationBudget key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state hvalid ((requestInputs_subset key input next).trans hinputs) hbefore (answer, after) hstep
      cases answer with
      | none =>
          simp only [Option.elim_none, ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
          subst result
          exact hafter
      | some answer =>
          exact ih answer after
            (monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter input state hvalid (some answer, after) hstep)
            ((sourceInputs_next_subset key input next answer).trans hinputs) hafter result hresult

end SphincsSecurity.Concrete.RetainedResidual
