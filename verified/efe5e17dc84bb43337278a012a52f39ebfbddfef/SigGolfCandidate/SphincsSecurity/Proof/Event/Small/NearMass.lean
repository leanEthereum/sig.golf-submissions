import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.Probes
import SigGolfCandidate.SphincsSecurity.Proof.Forced.FtsGuessNearAssembly
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateCreationBudget
/-!
# The near-certificate creation mass of the capped adversary

A monitored step adds to the creation mass at most the macro cost of the request, which is at most
its visible charge. So on every run of the capped adversary the creation mass stays below its
budget, whatever the monitor's own budget: the adversary's charges sum to at most
`budget - keygenHashCost`, and the verifier adds at most `verifyHashBound < keygenHashCost`.
-/

namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec ENNReal
open FtsGuessSigning (Coordinate)
open SecretGuessObservation (initialState)
open EventSmall
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition

variable (parameter : PublicParameter) (root : Digest)
  (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (labels : CanonicalGraphLabels)
  (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs parameter ⊆ inputs)
  (selections : ReferenceFamily) (rows : CanonicalEncodingRows) (dummy : OtsReferenceWords) (slot : Nat)
  (budget : Nat) (required : Finset IndexGroup) (stopAfter : CertificateStopRule)

theorem macro_le_visWeight (input : (OracleWorld + SigningSpec).Domain) :
    (signingMacroHashCost input : ENNReal) ≤ (visWeight input : ENNReal) := by
  rcases input with (input | input) | message
  · simp [signingMacroHashCost, visWeight]
  · simp [signingMacroHashCost, visWeight]
  · simp only [signingMacroHashCost, visWeight]
    exact_mod_cast two_pow_ftsTreeHeight_le_ftsOpenHashCost.trans ftsOpenHashCost_le_signCharge

theorem certificateMonitorMass_le_visWeight (key : SecretKey) (input : (OracleWorld + SigningSpec).Domain)
    (state : CertificateMonitorState) :
    certificateMonitorMass key budget input state ≤ (visWeight input : ENNReal) := by
  rw [certificateMonitorMass]
  split
  · exact (targetCreationMultiplier_le_macro key state.1 input).trans (macro_le_visWeight input)
  · exact zero_le

private theorem map_nonzero_source {First Result : Type} (function : First → Result) (law : SPMF First) (result : Result)
    (h : (function <$> law) result ≠ 0) : ∃ first, law first ≠ 0 ∧ result = function first := by
  simpa only [map_eq_bind_pure_comp, RetainedObservation.bind_nonzero, Function.comp_def,
    ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] using h

theorem monitoredStep_mass (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState)
    (step : AdversaryStep input × MonitoredState)
    (hstep : monitoredStep parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      input state step ≠ 0) :
    step.2.2.creationMass ≤ state.2.creationMass + (visWeight input : ENNReal) := by
  cases input with
  | inl input =>
      rw [monitoredStep, monitoredWorldStep] at hstep
      obtain ⟨result, _, rfl⟩ := map_nonzero_source _ _ _ hstep
      rw [certificateMonitorUpdate_creationMass]
      exact add_le_add le_rfl (certificateMonitorMass_le_visWeight budget _ _ _)
  | inr message =>
      rw [monitoredStep, monitoredSignStep, RetainedObservation.bind_nonzero] at hstep
      obtain ⟨annotation, _, hstep⟩ := hstep
      obtain ⟨result, _, rfl⟩ := map_nonzero_source _ _ _ hstep
      rw [certificateMonitorUpdate_creationMass]
      exact add_le_add le_rfl (certificateMonitorMass_le_visWeight budget _ _ _)


theorem monitoredRun_mass {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result) (weight : Nat)
    (hweight : WeightBound computation weight) (state : MonitoredState) (result : _)
    (hresult : monitoredRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) :
    result.2.2.creationMass ≤ state.2.creationMass + (weight : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing weight state result with
  | pure value =>
      rw [monitoredRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact le_self_add
  | query_bind input next ih =>
      rw [weightBound_query_bind_iff] at hweight
      rw [monitoredRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source _ _ _ hresult
      have hfirst := monitoredStep_mass parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter input state step hstep
      have hrest := ih step.1.1.1 _ (hweight.2 _) step.2 tail htail
      calc
        _ ≤ step.2.2.creationMass + ((weight - visWeight input : Nat) : ENNReal) := hrest
        _ ≤ state.2.creationMass + (visWeight input : ENNReal) + ((weight - visWeight input : Nat) : ENNReal) :=
          add_le_add hfirst le_rfl
        _ = state.2.creationMass + (weight : ENNReal) := by
          rw [add_assoc]
          congr 1
          exact_mod_cast (show visWeight input + (weight - visWeight input) = weight by have := hweight.1; omega)

theorem monitoredWorldRun_mass {Result : Type} (computation : OracleComp OracleWorld Result) (bound : Nat)
    (hbound : computation.IsQueryBoundP (fun input : OracleWorld.Domain => input matches .inr _) bound)
    (state : MonitoredState) (result : _)
    (hresult : monitoredWorldRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      computation state result ≠ 0) :
    result.2.2.creationMass ≤ state.2.creationMass + (bound : ENNReal) := by
  induction computation using OracleComp.inductionOn generalizing bound state result with
  | pure value =>
      rw [monitoredWorldRun_pure] at hresult
      simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hresult
      subst result
      exact le_self_add
  | query_bind input next ih =>
      rw [isQueryBoundP_query_bind_iff] at hbound
      rw [monitoredWorldRun_query_bind, RetainedObservation.bind_nonzero] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      obtain ⟨tail, htail, rfl⟩ := map_nonzero_source _ _ _ hresult
      have hfirst := monitoredStep_mass parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required
        stopAfter (.inl input) state step hstep
      have hrest := ih step.1.1.1 _ (hbound.2 _) step.2 tail htail
      change tail.2.2.creationMass ≤ _
      cases input with
      | inl sample =>
          simp only [Bool.false_eq_true, if_false] at hrest
          simp only [visWeight, Nat.cast_zero, add_zero] at hfirst
          exact hrest.trans (add_le_add hfirst le_rfl)
      | inr hash =>
          simp only [if_true] at hrest
          simp only [visWeight, Nat.cast_one] at hfirst
          have hpos : 0 < bound := by simpa only [if_true, not_true_eq_false, false_or] using hbound.1
          calc
            _ ≤ step.2.2.creationMass + ((bound - 1 : Nat) : ENNReal) := hrest
            _ ≤ state.2.creationMass + 1 + ((bound - 1 : Nat) : ENNReal) := add_le_add hfirst le_rfl
            _ = state.2.creationMass + (bound : ENNReal) := by
              rw [add_assoc]
              congr 1
              exact_mod_cast (show 1 + (bound - 1) = bound by omega)


theorem monitoredCompletedRun_mass_visAdversary (adversary : Adversary) (visBudget : Nat) (hvis : keygenHashCost + 1 ≤ visBudget)
    (spent : Nat) (stopped : Bool) (result : Completed × MonitoredState)
    (hresult : monitoredCompletedRun parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
      (visAdversary adversary visBudget) (nearStart spent stopped) result ≠ 0) :
    result.2.2.creationMass ≤ (visBudget : ENNReal) := by
  rw [monitoredCompletedRun, RetainedObservation.bind_nonzero] at hresult
  obtain ⟨before, hbefore, hresult⟩ := hresult
  obtain ⟨checked, hchecked, rfl⟩ := map_nonzero_source _ _ _ hresult
  have hA := monitoredRun_mass parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    _ _ (visAdversary_weightBound adversary visBudget ⟨root, parameter⟩ hvis) _ before hbefore
  have hV := monitoredWorldRun_mass parameter root otsSecret labels inputs hencoding selections rows dummy slot budget required stopAfter
    _ verifyHashBound (isQueryBoundP_liftM_of_evenBound _ _ (evenBound_verify _ _ _)) before.2 checked hchecked
  have hK := verifyHashBound_lt_keygen
  have hzero : (nearStart spent stopped).2.creationMass = 0 := rfl
  rw [hzero, zero_add] at hA
  change checked.2.2.creationMass ≤ _
  calc
    _ ≤ before.2.2.creationMass + (verifyHashBound : ENNReal) := hV
    _ ≤ ((visBudget - keygenHashCost : Nat) : ENNReal) + (verifyHashBound : ENNReal) := add_le_add hA le_rfl
    _ ≤ _ := by exact_mod_cast (show visBudget - keygenHashCost + verifyHashBound ≤ visBudget by omega)


end SphincsSecurity.Concrete.FtsGuessHash

namespace SphincsSecurity.Concrete.FtsGuessHash

open _root_.OracleComp OracleSpec ENNReal
open SecretGuessObservation (initialState)
open EventSmall
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs canonicalGraphGameInputs instFintypePosition

private theorem pmf_mem_of_evalDist' {Result : Type} (law : PMF Result) (result : Result)
    (hresult : result ∈ support 𝒮[law]) : result ∈ law.support := by
  change result ∈ (𝒮[law]).support at hresult
  simpa only [PMF.evalSPMF_eq, SPMF.support_liftM] using hresult

theorem cachedNearGame_le_visAdversary (dummy : OtsReferenceWords) (adversary : Adversary) (visBudget : Nat)
    (hvis : keygenHashCost + 1 ≤ visBudget) (q : Nat) (hbound : HasHashQueryBound scheme (visAdversary adversary visBudget) q)
    (hbudget : q ≤ 2 ^ 127) (slot : Nat) :
    Pr[fun hit => hit = true | cachedNearGame dummy (visAdversary adversary visBudget) slot] ≤ nearMixedBound visBudget q := by
  unfold cachedNearGame
  refine probEvent_bind_le_of_forall_le fun parameter hparameter => ?_
  have hparameter := mem_support_sampleParameter_of_evalSPMF hparameter
  refine probEvent_bind_le_of_forall_le fun otsSecret _ => ?_
  refine probEvent_bind_le_of_forall_le fun selections hselections => ?_
  refine probEvent_bind_le_of_forall_le fun rows hrows => ?_
  refine probEvent_bind_le_of_forall_le fun labels _ => ?_
  rw [probEvent_map]
  have hsel := pmf_mem_of_evalDist' _ _ hselections
  have hrow := pmf_mem_of_evalDist' _ _ hrows
  have hauxiliary : ∀ seed : canonicalGraphGameInputs (visAdversary adversary visBudget) → HashOutput,
      (⟨selections, Function.uncurry rows, seed⟩ : ReferenceAuxiliary (canonicalGraphGameInputs (visAdversary adversary visBudget))) ∈
        (referenceAuxiliarySample (canonicalGraphGameInputs (visAdversary adversary visBudget))).support :=
    fun seed => referenceAuxiliary_mem_support _ selections hsel rows hrow seed
  have hcovered : ∀ monitor, CoveredRun parameter (canonicalGraphRoot labels) otsSecret labels
      (canonicalGraphGameInputs (visAdversary adversary visBudget))
      ((visAdversary adversary visBudget).main ⟨canonicalGraphRoot labels, parameter⟩) ((∅, initialState PUnit.unit), monitor) :=
    fun _ secrets _ =>
      coveredInputs_main_subset (visAdversary adversary visBudget)
        ⟨parameter, canonicalGraphRoot labels, otsSecret, FtsGuessSigning.secretTable.symm secrets, graphTop labels⟩ hparameter
  have hwork : ∀ result : Completed × CachedState,
      nearLaw parameter (canonicalGraphRoot labels) otsSecret labels (canonicalGraphGameInputs (visAdversary adversary visBudget))
        (canonicalEncodingInputs_subset_gameInputs (visAdversary adversary visBudget) parameter) selections (Function.uncurry rows)
        dummy slot (visAdversary adversary visBudget) result ≠ 0 →
        keygenHashCost + completedWork result.1 ≤ q := by
    intro result hresult
    have h := cachedForcedRun_original_budget dummy (visAdversary adversary visBudget) q slot hbound parameter hparameter otsSecret labels
      ⟨selections, Function.uncurry rows, fun _ => Classical.arbitrary _⟩ (hauxiliary _)
    have hsel' : (⟨selections, Function.uncurry rows, fun _ => Classical.arbitrary _⟩ :
      ReferenceAuxiliary (canonicalGraphGameInputs (visAdversary adversary visBudget))).selections = selections := rfl
    have hrows' : (⟨selections, Function.uncurry rows, fun _ => Classical.arbitrary _⟩ :
      ReferenceAuxiliary (canonicalGraphGameInputs (visAdversary adversary visBudget))).rows = Function.uncurry rows := rfl
    rw [hsel', hrows'] at h
    exact (h result hresult).1
  have h := nearLaw_certificate_mixed_le parameter (canonicalGraphRoot labels) otsSecret labels
    (canonicalGraphGameInputs (visAdversary adversary visBudget))
    (canonicalEncodingInputs_subset_gameInputs (visAdversary adversary visBudget) parameter) selections (Function.uncurry rows) dummy slot
    hauxiliary q visBudget (visAdversary adversary visBudget) hbudget hcovered
    (fun required spent stopped result hresult => monitoredCompletedRun_mass_visAdversary parameter (canonicalGraphRoot labels) otsSecret labels
      _ _ selections (Function.uncurry rows) dummy slot q required _ adversary visBudget hvis spent stopped result hresult) hwork
  simpa only [Function.comp_def, decide_eq_true_eq] using h

theorem forcedNearGame_le_visAdversary (dummy : OtsReferenceWords) (adversary : Adversary) (visBudget : Nat)
    (hvis : keygenHashCost + 1 ≤ visBudget) (q : Nat) (hbound : HasHashQueryBound scheme (visAdversary adversary visBudget) q)
    (hbudget : q ≤ 2 ^ 127) (slot : Nat) :
    Pr[fun hit => hit = true | forcedNearGame dummy (visAdversary adversary visBudget) slot] ≤ nearMixedBound visBudget q := by
  rw [forcedNearGame_cached]
  exact cachedNearGame_le_visAdversary dummy adversary visBudget hvis q hbound hbudget slot

end SphincsSecurity.Concrete.FtsGuessHash
