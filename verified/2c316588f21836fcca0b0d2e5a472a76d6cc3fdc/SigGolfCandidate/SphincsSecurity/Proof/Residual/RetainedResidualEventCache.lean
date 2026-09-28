import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualCacheHistory
import SigGolfCandidate.SphincsSecurity.Proof.Event.TruncatedCharge
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualEventPotential
/-!
# The cache exception, counted within the budget

The cache-exception weight grows by at most the exception rate per message-digest call. Counted only
on paths that stay within the budget, with the rate paid for every hash call still left, it is a
supermartingale; inside a signing request only the digest loop touches the cache, and the loop's hash
calls are part of the request's. So the probability that the cache becomes exceptional while the whole
run stays within `q` calls is at most `q` times the rate, whatever the adversary does.
-/
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting ResidualByteAction
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
open FtsProbeSimulation (messageAnswers MessageHashInput messageHashCharge)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalEncodingInputs canonicalGraphInputs instFintypePosition hashInputs sourceInputs
  signDigestLoop certificateCacheExceptionWeight
set_option backward.isDefEq.respectTransparency false

theorem certificateCacheExceptionWeight_rom_rate (key : SecretKey) (query : OracleWorld.Domain)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) :
    (∑' result, Pr[= result | (romImpl query).run cache] * certificateCacheExceptionWeight key result.2) ≤
      certificateCacheExceptionWeight key cache + (if query matches .inr _ then certificateCacheExceptionRate else 0) := by
  refine (expected_certificateCacheExceptionWeight_rom key query cache hfinite).trans (add_le_add le_rfl ?_)
  cases query with
  | inl sample => simp [hashQueryCharge]
  | inr input =>
      simp only [hashQueryCharge, Sum.elim_inr, messageHashCharge, if_true]
      split_ifs <;> simp

theorem truncatedPotential_mono (potential : QueryCache HashSpec → ℝ≥0∞) (rate : ℝ≥0∞) (budget start cost loop : Nat)
    (cache : QueryCache HashSpec) (hloop : loop ≤ cost) :
    truncatedPotential potential rate budget (start + cost) cache ≤ truncatedPotential potential rate (budget - start) loop cache := by
  unfold truncatedPotential
  by_cases h : start + cost ≤ budget
  · rw [if_pos h, if_pos (by omega)]
    exact add_le_add le_rfl (mul_le_mul' le_rfl (Nat.cast_le.mpr (by omega)))
  · rw [if_neg h]
    exact zero_le

theorem expected_le_of_pointwise' {Sample : Type} (law : SPMF Sample) (f : Sample → ℝ≥0∞) (bound : ℝ≥0∞)
    (h : ∀ sample, f sample ≤ bound) : (∑' sample, Pr[= sample | law] * f sample) ≤ bound := by
  calc
    _ ≤ ∑' sample, Pr[= sample | law] * bound := ENNReal.tsum_le_tsum fun sample => mul_le_mul' le_rfl (h sample)
    _ ≤ bound := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)

theorem expected_publicSigningWork_truncated_le (known : Labels) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (budget start : Nat) :
    (∑' result, Pr[= result | (simulateQ romImpl
        (ResidualByteFrontend.publicSigningWork key.parameter key.root known words selections message)).run cache] *
      truncatedPotential (certificateCacheExceptionWeight key) certificateCacheExceptionRate budget
        (start + result.1.1.2.hashCalls) result.2) ≤
      certificateCacheExceptionWeight key cache + certificateCacheExceptionRate * ((budget - start : Nat) : ℝ≥0∞) := by
  rw [publicSigningWork_eq_digestWork, simulateQ_map, StateT.run_map, tsum_probOutput_map_mul,
    publicDigestLoop_eq, simulateQ_boundaryComputation]
  have hgeneric := expected_truncatedPotential_le (certificateCacheExceptionWeight key) certificateCacheExceptionRate
    (certificateCacheExceptionWeight_rom_rate key) (signDigestLoop digestAttemptLimit key message) cache hfinite (budget - start)
  rw [← boundaryRun_count key.parameter (signDigestLoop digestAttemptLimit key message) cache, tsum_probOutput_map_mul] at hgeneric
  refine le_trans ?_ hgeneric
  apply ENNReal.tsum_le_tsum
  rintro ⟨⟨selected, trace⟩, after⟩
  apply mul_le_mul' le_rfl
  apply truncatedPotential_mono
  dsimp only [Prod.map, id]
  unfold digestWork
  cases selected with
  | none => exact le_rfl
  | some value =>
      simp only [SigningBoundaryTrace.hashCalls_mul]
      exact Nat.le_add_right _ _

theorem completePublicSigningRecord_trace (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (record : PublicSigningRecord) :
    (completePublicSigningRecord ftsSecret record).2 = record.2 := by
  unfold completePublicSigningRecord
  split <;> rfl

attribute [local irreducible] lazyRun environment ResidualByteFrontend.jointSigningProgram in
theorem expected_lazySigning_truncated_le (message : Message) (state : State inputs)
    (hinputs : requestInputs key (.inr message) ⊆ inputs)
    (ha : ∀ coordinate, (state.candidates coordinate).Nonempty)
    (hcovered : ResidualByteFrontend.RowsCovered inputs (project state)) (hfinite : Finite state.memory.external.cache)
    (budget : Nat) :
    (∑' result, Pr[= result | lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
        (simulateQ (embed inputs state.memory.routing)
          (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state] *
      truncatedPotential (certificateCacheExceptionWeight key) certificateCacheExceptionRate budget
        result.2.memory.external.hashCalls result.2.memory.external.cache) ≤
      certificateCacheExceptionWeight key state.memory.external.cache +
        certificateCacheExceptionRate * ((budget - state.memory.external.hashCalls : Nat) : ℝ≥0∞) := by
  have hin := digestInputs_of_request key inputs words selections message state.memory.routing.known hinputs
  have hloop : hashInputs (publicDigestLoop key.parameter key.root message digestAttemptLimit) ⊆ inputs := by
    simpa only [publicDigestLoop_eq] using hin
  set law := lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
    (simulateQ (embed inputs state.memory.routing)
      (ResidualByteFrontend.jointSigningProgram inputs key.parameter key.root state.memory.routing.known words selections message)) state
  let weight : Option SigningRecord × QueryCache HashSpec → ℝ≥0∞ := fun result =>
    result.1.elim 0 (fun record => truncatedPotential (certificateCacheExceptionWeight key) certificateCacheExceptionRate budget
      (state.memory.external.hashCalls + record.2.hashCalls) result.2)
  have hpoint : (∑' result, Pr[= result | law] *
      truncatedPotential (certificateCacheExceptionWeight key) certificateCacheExceptionRate budget
        result.2.memory.external.hashCalls result.2.memory.external.cache) =
      ∑' result, Pr[= result | law] * weight (cacheResult result) := by
    apply tsum_congr
    intro result
    by_cases hr : Pr[= result | law] = 0
    · simp only [hr, zero_mul]
    rw [SPMF.probOutput_eq_apply] at hr
    obtain ⟨record, hrecord, hmemory⟩ := lazyRun_jointSigningProgram_memory_trace key.parameter inputs hencoding words publicReplies
      selections rows state.memory.routing key.root message hloop state ha hcovered result hr
    congr 1
    simp only [weight, cacheResult, hrecord, Option.elim_some, hmemory]
    rfl
  rw [hpoint, ← tsum_probOutput_map_mul law cacheResult weight,
    lazyRun_jointSigningProgram_cache key.parameter inputs hencoding words publicReplies selections rows state.memory.routing
      key.root message hloop state ha hcovered, tsum_probOutput_bind_mul]
  apply expected_le_of_pointwise'
  intro actual
  rw [tsum_probOutput_map_mul]
  simp only [weight, Option.elim_some, completePublicSigningRecord_trace]
  exact expected_publicSigningWork_truncated_le key words selections state.memory.routing.known message
    state.memory.external.cache hfinite budget state.memory.external.hashCalls

variable (budget : Nat) (required : Finset IndexGroup) (stopAfter : CertificateStopRule)

theorem monitoredStep_hashCalls_mono (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs)
    (result : Option ((OracleWorld + SigningSpec).Range input) × MonitoredState inputs)
    (hresult : monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state result ≠ 0) :
    state.1.memory.external.hashCalls ≤ result.2.1.memory.external.hashCalls := by
  have h := map_nonzero _ (fun result => (result.1, result.2.1)) result hresult
  rw [monitoredStep_erasure] at h
  exact lazyRun_request_hashCalls_mono inputs words publicReplies selections rows key hencoding input hinputs state.1
    hvalid.1 hvalid.2 _ h

attribute [local irreducible] lazyRun environment ResidualByteFrontend.jointSigningProgram in
theorem expected_monitoredStep_truncatedCache_le (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs)
    (hbound : CacheSizeBound state.1.memory) (q : Nat) :
    (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      truncatedPotential (certificateCacheExceptionWeight key) certificateCacheExceptionRate q
        result.2.1.memory.external.hashCalls result.2.1.memory.external.cache) ≤
      truncatedPotential (certificateCacheExceptionWeight key) certificateCacheExceptionRate q
        state.1.memory.external.hashCalls state.1.memory.external.cache := by
  by_cases hwithin : state.1.memory.external.hashCalls ≤ q
  swap
  · apply expected_le_of_pointwise
    intro result hresult
    have hm := monitoredStep_hashCalls_mono key inputs hencoding words publicReplies selections rows budget required stopAfter
      input state hvalid hinputs result hresult
    unfold truncatedPotential
    rw [if_neg (by omega)]
    exact zero_le
  have hright : truncatedPotential (certificateCacheExceptionWeight key) certificateCacheExceptionRate q
      state.1.memory.external.hashCalls state.1.memory.external.cache =
      certificateCacheExceptionWeight key state.1.memory.external.cache +
        certificateCacheExceptionRate * ((q - state.1.memory.external.hashCalls : Nat) : ℝ≥0∞) := by
    unfold truncatedPotential
    rw [if_pos hwithin]
  rw [hright]
  have hfinite : Finite state.1.memory.external.cache := Finite.of_enncard_le hbound
  cases input with
  | inr message =>
      rw [monitoredStep, tsum_probOutput_bind_mul]
      apply expected_le_of_pointwise'
      intro annotation
      rw [tsum_probOutput_map_mul]
      have hproj (raw : Option SigningRecord × State inputs) :
          (monitoredSigningResult key budget required stopAfter message annotation state raw).2.1.memory.external =
            raw.2.memory.external := by
        rcases raw with ⟨answer, after⟩
        cases answer <;> rfl
      simp only [hproj]
      exact expected_lazySigning_truncated_le key inputs hencoding words publicReplies selections rows message state.1 hinputs
        hvalid.1 hvalid.2 hfinite q
  | inl world =>
      rw [monitoredStep, tsum_probOutput_map_mul, lazyRun_externalProgram]
      have hproj (raw : Option (OracleWorld.Range world) × State inputs) :
          (monitoredWorldResult key budget required stopAfter world state raw).2.1 = raw.2 := rfl
      simp only [hproj]
      cases world with
      | inl sample =>
          apply expected_le_of_pointwise
          intro raw hraw
          have hsame : raw.2 = state.1 := by
            rw [← bind_pure (liftM (OracleWorld.query (.inl sample))), lazyByteRun_random_bind,
              RetainedObservation.bind_nonzero] at hraw
            obtain ⟨answer, _, hraw⟩ := hraw
            rw [lazyByteRun_pure] at hraw
            simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hraw
            rw [hraw]
          rw [hsame, ← hright]
      | inr hash =>
          have hh (raw : Option (OracleWorld.Range (.inr hash)) × State inputs)
              (hraw : lazyByteRun key.parameter inputs hencoding words publicReplies selections rows state.1.memory.routing
                (liftM (OracleWorld.query (.inr hash))) state.1 raw ≠ 0) :
              raw.2.memory.external.hashCalls = state.1.memory.external.hashCalls + 1 :=
            lazyByteRun_world_hashCalls key.parameter inputs hencoding words publicReplies selections rows state.1.memory.routing
              (.inr hash) hinputs state.1 hvalid.1 raw hraw
          by_cases hroom : state.1.memory.external.hashCalls + 1 ≤ q
          · have hkernel := expected_lazyWorld_cacheWeight_le key inputs hencoding words publicReplies selections rows
              state.1.memory.routing (.inr hash) state.1 hinputs hvalid.1 hvalid.2 hbound
            have hcharge : hashQueryCharge (fun cache hash => messageHashCharge key.parameter cache hash * certificateCacheExceptionRate)
                state.1.memory.external.cache (.inr hash) ≤ certificateCacheExceptionRate := by
              simp only [hashQueryCharge, Sum.elim_inr, messageHashCharge]
              split_ifs <;> simp
            calc
              _ ≤ ∑' raw, Pr[= raw | lazyByteRun key.parameter inputs hencoding words publicReplies selections rows
                    state.1.memory.routing (liftM (OracleWorld.query (.inr hash))) state.1] *
                  (certificateCacheExceptionWeight key raw.2.memory.external.cache +
                    certificateCacheExceptionRate * ((q - (state.1.memory.external.hashCalls + 1) : Nat) : ℝ≥0∞)) := by
                apply ENNReal.tsum_le_tsum
                intro raw
                by_cases hr : Pr[= raw | lazyByteRun key.parameter inputs hencoding words publicReplies selections rows
                    state.1.memory.routing (liftM (OracleWorld.query (.inr hash))) state.1] = 0
                · simp only [hr, zero_mul, le_refl]
                rw [SPMF.probOutput_eq_apply] at hr
                apply mul_le_mul' le_rfl
                unfold truncatedPotential
                rw [hh raw hr, if_pos hroom]
              _ ≤ (certificateCacheExceptionWeight key state.1.memory.external.cache + certificateCacheExceptionRate) +
                    certificateCacheExceptionRate * ((q - (state.1.memory.external.hashCalls + 1) : Nat) : ℝ≥0∞) := by
                simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right]
                apply add_le_add (hkernel.trans (add_le_add le_rfl hcharge))
                exact mul_le_of_le_one_left' tsum_probOutput_le_one
              _ = _ := by
                rw [add_assoc]
                congr 1
                have : q - state.1.memory.external.hashCalls = (q - (state.1.memory.external.hashCalls + 1)) + 1 := by omega
                rw [this]
                push_cast
                ring
          · apply expected_le_of_pointwise
            intro raw hraw
            unfold truncatedPotential
            rw [hh raw hraw, if_neg hroom]
            exact zero_le

noncomputable def eventCacheHistory {inputs : Finset HashInput} (key : SecretKey) (q : Nat) (state : ExceptionHistoryState inputs) :
    ℝ≥0∞ :=
  if state.1.1.memory.external.hashCalls ≤ q then
    cacheHistoryWeight key state + certificateCacheExceptionRate * ((q - state.1.1.memory.external.hashCalls : Nat) : ℝ≥0∞)
  else 0

theorem expected_exceptionHistoryStep_eventCache_le (input : (OracleWorld + SigningSpec).Domain) (state : ExceptionHistoryState inputs)
    (hvalid : MonitoredValid inputs state.1) (hinputs : requestInputs key input ⊆ inputs) (hbound : CacheSizeBound state.1.1.memory)
    (q : Nat) :
    (∑' result, Pr[= result | exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter input state] *
      eventCacheHistory key q result.2) ≤ eventCacheHistory key q state := by
  rw [exceptionHistoryStep, tsum_probOutput_map_mul]
  by_cases hwithin : state.1.1.memory.external.hashCalls ≤ q
  swap
  · apply expected_le_of_pointwise
    intro result hresult
    have hm := monitoredStep_hashCalls_mono key inputs hencoding words publicReplies selections rows budget required stopAfter
      input state.1 hvalid hinputs result hresult
    unfold eventCacheHistory
    rw [if_neg (by dsimp only; omega)]
    exact zero_le
  have hfinite : Finite state.1.1.memory.external.cache := Finite.of_enncard_le hbound
  have hright : eventCacheHistory key q state =
      cacheHistoryWeight key state + certificateCacheExceptionRate * ((q - state.1.1.memory.external.hashCalls : Nat) : ℝ≥0∞) := by
    unfold eventCacheHistory
    rw [if_pos hwithin]
  rw [hright]
  cases hflag : state.2.1 with
  | true =>
      apply expected_le_of_pointwise
      intro result hresult
      have hm := monitoredStep_hashCalls_mono key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state.1 hvalid hinputs result hresult
      unfold eventCacheHistory cacheHistoryWeight
      simp only [exceptionHistoryUpdate, hflag, Bool.true_or, if_true]
      split_ifs with hr
      · exact add_le_add le_rfl (mul_le_mul' le_rfl (Nat.cast_le.mpr (by omega)))
      · exact zero_le
  | false =>
      have hstate : cacheHistoryWeight key state = certificateCacheExceptionWeight key state.1.1.memory.external.cache := by
        simp only [cacheHistoryWeight, hflag, Bool.false_eq_true, if_false]
      rw [hstate]
      by_cases hbefore : CertificateCacheExceptional key state.1.1.memory.external.cache
      · apply expected_le_of_pointwise
        intro result hresult
        have hm := monitoredStep_hashCalls_mono key inputs hencoding words publicReplies selections rows budget required stopAfter
          input state.1 hvalid hinputs result hresult
        have hone := certificateCacheExceptionWeight_bad key _ hfinite hbefore
        unfold eventCacheHistory cacheHistoryWeight
        simp only [exceptionHistoryUpdate, hflag, Bool.false_or, decide_eq_true hbefore, Bool.true_or, if_true]
        split_ifs with hr
        · exact add_le_add hone (mul_le_mul' le_rfl (Nat.cast_le.mpr (by omega)))
        · exact zero_le
      · refine le_trans ?_ (expected_monitoredStep_truncatedCache_le key inputs hencoding words publicReplies selections rows budget
          required stopAfter input state.1 hvalid hinputs hbound q |>.trans (le_of_eq ?_))
        · apply ENNReal.tsum_le_tsum
          intro result
          by_cases hr : Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter
              input state.1] = 0
          · simp only [hr, zero_mul, le_refl]
          apply mul_le_mul' le_rfl
          rw [SPMF.probOutput_eq_apply] at hr
          have hb := monitoredStep_cacheSizeBound key inputs hencoding words publicReplies selections rows budget required stopAfter
            input state.1 hvalid hinputs hbound result hr
          unfold eventCacheHistory cacheHistoryWeight truncatedPotential
          simp only [exceptionHistoryUpdate, hflag, Bool.false_or, decide_eq_false hbefore]
          split_ifs with hc hex
          · exact add_le_add (certificateCacheExceptionWeight_bad key _ (Finite.of_enncard_le hb) (by simpa using hex)) le_rfl
          · exact le_rfl
          · exact le_rfl
        · unfold truncatedPotential
          rw [if_pos hwithin]

theorem expected_exceptionHistoryRun_eventCache_le {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : ExceptionHistoryState inputs) (hvalid : MonitoredValid inputs state.1)
    (hinputs : sourceInputs key computation ⊆ inputs) (hbound : CacheSizeBound state.1.1.memory) (q : Nat) :
    (∑' result, Pr[= result | exceptionHistoryRun key inputs hencoding words publicReplies selections rows budget required stopAfter computation state] *
      eventCacheHistory key q result.2) ≤ eventCacheHistory key q state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value => simp only [exceptionHistoryRun_pure, tsum_probOutput_pure_mul, le_refl]
  | query_bind input next ih =>
      rw [exceptionHistoryRun_query_bind, tsum_probOutput_bind_mul]
      have hin := (requestInputs_subset key input next).trans hinputs
      refine le_trans ?_ (expected_exceptionHistoryStep_eventCache_le key inputs hencoding words publicReplies selections rows budget
        required stopAfter input state hvalid hin hbound q)
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : Pr[= result | exceptionHistoryStep key inputs hencoding words publicReplies selections rows budget required stopAfter
          input state] = 0
      · simp only [hr, zero_mul, le_refl]
      apply mul_le_mul' le_rfl
      rw [SPMF.probOutput_eq_apply] at hr
      have hn := (exceptionHistoryStep_support key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state result hr).1
      rcases result with ⟨answer, after⟩
      cases answer with
      | none => simp only [Option.elim_none, tsum_probOutput_pure_mul, le_refl]
      | some answer =>
          have hv := monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter
            input state.1 hvalid _ hn
          have hb := monitoredStep_cacheSizeBound key inputs hencoding words publicReplies selections rows budget required stopAfter
            input state.1 hvalid hin hbound _ hn
          exact ih answer after hv ((sourceInputs_next_subset key input next answer).trans hinputs) hb

end SphincsSecurity.Concrete.RetainedResidual
