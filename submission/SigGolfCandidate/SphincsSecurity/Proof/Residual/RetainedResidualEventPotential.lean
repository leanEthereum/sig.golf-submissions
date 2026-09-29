import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualPrimitivePotential
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualCreationBudget
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualAccounting
/-!
# The primitive potential truncated at the budget event

The potential of `RetainedResidualPrimitivePotential` pays for the residual hazards and the message
calls out of the remaining budget, which requires every path to stay within the budget. Here the
hazards are counted only while the hash count is within the budget, and the message side pays for
the monitor's creation mass, which the monitor stops accruing once its budget is spent. A signing
request that overshoots the budget is live only if its charge cost fits, and its creation mass is at
most that charge cost, so the remaining budget still pays for it.
-/
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open InterleavedResidual (Routing SigningRecord)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

namespace EventPotential

/-- A live signing request that stays within the budget: its creation mass fits in the budget it consumes. -/
theorem live_within (space probes remaining cost : ℝ) (charge : Nat) (hspace : 0 < space) (hprobes : 0 ≤ probes)
    (hcost : (charge : ℝ) ≤ cost) (hleft : cost ≤ remaining) (hbudget : 2 * (probes + remaining) ≤ space) :
    (charge : ℝ) / space + PrimitiveMessagePotential.value space probes (remaining - cost) ≤
      PrimitiveMessagePotential.value space probes remaining := by
  have hmacro : (0 : ℝ) ≤ charge := Nat.cast_nonneg _
  have hm := PrimitiveMessagePotential.mono_remaining space probes (remaining - cost) (remaining - charge)
    (by linarith) (by linarith) (by linarith)
  have hp := PrimitiveMessagePotential.messages_payment space probes (remaining - charge) charge hspace hprobes
    (by linarith) (by linarith)
  have heq : remaining - charge + charge = remaining := by ring
  rw [heq] at hp
  linarith

/-- A live signing request that overshoots: its creation mass is still paid by what remained. -/
theorem live_over (space probes remaining : ℝ) (charge : Nat) (hspace : 0 < space) (hprobes : 0 ≤ probes)
    (hleft : (charge : ℝ) ≤ remaining) (hbudget : 2 * (probes + remaining) ≤ space) :
    (charge : ℝ) / space ≤ PrimitiveMessagePotential.value space probes remaining := by
  have h := live_within space probes remaining charge charge hspace hprobes le_rfl hleft hbudget
  have hmacro : (0 : ℝ) ≤ charge := Nat.cast_nonneg _
  have hz := PrimitiveMessagePotential.bounds space probes (remaining - charge) (by linarith) (by linarith)
  linarith [hz.1]

end EventPotential

noncomputable def eventGate (budget : Nat) (memory : Memory) (value : ENNReal) : ENNReal :=
  if memory.external.hashCalls ≤ budget then value else 0

noncomputable def eventLivePotential {inputs : Finset HashInput} (budget : Nat) (state : MonitoredState inputs) : ENNReal :=
  state.2.creationMass / 2 ^ digestBits + eventGate budget state.1.memory (primitiveContinuation budget state.1.memory)

noncomputable def eventResultPotential {Result : Type} {inputs : Finset HashInput} (budget : Nat)
    (result : Option Result × MonitoredState inputs) : ENNReal :=
  result.2.2.creationMass / 2 ^ digestBits +
    eventGate budget result.2.1.memory (result.1.elim 1 (fun _ => primitiveContinuation budget result.2.1.memory))

theorem natCast_div_digest (n : Nat) :
    (n : ENNReal) / 2 ^ digestBits = ENNReal.ofReal ((n : ℝ) / 2 ^ digestBits) := by
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast]
  norm_num only [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]

theorem monitor_inactive_of_over {inputs : Finset HashInput} (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs) (haccount : MonitoredAccounting state)
    (hover : budget < state.1.memory.external.hashCalls) : ¬ CertificateMonitorActive key budget input (monitorView state) := by
  intro hactive
  have hspent : state.2.spent ≤ budget := hactive.2.1.2.2
  have heq := haccount hactive.1
  omega

theorem monitor_active_room {inputs : Finset HashInput} (key : SecretKey) (budget : Nat)
    (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs) (haccount : MonitoredAccounting state)
    (hactive : CertificateMonitorActive key budget input (monitorView state)) :
    state.1.memory.external.hashCalls + signingMacroHashCost input ≤ budget := by
  have hspent : state.2.spent ≤ budget := hactive.2.1.2.2
  have hmacro := hactive.2.2.2
  have heq := haccount hactive.1
  change signingMacroHashCost input ≤ budget - state.2.spent at hmacro
  omega

/-- The pathwise step of a signing request. -/
theorem eventLivePotential_signing {inputs : Finset HashInput} (key : SecretKey) (budget : Nat) (message : Message)
    (state : MonitoredState inputs) (haccount : MonitoredAccounting state) (hresources : ProbeMessageBound state.1.memory)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) (mass : ENNReal) (memory : Memory) (cost : Nat)
    (hhash : memory.external.hashCalls = state.1.memory.external.hashCalls + cost)
    (hprobes : memory.external.probes = state.1.memory.external.probes)
    (hmass : mass ≤ state.2.creationMass + certificateMonitorMass key budget (.inr message) (monitorView state))
    (hcost : 2 ^ ftsTreeHeight ≤ cost) :
    mass / 2 ^ digestBits + eventGate budget memory (primitiveContinuation budget memory) ≤
      eventLivePotential budget state := by
  have hS : (0 : ℝ) < 2 ^ digestBits := by positivity
  have hb : 2 * (budget : ℝ) ≤ 2 ^ digestBits := by exact_mod_cast hbudget
  have hp : (state.1.memory.external.probes : ℝ) ≤ state.1.memory.external.hashCalls := by
    exact_mod_cast (show state.1.memory.external.probes ≤ state.1.memory.external.hashCalls from
      (Nat.le_add_right _ _).trans hresources)
  unfold eventLivePotential eventGate primitiveContinuation
  by_cases hover : budget < state.1.memory.external.hashCalls
  · have hinactive := monitor_inactive_of_over key budget (.inr message) state haccount hover
    rw [certificateMonitorMass, if_neg hinactive, add_zero] at hmass
    rw [if_neg (by omega), if_neg (by omega), add_zero, add_zero]
    exact ENNReal.div_le_div_right hmass _
  have hwithin : state.1.memory.external.hashCalls ≤ budget := by omega
  rw [if_pos hwithin]
  by_cases hactive : CertificateMonitorActive key budget (.inr message) (monitorView state)
  · have hroom := monitor_active_room key budget (.inr message) state haccount hactive
    change state.1.memory.external.hashCalls + 2 ^ ftsTreeHeight ≤ budget at hroom
    rw [certificateMonitorMass, if_pos hactive] at hmass
    have hmult : targetCreationMultiplier key (monitorView state).1 (.inr message) ≤ ((2 ^ ftsTreeHeight : Nat) : ENNReal) :=
      targetCreationMultiplier_le_macro key _ (.inr message)
    have hm : mass / 2 ^ digestBits ≤ state.2.creationMass / 2 ^ digestBits + ((2 ^ ftsTreeHeight : Nat) : ENNReal) / 2 ^ digestBits := by
      rw [← ENNReal.add_div]
      exact ENNReal.div_le_div_right (hmass.trans (add_le_add le_rfl hmult)) _
    rw [natCast_div_digest] at hm
    have hr : ((2 ^ ftsTreeHeight : Nat) : ℝ) ≤ (budget : ℝ) - state.1.memory.external.hashCalls := by
      have : ((state.1.memory.external.hashCalls + 2 ^ ftsTreeHeight : Nat) : ℝ) ≤ budget := by exact_mod_cast hroom
      push_cast at this ⊢
      linarith
    have hB : 2 * ((state.1.memory.external.probes : ℝ) + ((budget : ℝ) - state.1.memory.external.hashCalls)) ≤ 2 ^ digestBits := by
      linarith
    by_cases hfit : memory.external.hashCalls ≤ budget
    · rw [if_pos hfit]
      have hc : ((2 ^ ftsTreeHeight : Nat) : ℝ) ≤ cost := by exact_mod_cast hcost
      have hleft : (cost : ℝ) ≤ (budget : ℝ) - state.1.memory.external.hashCalls := by
        have : ((state.1.memory.external.hashCalls + cost : Nat) : ℝ) ≤ budget := by rw [← hhash]; exact_mod_cast hfit
        push_cast at this
        linarith
      have hreal := EventPotential.live_within (2 ^ digestBits) state.1.memory.external.probes
        ((budget : ℝ) - state.1.memory.external.hashCalls) cost (2 ^ ftsTreeHeight) hS (Nat.cast_nonneg _) hc hleft hB
      have hvalue : (budget : ℝ) - (memory.external.hashCalls : ℝ) = (budget : ℝ) - state.1.memory.external.hashCalls - cost := by
        rw [hhash]; push_cast; ring
      rw [hvalue, hprobes]
      have hnonneg := (PrimitiveMessagePotential.bounds (2 ^ digestBits) state.1.memory.external.probes
        ((budget : ℝ) - state.1.memory.external.hashCalls - cost) (by linarith) (by linarith)).1
      calc
        _ ≤ (state.2.creationMass / 2 ^ digestBits + ENNReal.ofReal (((2 ^ ftsTreeHeight : Nat) : ℝ) / 2 ^ digestBits)) +
            ENNReal.ofReal (PrimitiveMessagePotential.value (2 ^ digestBits) state.1.memory.external.probes
              ((budget : ℝ) - state.1.memory.external.hashCalls - cost)) := add_le_add hm le_rfl
        _ = state.2.creationMass / 2 ^ digestBits + ENNReal.ofReal (((2 ^ ftsTreeHeight : Nat) : ℝ) / 2 ^ digestBits +
            PrimitiveMessagePotential.value (2 ^ digestBits) state.1.memory.external.probes
              ((budget : ℝ) - state.1.memory.external.hashCalls - cost)) := by
          rw [add_assoc, ENNReal.ofReal_add (by positivity) hnonneg]
        _ ≤ _ := add_le_add le_rfl (ENNReal.ofReal_le_ofReal hreal)
    · rw [if_neg hfit, add_zero]
      have hreal := EventPotential.live_over (2 ^ digestBits) state.1.memory.external.probes
        ((budget : ℝ) - state.1.memory.external.hashCalls) (2 ^ ftsTreeHeight) hS (Nat.cast_nonneg _) hr hB
      exact hm.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hreal))
  · rw [certificateMonitorMass, if_neg hactive, add_zero] at hmass
    apply add_le_add (ENNReal.div_le_div_right hmass _)
    split_ifs with hfit
    · apply ENNReal.ofReal_le_ofReal
      rw [hprobes]
      apply PrimitiveMessagePotential.mono_remaining
      · have : ((memory.external.hashCalls : Nat) : ℝ) ≤ budget := by exact_mod_cast hfit
        linarith
      · rw [hhash]; push_cast; linarith [(Nat.cast_nonneg cost : (0 : ℝ) ≤ cost)]
      · have : ((state.1.memory.external.hashCalls : Nat) : ℝ) ≤ budget := by exact_mod_cast hwithin
        linarith
    · exact zero_le

theorem expected_le_of_pointwise {Result : Type} (law : SPMF Result) (f : Result → ENNReal) (bound : ENNReal)
    (h : ∀ result, law result ≠ 0 → f result ≤ bound) : (∑' result, Pr[= result | law] * f result) ≤ bound := by
  calc
    _ ≤ ∑' result, Pr[= result | law] * bound := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : law result = 0
      · simp only [SPMF.probOutput_eq_apply, hr, zero_mul, le_refl]
      · exact mul_le_mul' le_rfl (h result hr)
    _ ≤ bound := by
      rw [ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one

variable (key : SecretKey) (inputs : Finset HashInput) (hencoding : canonicalEncodingInputs key.parameter ⊆ inputs)
  (words : OtsReferenceWords) (publicReplies : CanonicalGraphLabels) (selections : ReferenceFamily) (rows : CanonicalEncodingRows)
  (budget : Nat) (required : Finset IndexGroup) (stopAfter : CertificateStopRule)

theorem monitoredWorldResult_creationMass_le (input : OracleWorld.Domain) (state : MonitoredState inputs)
    (raw : Option (OracleWorld.Range input) × State inputs) :
    (monitoredWorldResult key budget required stopAfter input state raw).2.2.creationMass ≤
      state.2.creationMass + raw.1.elim 0 (fun _ => certificateMonitorMass key budget (.inl input) (monitorView state)) := by
  rcases raw with ⟨answer, after⟩
  cases answer with
  | none => simp only [monitoredWorldResult, Option.elim_none, add_zero, le_refl]
  | some answer =>
      simp only [monitoredWorldResult, Option.elim_some]
      rw [certificateMonitorUpdate_creationMass]
      rfl

theorem certificateMonitorMass_world_le_messages (input : OracleWorld.Domain) (state : MonitoredState inputs)
    (answer : OracleWorld.Range input) :
    certificateMonitorMass key budget (.inl input) (monitorView state) ≤
      ((signingBoundaryTrace key.parameter input answer).messageCalls.length : ENNReal) := by
  unfold certificateMonitorMass
  split_ifs
  · cases input with
    | inl sample => simp [targetCreationMultiplier, freshWorldTargetHashCost]
    | inr hash =>
        simp only [targetCreationMultiplier, freshWorldTargetHashCost, signingBoundaryTrace,
          SigningBoundaryTrace.messageCalls]
        by_cases hm : FtsProbeSimulation.MessageHashInput key.parameter hash
        · simp only [hm, true_and, if_true, FreeMonoid.toList_of, List.filterMap_cons, id, List.filterMap_nil,
            List.length_singleton, Nat.cast_one]
          split_ifs <;> norm_num
        · simp [hm]
  · exact zero_le

attribute [local irreducible] certificateMonitorUpdate monitoredSigningResult in
theorem expected_monitoredWorld_eventPotential (input : OracleWorld.Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : hashInputs (liftM (OracleWorld.query input)) ⊆ inputs)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.1.memory.routing.disclosed (project state.1))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.1.memory.routing.known) words selections)
        state.1.memory.external.cache)
    (hresources : ProbeMessageBound state.1.memory) (haccount : MonitoredAccounting state)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter
        (.inl input) state] * eventResultPotential budget result) ≤ eventLivePotential budget state := by
  have htotal : (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter
      (.inl input) state]) = 1 :=
    tsum_monitoredStep_eq_one key inputs hencoding words publicReplies selections rows budget required stopAfter (.inl input) state hvalid.1
  rw [monitoredStep, tsum_probOutput_map_mul, lazyRun_externalProgram]
  rw [monitoredStep, lazyRun_externalProgram] at htotal
  have htotal' : (∑' raw, Pr[= raw | lazyByteRun key.parameter inputs hencoding words publicReplies selections rows
      state.1.memory.routing (liftM (OracleWorld.query input)) state.1]) = 1 := by
    have h := tsum_probOutput_map_mul (lazyByteRun key.parameter inputs hencoding words publicReplies selections rows
      state.1.memory.routing (liftM (OracleWorld.query input)) state.1)
      (monitoredWorldResult key budget required stopAfter input state) (fun _ => (1 : ENNReal))
    simp only [mul_one] at h
    rw [← h]
    exact htotal
  set law := lazyByteRun key.parameter inputs hencoding words publicReplies selections rows
    state.1.memory.routing (liftM (OracleWorld.query input)) state.1 with hlaw
  have hfacts (raw : Option (OracleWorld.Range input) × State inputs) (hraw : law raw ≠ 0) :
      raw.2.memory.external.hashCalls = state.1.memory.external.hashCalls + signingMacroHashCost (.inl input) ∧
      raw.2.memory.messageCalls = state.1.memory.messageCalls ++
        raw.1.elim [] (fun answer => (signingBoundaryTrace key.parameter input answer).messageCalls) :=
    ⟨by
      have h := lazyByteRun_world_hashCalls key.parameter inputs hencoding words publicReplies selections rows state.1.memory.routing
        input hinputs state.1 hvalid.1 raw hraw
      cases input <;> exact h,
     lazyByteRun_world_messageTrace key.parameter inputs hencoding words publicReplies selections rows state.1.memory.routing
      input hinputs state.1 hvalid.1 raw hraw⟩
  by_cases hroom : state.1.memory.external.hashCalls + signingMacroHashCost (.inl input) ≤ budget
  · cases input with
    | inl sample =>
        apply expected_le_of_pointwise
        intro raw hraw
        have hsame : raw.2 = state.1 := by
          rw [hlaw, ← bind_pure (liftM (OracleWorld.query (.inl sample))), lazyByteRun_random_bind,
            RetainedObservation.bind_nonzero] at hraw
          obtain ⟨answer, _, hraw⟩ := hraw
          rw [lazyByteRun_pure] at hraw
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hraw
          rw [hraw]
        have hmass := monitoredWorldResult_creationMass_le key inputs budget required stopAfter (.inl sample) state raw
        have hzero : certificateMonitorMass key budget (.inl (.inl sample)) (monitorView state) = 0 := by
          unfold certificateMonitorMass
          split_ifs <;> simp [targetCreationMultiplier, freshWorldTargetHashCost]
        have hlive : raw.1 ≠ none := by
          rw [hlaw, ← bind_pure (liftM (OracleWorld.query (.inl sample))), lazyByteRun_random_bind,
            RetainedObservation.bind_nonzero] at hraw
          obtain ⟨answer, _, hraw⟩ := hraw
          rw [lazyByteRun_pure] at hraw
          simp only [ne_eq, SPMF.pure_apply_eq_zero_iff, not_not] at hraw
          rw [hraw]; simp
        obtain ⟨answer, hanswer⟩ := Option.ne_none_iff_exists'.mp hlive
        rw [hanswer, Option.elim_some, hzero, add_zero] at hmass
        unfold eventResultPotential eventLivePotential
        change _ / _ + eventGate budget raw.2.memory (raw.1.elim 1 fun _ => primitiveContinuation budget raw.2.memory) ≤ _
        rw [hanswer, Option.elim_some, hsame]
        exact add_le_add (ENNReal.div_le_div_right hmass _) le_rfl
    | inr hash =>
        have hin : hash ∈ inputs := hinputs (by simpa only [bind_pure] using mem_hashInputs_hash_bind hash pure)
        have hquery : state.1.memory.external.hashCalls + 1 ≤ budget := hroom
        have hkernel := lazyByteRun_hash_jointPotential key.parameter inputs hencoding words publicReplies selections rows
          state.1.memory.routing hash hin state.1 budget hselect hvalid.1 hvalid.2 hcandidates hclean hresources hquery hbudget
        have hwithin : state.1.memory.external.hashCalls ≤ budget := by omega
        set messages : ENNReal := (state.1.memory.messageCalls.length : ENNReal) / 2 ^ digestBits
        have hfinite : messages ≠ ⊤ := by
          simp only [messages]
          exact ENNReal.div_ne_top (ENNReal.natCast_ne_top _) (by positivity)
        apply ENNReal.le_of_add_le_add_right hfinite
        calc
          _ = ∑' raw, Pr[= raw | law] * (eventResultPotential budget
                (monitoredWorldResult key budget required stopAfter (.inr hash) state raw) + messages) := by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, htotal', one_mul]
          _ ≤ ∑' raw, Pr[= raw | law] * (state.2.creationMass / 2 ^ digestBits + primitiveResultPotential budget raw) := by
            apply ENNReal.tsum_le_tsum
            intro raw
            by_cases hr : Pr[= raw | law] = 0
            · simp only [hr, zero_mul, le_refl]
            apply mul_le_mul' le_rfl
            rw [SPMF.probOutput_eq_apply] at hr
            obtain ⟨hh, hm⟩ := hfacts raw hr
            have hmass := monitoredWorldResult_creationMass_le key inputs budget required stopAfter (.inr hash) state raw
            have hgate : raw.2.memory.external.hashCalls ≤ budget := by rw [hh]; exact hquery
            unfold eventResultPotential primitiveResultPotential eventGate
            change _ / _ + (if raw.2.memory.external.hashCalls ≤ budget then
              raw.1.elim 1 (fun _ => primitiveContinuation budget raw.2.memory) else 0) + _ ≤ _
            rw [if_pos hgate]
            rcases raw with ⟨answer, after⟩
            cases answer with
            | none =>
                simp only [Option.elim_none, add_zero] at hmass hm ⊢
                rw [hm, List.append_nil]
                calc
                  _ ≤ state.2.creationMass / 2 ^ digestBits + 1 + messages := add_le_add (add_le_add (ENNReal.div_le_div_right hmass _) le_rfl) le_rfl
                  _ = _ := by simp only [messages]; ring
            | some answer =>
                simp only [Option.elim_some] at hmass hm ⊢
                have hmsg := certificateMonitorMass_world_le_messages key inputs budget (.inr hash) state answer
                rw [hm, List.length_append, Nat.cast_add, ENNReal.add_div]
                calc
                  _ ≤ (state.2.creationMass / 2 ^ digestBits +
                        ((signingBoundaryTrace key.parameter (.inr hash) answer).messageCalls.length : ENNReal) / 2 ^ digestBits) +
                        primitiveContinuation budget after.memory + messages := by
                    apply add_le_add (add_le_add _ le_rfl) le_rfl
                    rw [← ENNReal.add_div]
                    exact ENNReal.div_le_div_right (hmass.trans (add_le_add le_rfl hmsg)) _
                  _ = _ := by simp only [messages]; ring
          _ = state.2.creationMass / 2 ^ digestBits + ∑' raw, Pr[= raw | law] * primitiveResultPotential budget raw := by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, htotal', one_mul]
          _ ≤ state.2.creationMass / 2 ^ digestBits + primitiveLivePotential budget state.1.memory := add_le_add le_rfl hkernel
          _ = _ := by
            unfold eventLivePotential eventGate primitiveLivePotential
            rw [if_pos hwithin]
            simp only [messages]
            ring
  · apply expected_le_of_pointwise
    intro raw hraw
    obtain ⟨hh, _⟩ := hfacts raw hraw
    have hinactive : ¬ CertificateMonitorActive key budget (.inl input) (monitorView state) := by
      intro hactive
      exact hroom (monitor_active_room key budget (.inl input) state haccount hactive)
    have hmass := monitoredWorldResult_creationMass_le key inputs budget required stopAfter input state raw
    have hzero : certificateMonitorMass key budget (.inl input) (monitorView state) = 0 := by
      rw [certificateMonitorMass, if_neg hinactive]
    have hmass' : (monitoredWorldResult key budget required stopAfter input state raw).2.2.creationMass ≤ state.2.creationMass := by
      rcases raw with ⟨answer, after⟩
      cases answer <;> simpa [hzero] using hmass
    have hover : ¬ raw.2.memory.external.hashCalls ≤ budget := by rw [hh]; exact hroom
    unfold eventResultPotential eventLivePotential eventGate
    change _ / _ + (if raw.2.memory.external.hashCalls ≤ budget then _ else 0) ≤ _
    rw [if_neg hover, add_zero]
    exact (ENNReal.div_le_div_right hmass' _).trans le_self_add

attribute [local irreducible] lazyRun environment ResidualByteFrontend.jointSigningProgram in
theorem expected_monitoredSigning_eventPotential (message : Message) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key (.inr message) ⊆ inputs)
    (hresources : ProbeMessageBound state.1.memory) (haccount : MonitoredAccounting state)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter
        (.inr message) state] * eventResultPotential budget result) ≤ eventLivePotential budget state := by
  apply expected_le_of_pointwise
  intro result hresult
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
  unfold eventResultPotential
  simp only [monitoredSigningResult, Option.elim_some]
  apply eventLivePotential_signing key budget message state haccount hresources hbudget _ _ record.2.hashCalls
  · rw [hm]; rfl
  · rw [hm]; rfl
  · rw [certificateMonitorUpdate_creationMass]
    exact le_rfl
  · exact two_pow_ftsTreeHeight_le_ftsOpenHashCost.trans hmin

theorem expected_monitoredStep_eventPotential (input : (OracleWorld + SigningSpec).Domain) (state : MonitoredState inputs)
    (hvalid : MonitoredValid inputs state) (hinputs : requestInputs key input ⊆ inputs)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.1.memory.routing.disclosed (project state.1))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.1.memory.routing.known) words selections)
        state.1.memory.external.cache)
    (hresources : ProbeMessageBound state.1.memory) (haccount : MonitoredAccounting state)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter
        input state] * eventResultPotential budget result) ≤ eventLivePotential budget state := by
  cases input with
  | inl world =>
      exact expected_monitoredWorld_eventPotential key inputs hencoding words publicReplies selections rows budget required stopAfter
        world state hvalid hinputs hselect hcandidates hclean hresources haccount hbudget
  | inr message =>
      exact expected_monitoredSigning_eventPotential key inputs hencoding words publicReplies selections rows budget required stopAfter
        message state hvalid hinputs hresources haccount hbudget

theorem expected_monitoredRun_eventPotential {Result : Type} (computation : OracleComp (OracleWorld + SigningSpec) Result)
    (state : MonitoredState inputs) (hvalid : MonitoredValid inputs state) (hinputs : sourceInputs key computation ⊆ inputs)
    (hselect : ∀ position, FirstSuccessTable.select decodeEncodingOutput (fun counter => rows (position, counter)) = selections position)
    (hcandidates : ResidualByteFrontend.HiddenCandidateBound words state.1.memory.routing.disclosed (project state.1))
    (hclean : ResidualByteFrontend.ReplyClean
      (PublicEncodingMatch.Match key.parameter (knownEncodingMessage state.1.memory.routing.known) words selections)
        state.1.memory.external.cache)
    (hresources : ProbeMessageBound state.1.memory) (haccount : MonitoredAccounting state)
    (hbudget : 2 * budget ≤ 2 ^ digestBits) :
    (∑' result, Pr[= result | monitoredRun key inputs hencoding words publicReplies selections rows budget required stopAfter
        computation state] * eventResultPotential budget result) ≤ eventLivePotential budget state := by
  induction computation using OracleComp.inductionOn generalizing state with
  | pure value =>
      rw [monitoredRun_pure, tsum_probOutput_pure_mul]
      exact le_rfl
  | query_bind input next ih =>
      rw [monitoredRun_query_bind, tsum_probOutput_bind_mul]
      have hin := (requestInputs_subset key input next).trans hinputs
      refine le_trans ?_ (expected_monitoredStep_eventPotential key inputs hencoding words publicReplies selections rows budget
        required stopAfter input state hvalid hin hselect hcandidates hclean hresources haccount hbudget)
      apply ENNReal.tsum_le_tsum
      intro middle
      by_cases hm : Pr[= middle | monitoredStep key inputs hencoding words publicReplies selections rows budget required stopAfter
          input state] = 0
      · simp only [hm, zero_mul, le_refl]
      apply mul_le_mul' le_rfl
      rw [SPMF.probOutput_eq_apply] at hm
      have hlazy : lazyRun (environment key.parameter inputs hencoding words publicReplies selections rows)
          (adversaryImpl inputs key.parameter key.root words selections input) state.1 (middle.1, middle.2.1) ≠ 0 := by
        have h := map_nonzero _ (fun result => (result.1, result.2.1)) middle hm
        rwa [monitoredStep_erasure] at h
      rcases middle with ⟨answer, after⟩
      cases answer with
      | none =>
          rw [Option.elim_none, tsum_probOutput_pure_mul]
          exact le_rfl
      | some answer =>
          rw [Option.elim_some]
          have hvalid' := monitoredStep_valid key inputs hencoding words publicReplies selections rows budget required stopAfter
            input state hvalid (some answer, after) hm
          have hcandidates' := lazyRun_request_hiddenCandidateBound key inputs hencoding words publicReplies selections rows input
            hin state.1 hvalid.1 hvalid.2 hcandidates _ hlazy
          have hclean' := lazyRun_request_encodingClean inputs words publicReplies selections rows key hencoding input hin state.1
            hvalid.1 hvalid.2 hclean _ hlazy (by simp)
          have hresources' := lazyRun_request_probeMessageBound inputs words publicReplies selections rows key hencoding input hin
            state.1 hvalid.1 hvalid.2 hresources _ hlazy
          have haccount' := (monitoredStep_accounting key inputs hencoding words publicReplies selections rows budget required stopAfter
            input state hvalid hin haccount (some answer, after) hm).1
          exact ih answer after hvalid' ((sourceInputs_next_subset key input next answer).trans hinputs)
            hcandidates' hclean' hresources' haccount'

omit hencoding words publicReplies selections rows required stopAfter in
theorem initialMonitoredSource_event_primitive (adversary : Adversary)
    (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (required : Finset IndexGroup) (stopAfter : CertificateStopRule) (stopped : Bool)
    (hencoding : encoding ∈ referenceEncodingAuxiliarySample.support) (hbudget : budget ≤ 2 ^ 127) :
    Pr[fun result => result.1 = none ∧ result.2.1.memory.external.hashCalls ≤ budget |
      initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped] +
      (∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped] *
        result.2.2.creationMass) / 2 ^ digestBits ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) := by
  let law := initialMonitoredSource key adversary encoding dummy exposed high budget required stopAfter stopped
  have hd : 2 * budget ≤ 2 ^ digestBits := by
    norm_num only [digestBits]
    omega
  have hrun := expected_monitoredRun_eventPotential key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows budget required stopAfter
    (FtsProbeSimulation.unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)
    (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
      initialCertificateMonitor keygenHashCost stopped)
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_unlogged_subset_gameInputs adversary key) (referenceEncodingAuxiliary_select encoding hencoding)
    (initialState_hiddenCandidateBound _ _ exposed) (ResidualByteFrontend.replyClean_empty _) (Nat.zero_le _)
    (fun _ => rfl) hd
  change (∑' result, Pr[= result | law] * eventResultPotential budget result) ≤ _ at hrun
  have hinitial : eventLivePotential budget
      ((initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
        initialCertificateMonitor keygenHashCost stopped) : MonitoredState (gameInputs adversary)) ≤
      ENNReal.ofReal (2 * ((budget : ℝ) / 2 ^ digestBits) - ((budget : ℝ) / 2 ^ digestBits) ^ 2) := by
    unfold eventLivePotential eventGate
    change (0 : ENNReal) / 2 ^ digestBits + (if keygenHashCost ≤ budget then _ else 0) ≤ _
    rw [ENNReal.zero_div, zero_add]
    split_ifs with hk
    · have h := primitiveLivePotential_initial_le (gameInputs adversary) (referenceFamilyWords encoding.selections dummy)
        exposed budget hk hd
      refine le_trans ?_ h
      unfold primitiveLivePotential
      exact le_add_self
    · exact zero_le
  refine le_trans ?_ (hrun.trans hinitial)
  rw [probEvent_eq_tsum_ite, div_eq_mul_inv, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro result
  unfold eventResultPotential eventGate
  rw [mul_add, mul_assoc, ← div_eq_mul_inv]
  change _ ≤ Pr[= result | law] * (result.2.2.creationMass / 2 ^ digestBits) + _
  split_ifs with hevent hgate hgate
  · rw [hevent.1, Option.elim_none, mul_one, add_comm]
  · exact absurd hevent.2 hgate
  · rw [zero_add]; exact le_self_add
  · rw [zero_add, mul_zero, add_zero]

end SphincsSecurity.Concrete.RetainedResidual
