import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.Joint
import SigGolfCandidate.SphincsSecurity.Proof.Fts.MessageDigestHazard
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateBoundaryInvariants
import SigGolfCandidate.SphincsSecurity.Proof.Fts.DigestMessageCost
/-!
# The capped adversary's budget in the random-oracle game

In the random-oracle game each own hash query of the capped adversary costs one call, counted either
as a message call or by the marker, and each signing request costs in expectation at most `2^11`
message calls, well below its charge: the randomizer of each digest trial is fresh, so a trial is
admissible with probability about `2^-10`.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

/-- Every random-oracle run with trace is a fixed-hash run. -/
theorem boundaryRun_mem_fixed (parameter : PublicParameter) {α : Type} (computation : OracleComp OracleWorld α)
    (cache : QueryCache HashSpec) (result : (α × SigningBoundaryTrace) × QueryCache HashSpec)
    (hresult : result ∈ support (boundaryRun parameter computation cache)) :
    ∃ f : QueryImpl HashSpec Id, result.1 ∈ support (fixedBoundaryRun parameter f computation) := by
  classical
  let inputs := hashInputs (boundaryComputation parameter computation)
  let _ : SampleableType (inputs → HashOutput) := SampleableType.ofFintype _
  have heq := evalDist_romRun_eq_finiteHash (boundaryComputation parameter computation) inputs (Finset.Subset.refl _) cache
  have hfst : result.1 ∈ support ((simulateQ romImpl (boundaryComputation parameter computation)).run' cache) := by
    rw [← boundaryRun_fst_eq_boundaryComputation, support_map]
    exact ⟨result, hresult, rfl⟩
  have hs : result.1 ∈ support (do
      let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
      simulateQ (fixedHashWorld (finiteHashAnswer cache inputs table)) (boundaryComputation parameter computation)) := by
    rw [mem_support_iff, probOutput_def, ← heq, ← probOutput_def, ← mem_support_iff]
    exact hfst
  rw [mem_support_bind_iff] at hs
  obtain ⟨table, _, hs⟩ := hs
  exact ⟨_, by rwa [fixedBoundaryRun_eq_boundaryComputation]⟩

theorem boundaryRun_sign_hashCalls (parameter : PublicParameter) (key : SecretKey) (message : Message)
    (cache : QueryCache HashSpec) (result : _) (hresult : result ∈ support (boundaryRun parameter (sign key message) cache)) :
    result.1.2.hashCalls ≤ signHashBound := by
  obtain ⟨f, hf⟩ := boundaryRun_mem_fixed parameter _ cache result hresult
  exact fixed_sign_cost parameter f key message _ hf

theorem boundaryRun_lift_messageCalls (parameter : PublicParameter) {α : Type} (computation : OracleComp HashSpec α)
    (hnone : ∀ f : QueryImpl HashSpec Id, (boundaryEval parameter f computation).2.messageCalls = [])
    (cache : QueryCache HashSpec) (result : _)
    (hresult : result ∈ support (boundaryRun parameter (liftM computation : OracleComp OracleWorld α) cache)) :
    result.1.2.messageCalls = [] := by
  obtain ⟨f, hf⟩ := boundaryRun_mem_fixed parameter _ cache result hresult
  rw [fixedBoundaryRun_lift_hash, support_pure, Set.mem_singleton_iff] at hf
  rw [hf]
  exact hnone f


theorem expectedBoundaryMessageCalls_signAfterDigest (key : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (cache : QueryCache HashSpec) :
    expectedBoundaryMessageCalls key.parameter
      (liftM (signAfterDigest key randomness index leaves : OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld _)
      cache = 0 := by
  rw [expectedBoundaryMessageCalls]
  apply ENNReal.tsum_eq_zero.mpr
  intro result
  by_cases hresult : result ∈ support (boundaryRun key.parameter
      (liftM (signAfterDigest key randomness index leaves : OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld _)
      cache)
  · rw [boundaryRun_lift_messageCalls key.parameter _ (fun f => by
      rw [boundaryEval_signAfterDigest, SigningBoundaryTrace.messageCalls_pow_none]) cache result hresult]
    simp
  · rw [probOutput_eq_zero_of_not_mem_support hresult, zero_mul]

theorem digestAttemptExpectation_le (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hcache : QueryCache.enncard cache ≤ 2 ^ 126) :
    digestAttemptExpectation digestAttemptLimit key message cache ≤ 2 ^ 11 := by
  have hrate : ((2 ^ 11 : ENNReal))⁻¹ ≤ (1 - (2 ^ 127 : ENNReal) * ((2 ^ randomnessBits : Nat) : ENNReal)⁻¹) *
      ((2 ^ ftsTreeHeight : Nat) : ENNReal)⁻¹ := by
    apply le_of_eq
    apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by
      apply ENNReal.mul_ne_top (by finiteness) (by finiteness))).mp
    rw [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le (by
      apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
      norm_num [randomnessBits, ENNReal.toReal_mul, ENNReal.toReal_inv]) (by finiteness)]
    norm_num [randomnessBits, ftsTreeHeight, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hbudget : cachedMessageEntryCount cache key.parameter key.root message + (digestAttemptLimit : ENNReal) ≤ 2 ^ 127 := by
    refine (add_le_add (cachedMessageEntryCount_le_enncard cache key.parameter key.root message) le_rfl).trans ?_
    refine (add_le_add hcache le_rfl).trans ?_
    rw [digestAttemptLimit]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num
  have h := digestAttemptExpectation_mul_message_rate_le_freshSelection digestAttemptLimit key message cache cache le_rfl
    (2 ^ 127) ((2 ^ 11 : ENNReal)⁻¹) hrate hbudget
  have hone := h.trans probEvent_le_one
  rwa [← div_eq_mul_inv, ENNReal.div_le_iff (by positivity) (by finiteness), one_mul] at hone

theorem expectedBoundaryMessageCalls_sign_le (key : SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hcache : QueryCache.enncard cache ≤ 2 ^ 126) :
    expectedBoundaryMessageCalls key.parameter (sign key message) cache ≤ 2 ^ 11 := by
  rw [sign_eq, expectedBoundaryMessageCalls_bind]
  refine le_trans (add_le_add le_rfl (le_of_eq (ENNReal.tsum_eq_zero.mpr fun result => ?_))) ?_
  · apply mul_eq_zero_of_right
    split
    · exact expectedBoundaryMessageCalls_pure _ _ _
    · exact expectedBoundaryMessageCalls_signAfterDigest key _ _ _ _
  rw [add_zero, expectedBoundaryMessageCalls_eq_queryCharge, expectedQueryCharge_signDigestLoop_message]
  exact digestAttemptExpectation_le key message cache hcache


theorem boundaryRun_map' (parameter : PublicParameter) {α β : Type} (computation : OracleComp OracleWorld α) (g : α → β)
    (cache : QueryCache HashSpec) :
    boundaryRun parameter (g <$> computation) cache =
      (fun result => ((g result.1.1, result.1.2), result.2)) <$> boundaryRun parameter computation cache := by
  simp only [boundaryRun, simulateQ_map, WriterT.run_map, StateT.run_map, Functor.map_map]

/-- The expected message calls of one adversary step, plus its nonmessage own queries. -/
theorem advStep_expected_le (sk : SecretKey) (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (hcache : QueryCache.enncard cache ≤ 2 ^ 126) :
    (∑' first, Pr[= first | boundaryRun sk.parameter (advStep sk input) cache] *
      (((if NonmessageQuery sk.parameter input then 1 else 0 : Nat) : ENNReal) + first.1.2.messageCalls.length)) ≤
      (visWeight input : ENNReal) := by
  rcases input with (input | input) | message
  · have hstep : advStep sk (.inl (.inl input)) =
        (fun answer => (answer, [])) <$> (liftM (OracleWorld.query (.inl input)) : OracleComp OracleWorld _) := rfl
    rw [hstep, boundaryRun_map', boundaryRun_query, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
    simp [NonmessageQuery, signingBoundaryTrace, SigningBoundaryTrace.messageCalls, visWeight]
  · rw [advStep_world]
    change (∑' first, Pr[= first | boundaryRun sk.parameter ((fun answer => (answer, [])) <$>
      (liftM (OracleWorld.query (.inr input)) : OracleComp OracleWorld _)) cache] * _) ≤ _
    rw [boundaryRun_map', boundaryRun_query, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
    have hone : ∀ answer : HashOutput,
        (((if NonmessageQuery sk.parameter (.inl (.inr input)) then 1 else 0 : Nat) : ENNReal) +
          (signingBoundaryTrace sk.parameter (.inr input) answer).messageCalls.length) = 1 := by
      intro answer
      have h := isMessageInput_iff sk.parameter input
      by_cases hm : FtsProbeSimulation.MessageHashInput sk.parameter input
      · have hb : isMessageInput sk.parameter input = true := h.mpr hm
        simp [NonmessageQuery, hb, signingBoundaryTrace, hm, SigningBoundaryTrace.messageCalls]
      · have hb : isMessageInput sk.parameter input = false := by
          cases hb' : isMessageInput sk.parameter input
          · rfl
          · exact absurd (h.mp hb') hm
        simp [NonmessageQuery, hb, signingBoundaryTrace, hm, SigningBoundaryTrace.messageCalls]
    simp only [hone, mul_one, visWeight, Nat.cast_one]
    exact tsum_probOutput_le_one
  · rw [advStep_sign, boundaryRun_map', tsum_probOutput_map_mul]
    simp only [NonmessageQuery, Nat.cast_zero, zero_add, if_false]
    refine (expectedBoundaryMessageCalls_sign_le sk message cache hcache).trans ?_
    simp only [visWeight]
    rw [ftsOpenHashCost_eq]
    norm_num


theorem advStep_enncard_le (sk : SecretKey) (input : (OracleWorld + SigningSpec).Domain) (cache : QueryCache HashSpec)
    (first : _) (hfirst : first ∈ support (boundaryRun sk.parameter (advStep sk input) cache)) :
    QueryCache.enncard first.2 ≤ QueryCache.enncard cache + ((signRatio * visWeight input : Nat) : ENNReal) := by
  refine (boundaryRun_enncard_le _ _ cache first hfirst).trans (add_le_add le_rfl ?_)
  obtain ⟨f, hf⟩ := boundaryRun_mem_fixed _ _ cache first hfirst
  exact_mod_cast advStep_cost_le sk sk.parameter f input first.1 hf

private theorem tsum_mul_const_add_le {β : Type} (weight : β → ENNReal) (hweight : ∑' x, weight x ≤ 1) (A : ENNReal)
    (B : β → ENNReal) : ∑' x, weight x * (A + B x) ≤ A + ∑' x, weight x * B x := by
  have h : ∀ x, weight x * (A + B x) = weight x * A + weight x * B x := fun x => mul_add _ _ _
  simp only [h]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
  exact add_le_add (mul_le_of_le_one_left' hweight) le_rfl

private theorem tsum_mul_add_const_le {β : Type} (weight : β → ENNReal) (hweight : ∑' x, weight x ≤ 1) (A : β → ENNReal)
    (C : ENNReal) : ∑' x, weight x * (A x + C) ≤ ∑' x, weight x * A x + C := by
  have h : ∀ x, weight x * (A x + C) = weight x * A x + weight x * C := fun x => mul_add _ _ _
  simp only [h]
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
  exact add_le_add le_rfl (mul_le_of_le_one_left' hweight)

/-- The expected own queries and message calls of the adversary phase stay within the charge. -/
theorem advPhase_expected_le (sk : SecretKey) {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (budget : Nat) (hbudget : WeightBound computation budget) (cache : QueryCache HashSpec)
    (hcache : QueryCache.enncard cache + ((signRatio * budget : Nat) : ENNReal) ≤ 2 ^ 126) :
    (∑' result, Pr[= result | boundaryRun sk.parameter
        (advPhase sk (QueryCap.counted (NonmessageQuery sk.parameter) computation)) cache] *
      ((result.1.1.1.2 : ENNReal) + result.1.2.messageCalls.length)) ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget cache with
  | pure value =>
      rw [QueryCap.counted_pure, advPhase_pure]
      have hpure : boundaryRun sk.parameter (pure ((value, 0), ([] : QueryLog SigningSpec)) : OracleComp OracleWorld _) cache =
          pure ((((value, 0), ([] : QueryLog SigningSpec)), 1), cache) := rfl
      rw [hpure, tsum_probOutput_pure_mul]
      simp [SigningBoundaryTrace.messageCalls]
  | query_bind input next ih =>
      rw [weightBound_query_bind_iff] at hbudget
      rw [QueryCap.counted_query_bind]
      simp only [bind_pure_comp]
      rw [advPhase_query_bind, boundaryRun_bind, tsum_probOutput_bind_mul]
      have hstep := advStep_expected_le sk input cache (le_trans le_self_add hcache)
      calc
        _ ≤ ∑' first, Pr[= first | boundaryRun sk.parameter (advStep sk input) cache] *
            ((((if NonmessageQuery sk.parameter input then 1 else 0 : Nat) : ENNReal) + first.1.2.messageCalls.length) +
              ((budget - visWeight input : Nat) : ENNReal)) := by
          apply ENNReal.tsum_le_tsum
          intro first
          by_cases hfirst : first ∈ support (boundaryRun sk.parameter (advStep sk input) cache)
          · apply mul_le_mul' le_rfl
            rw [tsum_probOutput_map_mul, advPhase_map, boundaryRun_map', boundaryRun_map', tsum_probOutput_map_mul,
              tsum_probOutput_map_mul]
            have hgrow := advStep_enncard_le sk input cache first hfirst
            have hcache' : QueryCache.enncard first.2 + ((signRatio * (budget - visWeight input) : Nat) : ENNReal) ≤ 2 ^ 126 := by
              refine le_trans ?_ hcache
              calc
                _ ≤ QueryCache.enncard cache + ((signRatio * visWeight input : Nat) : ENNReal) +
                    ((signRatio * (budget - visWeight input) : Nat) : ENNReal) := add_le_add hgrow le_rfl
                _ = _ := by
                  rw [add_assoc, ← Nat.cast_add, ← Nat.mul_add,
                    show visWeight input + (budget - visWeight input) = budget by have := hbudget.1; omega]
            have hrec := ih first.1.1.1 (budget - visWeight input) (hbudget.2 _) first.2 hcache'
            calc
              _ = ∑' last, Pr[= last | boundaryRun sk.parameter
                    (advPhase sk (QueryCap.counted (NonmessageQuery sk.parameter) (next first.1.1.1))) first.2] *
                  ((((if NonmessageQuery sk.parameter input then 1 else 0 : Nat) : ENNReal) + first.1.2.messageCalls.length) +
                    ((last.1.1.1.2 : ENNReal) + last.1.2.messageCalls.length)) := by
                apply tsum_congr
                intro last
                congr 1
                simp only [Prod.map, id, SigningBoundaryTrace.messageCalls_mul, List.length_append, Nat.cast_add]
                ring
              _ ≤ (((if NonmessageQuery sk.parameter input then 1 else 0 : Nat) : ENNReal) + first.1.2.messageCalls.length) +
                  ((budget - visWeight input : Nat) : ENNReal) := by
                exact (tsum_mul_const_add_le _ tsum_probOutput_le_one _ _).trans (add_le_add le_rfl hrec)
          · rw [probOutput_eq_zero_of_not_mem_support hfirst, zero_mul, zero_mul]
        _ ≤ (visWeight input : ENNReal) + ((budget - visWeight input : Nat) : ENNReal) := by
          exact (tsum_mul_add_const_le _ tsum_probOutput_le_one _ _).trans (add_le_add hstep le_rfl)
        _ = budget := by
          exact_mod_cast (show visWeight input + (budget - visWeight input) = budget by have := hbudget.1; omega)


theorem markerValue_mul_of_odd (first second : SigningBoundaryTrace)
    (hsecond : (second.messageCalls.filter oddEntry) ≠ []) :
    markerValue (first * second) = markerValue second := by
  simp only [markerValue, SigningBoundaryTrace.messageCalls_mul, List.filter_append,
    List.getLast?_append_of_ne_nil _ hsecond]

theorem marker_filter_ne_nil (trace : SigningBoundaryTrace) (parameter : PublicParameter) (count : Nat) (answer : HashOutput) :
    ((trace * signingBoundaryTrace parameter (.inr (markerInput parameter count)) answer).messageCalls.filter oddEntry) ≠ [] := by
  have hodd : oddEntry (markerInput parameter count, answer) = true := by
    simp only [oddEntry, length_markerInput, beq_iff_eq]
    omega
  simp only [signingBoundaryTrace, if_pos (messageHashInput_markerInput parameter count),
    SigningBoundaryTrace.messageCalls_mul, SigningBoundaryTrace.messageCalls, FreeMonoid.toList_of, List.filterMap_cons,
    List.filterMap_nil, id, List.filter_append, List.filter_cons, hodd, if_true, List.filter_nil]
  simp [hodd]

theorem boundaryEval_even (parameter : PublicParameter) (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp HashSpec α) (bound : Nat) (h : EvenBound computation bound) :
    ∀ entry ∈ (boundaryEval parameter f computation).2.messageCalls, entry.1.length % 2 = 0 := by
  induction computation using OracleComp.inductionOn generalizing bound with
  | pure value =>
      intro entry hentry
      simp [SigningBoundaryTrace.messageCalls] at hentry
  | query_bind input next ih =>
      rw [evenBound_query_bind_iff] at h
      have heval : evalWithAnswerFn f (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) = f input := rfl
      rw [boundaryEval_bind, boundaryEval_hash_query, heval]
      intro entry hentry
      rw [SigningBoundaryTrace.messageCalls_mul, List.mem_append] at hentry
      rcases hentry with hentry | hentry
      · by_cases hm : FtsProbeSimulation.MessageHashInput parameter input
        · simp only [signingBoundaryTrace, if_pos hm, SigningBoundaryTrace.messageCalls, FreeMonoid.toList_of,
            List.filterMap_cons, List.filterMap_nil, id, List.mem_singleton] at hentry
          subst entry
          exact Nat.even_iff.mp h.1.1
        · simp [signingBoundaryTrace, if_neg hm, SigningBoundaryTrace.messageCalls] at hentry
      · exact ih (f input) _ (h.2 _) entry hentry

/-- The verification step keeps the marker and adds at most `verifyHashBound` message calls. -/
theorem boundaryRun_finishGame (pk : PublicKey) (outcome : Forgery × QueryLog SigningSpec) (cache : QueryCache HashSpec)
    (result : _) (hresult : result ∈ support (boundaryRun pk.parameter (finishGame pk outcome) cache)) :
    (∀ entry ∈ result.1.2.messageCalls, entry.1.length % 2 = 0) ∧ result.1.2.messageCalls.length ≤ verifyHashBound := by
  obtain ⟨f, hf⟩ := boundaryRun_mem_fixed _ _ cache result hresult
  rw [finishGame, fixedBoundaryRun_bind, mem_support_bind_iff] at hf
  obtain ⟨checked, hchecked, hf⟩ := hf
  rw [fixedBoundaryRun_pure, map_pure, support_pure, Set.mem_singleton_iff] at hf
  change checked ∈ support (fixedBoundaryRun pk.parameter f (liftM (verify pk outcome.1.message outcome.1.signature :
    OracleComp HashSpec Bool))) at hchecked
  rw [fixedBoundaryRun_lift_hash, support_pure, Set.mem_singleton_iff] at hchecked
  rw [hf, hchecked]
  simp only [mul_one]
  refine ⟨boundaryEval_even _ f _ _ (evenBound_verify _ _ _), ?_⟩
  have hcalls := evenBound_boundaryEval pk.parameter f (evenBound_verify pk outcome.1.message outcome.1.signature)
  refine le_trans ?_ hcalls
  have := SigningBoundaryTrace.partition (boundaryEval pk.parameter f (verify pk outcome.1.message outcome.1.signature :
    OracleComp HashSpec Bool)).2
  omega


theorem markerValue_mul_of_marker (trace : SigningBoundaryTrace) (parameter : PublicParameter) (count : Nat)
    (answer : HashOutput) : markerValue (trace * FreeMonoid.of (some (markerInput parameter count, answer))) = count := by
  have h := markerValue_mul_marker trace parameter count answer
  simpa only [signingBoundaryTrace, if_pos (messageHashInput_markerInput parameter count)] using h

theorem visAdversary_advPhase_expected (adversary : Adversary) (budget : Nat) (hbudget : keygenHashCost + 1 ≤ budget)
    (sk : SecretKey) (root : Digest) (cache : QueryCache HashSpec)
    (hcache : QueryCache.enncard cache + ((signRatio * (budget - keygenHashCost - 1) : Nat) : ENNReal) ≤ 2 ^ 126) :
    (∑' result, Pr[= result | boundaryRun sk.parameter
        (advPhase sk ((visAdversary adversary budget).main ⟨root, sk.parameter⟩)) cache] *
      ((markerValue result.1.2 : ENNReal) + result.1.2.messageCalls.length)) ≤ ((budget - keygenHashCost : Nat) : ENNReal) := by
  rw [advPhase_visAdversary, boundaryRun_bind, tsum_probOutput_bind_mul]
  have hmain := advPhase_expected_le sk (weightCap (adversary.main ⟨root, sk.parameter⟩) (budget - keygenHashCost - 1))
    (budget - keygenHashCost - 1) (weightCap_weightBound _ _) cache hcache
  calc
    _ ≤ ∑' first, Pr[= first | boundaryRun sk.parameter (advPhase sk (QueryCap.counted (NonmessageQuery sk.parameter)
          (weightCap (adversary.main ⟨root, sk.parameter⟩) (budget - keygenHashCost - 1)))) cache] *
        (((first.1.1.1.2 : ENNReal) + first.1.2.messageCalls.length) + 1) := by
      apply ENNReal.tsum_le_tsum
      intro first
      apply mul_le_mul' le_rfl
      have hquery : ∀ (input : HashInput) (store : QueryCache HashSpec),
          boundaryRun sk.parameter (oracleHash input : OracleComp OracleWorld HashOutput) store =
            (fun result => ((result.1, signingBoundaryTrace sk.parameter (.inr input) result.1), result.2)) <$>
              (romImpl (.inr input)).run store := fun input store => boundaryRun_query _ (.inr input) store
      rw [boundaryRun_map', tsum_probOutput_map_mul, boundaryRun_map', tsum_probOutput_map_mul, tsum_probOutput_map_mul,
        hquery, tsum_probOutput_map_mul]
      rw [show (∑' last, _) = ∑' last, Pr[= last | (romImpl (.inr (markerInput sk.parameter first.1.1.1.2))).run first.2] *
          ((first.1.1.1.2 : ENNReal) + first.1.2.messageCalls.length + 1) from tsum_congr fun last => by
        congr 1
        simp only [Prod.map, id, markerValue_mul_marker, SigningBoundaryTrace.messageCalls_mul, List.length_append,
          signingBoundaryTrace, if_pos (messageHashInput_markerInput sk.parameter _), SigningBoundaryTrace.messageCalls,
          FreeMonoid.toList_of, List.filterMap_cons, List.filterMap_nil, List.length_cons, List.length_nil, Nat.cast_add,
          Nat.cast_one, markerValue_mul_of_marker]
        simp [SigningBoundaryTrace.messageCalls]
        ring, ENNReal.tsum_mul_right]
      exact mul_le_of_le_one_left' tsum_probOutput_le_one
    _ ≤ ((budget - keygenHashCost - 1 : Nat) : ENNReal) + 1 :=
      (tsum_mul_add_const_le _ tsum_probOutput_le_one _ _).trans (add_le_add hmain le_rfl)
    _ = _ := by exact_mod_cast (show budget - keygenHashCost - 1 + 1 = budget - keygenHashCost by omega)


theorem markerValue_mul_of_nil (first second : SigningBoundaryTrace) (hfirst : first.messageCalls = []) :
    markerValue (first * second) = markerValue second := by
  simp only [markerValue, SigningBoundaryTrace.messageCalls_mul, hfirst, List.nil_append]

theorem boundaryRun_keygen (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) (result : _)
    (hresult : result ∈ support (boundaryRun parameter
      (liftM (keygenRoot parameter secret : OracleComp HashSpec Digest) : OracleComp OracleWorld Digest) ∅)) :
    result.1.2.messageCalls = [] ∧ QueryCache.enncard result.2 ≤ keygenHashCost := by
  obtain ⟨f, hf⟩ := boundaryRun_mem_fixed _ _ ∅ result hresult
  rw [fixedBoundaryRun_lift_hash, boundaryEval_keygenRoot, support_pure, Set.mem_singleton_iff] at hf
  have hgrow := boundaryRun_enncard_le _ _ ∅ result hresult
  rw [hf] at hgrow ⊢
  simp only [SigningBoundaryTrace.messageCalls_pow_none, SigningBoundaryTrace.hashCalls_pow_none,
    QueryCache.enncard_empty, zero_add] at hgrow ⊢
  exact ⟨trivial, hgrow⟩

private theorem expectation_le_of_forall {β : Type} (law : ProbComp β) (value : β → ENNReal) (bound : ENNReal)
    (h : ∀ x ∈ support law, value x ≤ bound) : (∑' x, Pr[= x | law] * value x) ≤ bound := by
  calc
    _ ≤ ∑' x, Pr[= x | law] * bound := ENNReal.tsum_le_tsum fun x => by
          by_cases hx : x ∈ support law
          · exact mul_le_mul' le_rfl (h x hx)
          · rw [probOutput_eq_zero_of_not_mem_support hx, zero_mul, zero_mul]
    _ ≤ bound := by rw [ENNReal.tsum_mul_right]; exact mul_le_of_le_one_left' tsum_probOutput_le_one

theorem secretsGameRest_eq_advPhase (adversary : Adversary) (pk : PublicKey) (sk : SecretKey) :
    SphincsSecurity.gameRest scheme adversary pk sk = advPhase sk (adversary.main pk) >>= finishGame pk :=
  gameRest_eq_advPhase adversary pk sk

/-- In the random-oracle game the marker plus the message calls of the capped adversary are at most its
budget minus key generation, plus the verifier's queries, in expectation. -/
theorem lazy_visAdversary_expected (adversary : Adversary) (budget : Nat) (hbudget : keygenHashCost + 1 ≤ budget)
    (hsize : keygenHashCost + signRatio * budget ≤ 2 ^ 126) :
    (∑' result, Pr[= result | (simulateQ romImpl (boundaryGameCore (visAdversary adversary budget))).run' ∅] *
      ((markerValue result.2 : ENNReal) + result.2.messageCalls.length)) ≤
      ((budget - keygenHashCost : Nat) : ENNReal) + verifyHashBound := by
  rw [boundaryGameCore, simulateQ_romImpl_liftM_bind_run', tsum_probOutput_bind_mul]
  refine expectation_le_of_forall _ _ _ fun parameter _ => ?_
  rw [simulateQ_romImpl_liftM_bind_run', tsum_probOutput_bind_mul]
  refine expectation_le_of_forall _ _ _ fun otsSecret _ => ?_
  rw [simulateQ_romImpl_liftM_bind_run', tsum_probOutput_bind_mul]
  refine expectation_le_of_forall _ _ _ fun ftsSecret _ => ?_
  rw [← boundaryRun_fst_eq_boundaryComputation, tsum_probOutput_map_mul, gameAfterSecrets, boundaryRun_bind,
    tsum_probOutput_bind_mul]
  refine expectation_le_of_forall _ _ _ fun keygen hkeygen => ?_
  obtain ⟨hkmsg, hkcache⟩ := boundaryRun_keygen _ _ keygen hkeygen
  rw [tsum_probOutput_map_mul, secretsGameRest_eq_advPhase, boundaryRun_bind, tsum_probOutput_bind_mul]
  have hcache : QueryCache.enncard keygen.2 + ((signRatio * (budget - keygenHashCost - 1) : Nat) : ENNReal) ≤ 2 ^ 126 := by
    refine (add_le_add hkcache le_rfl).trans ?_
    have : signRatio * (budget - keygenHashCost - 1) ≤ signRatio * budget := Nat.mul_le_mul_left _ (by omega)
    exact_mod_cast (show keygenHashCost + signRatio * (budget - keygenHashCost - 1) ≤ 2 ^ 126 by omega)
  have hadv := visAdversary_advPhase_expected adversary budget hbudget ⟨parameter, keygen.1.1, otsSecret, ftsSecret⟩
    keygen.1.1 keygen.2 hcache
  calc
    _ ≤ ∑' first, Pr[= first | boundaryRun parameter (advPhase ⟨parameter, keygen.1.1, otsSecret, ftsSecret⟩
          ((visAdversary adversary budget).main ⟨keygen.1.1, parameter⟩)) keygen.2] *
        (((markerValue first.1.2 : ENNReal) + first.1.2.messageCalls.length) + verifyHashBound) := by
      apply ENNReal.tsum_le_tsum
      intro first
      apply mul_le_mul' le_rfl
      rw [tsum_probOutput_map_mul]
      refine expectation_le_of_forall _ _ _ fun last hlast => ?_
      obtain ⟨heven, hcalls⟩ := boundaryRun_finishGame ⟨keygen.1.1, parameter⟩ first.1.1 first.2 last hlast
      simp only [SigningBoundaryTrace.messageCalls_mul, List.length_append, hkmsg, List.length_nil, zero_add,
        markerValue_mul_of_nil _ _ hkmsg, markerValue_mul_even _ _ heven, Nat.cast_add]
      rw [add_assoc]
      exact add_le_add le_rfl (add_le_add le_rfl (by exact_mod_cast hcalls))
    _ ≤ _ := (tsum_mul_add_const_le _ tsum_probOutput_le_one _ _).trans (add_le_add hadv le_rfl)

end SphincsSecurity.Concrete.EventSmall
