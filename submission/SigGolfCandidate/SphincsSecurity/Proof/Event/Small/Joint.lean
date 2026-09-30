import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.Marker
import SigGolfCandidate.SphincsSecurity.Proof.Fts.OriginalMessageAllocation
/-!
# The joint query budget of the capped adversary, in expectation

In the recorded reference game the prefix, encoding and other classes partition the recorded
nonmessage queries, which the marker bounds up to the verifier's queries. The marker and the message
calls are read off the trace, whose law is the same in the reference game and in the random-oracle
game, so their expectations can be computed in the latter.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs

private theorem probComp_mem_of_evalDist' {Result : Type} (computation : ProbComp Result) (result : Result)
    (hresult : result ∈ support 𝒮[computation]) : result ∈ support computation :=
  (mem_support_iff_of_evalSPMF_eq (mx := computation) (mx' := 𝒮[computation]) rfl result).mpr hresult

theorem referenceRecordedGame_visAdversary_nonmessage (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame inputs hencoding dummy (visAdversary adversary budget))) :
    QueryCap.calls (CausalFrontierProgram.NonmessageHash result.1) result.2.2.2 ≤
      markerValue result.2.2.1.2 + verifyHashBound := by
  simp only [referenceRecordedGame, mem_support_bind_iff] at hresult
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, reference, _, output, houtput, hresult⟩ := hresult
  rw [mem_support_pure_iff] at hresult
  subst result
  have hrecorded := QueryCap.simulate_oracle_mem_support _ _ output (probComp_mem_of_evalDist' _ output houtput)
  exact QueryCap.recorded_calls_le (CausalFrontierProgram.NonmessageHash parameter) _
    (fun result => markerValue result.2 + verifyHashBound)
    (fun result hresult => causalGame_nonmessage_marker parameter _ _ _ _ adversary budget result hresult) output hrecorded

theorem referenceRecordedGame_visAdversary_classes (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs)
    (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat) (result : ReferenceRecordedResult)
    (hresult : result ∈ support (referenceRecordedGame inputs hencoding dummy (visAdversary adversary budget))) :
    result.prefixCalls dummy + result.remainingCalls dummy ≤
      markerValue result.2.2.1.2 + verifyHashBound + result.2.2.1.2.messageCalls.length := by
  have hpartition := QueryClass.allocation_calls result.1 (referenceFamilyWords result.2.1 dummy) result.2.2.2
  have hmarker := referenceRecordedGame_visAdversary_nonmessage inputs hencoding dummy adversary budget result hresult
  dsimp only [ReferenceRecordedResult.prefixCalls, ReferenceRecordedResult.remainingCalls,
    ReferenceRecordedResult.encodingCalls, ReferenceRecordedResult.otherCalls, ReferenceRecordedResult.messageCalls]
  omega

/-- The law of the trace is the same in the random-oracle game and in the recorded reference game. -/
theorem boundaryGameCore_expectation_eq_referenceRecorded (dummy : OtsReferenceWords) (adversary : Adversary)
    (weight : Bool × SigningBoundaryTrace → ENNReal) :
    (∑' result, Pr[= result | (simulateQ romImpl (boundaryGameCore adversary)).run' ∅] * weight result) =
      ∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * weight result.2.2.1 := by
  have h := evalDist_boundaryGameCore_referenceFamily (canonicalGraphGameInputs adversary)
    (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
    dummy adversary (hashInputs_subset_canonicalGraphGameInputs adversary)
  have hp := (evalSPMF_ext_iff
    (mx := (simulateQ romImpl (boundaryGameCore adversary)).run' ∅)
    (mx' := Prod.snd <$> referenceFamilyGame (canonicalGraphGameInputs adversary)
      (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary)).mp h
  calc
    _ = ∑' result, Pr[= result | Prod.snd <$> referenceFamilyGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary] * weight result :=
      tsum_congr fun result => congrArg (· * _) (hp result)
    _ = _ := by
      rw [tsum_probOutput_map_mul,
        ← referenceRecordedGame_erased (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) dummy adversary, tsum_probOutput_map_mul]
      rfl

end SphincsSecurity.Concrete.EventSmall
