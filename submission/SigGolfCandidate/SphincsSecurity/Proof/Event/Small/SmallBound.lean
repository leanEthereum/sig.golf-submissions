import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.Primitive
import SigGolfCandidate.SphincsSecurity.Proof.Forced.FtsGuessNearSource
import SigGolfCandidate.SphincsSecurity.Proof.Forced.FtsGuessRemaining
/-!
# The small-budget bound for the capped adversary

The same case split as for a query-bounded adversary: a forgery is a primitive event, a full few-time
certificate, two guessed few-time secrets, or a near certificate with one guess. The primitive events
and full certificates share the budget in expectation; the certificate monitors run at the crude budget
`signRatio * budget`; the guesses are made among at most `budget` probes.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs

/-- The small-budget bound for the capped adversary with budget `budget`. -/
noncomputable def visSmallBound (budget : Nat) : ENNReal :=
  primitiveCoefficient * ((budget : ENNReal) / 2 ^ 128) + ((signRatio * budget : Nat) : ENNReal) * fullCertificateExcessRate +
    proposalPrefixExceptionBound + FtsGuessHash.pairRate budget +
    ((2 ^ 128 - budget : Nat) : ENNReal)⁻¹ * ((budget : ENNReal) * FtsGuessHash.nearMixedBound budget (signRatio * budget))

theorem signRatio_budget_le (budget : Nat) (hsmall : budget ≤ budgetSplit) : signRatio * budget ≤ 2 ^ 127 := by
  rw [budgetSplit_def] at hsmall
  rw [signRatio]
  omega

theorem forgeAdvantage_visAdversary_le (dummy : OtsReferenceWords) (hdummy : ∀ lay tree leaf, OtsCode.Valid (dummy lay tree leaf))
    (adversary : Adversary) (budget : Nat) (hbudget : keygenHashCost + 1 ≤ budget) (hsmall : budget ≤ budgetSplit) :
    forgeAdvantage scheme (visAdversary adversary budget) ≤ visSmallBound budget := by
  let vis := visAdversary adversary budget
  have hcrude := hasHashQueryBound_visAdversary adversary budget hbudget
  have hcrude127 := signRatio_budget_le budget hsmall
  have hprobe := probeBudget_visAdversary dummy adversary budget hbudget
  have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
  -- primitive events and full certificates
  have hjoint := visAdversary_primitive_joint dummy adversary budget hbudget hsmall
  rw [hcard] at hjoint
  simp only [Nat.cast_pow, Nat.cast_ofNat] at hjoint
  have hrate : (2 ^ 128 : ENNReal)⁻¹ + certificateCacheExceptionRate ≤ primitiveCoefficient / 2 ^ 128 := by
    apply (add_le_add le_rfl certificateCacheExceptionRate_le).trans
    rw [primitiveCoefficient_def]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_add, ENNReal.toReal_inv, ENNReal.toReal_div]
  have hfull := (originalCertificateSource_full_le_original_message_add_prefix vis (signRatio * budget) hcrude127 hcrude).trans
    (add_le_add (add_le_add (mul_le_mul' hrate (originalCertificateMessageCost_le_referenceRecorded dummy vis)) le_rfl)
      (certificateContextGame_prefix_le vis _ Finset.univ (fun _ => proposalPrefixStop) false))
  have hprimitiveFull : Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs vis)
      (canonicalEncodingInputs_subset_gameInputs vis) dummy vis] + Pr[OriginalFullCertificate | originalCertificateSource vis] ≤
      primitiveCoefficient * ((budget : ENNReal) / 2 ^ 128) +
        ((signRatio * budget : Nat) : ENNReal) * fullCertificateExcessRate + proposalPrefixExceptionBound := by
    refine (add_le_add le_rfl hfull).trans ?_
    rw [← add_assoc, ← add_assoc]
    exact add_le_add (add_le_add hjoint le_rfl) le_rfl
  -- remaining few-time outcomes
  have hremaining : Pr[ReferenceForgerySample.remainingFts dummy | referenceForgeryGame (canonicalGraphGameInputs vis)
      (canonicalEncodingInputs_subset_gameInputs vis) dummy vis] ≤
      FtsGuessHash.pairRate budget +
      ((2 ^ 128 - budget : Nat) : ENNReal)⁻¹ * ((budget : ENNReal) * FtsGuessHash.nearMixedBound budget (signRatio * budget)) := by
    refine (_root_.probEvent_mono'' (mx := referenceForgeryGame (canonicalGraphGameInputs vis)
      (canonicalEncodingInputs_subset_gameInputs vis) dummy vis)
      (fun sample h => sample.remainingFts_cases dummy h)).trans ?_
    refine (probEvent_or_le _ _ _).trans (add_le_add (FtsGuessHash.referenceForgeryGame_two_guesses dummy vis budget hprobe) ?_)
    refine (FtsGuessHash.referenceForgeryGame_near_guess_le_forced dummy vis budget hprobe).trans (mul_le_mul' le_rfl ?_)
    have hslots := Finset.sum_le_card_nsmul (Finset.range budget)
      (fun slot => Pr[fun hit => hit = true | FtsGuessHash.forcedNearGame dummy vis slot])
      (FtsGuessHash.nearMixedBound budget (signRatio * budget))
      (fun slot _ => FtsGuessHash.forcedNearGame_le_visAdversary dummy adversary budget hbudget _ hcrude hcrude127 slot)
    rwa [Finset.card_range, nsmul_eq_mul] at hslots
  -- assembly
  have hfts : Pr[ReferenceForgerySample.ftsOutcome dummy | referenceForgeryGame (canonicalGraphGameInputs vis)
      (canonicalEncodingInputs_subset_gameInputs vis) dummy vis] ≤
      Pr[OriginalFullCertificate | originalCertificateSource vis] +
      Pr[ReferenceForgerySample.remainingFts dummy | referenceForgeryGame (canonicalGraphGameInputs vis)
        (canonicalEncodingInputs_subset_gameInputs vis) dummy vis] := by
    refine (_root_.probEvent_mono (mx := referenceForgeryGame (canonicalGraphGameInputs vis)
      (canonicalEncodingInputs_subset_gameInputs vis) dummy vis)
      (p := ReferenceForgerySample.ftsOutcome dummy)
      (q := fun sample => sample.fullCertificate dummy ∨ sample.remainingFts dummy)
      (fun sample _ h => sample.ftsOutcome_cases dummy h)).trans ?_
    exact (probEvent_or_le _ _ _).trans (add_le_add (referenceForgeryGame_full_le dummy vis) le_rfl)
  have h := (forgeAdvantage_le_referenceForgery_cases dummy hdummy vis).trans (add_le_add hfts le_rfl)
  refine h.trans ?_
  calc
    _ = (Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver (canonicalGraphGameInputs vis)
          (canonicalEncodingInputs_subset_gameInputs vis) dummy vis] + Pr[OriginalFullCertificate | originalCertificateSource vis]) +
        Pr[ReferenceForgerySample.remainingFts dummy | referenceForgeryGame (canonicalGraphGameInputs vis)
          (canonicalEncodingInputs_subset_gameInputs vis) dummy vis] := by ring
    _ ≤ _ := add_le_add hprimitiveFull hremaining
    _ = _ := by rw [visSmallBound]; ring

end SphincsSecurity.Concrete.EventSmall
