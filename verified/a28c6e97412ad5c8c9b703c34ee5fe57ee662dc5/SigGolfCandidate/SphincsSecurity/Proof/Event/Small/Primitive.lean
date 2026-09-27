import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.LazyBudget
/-!
# The primitive bound for the capped adversary

The primitive events of the reference game are paid per query class at rates evaluated at the budget,
and the expected number of classified queries plus message calls is at most the budget.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphInputs canonicalEncodingInputs canonicalGraphGameInputs

theorem verifyHashBound_twice_le : 2 * verifyHashBound ≤ keygenHashCost := by
  rw [verifyHashBound_eq, keygenHashCost_eq]
  norm_num

theorem referenceRecorded_visAdversary_joint (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : keygenHashCost + 1 ≤ budget) (hsize : keygenHashCost + signRatio * budget ≤ 2 ^ 126) :
    (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs (visAdversary adversary budget))
        (canonicalEncodingInputs_subset_gameInputs (visAdversary adversary budget)) dummy (visAdversary adversary budget)] *
      ((result.prefixCalls dummy + result.remainingCalls dummy : Nat) : ENNReal)) ≤ budget := by
  let law := referenceRecordedGame (canonicalGraphGameInputs (visAdversary adversary budget))
    (canonicalEncodingInputs_subset_gameInputs (visAdversary adversary budget)) dummy (visAdversary adversary budget)
  have htransport := boundaryGameCore_expectation_eq_referenceRecorded dummy (visAdversary adversary budget)
    (fun result => (markerValue result.2 : ENNReal) + result.2.messageCalls.length)
  have hlazy := lazy_visAdversary_expected adversary budget hbudget hsize
  rw [htransport] at hlazy
  calc
    _ ≤ ∑' result, Pr[= result | law] *
        (((markerValue result.2.2.1.2 : ENNReal) + result.2.2.1.2.messageCalls.length) + verifyHashBound) := by
      apply ENNReal.tsum_le_tsum
      intro result
      by_cases hr : result ∈ support law
      · apply mul_le_mul' le_rfl
        have h := referenceRecordedGame_visAdversary_classes _ _ dummy adversary budget result hr
        have h' : ((result.prefixCalls dummy + result.remainingCalls dummy : Nat) : ENNReal) ≤
            ((markerValue result.2.2.1.2 + result.2.2.1.2.messageCalls.length + verifyHashBound : Nat) : ENNReal) := by
          exact_mod_cast (by omega)
        simpa only [Nat.cast_add] using h'
      · rw [probOutput_eq_zero_of_not_mem_support hr, zero_mul, zero_mul]
    _ ≤ (((budget - keygenHashCost : Nat) : ENNReal) + verifyHashBound) + verifyHashBound := by
      have hsum : ∀ result, Pr[= result | law] *
          (((markerValue result.2.2.1.2 : ENNReal) + result.2.2.1.2.messageCalls.length) + verifyHashBound) =
          Pr[= result | law] * ((markerValue result.2.2.1.2 : ENNReal) + result.2.2.1.2.messageCalls.length) +
            Pr[= result | law] * verifyHashBound := fun result => mul_add _ _ _
      simp only [hsum]
      rw [ENNReal.tsum_add, ENNReal.tsum_mul_right]
      exact add_le_add hlazy (mul_le_of_le_one_left' tsum_probOutput_le_one)
    _ ≤ budget := by
      have := verifyHashBound_twice_le
      exact_mod_cast (show budget - keygenHashCost + verifyHashBound + verifyHashBound ≤ budget by omega)


theorem visAdversary_primitive_joint (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hbudget : keygenHashCost + 1 ≤ budget) (hsmall : budget ≤ budgetSplit) :
    Pr[GraphPrimitiveEvent dummy | referenceGraphContextGame contactObserver
      (canonicalGraphGameInputs (visAdversary adversary budget))
      (canonicalEncodingInputs_subset_gameInputs (visAdversary adversary budget)) dummy (visAdversary adversary budget)] +
      (primitiveCoefficient / Fintype.card Digest) *
        (∑' result, Pr[= result | referenceRecordedGame (canonicalGraphGameInputs (visAdversary adversary budget))
          (canonicalEncodingInputs_subset_gameInputs (visAdversary adversary budget)) dummy (visAdversary adversary budget)] *
          (result.messageCalls : ENNReal)) ≤
        primitiveCoefficient * ((budget : ENNReal) / Fintype.card Digest) := by
  have hcard : Fintype.card Digest = 2 ^ 128 := by simp [digestBits]
  have hq : budget < Fintype.card Digest := hsmall.trans_lt (budgetSplit_le.trans_lt (by rw [hcard]; norm_num))
  have hr := primitive_rates_small budget hsmall
  have ho : (Fintype.card Digest : ENNReal)⁻¹ ≤ primitiveCoefficient / Fintype.card Digest := by
    rw [primitiveCoefficient_def]
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    norm_num [ENNReal.toReal_inv, ENNReal.toReal_div, hcard]
  have hsize : keygenHashCost + signRatio * budget ≤ 2 ^ 126 := by
    rw [budgetSplit_def] at hsmall
    rw [keygenHashCost_eq, signRatio]
    omega
  let rate := primitiveCoefficient / (Fintype.card Digest : ENNReal)
  let law := referenceRecordedGame (canonicalGraphGameInputs (visAdversary adversary budget))
    (canonicalEncodingInputs_subset_gameInputs (visAdversary adversary budget)) dummy (visAdversary adversary budget)
  have h := add_le_add (referenceGraphContextGame_primitive_le dummy (visAdversary adversary budget) budget
    (prefixBudget_visAdversary dummy adversary budget hbudget) (contactBudget_visAdversary dummy adversary budget hbudget) hq)
    (le_refl (rate * ∑' result, Pr[= result | law] * (result.messageCalls : ENNReal)))
  refine h.trans ?_
  calc
    _ ≤ rate * (∑' result, Pr[= result | law] * (result.prefixCalls dummy : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.encodingCalls : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.otherCalls dummy : ENNReal)) +
        rate * (∑' result, Pr[= result | law] * (result.messageCalls : ENNReal)) :=
      add_le_add (add_le_add (add_le_add (mul_le_mul' hr.1 le_rfl) (mul_le_mul' hr.2 le_rfl)) (mul_le_mul' ho le_rfl)) le_rfl
    _ = rate * ∑' result, Pr[= result | law] * ((result.prefixCalls dummy + result.remainingCalls dummy : Nat) : ENNReal) := by
      simp only [ReferenceRecordedResult.remainingCalls, Nat.cast_add, mul_add, ENNReal.tsum_add, add_assoc]
    _ ≤ rate * budget := mul_le_mul' le_rfl
      (referenceRecorded_visAdversary_joint dummy adversary budget hbudget hsize)
    _ = _ := by
      simp only [rate, div_eq_mul_inv]
      ring

end SphincsSecurity.Concrete.EventSmall
