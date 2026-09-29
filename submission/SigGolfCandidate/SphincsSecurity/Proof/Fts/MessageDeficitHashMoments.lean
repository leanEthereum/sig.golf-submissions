import SigGolfCandidate.SphincsSecurity.Proof.Fts.MessageDeficitCacheGrowth
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedIndexHashMoments

/-! ## MessageDeficitBernoulli -/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

theorem messageDeficit_secondMoment_ennreal (score : ℝ) :
    Concrete.admissibleProbability * positiveScoreMoment (score + (Concrete.admissibleProbability.toReal - 1)) 2 +
      (1 - Concrete.admissibleProbability) * positiveScoreMoment (score + Concrete.admissibleProbability.toReal) 2 ≤
        positiveScoreMoment score 2 + 1 := by
  have hp := Concrete.admissibleProbability_le_one
  have hq : 1 - Concrete.admissibleProbability ≤ 1 := tsub_le_self
  have h := Concrete.bernoulliExcess_secondMoment_ennreal score (1 - Concrete.admissibleProbability) hq
  have hsub : (1 - Concrete.admissibleProbability).toReal = 1 - Concrete.admissibleProbability.toReal := by
    rw [ENNReal.toReal_sub_of_le hp (by simp), ENNReal.toReal_one]
  have hback : 1 - (1 - Concrete.admissibleProbability) = Concrete.admissibleProbability :=
    ENNReal.sub_sub_cancel (by simp) hp
  rw [hsub, hback] at h
  calc
    _ = (1 - Concrete.admissibleProbability) * positiveScoreMoment (score + (1 - (1 - Concrete.admissibleProbability.toReal))) 2 +
        Concrete.admissibleProbability * positiveScoreMoment (score + -(1 - Concrete.admissibleProbability.toReal)) 2 := by
      rw [add_comm]
      congr 3 <;> ring
    _ ≤ positiveScoreMoment score 2 + (1 - Concrete.admissibleProbability) := h
    _ ≤ _ := add_le_add le_rfl hq

end SphincsSecurity

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal
open Concrete (Admissible)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] messageDeficitScore positiveScoreMoment messageDeficitMoment
set_option backward.isDefEq.respectTransparency false

theorem probEvent_uniformHashOutput_admissible :
    Pr[fun output => Admissible (truncateMessageDigest output) | ($ᵗ HashOutput : ProbComp HashOutput)] =
      Concrete.admissibleProbability := by
  have h := Concrete.probEvent_uniformHashOutput_admissible_view (fun _ => True)
  simp only [and_true, Concrete.signAttemptResultOfOutput_ne_none_iff] at h
  rw [h, probEvent_True_eq_sub, Concrete.probFailure_signerViewSample, tsub_zero, mul_one]

private theorem expected_admissible_choice (accepted rejected : ENNReal) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then accepted else rejected)) =
      Concrete.admissibleProbability * accepted + (1 - Concrete.admissibleProbability) * rejected := by
  have hnot : Pr[fun output => ¬Admissible (truncateMessageDigest output) | ($ᵗ HashOutput : ProbComp HashOutput)] = 1 - Concrete.admissibleProbability := by
    have h := probEvent_compl ($ᵗ HashOutput : ProbComp HashOutput) (fun output => Admissible (truncateMessageDigest output))
    rw [probFailure_of_liftM_PMF, tsub_zero, probEvent_uniformHashOutput_admissible, add_comm] at h
    exact ENNReal.eq_sub_of_add_eq' (by simp) h
  have hsplit (output : HashOutput) :
      Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] * (if Admissible (truncateMessageDigest output) then accepted else rejected) =
        (if Admissible (truncateMessageDigest output) then Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * accepted +
        (if ¬Admissible (truncateMessageDigest output) then Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] else 0) * rejected := by
    split_ifs <;> simp_all only [zero_mul, zero_add, add_zero]
  simp_rw [hsplit, ENNReal.tsum_add, ENNReal.tsum_mul_right, ← probEvent_eq_tsum_ite, probEvent_uniformHashOutput_admissible, hnot]

private theorem expected_messageDeficitMoment_at (parameter : PublicParameter) (root : Digest) (message : Message)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none)
    (hat : MessageInputAt parameter root message input) (power : Nat) (charge : ENNReal)
    (hshift : Concrete.admissibleProbability * positiveScoreMoment (messageDeficitScore parameter root message cache + (Concrete.admissibleProbability.toReal - 1)) power +
      (1 - Concrete.admissibleProbability) * positiveScoreMoment (messageDeficitScore parameter root message cache + Concrete.admissibleProbability.toReal) power ≤
      positiveScoreMoment (messageDeficitScore parameter root message cache) power + charge) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      messageDeficitMoment parameter root (cache.cacheQuery input output) power) ≤ messageDeficitMoment parameter root cache power + charge := by
  let rest := ∑ other ∈ Finset.univ.erase message, positiveScoreMoment (messageDeficitScore parameter root other cache) power
  have hbefore : messageDeficitMoment parameter root cache power = positiveScoreMoment (messageDeficitScore parameter root message cache) power + rest := by
    unfold messageDeficitMoment
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ message)).symm
  have hafter (output : HashOutput) : messageDeficitMoment parameter root (cache.cacheQuery input output) power =
      (if Admissible (truncateMessageDigest output) then positiveScoreMoment (messageDeficitScore parameter root message cache + (Concrete.admissibleProbability.toReal - 1)) power
       else positiveScoreMoment (messageDeficitScore parameter root message cache + Concrete.admissibleProbability.toReal) power) + rest := by
    unfold messageDeficitMoment
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ message)]
    apply congrArg₂ (· + ·)
    · rw [messageDeficitScore_cacheQuery _ _ _ _ hfinite _ _ hfresh, if_pos hat]
      split_ifs <;> rfl
    · apply Finset.sum_congr rfl
      intro other hother
      rw [messageDeficitScore_cacheQuery _ _ _ _ hfinite _ _ hfresh,
        if_neg (fun h => (Finset.mem_erase.mp hother).1 (h.unique hat))]
  simp_rw [hafter, mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
  rw [expected_admissible_choice, hbefore]
  exact (add_le_add hshift le_rfl).trans_eq (add_right_comm _ _ rest)

private theorem expected_messageDeficitMoment_other (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none)
    (hother : ¬∃ message, MessageInputAt parameter root message input) (power : Nat) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      messageDeficitMoment parameter root (cache.cacheQuery input output) power) = messageDeficitMoment parameter root cache power := by
  have heq (output : HashOutput) : messageDeficitMoment parameter root (cache.cacheQuery input output) power = messageDeficitMoment parameter root cache power := by
    unfold messageDeficitMoment
    apply Finset.sum_congr rfl
    intro message _
    rw [messageDeficitScore_cacheQuery _ _ _ _ hfinite _ _ hfresh, if_neg (fun h => hother ⟨message, h⟩)]
  simp_rw [heq, ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

theorem expected_messageDeficitMoment_second_le (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hfinite : Finite cache) (input : HashInput) (hfresh : cache input = none) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      messageDeficitMoment parameter root (cache.cacheQuery input output) 2) ≤ messageDeficitMoment parameter root cache 2 + 1 := by
  by_cases hat : ∃ message, MessageInputAt parameter root message input
  · obtain ⟨message, hat⟩ := hat
    exact expected_messageDeficitMoment_at parameter root message cache hfinite input hfresh hat 2 1
      (messageDeficit_secondMoment_ennreal _)
  · rw [expected_messageDeficitMoment_other parameter root cache hfinite input hfresh hat]
    exact le_self_add

end SphincsSecurity
