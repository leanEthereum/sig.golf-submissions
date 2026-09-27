import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FixedProposalMoments
import SigGolfCandidate.SphincsSecurity.Proof.Fts.TerminalProposalEnvelope

namespace SphincsSecurity.Concrete

open ENNReal

set_option maxHeartbeats 5000000 in
theorem stirlingPowerMoment_near_le :
    (15 : ENNReal) * ((15 : ENNReal) ^ 14 / 2 ^ 196) * stirlingPowerMoment (19 / 50) 14 ≤ 1241 / 2 ^ 128 := by
  have hm := stirlingPowerMoment_ne_top (19 / 50) (by finiteness) 14
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_div,
    ENNReal.toReal_ofNat]
  unfold stirlingPowerMoment
  rw [ENNReal.toReal_sum (fun order _ => by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_div, ENNReal.toReal_ofNat,
    ENNReal.toReal_natCast]
  norm_num [Finset.sum_range_succ, Nat.stirlingSecond]

/-- The average price, over a uniform proposal word of the fixed length, of a certificate that covers all
digest slots but one. -/
theorem uniformWordAverage_nearPrice (required : Finset IndexGroup) (hdegree : required.card + 1 = Fintype.card IndexGroup) :
    uniformWordAverage fixedProposalLength (terminalCertificatePrice required) ≤
      nearCertificatePrice := by
  rw [nearCertificatePrice_def]
  replace hdegree : required.card = 14 := by
    have hslots : Fintype.card IndexGroup = 15 := by simp [ftsOpenings]
    omega
  have hprice : terminalCertificatePrice required = fun word =>
      ((Fintype.card Index : ENNReal)⁻¹ * targetCertificateScale required) *
        proposalPowerSum required.card word := by
    funext word
    unfold terminalCertificatePrice proposalPowerSum
    ring
  rw [hprice, uniformWordAverage_mul_left]
  refine (mul_le_mul' le_rfl (uniformWordAverage_powerSum_le (α := Index) fixedProposalLength required.card (19 / 50)
    fixedProposalLength_rate_le)).trans ?_
  rw [hdegree]
  unfold targetCertificateScale coverScale
  rw [hdegree]
  have hindex : Fintype.card Index = 2 ^ 34 := Fintype.card_fin _
  have hleaf : Fintype.card FtsLeaf = 2 ^ 14 := by simp [ftsTreeHeight]
  rw [hindex, hleaf]
  have hnear := stirlingPowerMoment_near_le
  have hs := stirlingPowerMoment_ne_top (19 / 50) (by finiteness) 14
  have hr := (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mpr hnear
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  simp only [ENNReal.toReal_mul, ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_natCast,
    ENNReal.toReal_ofNat, ENNReal.toReal_inv, ftsOpenings] at hr ⊢
  norm_num at hr ⊢
  linarith

end SphincsSecurity.Concrete
