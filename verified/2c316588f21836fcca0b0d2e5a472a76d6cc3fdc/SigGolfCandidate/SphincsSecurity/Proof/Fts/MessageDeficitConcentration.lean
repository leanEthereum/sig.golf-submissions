import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.MessageDeficitMomentGrowth
namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

def MessageDeficitExceptional (key : SecretKey) (cache : QueryCache HashSpec) : Prop :=
  ∃ message, ((2 ^ 83 : Nat) : ENNReal) < Concrete.messageAdmissibleDeficit key message cache

theorem positiveScoreMoment_eq_pow_ofReal (score : ℝ) (power : Nat) :
    positiveScoreMoment score power = ENNReal.ofReal score ^ power := by
  rw [positiveScoreMoment, ENNReal.ofReal_pow (le_max_right _ _)]
  simp only [ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (show 0 ≤ ENNReal.ofReal score from zero_le)]

theorem cachedMessageEntryCount_zero_of_no_inputs (parameter : PublicParameter) (root : Digest)
    (cache : QueryCache HashSpec) (hnone : ∀ payload, cache (tweakableHashInput parameter .message payload) = none)
    (message : Message) : cachedMessageEntryCount cache parameter root message = 0 := by
  have hempty : cachedMessageInputSet cache parameter root message = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro ⟨input, answer⟩ ⟨hcached, randomness, hinput⟩
    change cache input = some answer at hcached
    have h := hnone (Concrete.messageDigestPayload root message randomness)
    rw [← hinput, hcached] at h
    cases h
  simp only [cachedMessageEntryCount, hempty, Set.encard_empty, ENat.toENNReal_zero]

end SphincsSecurity
