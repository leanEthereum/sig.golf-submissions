import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.CachedIndexExcessConcentration
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal

def CertificateCacheExceptional (key : SecretKey) (cache : QueryCache HashSpec) : Prop :=
  MessageDeficitExceptional key cache ∨ CachedIndexExcessExceptional key.parameter cache

/-- A cache without message inputs is not exceptional. -/
theorem not_certificateCacheExceptional_of_no_message (key : SecretKey) (cache : QueryCache HashSpec)
    (hnone : ∀ input, FtsProbeSimulation.MessageHashInput key.parameter input → cache input = none) :
    ¬ CertificateCacheExceptional key cache := by
  have hcells : ∀ payload, cache (tweakableHashInput key.parameter .message payload) = none :=
    fun payload => hnone _ ⟨payload, rfl⟩
  have hcounts := cachedMessageEntryCount_zero_of_no_inputs key.parameter key.root cache hcells
  rintro (⟨message, hmessage⟩ | hindex)
  · rw [messageAdmissibleDeficit, hcounts, zero_mul, zero_tsub] at hmessage
    exact not_lt_of_ge zero_le hmessage
  · have hge := cachedIndexExcessExceptional_moment_ge key.parameter cache hindex
    rw [cachedIndexExcessMoment_zero_of_no_message key.parameter cache hnone] at hge
    exact absurd hge (not_le_of_gt (by positivity))

end SphincsSecurity.Concrete
