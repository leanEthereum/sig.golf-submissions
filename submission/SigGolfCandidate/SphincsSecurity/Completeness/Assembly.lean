import SigGolfCandidate.SphincsSecurity.Completeness.Game
import SigGolfCandidate.SphincsSecurity.Completeness.Signing
import SigGolfCandidate.SphincsSecurity.Completeness.Keygen
import SigGolfCandidate.SphincsSecurity.Completeness.Decay

/-!
# Completeness

The proofs of the claims of `Completeness.lean`. Correctness is `Game.correct`, which reads
`verify_of_sign` of `Recovery.lean` off key generation. For completeness:

`Game.lean` pulls the seed out of the experiment and, through recovery, charges failure to signing
returning `none`. `Keygen.lean` shows key generation leaves every input a later search hashes
uncached, and `Signing.lean` charges a signing failure to its eight searches: the randomizer search
(`Digest.lean`) and the seven counter searches (`Counter.lean`, with the code's size from `Code.lean`
and `Encoding.lean`). Each search is long enough that its failure decays exponentially
(`Decay.lean`), which is what closes the bound below. Nothing in the bound depends on the seed, so it
holds for every seed (`complete_seeded`), and averaging over the seed gives `complete`.

The numbers: a randomizer trial fails with probability at most `1 - 2⁻¹⁰ + 2²⁰/2¹²⁸`, which leaves
room for `1/1025`, so `2²⁰ ≥ 1025 · 1023` trials all fail with probability at most `2⁻¹⁰²³`. A
counter trial accepts at least `2¹¹⁹` of the `2¹²⁸` digests, so `2²⁰ = 2⁹ · 2¹¹` counters all fail
with probability at most `2⁻²⁰⁴⁸`. Over `2²⁵⁶` messages, `2²⁵⁶ · (2⁻¹⁰²³ + 7 · 2⁻²⁰⁴⁸) ≤ 2⁻²⁵⁶`.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete

theorem digestFactor_pow_le : digestFactor ^ digestAttemptLimit ≤ (2⁻¹ : ℝ≥0∞) ^ 1023 := by
  have hroom : digestFactor + ((1025 : Nat) : ℝ≥0∞)⁻¹ ≤ 1 :=
    digest_room digestReject digestReject_add
  have hhalf := pow_le_half_ennreal 1025 (by norm_num) digestFactor hroom
  have hone : digestFactor ≤ 1 := le_trans le_self_add hroom
  calc digestFactor ^ digestAttemptLimit ≤ digestFactor ^ (1025 * 1023) :=
        pow_le_pow_right_of_le_one' hone (by rw [digestAttemptLimit]; norm_num)
    _ = (digestFactor ^ 1025) ^ 1023 := pow_mul _ _ _
    _ ≤ (2⁻¹ : ℝ≥0∞) ^ 1023 := pow_le_pow_left₀ (by positivity) hhalf _

theorem encoding_pow_le : encodingBound ≤ (2⁻¹ : ℝ≥0∞) ^ (2 ^ 11) := by
  have hroom : failMass (fun out => TargetSum.decodeDigest (truncateHash out))
      + ((2 ^ 9 : Nat) : ℝ≥0∞)⁻¹ ≤ 1 := by
    have h := failMass_encoding_add_le
    rwa [← Nat.cast_ofNat, ← Nat.cast_pow] at h
  have hhalf := pow_le_half_ennreal (2 ^ 9) (by positivity) _ hroom
  rw [encodingBound, show encodingAttemptLimit = 2 ^ 9 * 2 ^ 11 by rw [encodingAttemptLimit]; norm_num,
    pow_mul]
  exact pow_le_pow_left₀ (by positivity) hhalf _

/-- Key generation then signing fails only if one of signing's eight searches does. -/
theorem probEvent_signedWithKeys_none (seed : MasterSeed) (message : Message) :
    Pr[fun r => r.1.2 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signedWithKeys seed message)).run ∅]
      ≤ digestFactor ^ digestAttemptLimit + (numLayers : ℝ≥0∞) * encodingBound := by
  rw [signedWithKeys]
  refine probEvent_bind_le _ _ _ ∅ _ (fun r hr => ?_)
  obtain ⟨hrand, hmsg, henc⟩ := keygen_fresh seed r hr message
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ r.2 0 ?_) ?_
  · rintro ⟨result, c⟩ _ hsome
    obtain ⟨signature, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    simp
  · rw [add_zero]
    exact probEvent_sign_none r.1.2 message r.2 hrand hmsg henc

/-- One message fails from a fixed seed with probability at most `2⁻¹⁰²³ + 7 · 2⁻²⁰⁴⁸`. -/
theorem seeded_failure_le (seed : MasterSeed) (message : Message) :
    Pr[= false | seededExperiment seed message]
      ≤ (2⁻¹ : ℝ≥0∞) ^ 1023 + 7 * (2⁻¹ : ℝ≥0∞) ^ (2 ^ 11) := by
  rw [seededExperiment_eq, ← probEvent_eq_eq_probOutput, probEvent_map]
  refine ((probEvent_honest_false_le seed message).trans
    (probEvent_signedWithKeys_none seed message)).trans ?_
  refine add_le_add digestFactor_pow_le ?_
  rw [show ((numLayers : Nat) : ℝ≥0∞) = 7 by norm_num [numLayers]]
  exact mul_le_mul_right encoding_pow_le _

/-- **Per-seed completeness.** From every master seed, the scheme is `2⁻²⁵⁶`-complete. -/
theorem complete_seeded : SphincsSeededCompletenessStatement := by
  intro seed
  calc
    ∑' message : Message, Pr[= false | seededExperiment seed message]
        ≤ ∑' _message : Message, ((2⁻¹ : ℝ≥0∞) ^ 1023 + 7 * (2⁻¹ : ℝ≥0∞) ^ (2 ^ 11)) :=
          ENNReal.tsum_le_tsum fun message => seeded_failure_le seed message
    _ = (2 : ℝ≥0∞) ^ 256 * ((2⁻¹ : ℝ≥0∞) ^ 1023 + 7 * (2⁻¹ : ℝ≥0∞) ^ (2 ^ 11)) := by
          rw [tsum_fintype, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
            show Fintype.card Message = 2 ^ 256 by simp [messageBits], Nat.cast_pow, Nat.cast_ofNat]
    _ ≤ ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ := closing_sum

/-- **Completeness.** Averaging the per-seed bound over the sampled seed: the scheme is
`2⁻²⁵⁶`-complete. -/
theorem complete : SphincsCompletenessStatement := by
  calc
    ∑' message : Message, Pr[= false | experiment message]
        = ∑' message : Message, ∑' seed : MasterSeed,
            Pr[= seed | sampleMasterSeed] * Pr[= false | seededExperiment seed message] := by
          refine tsum_congr fun message => ?_
          rw [experiment_eq, probOutput_bind_eq_tsum]
    _ = ∑' seed : MasterSeed, Pr[= seed | sampleMasterSeed]
          * ∑' message : Message, Pr[= false | seededExperiment seed message] := by
          rw [ENNReal.tsum_comm]
          exact tsum_congr fun seed => ENNReal.tsum_mul_left
    _ ≤ ∑' seed : MasterSeed, Pr[= seed | sampleMasterSeed] * ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ :=
          ENNReal.tsum_le_tsum fun seed => mul_le_mul' le_rfl (complete_seeded seed)
    _ ≤ ((2 ^ 256 : Nat) : ℝ≥0∞)⁻¹ := by
          rw [ENNReal.tsum_mul_right]
          exact mul_le_of_le_one_left' tsum_probOutput_le_one

end SphincsSecurity.Completeness
