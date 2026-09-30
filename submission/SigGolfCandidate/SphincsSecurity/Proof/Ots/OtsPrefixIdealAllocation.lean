import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainCapCost
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixAccounting
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixObservedBudget
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixObservedAllocation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

noncomputable def prefixIdealCostGame (inputs : Finset HashInput)
    (hencoding : ∀ parameter, canonicalEncodingInputs parameter ⊆ inputs) (hgraph : ∀ parameter, canonicalGraphInputs parameter ⊆ inputs)
    (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat) : SPMF Nat := do
  let parameter ← 𝒮[sampleParameter]
  let ftsSecret ← 𝒮[sampleFtsSecrets]
  let selections ← 𝒮[FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit]
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  let other ← 𝒮[PMF.uniformOfFintype segment.ErasedSecrets]
  let auxiliary ← 𝒮[segment.referenceAuxSeedLaw inputs (hencoding parameter) (hgraph parameter) selections]
  let result ← 𝒮[PartialChainEndpoint.idealRun (fun _ => OtsPrefix.uniformImpl)
    (fun endpoint => QueryCap.run PartialChainEndpoint.IsPrefixQuery
      (segment.seedGame inputs (hencoding parameter) (hgraph parameter) auxiliary other.val ftsSecret words endpoint adversary) q)
    (fun _ _ => none)]
  pure (QueryCap.spent q result.2.1)

private theorem probComp_mem_of_evalDist {Result : Type} (computation : ProbComp Result) (result : Result)
    (hresult : result ∈ support 𝒮[computation]) : result ∈ support computation :=
  (mem_support_iff_of_evalSPMF_eq (mx := computation) (mx' := 𝒮[computation]) rfl result).mpr hresult

private theorem pmf_mem_of_evalDist {Result : Type} (law : PMF Result) (result : Result)
    (hresult : result ∈ support 𝒮[law]) : result ∈ law.support := by
  change result ∈ (𝒮[law]).support at hresult
  simpa only [PMF.evalSPMF_eq, SPMF.support_liftM] using hresult

theorem prefixIdealCostGame_lower (address : OtsPrefix.ChainAddress) (dummy : OtsReferenceWords)
    (adversary : Adversary) (q : Nat) (hprefix : PrefixBudget dummy adversary q) :
    (1 - (q : ENNReal) / Fintype.card Digest) *
        (∑' count, Pr[= count | prefixIdealCostGame (canonicalGraphGameInputs adversary)
          (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
          address dummy adversary q] * (count : ENNReal)) ≤
      ∑' result : PrefixCountedResult, Pr[= result | prefixCountedObservedGame (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary) (canonicalGraphInputs_subset_gameInputs adversary)
        address dummy adversary] * (result.2.2.2 : ENNReal) := by
  unfold prefixIdealCostGame prefixCountedObservedGame
  apply QueryCap.scaled_expectation_bind_le
  intro parameter hparameter
  apply QueryCap.scaled_expectation_bind_le
  intro ftsSecret _
  apply QueryCap.scaled_expectation_bind_le
  intro selections hselections
  apply QueryCap.scaled_expectation_bind_le
  intro other _
  apply QueryCap.scaled_expectation_bind_le
  intro auxiliary hauxiliary
  let words := referenceFamilyWords selections dummy
  let segment := OtsPrefix.atAddress parameter words address
  let inputs := canonicalGraphGameInputs adversary
  let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
  let hgraph := canonicalGraphInputs_subset_gameInputs adversary parameter
  let computation := fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary other.val ftsSecret words endpoint adversary
  obtain ⟨cost, hcharge, _, hreal⟩ := hprefix parameter (probComp_mem_of_evalDist _ parameter hparameter) ftsSecret address
    selections (pmf_mem_of_evalDist _ selections hselections) other auxiliary (pmf_mem_of_evalDist _ auxiliary hauxiliary)
  have h := PartialChainEndpoint.idealRun_cap_spent_lower (fun _ => OtsPrefix.uniformImpl) computation cost q hcharge hreal
  simpa only [tsum_probOutput_bind_mul, tsum_probOutput_pure_mul, ← PMF.monad_map_eq_map,
    evalSPMF_map, tsum_probOutput_map_mul, PMF.evalSPMF_eq, SPMF.probOutput_liftM, PMF.probOutput_eq_apply] using h

end SphincsSecurity.Concrete
