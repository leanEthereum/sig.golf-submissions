import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixObservedSource
import SigGolfCandidate.SphincsSecurity.Proof.Chains.AdaptiveChainSupport
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsSeedCost
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] canonicalGraphLabels canonicalEncodingInputs canonicalGraphInputs instFintypePosition

private theorem pmf_mem_evalDist {Result : Type} (law : PMF Result) (result : Result) (h : result ∈ law.support) :
    result ∈ support 𝒮[law] := by
  change result ∈ (𝒮[law]).support
  simpa only [PMF.evalSPMF_eq, SPMF.support_liftM] using h

private theorem probComp_mem_evalDist {Result : Type} (law : ProbComp Result) (result : Result)
    (h : result ∈ support law) : result ∈ support 𝒮[law] :=
  (mem_support_iff_of_evalSPMF_eq (mx := law) (mx' := 𝒮[law]) rfl result).mp h

private theorem ftsSecret_mem_evalDist (ftsSecret : Index → FtsTree → FtsLeaf → Digest) :
    ftsSecret ∈ support 𝒮[sampleFtsSecrets] := by
  apply probComp_mem_evalDist
  unfold sampleFtsSecrets
  change ftsSecret ∈ support (@SampleableType.selectElem (Index → FtsTree → FtsLeaf → Digest) ftsSecretsSampleableType)
  exact ftsSecretsSampleableType.mem_support_selectElem ftsSecret

theorem prefixObservedRun_hashCalls_le (parameter : PublicParameter) (hparameter : parameter ∈ support sampleParameter)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (dummy : OtsReferenceWords) (adversary : Adversary) (selections : ReferenceFamily)
    (hselections : selections ∈ (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).support)
    (q : Nat) (hbound : HasHashQueryBound scheme adversary q) :
    let words := referenceFamilyWords selections dummy
    let segment : OtsPrefix := ⟨parameter, lay, tree, leaf, chainIdx, words lay tree leaf chainIdx⟩
    let inputs := canonicalGraphGameInputs adversary
    let hencoding := canonicalEncodingInputs_subset_gameInputs adversary parameter
    let hgraph := canonicalGraphInputs_subset_gameInputs adversary parameter
    ∀ (other : segment.ErasedSecrets) (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph),
      auxiliary ∈ (segment.referenceAuxSeedLaw inputs hencoding hgraph selections).support →
      ∀ result ∈ (segment.seedObservedRun inputs hencoding hgraph auxiliary other.val ftsSecret words adversary).support,
        result.2.1.2.hashCalls ≤ q := by
  dsimp only
  intro other auxiliary hauxiliary result hresult
  apply prefixObservedSourceGame_hashCalls_le lay tree leaf chainIdx dummy adversary q hbound (selections, result.2.1)
  unfold prefixObservedSourceGame
  refine (mem_support_bind_iff _ _ _).mpr ⟨parameter, probComp_mem_evalDist _ _ hparameter, ?_⟩
  refine (mem_support_bind_iff _ _ _).mpr ⟨ftsSecret, ftsSecret_mem_evalDist ftsSecret, ?_⟩
  refine (mem_support_bind_iff _ _ _).mpr ⟨selections, pmf_mem_evalDist _ _ hselections, ?_⟩
  refine (mem_support_bind_iff _ _ _).mpr ⟨other, pmf_mem_evalDist _ _ (PMF.mem_support_uniformOfFintype other), ?_⟩
  refine (mem_support_bind_iff _ _ _).mpr ⟨auxiliary, pmf_mem_evalDist _ _ hauxiliary, ?_⟩
  refine (mem_support_bind_iff _ _ _).mpr ⟨result.2.1, ?_, ?_⟩
  · apply pmf_mem_evalDist
    rw [PMF.mem_support_map_iff]
    exact ⟨result, hresult, rfl⟩
  · exact (mem_support_pure_iff _ _).mpr rfl

/-- Every seed game of a chain segment admits a cost bounding its prefix queries within `budget`. -/
def PrefixBudget (dummy : OtsReferenceWords) (adversary : Adversary) (budget : Nat) : Prop :=
  ∀ parameter ∈ support sampleParameter, ∀ (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (address : OtsPrefix.ChainAddress)
    (selections : ReferenceFamily), selections ∈ (FirstSuccessFamily.selected decodeEncodingOutput encodingAttemptLimit).support →
    ∀ (other : (OtsPrefix.atAddress parameter (referenceFamilyWords selections dummy) address).ErasedSecrets)
      (auxiliary : (OtsPrefix.atAddress parameter (referenceFamilyWords selections dummy) address).ReferenceAuxSeed
        (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary parameter)
        (canonicalGraphInputs_subset_gameInputs adversary parameter)),
      auxiliary ∈ ((OtsPrefix.atAddress parameter (referenceFamilyWords selections dummy) address).referenceAuxSeedLaw
        (canonicalGraphGameInputs adversary) (canonicalEncodingInputs_subset_gameInputs adversary parameter)
        (canonicalGraphInputs_subset_gameInputs adversary parameter) selections).support →
      OtsPrefix.SeedCost (OtsPrefix.atAddress parameter (referenceFamilyWords selections dummy) address) (canonicalGraphGameInputs adversary)
        (canonicalEncodingInputs_subset_gameInputs adversary parameter) (canonicalGraphInputs_subset_gameInputs adversary parameter)
        auxiliary other.val ftsSecret (referenceFamilyWords selections dummy) adversary budget

theorem prefixBudget_of_hasHashQueryBound (dummy : OtsReferenceWords) (adversary : Adversary) (q : Nat)
    (hbound : HasHashQueryBound scheme adversary q) : PrefixBudget dummy adversary q := by
  intro parameter hparameter ftsSecret address selections hselections other auxiliary hauxiliary
  exact OtsPrefix.SeedCost.of_hashCalls _ _ _ _ _ _ _ _ _ _
    (prefixObservedRun_hashCalls_le parameter hparameter ftsSecret address.1 address.2.1 address.2.2.1 address.2.2.2 dummy adversary
      selections hselections q hbound other auxiliary hauxiliary)

end SphincsSecurity.Concrete
