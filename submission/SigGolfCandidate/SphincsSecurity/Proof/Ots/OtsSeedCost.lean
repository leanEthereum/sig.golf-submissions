import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixVisibleAccounting
import SigGolfCandidate.SphincsSecurity.Proof.Ots.OtsPrefixAccounting
/-!
# A cost that bounds the prefix queries of a seed game

The chain arguments need some cost of the seed game's result that bounds its prefix queries on every
path and stays within the budget on the real runs. The trace length is one such cost; a constant is
another, when the prefix queries are bounded structurally.
-/

namespace SphincsSecurity.Concrete.OtsPrefix

open _root_.OracleComp OracleSpec

def SeedCost (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary) (budget : Nat) : Prop :=
  ∃ cost : Bool × SigningBoundaryTrace → Nat,
    (∀ endpoint result, result ∈ support (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
        (segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)) → result.2 ≤ cost result.1) ∧
    (∀ endpoint result, result ∈ support (QueryCap.counted PartialChainEndpoint.IsPrefixQuery
        (segment.visibleSeedGame inputs hencoding hgraph auxiliary secrets ftsSecret words adversary endpoint)) →
          result.2 ≤ cost result.1) ∧
    (∀ result ∈ (PartialChainEndpoint.realRun (fun _ => uniformImpl)
        (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
        (fun _ _ => none)).support, cost result.2.1 ≤ budget)

theorem SeedCost.of_hashCalls (segment : OtsPrefix) (inputs : Finset HashInput)
    (hencoding : canonicalEncodingInputs segment.parameter ⊆ inputs) (hgraph : canonicalGraphInputs segment.parameter ⊆ inputs)
    (auxiliary : segment.ReferenceAuxSeed inputs hencoding hgraph) (secrets : OtsFrontierValues)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords) (adversary : Adversary) (budget : Nat)
    (hreal : ∀ result ∈ (PartialChainEndpoint.realRun (fun _ => uniformImpl)
      (fun endpoint => segment.seedGame inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint adversary)
      (fun _ _ => none)).support, result.2.1.2.hashCalls ≤ budget) :
    SeedCost segment inputs hencoding hgraph auxiliary secrets ftsSecret words adversary budget :=
  ⟨fun result => result.2.hashCalls,
    fun endpoint result hresult => segment.seedGame_counted_le inputs hencoding hgraph auxiliary secrets ftsSecret words endpoint
      adversary result hresult,
    fun endpoint result hresult => segment.visibleSeedGame_counted_le inputs hencoding hgraph auxiliary secrets ftsSecret words
      adversary endpoint result hresult,
    hreal⟩

end SphincsSecurity.Concrete.OtsPrefix
