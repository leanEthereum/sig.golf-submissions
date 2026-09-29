import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeWitness
/-!
# Probability of a fixed few-time coverage pattern

The relevant part of a digest is its 34-bit index and its fifteen 14-bit leaf indices (the digest
slots). A signing on the digest opens the leaves in its slots; a slot `i` of a target is covered by a
view on the same index whose opened leaf set contains the target's leaf `t_i`.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec ENNReal

abbrev FewTimeView := Index × (IndexGroup → FtsLeaf)

theorem fewTimeView_card : Fintype.card FewTimeView =
    2 ^ (totalHeight + ftsTreeHeight * ftsOpenings) := by
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, ← pow_mul, ← pow_add]

noncomputable local instance instSampleableTypeOfFintypeOfNonempty_sphincsSecurity {R : Type} [Fintype R] [Nonempty R] : SampleableType R :=
  SampleableType.ofFintype R

end SphincsSecurity.Concrete
