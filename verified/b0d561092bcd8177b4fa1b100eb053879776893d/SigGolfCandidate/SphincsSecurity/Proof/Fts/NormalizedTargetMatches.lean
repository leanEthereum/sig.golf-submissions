import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FutureCoverageBound
import SigGolfCandidate.SphincsSecurity.Proof.Fts.SubsetTargetExpectation
set_option autoImplicit true

/-!
# Normalized coverage and the exact coverage rates

A source covers a coordinate set `U` of a target with normalized weight `(2^14/15)^|U|` (the inverse of
the chance that a uniform leaf vector is covered by one opened set of 15 leaves). The rate at which the
fresh digest of a signing covers `U` is `signerRate target U`, the exact expectation over the signer's
view law; for PORS+FP it depends on the target (the accepted leaf sets are clustered). A fresh message
query adds an admissible cached source at the rate `arrivalRate target U = p · signerRate target U`.
Averaged over the target's leaves, both rates are at most their index-level values `2^-34` and `p·2^-34`
(`leafAverage_signerRate_le`, `leafAverage_arrivalRate_le`).
-/

namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

theorem sourceSubsetMatch_prod (target source : FewTimeView) (groups : Fin m → Finset IndexGroup) (selected : Finset (Fin m)) :
    (∏ slot ∈ selected, sourceSubsetMatch target source (groups slot)) =
      sourceSubsetMatch target source (selected.biUnion groups) := by
  induction selected using Finset.induction_on with
  | empty => simp [sourceSubsetMatch]
  | @insert slot selected hnot ih =>
      rw [Finset.prod_insert hnot, Finset.biUnion_insert, ih, sourceSubsetMatch_mul]

/-- The per-coordinate normalization `2^14 / 15`. -/
noncomputable def coverNormalization : ENNReal := (Fintype.card FtsLeaf : ENNReal) / ftsOpenings

theorem coverNormalization_ne_top : coverNormalization ≠ ⊤ :=
  ENNReal.div_ne_top (by simp) (by simp [ftsOpenings])

theorem coverNormalization_ne_zero : coverNormalization ≠ 0 :=
  ENNReal.div_ne_zero.mpr ⟨by simp, by simp⟩

/-- The per-coordinate coverage probability of one opened set, `15 / 2^14`. -/
noncomputable def coverScale : ENNReal := (ftsOpenings : ENNReal) / Fintype.card FtsLeaf

theorem coverNormalization_mul_coverScale : coverNormalization * coverScale = 1 := by
  unfold coverNormalization coverScale
  rw [div_eq_mul_inv, div_eq_mul_inv]
  calc
    _ = ((Fintype.card FtsLeaf : ENNReal) * (Fintype.card FtsLeaf : ENNReal)⁻¹) *
        (((ftsOpenings : Nat) : ENNReal)⁻¹ * ftsOpenings) := by ring
    _ = 1 := by
      rw [ENNReal.mul_inv_cancel (by simp) (by simp), ENNReal.inv_mul_cancel (by simp [ftsOpenings]) (by simp), one_mul]

noncomputable def normalizedSourceSubsetMatch (target source : FewTimeView) (required : Finset IndexGroup) : ENNReal :=
  coverNormalization ^ required.card * (sourceSubsetMatch target source required : ENNReal)

theorem normalizedSourceSubsetMatch_prod (target source : FewTimeView) (groups : Fin m → Finset IndexGroup)
    (selected : Finset (Fin m)) (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) =
      normalizedSourceSubsetMatch target source (selected.biUnion groups) := by
  simp only [normalizedSourceSubsetMatch, Finset.prod_mul_distrib, ← Nat.cast_prod,
    Finset.prod_pow_eq_pow_sum, sourceSubsetMatch_prod, Finset.card_biUnion hdisjoint]

/-- The exact rate at which the fresh accepted digest of one signing covers the coordinates `coords`
of `target` (the signer's view law is `signerViewSample`). -/
noncomputable def signerRate (target : FewTimeView) : TargetRate := fun coords =>
  ∑' source, Pr[= source | signerViewSample] * normalizedSourceSubsetMatch target source coords

/-- The exact rate at which one fresh message query adds an admissible cached source covering `coords`. -/
noncomputable def arrivalRate (target : FewTimeView) : TargetRate := fun coords =>
  admissibleProbability * signerRate target coords

theorem expected_signer_normalizedSourceSubsetMatch_prod (target : FewTimeView) (groups : Fin m → Finset IndexGroup)
    (selected : Finset (Fin m)) (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∑' source, Pr[= source | signerViewSample] *
      ∏ slot ∈ selected, normalizedSourceSubsetMatch target source (groups slot)) =
      signerRate target (selected.biUnion groups) := by
  simp only [normalizedSourceSubsetMatch_prod target _ groups selected hdisjoint, signerRate]

theorem expected_hash_normalizedSourceSubsetMatch (target : FewTimeView) (coords : Finset IndexGroup) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        normalizedSourceSubsetMatch target (hashOutputFewTimeView output) coords else 0)) =
      arrivalRate target coords := by
  rw [expected_uniformHashOutput_admissible_weight (fun source => normalizedSourceSubsetMatch target source coords)]
  rfl

theorem expected_hash_normalizedSourceSubsetMatch_prod (target : FewTimeView) (groups : Fin m → Finset IndexGroup)
    (selected : Finset (Fin m)) (hdisjoint : (selected : Set (Fin m)).PairwiseDisjoint groups) :
    (∑' output, Pr[= output | ($ᵗ HashOutput : ProbComp HashOutput)] *
      (if Admissible (truncateMessageDigest output) then
        ∏ slot ∈ selected, normalizedSourceSubsetMatch target (hashOutputFewTimeView output) (groups slot) else 0)) =
      arrivalRate target (selected.biUnion groups) := by
  simp only [normalizedSourceSubsetMatch_prod target _ groups selected hdisjoint]
  exact expected_hash_normalizedSourceSubsetMatch target _

/-! ### Locality and the average over the target's leaves -/

theorem LocalTo.tsum {α : Type} {coords : Finset IndexGroup} (weight : α → ENNReal)
    {g : α → (IndexGroup → FtsLeaf) → ENNReal} (hg : ∀ x, LocalTo coords (g x)) :
    LocalTo coords (fun leaves => ∑' x, weight x * g x leaves) := by
  intro first second hagree
  exact tsum_congr (fun x => by rw [hg x first second hagree])

theorem leafAverage_tsum {α : Type} (weight : α → ENNReal) (g : α → (IndexGroup → FtsLeaf) → ENNReal) :
    leafAverage (fun leaves => ∑' x, weight x * g x leaves) = ∑' x, weight x * leafAverage (g x) := by
  unfold leafAverage
  simp only [← ENNReal.tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  apply tsum_congr
  intro x
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ring

theorem normalizedSourceSubsetMatch_local (index : Index) (source : FewTimeView) (coords : Finset IndexGroup) :
    LocalTo coords (fun leaves => normalizedSourceSubsetMatch (index, leaves) source coords) := by
  intro first second hagree
  dsimp only
  unfold normalizedSourceSubsetMatch
  have h := sourceSubsetMatch_local index source coords first second hagree
  dsimp only at h
  rw [h]

/-- One source covers a uniform target's coordinates with normalized average at most one. -/
theorem leafAverage_normalizedSourceSubsetMatch_le (index : Index) (source : FewTimeView)
    (coords : Finset IndexGroup) (hne : coords.Nonempty) :
    leafAverage (fun leaves => normalizedSourceSubsetMatch (index, leaves) source coords) ≤
      if source.1 = index then 1 else 0 := by
  unfold normalizedSourceSubsetMatch
  simp only [sourceSubsetMatch_leaves index _ source coords hne]
  have hrewrite : (fun leaves : IndexGroup → FtsLeaf => coverNormalization ^ coords.card *
      ((if source.1 = index then (1 : ENNReal) else 0) *
        ∏ i ∈ coords, if leaves i ∈ openedLeaves source then (1 : ENNReal) else 0)) =
      fun leaves => (coverNormalization ^ coords.card * if source.1 = index then (1 : ENNReal) else 0) *
        ∏ i ∈ coords, if leaves i ∈ openedLeaves source then (1 : ENNReal) else 0 := by
    funext leaves
    ring
  have hprod := leafAverage_prod_coord (L := FtsLeaf) coords
    (fun _ leaf => if leaf ∈ openedLeaves source then (1 : ENNReal) else 0)
  rw [hrewrite, leafAverage_mul_left, hprod]
  simp only [Finset.sum_boole, Finset.filter_mem_eq_inter, Finset.univ_inter]
  by_cases hindex : source.1 = index
  · simp only [hindex, if_true, mul_one]
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_one'
    intro i _
    have hopened : ((openedLeaves source).card : ENNReal) ≤ ftsOpenings := by
      exact_mod_cast card_openedLeaves_le source
    calc
      coverNormalization * ((Fintype.card FtsLeaf : ENNReal)⁻¹ * ((openedLeaves source).card : ENNReal)) ≤
          coverNormalization * ((Fintype.card FtsLeaf : ENNReal)⁻¹ * ftsOpenings) := by gcongr
      _ = 1 := by
        unfold coverNormalization
        rw [div_eq_mul_inv]
        calc
          _ = ((Fintype.card FtsLeaf : ENNReal) * (Fintype.card FtsLeaf : ENNReal)⁻¹) *
              (((ftsOpenings : Nat) : ENNReal)⁻¹ * ftsOpenings) := by ring
          _ = 1 := by
            rw [ENNReal.mul_inv_cancel (by simp) (by simp), ENNReal.inv_mul_cancel (by simp [ftsOpenings]) (by simp),
              one_mul]
  · simp only [hindex, if_false, mul_zero, zero_mul, le_refl]

theorem signerRate_local (index : Index) : RateLocal (fun leaves => signerRate (index, leaves)) :=
  fun coords => LocalTo.tsum _ (fun source => normalizedSourceSubsetMatch_local index source coords)

theorem arrivalRate_local (index : Index) : RateLocal (fun leaves => arrivalRate (index, leaves)) := by
  intro coords first second hagree
  show admissibleProbability * signerRate (index, first) coords = admissibleProbability * signerRate (index, second) coords
  have h := signerRate_local index coords first second hagree
  dsimp only at h
  rw [h]

theorem leafAverage_signerRate_le (index : Index) (coords : Finset IndexGroup) (hne : coords.Nonempty) :
    leafAverage (fun leaves => signerRate (index, leaves) coords) ≤ (Fintype.card Index : ENNReal)⁻¹ := by
  unfold signerRate
  rw [leafAverage_tsum]
  calc
    _ ≤ ∑' source, Pr[= source | signerViewSample] * (if source.1 = index then 1 else 0) :=
      ENNReal.tsum_le_tsum (fun source => mul_le_mul' le_rfl
        (leafAverage_normalizedSourceSubsetMatch_le index source coords hne))
    _ = _ := by
      rw [← probEvent_signerView_index index, probEvent_eq_tsum_ite]
      apply tsum_congr
      intro source
      split_ifs <;> simp

theorem leafAverage_arrivalRate_le (index : Index) (coords : Finset IndexGroup) (hne : coords.Nonempty) :
    leafAverage (fun leaves => arrivalRate (index, leaves) coords) ≤ cachedIndexRate := by
  unfold arrivalRate
  rw [leafAverage_mul_left]
  exact mul_le_mul' le_rfl (leafAverage_signerRate_le index coords hne)

end SphincsSecurity.Concrete
