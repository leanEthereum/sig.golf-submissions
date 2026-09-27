import SigGolfCandidate.SphincsSecurity.Completeness.Digest
import SigGolfCandidate.SphincsSecurity.Completeness.Counter
import SigGolfCandidate.SphincsSecurity.Completeness.Encoding

/-!
# When signing fails

`sign` runs the randomizer search, builds the few-time forest, and signs the seven layers from the
bottom up, each a counter search followed by its tree built once, returning `none` as soon as a
search runs out. A union bound through that structure charges the failure to the eight searches.
The tree builds never fail and do not matter for the probability except through what they cache.

Each counter search needs its own inputs uncached when it starts; `EncodingFresh` carries that from
the start of signing, past the digest loop and the forest, and past each layer below it: a layer's
own search hashes under a different layer field, and its tree hashes under structural tweaks only.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete

attribute [local irreducible] Seeded.signDigestLoop Concrete.buildLayerTree Concrete.buildForest
  Concrete.encodingSearch digestAttemptLimit encodingAttemptLimit SphincsSecurity.deriveKey

/-- One counter search's failure bound. -/
noncomputable def encodingBound : ℝ≥0∞ :=
  failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit

theorem EncodingFresh.mono {parameter : PublicParameter} {pending pending' : Layer → Prop}
    {cache : QueryCache HashSpec} (h : EncodingFresh parameter pending cache)
    (hsub : ∀ lay, pending' lay → pending lay) : EncodingFresh parameter pending' cache :=
  fun lay hlay => h lay (hsub lay hlay)

/-- The layers `remaining - 1, ..., 0` fail with probability at most `remaining` counter-search
failures, provided none of their encoding inputs is cached at the start. -/
theorem probEvent_signLayers_none (sk : Seeded.SecretKey) (index : Index) :
    ∀ (remaining : Nat), remaining ≤ numLayers → ∀ (message : Digest) (cache : QueryCache HashSpec),
      EncodingFresh sk.parameter (fun l => l.val < remaining) cache →
      Pr[fun r => r.1 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signLayers sk.parameter index (Seeded.otsSecret sk.parameter sk.seed) remaining message
          : OracleComp HashSpec (Option (Layer → LayerOutput)))).run cache]
        ≤ (remaining : ℝ≥0∞) * encodingBound := by
  intro remaining
  induction remaining with
  | zero => intro _ message cache _; simp [signLayers]
  | succ r ih =>
      intro hrem message cache hfresh
      rw [signLayers]
      split
      next hlayer =>
        refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ cache
          ((r : ℝ≥0∞) * encodingBound) ?_) ?_
        · rintro ⟨result, c1⟩ hr hsome
          obtain ⟨⟨counter, word⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
          dsimp only
          have h1 : EncodingFresh sk.parameter (fun l => l.val < r) c1 :=
            (hfresh.mono fun l hl => Nat.lt_succ_of_lt hl).step _ ⟨_, c1⟩ hr
              (fun f l hl tree leaf payload => Avoids.encodingSearch f _ _ _ _ _ _
                (fun _ => encodingInput_ne_of_layer_ne _
                  (fun h => by rw [← h] at hl; exact absurd hl (Nat.lt_irrefl _)) _ _ _ _ _ _) _ _)
          refine probEvent_bind_le _ _ _ c1 _ (fun built hbuilt => ?_)
          have h2 := h1.step _ built hbuilt (fun f l _ tree leaf payload =>
            Avoids.buildLayerTree_of_structural f _ _ _ _ _ _ _
              (structural_encoding sk.parameter sk.seed l tree leaf payload))
          obtain ⟨⟨values, path, root⟩, c2⟩ := built
          dsimp only
          refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ c2 0 ?_) ?_
          · rintro ⟨result3, c3⟩ _ hsome3
            obtain ⟨rest, rfl⟩ := Option.ne_none_iff_exists'.mp hsome3
            simp
          · rw [add_zero]
            exact ih (Nat.le_of_succ_le hrem) root c2 h2
        · calc _ ≤ encodingBound + (r : ℝ≥0∞) * encodingBound := by
                refine add_le_add ?_ le_rfl
                exact probEvent_encodingSearch sk.parameter _ _ _ message cache
                  (fun c _ => hfresh _ (Nat.lt_succ_self r) _ _ _)
            _ = ((r + 1 : Nat) : ℝ≥0∞) * encodingBound := by push_cast; ring
      next hlayer => exact absurd (Nat.lt_of_succ_le hrem) hlayer

/-- After the digest loop: the forest never fails, and the seven layers fail only through their
counter searches. -/
theorem probEvent_signFrom_none (sk : Seeded.SecretKey) (index : Index) (randomness : Randomness)
    (leaves : IndexGroup → FtsLeaf) (cache : QueryCache HashSpec)
    (hfresh : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => r.1 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signFrom sk.parameter index (Seeded.ftsSecret sk.parameter sk.seed index)
        (Seeded.otsSecret sk.parameter sk.seed) randomness leaves
        : OracleComp HashSpec (Option Signature))).run cache]
      ≤ (numLayers : ℝ≥0∞) * encodingBound := by
  rw [signFrom]
  refine probEvent_bind_le _ _ _ cache _ (fun forest hforest => ?_)
  have h1 := hfresh.step _ forest hforest (fun f l _ tree leaf payload =>
    Avoids.buildForest_of_structural f _ _ _ _ _
      (structural_encoding sk.parameter sk.seed l tree leaf payload))
  obtain ⟨⟨secrets, ftsPath, ftsPublicKey⟩, c1⟩ := forest
  dsimp only
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ c1 0 ?_) ?_
  · rintro ⟨result, c2⟩ _ hsome
    obtain ⟨parts, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    simp
  · rw [add_zero]
    exact probEvent_signLayers_none sk index numLayers le_rfl ftsPublicKey c1
      (h1.mono fun _ _ => trivial)

/-- Signing fails only if the randomizer search or one of the seven counter searches does. -/
theorem probEvent_sign_none (sk : Seeded.SecretKey) (message : Message) (cache : QueryCache HashSpec)
    (hrand : ∀ s, cache (randInput sk message s) = none)
    (hmsg : ∀ ρ, cache (msgInput sk message ρ) = none)
    (henc : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => r.1 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.sign sk message : OracleComp HashSpec (Option Signature))).run cache]
      ≤ digestFactor ^ digestAttemptLimit + (numLayers : ℝ≥0∞) * encodingBound := by
  rw [Seeded.sign]
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ cache
    ((numLayers : ℝ≥0∞) * encodingBound) ?_) ?_
  · rintro ⟨result, c1⟩ hr hsome
    obtain ⟨⟨randomness, index, leaves⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    dsimp only
    have h1 : EncodingFresh sk.parameter (fun _ => True) c1 :=
      henc.step _ ⟨_, c1⟩ hr (fun f l _ tree leaf payload =>
        Avoids.signDigestLoop_of_structural f _ sk message
          (structural_encoding sk.parameter sk.seed l tree leaf payload) _ _)
    exact probEvent_signFrom_none sk index randomness leaves c1 h1
  · exact add_le_add (probEvent_signDigestLoop sk message digestAttemptLimit 0 cache ∅
      (by rw [digestAttemptLimit]; omega) (by simp) (fun s _ _ => hrand s) (fun ρ _ => hmsg ρ)) le_rfl

end SphincsSecurity.Completeness
