import SigGolfCandidate.SphincsSecurity.Completeness.Digest
import SigGolfCandidate.SphincsSecurity.Completeness.Counter
import SigGolfCandidate.SphincsSecurity.Completeness.Encoding

/-!
# When signing fails

`sign` first checks the cache's MAC; for the cache key generation wrote, that query is a cache hit
returning the stored tag, so the check passes. Then it runs the randomizer search, builds the PORS tree
(one tree, secrets derived in pairs), and signs the five layers from the bottom up: layers `4, ..., 1` each a counter search followed
by its tree built once, and the top layer a counter search followed by its chains and the path read
from the cache. It returns `none` as soon as a search runs out. A union bound through that structure
charges the failure to the six searches. The tree builds and cache reads never fail and do not matter
for the probability except through what they cache.

Each counter search needs its own inputs uncached when it starts; `EncodingFresh` carries that from
the start of signing, past the digest loop and the PORS tree, and past each layer below it: a layer's
own search hashes under a different layer field, and its tree hashes under structural tweaks only.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Completeness

open Concrete

attribute [local irreducible] Seeded.signDigestLoop Concrete.buildLayerTreePaired Concrete.buildFtsTreePaired
  Concrete.encodingSearch digestAttemptLimit encodingAttemptLimit SphincsSecurity.deriveKey
  Seeded.signChecked

/-- One counter search's failure bound. -/
noncomputable def encodingBound : ℝ≥0∞ :=
  failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit

theorem EncodingFresh.mono {parameter : PublicParameter} {pending pending' : Layer → Prop}
    {cache : QueryCache HashSpec} (h : EncodingFresh parameter pending cache)
    (hsub : ∀ lay, pending' lay → pending lay) : EncodingFresh parameter pending' cache :=
  fun lay hlay => h lay (hsub lay hlay)

/-- The top layer fails only through its counter search, provided its encoding inputs are uncached. -/
theorem probEvent_signTopLayer_none (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (message : Digest) (cache : QueryCache HashSpec)
    (hfresh : EncodingFresh parameter (fun l => l.val < 1) cache) :
    Pr[fun r => r.1 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signTopLayerPaired parameter index secret topNode message
        : OracleComp HashSpec (Option LayerOutput))).run cache]
      ≤ encodingBound := by
  rw [signTopLayerPaired]
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ cache 0 ?_) ?_
  · rintro ⟨result, c1⟩ _ hsome
    obtain ⟨⟨counter, word⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    dsimp only
    refine probEvent_bind_le _ _ _ c1 0 (fun r1 _ => ?_)
    refine probEvent_bind_le _ _ _ r1.2 0 (fun r2 _ => ?_)
    simp
  · rw [add_zero]
    exact probEvent_encodingSearch parameter _ _ _ message cache
      (fun c _ => hfresh topLayer (by decide) _ _ _)

/-- The layers `remaining - 1, ..., 0` fail with probability at most `remaining` counter-search
failures, provided none of their encoding inputs is cached at the start. -/
theorem probEvent_signLayers_none (sk : Seeded.SecretKey) (index : Index)
    (topNode : Nat → Nat → OracleComp HashSpec Digest) :
    ∀ (remaining : Nat), remaining ≤ numLayers → ∀ (message : Digest) (cache : QueryCache HashSpec),
      EncodingFresh sk.parameter (fun l => l.val < remaining) cache →
      Pr[fun r => r.1 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
        (signLayersPaired sk.parameter index (Seeded.otsSecret sk.parameter sk.seed) topNode remaining message
          : OracleComp HashSpec (Option (Layer → LayerOutput)))).run cache]
        ≤ (remaining : ℝ≥0∞) * encodingBound := by
  intro remaining
  induction remaining with
  | zero => intro _ message cache _; simp [signLayersPaired]
  | succ r ih =>
      intro hrem message cache hfresh
      rw [signLayersPaired]
      split
      next hlayer =>
        by_cases hzero : r = 0
        · subst hzero
          rw [if_pos rfl]
          refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ cache 0 ?_) ?_
          · rintro ⟨result, c1⟩ _ hsome
            obtain ⟨output, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
            simp
          · rw [add_zero, Nat.zero_add, Nat.cast_one, one_mul]
            exact probEvent_signTopLayer_none sk.parameter index _ topNode message cache hfresh
        rw [if_neg hzero]
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
            Avoids.buildLayerTreePaired_of_structural f _ _ _ _ _ _ _
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

/-- After the digest loop: the PORS tree never fails, and the five layers fail only through their
counter searches. -/
theorem probEvent_signFrom_none (sk : Seeded.SecretKey) (index : Index)
    (topNode : Nat → Nat → OracleComp HashSpec Digest) (randomness : Randomness)
    (leaves : IndexGroup → FtsLeaf) (cache : QueryCache HashSpec)
    (hfresh : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => r.1 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signFromPaired sk.parameter index (Seeded.ftsSecret sk.parameter sk.seed index)
        (Seeded.otsSecret sk.parameter sk.seed) topNode randomness leaves
        : OracleComp HashSpec (Option Signature))).run cache]
      ≤ (numLayers : ℝ≥0∞) * encodingBound := by
  rw [signFromPaired]
  refine probEvent_bind_le _ _ _ cache _ (fun tree htree => ?_)
  have h1 := hfresh.step _ tree htree (fun f l _ t leaf payload =>
    Avoids.buildFtsTreePaired_of_structural f _ _ _ _
      (structural_encoding sk.parameter sk.seed l t leaf payload))
  obtain ⟨⟨secrets, table⟩, c1⟩ := tree
  dsimp only
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ c1 0 ?_) ?_
  · rintro ⟨result, c2⟩ _ hsome
    obtain ⟨parts, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    simp
  · rw [add_zero]
    exact probEvent_signLayers_none sk index topNode numLayers le_rfl (table ftsTreeHeight 0) c1
      (h1.mono fun _ _ => trivial)

/-- After the MAC check, signing fails only if the randomizer search or one of the five counter
searches does. -/
theorem probEvent_signChecked_none (sk : Seeded.SecretKey) (topCache : TopCache) (message : Message)
    (cache : QueryCache HashSpec)
    (hrand : ∀ s, cache (randInput sk message s) = none)
    (hmsg : ∀ ρ, cache (msgInput sk message ρ) = none)
    (henc : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => r.1 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.signChecked sk topCache message : OracleComp HashSpec (Option Signature))).run cache]
      ≤ digestFactor ^ digestAttemptLimit + (numLayers : ℝ≥0∞) * encodingBound := by
  rw [Seeded.signChecked]
  refine le_trans (probEvent_bind_le_add _ _ (fun r => r.1 = none) _ cache
    ((numLayers : ℝ≥0∞) * encodingBound) ?_) ?_
  · rintro ⟨result, c1⟩ hr hsome
    obtain ⟨⟨randomness, index, leaves⟩, rfl⟩ := Option.ne_none_iff_exists'.mp hsome
    dsimp only
    have h1 : EncodingFresh sk.parameter (fun _ => True) c1 :=
      henc.step _ ⟨_, c1⟩ hr (fun f l _ tree leaf payload =>
        Avoids.signDigestLoop_of_structural f _ sk message
          (structural_encoding sk.parameter sk.seed l tree leaf payload) _ _)
    exact probEvent_signFrom_none sk index _ randomness leaves c1 h1
  · exact add_le_add (probEvent_signDigestLoop sk message digestAttemptLimit 0 cache ∅
      (by rw [digestAttemptLimit]; omega) (by simp) (fun s _ _ => hrand s) (fun ρ _ => hmsg ρ)) le_rfl

/-- When the cache's MAC is already cached (key generation queried it), the check is a cache hit that
passes, and signing fails only if the randomizer search or one of the five counter searches does. -/
theorem probEvent_sign_none (sk : Seeded.SecretKey) (topCache : TopCache) (message : Message)
    (cache : QueryCache HashSpec)
    (hmac : cache (macHashInput sk.parameter sk.seed topCache.region) = some topCache.tag)
    (hrand : ∀ s, cache (randInput sk message s) = none)
    (hmsg : ∀ ρ, cache (msgInput sk message ρ) = none)
    (henc : EncodingFresh sk.parameter (fun _ => True) cache) :
    Pr[fun r => r.1 = none | (simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.sign sk topCache message : OracleComp HashSpec (Option Signature))).run cache]
      ≤ digestFactor ^ digestAttemptLimit + (numLayers : ℝ≥0∞) * encodingBound := by
  rw [Seeded.sign]
  simp only [oracleHash, HasQuery.query, simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
  rw [cached_run _ _ _ hmac, pure_bind, if_pos rfl]
  exact probEvent_signChecked_none sk topCache message cache hrand hmsg henc

end SphincsSecurity.Completeness
