import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeProbability
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Guess
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.HashOutputSplit
/-!
# Uniform few-time views

The low 244 bits of a fresh oracle answer are exactly the 34-bit index and the fifteen 14-bit
leaf slots of the digest. Splitting an answer into these and its unused high bits is bijective, so the
induced view is uniform.
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

namespace Concrete

abbrev FullDigestView := Index × (IndexGroup → FtsLeaf)

def fullDigestView (digest : MessageDigest) : FullDigestView :=
  (digestIndex digest, digestLeaves digest)

/-- The index and the fifteen leaf slots of an answer's digest. -/
def hashOutputFewTimeView (output : HashOutput) : FewTimeView :=
  fullDigestView (truncateMessageDigest output)

/-- The digest bits `244 .. 255`, which the scheme does not read. -/
abbrev DigestUnusedBits := BitVec (messageDigestBits - (totalHeight + ftsTreeHeight * ftsOpenings))

def digestUnusedBits (digest : MessageDigest) : DigestUnusedBits :=
  digest.extractLsb' (totalHeight + ftsTreeHeight * ftsOpenings) (messageDigestBits - (totalHeight + ftsTreeHeight * ftsOpenings))

def digestCoordinates (digest : MessageDigest) : FewTimeView × DigestUnusedBits :=
  (fullDigestView digest, digestUnusedBits digest)

theorem digestCoordinates_injective : Function.Injective digestCoordinates := by
  intro left right heq
  apply BitVec.eq_of_getLsbD_eq
  intro position hposition
  have hbits : messageDigestBits = 256 := rfl
  by_cases hindex : position < totalHeight
  · have hcomponent := congrArg (fun view : FewTimeView × DigestUnusedBits => BitVec.ofFin view.1.1) heq
    have hbit := congrArg (fun bits : BitVec totalHeight => bits.getLsbD position) hcomponent
    simpa [digestCoordinates, fullDigestView, digestIndex, BitVec.getLsbD_extractLsb', hindex] using hbit
  · by_cases hslots : position < totalHeight + ftsTreeHeight * ftsOpenings
    · let treeIndex := (position - totalHeight) / ftsTreeHeight
      have htreeIndex : treeIndex < ftsOpenings := by
        have hslots' : position < 244 := by simpa [totalHeight, ftsTreeHeight, ftsOpenings] using hslots
        have hindex' : 34 ≤ position := by
          simpa [totalHeight] using Nat.le_of_not_gt hindex
        simp only [treeIndex, ftsOpenings, ftsTreeHeight, totalHeight]
        omega
      let tree : IndexGroup := ⟨treeIndex, htreeIndex⟩
      let within := (position - totalHeight) % ftsTreeHeight
      have hwithin : within < ftsTreeHeight := by
        simp only [within, ftsTreeHeight]
        omega
      have hoffset : totalHeight + ftsTreeHeight * tree.val + within = position := by
        have hindex' : totalHeight ≤ position := Nat.le_of_not_gt hindex
        simp only [tree, treeIndex, within]
        calc
          totalHeight + ftsTreeHeight * ((position - totalHeight) / ftsTreeHeight) +
              (position - totalHeight) % ftsTreeHeight =
              totalHeight + ((position - totalHeight) % ftsTreeHeight +
                ftsTreeHeight * ((position - totalHeight) / ftsTreeHeight)) := by omega
          _ = totalHeight + (position - totalHeight) := by rw [Nat.mod_add_div]
          _ = position := Nat.add_sub_of_le hindex'
      have hcomponent := congrArg (fun view : FewTimeView × DigestUnusedBits => BitVec.ofFin (view.1.2 tree)) heq
      change left.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight =
        right.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight at hcomponent
      have hbit := congrArg (fun bits : BitVec ftsTreeHeight => bits.getLsbD within) hcomponent
      simp only [BitVec.getLsbD_extractLsb', hwithin, decide_true, Bool.true_and] at hbit
      rwa [hoffset] at hbit
    · have hcomponent := congrArg (fun view : FewTimeView × DigestUnusedBits => view.2) heq
      change digestUnusedBits left = digestUnusedBits right at hcomponent
      have hlow : totalHeight + ftsTreeHeight * ftsOpenings ≤ position := Nat.le_of_not_gt hslots
      have hwithin : position - (totalHeight + ftsTreeHeight * ftsOpenings) <
          messageDigestBits - (totalHeight + ftsTreeHeight * ftsOpenings) := by
        rw [hbits] at hposition ⊢
        simp only [totalHeight, ftsTreeHeight, ftsOpenings] at hlow ⊢
        omega
      have hbit := congrArg (fun bits : DigestUnusedBits =>
        bits.getLsbD (position - (totalHeight + ftsTreeHeight * ftsOpenings))) hcomponent
      simp only [digestUnusedBits, BitVec.getLsbD_extractLsb', hwithin, decide_true, Bool.true_and,
        Nat.add_sub_of_le hlow] at hbit
      exact hbit

theorem digestCoordinates_bijective : Function.Bijective digestCoordinates := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨digestCoordinates_injective, ?_⟩
  simp only [Fintype.card_bitVec, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
  rfl

noncomputable def digestCoordinatesEquiv : MessageDigest ≃ FewTimeView × DigestUnusedBits :=
  Equiv.ofBijective digestCoordinates digestCoordinates_bijective

set_option maxRecDepth 100000 in
theorem evalDist_hashOutput_digestCoordinates_uniform :
    𝒮[(fun output : HashOutput => digestCoordinates (truncateMessageDigest output)) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[($ᵗ (FewTimeView × DigestUnusedBits) : ProbComp (FewTimeView × DigestUnusedBits))] := by
  calc
    𝒮[(fun output : HashOutput => digestCoordinates (truncateMessageDigest output)) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)] =
        digestCoordinates <$>
          𝒮[truncateMessageDigest <$> ($ᵗ HashOutput : ProbComp HashOutput)] := by
      rw [evalSPMF_map, evalSPMF_map, Functor.map_map]
    _ = digestCoordinates <$>
          𝒮[($ᵗ MessageDigest : ProbComp MessageDigest)] := by
      rw [show truncateMessageDigest =
          (fun output : HashOutput => output.extractLsb' 0 messageDigestBits) from rfl,
        evalDist_hashOutput_extract_uniform
          (show messageDigestBits ≤ hashOutputBits by decide)]
    _ = 𝒮[digestCoordinates <$>
          ($ᵗ MessageDigest : ProbComp MessageDigest)] := by
      rw [evalSPMF_map]
    _ = 𝒮[($ᵗ (FewTimeView × DigestUnusedBits) :
          ProbComp (FewTimeView × DigestUnusedBits))] :=
      evalSPMF_map_bijective_uniform_cross
        (α := MessageDigest) (β := FewTimeView × DigestUnusedBits)
        digestCoordinates digestCoordinates_bijective

abbrev HashOutputCoordinates :=
  (FewTimeView × DigestUnusedBits) × BitVec (hashOutputBits - messageDigestBits)

noncomputable def hashOutputCoordinatesEquiv : HashOutput ≃ HashOutputCoordinates :=
  (splitHashOutputEquiv messageDigestBits
      (show messageDigestBits ≤ hashOutputBits by decide)).trans
    (Equiv.prodCongr digestCoordinatesEquiv
      (Equiv.refl (BitVec (hashOutputBits - messageDigestBits))))

theorem hashOutputCoordinatesEquiv_apply (output : HashOutput) :
    hashOutputCoordinatesEquiv output =
      ((hashOutputFewTimeView output,
          digestUnusedBits (truncateMessageDigest output)),
        output.extractLsb' messageDigestBits (hashOutputBits - messageDigestBits)) := rfl

set_option maxRecDepth 100000 in
theorem evalDist_uniformHashOutput_bind_coordinates {Result : Type}
    (continuation : HashOutput → ProbComp Result) :
    𝒮[($ᵗ HashOutput : ProbComp HashOutput) >>= continuation] =
      𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
        fun coordinates => continuation (hashOutputCoordinatesEquiv.symm coordinates)] := by
  have hmap :
      𝒮[hashOutputCoordinatesEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
        𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates)] :=
    evalSPMF_map_bijective_uniform_cross
      (α := HashOutput) (β := HashOutputCoordinates)
      hashOutputCoordinatesEquiv hashOutputCoordinatesEquiv.bijective
  have hcomputation :
      (hashOutputCoordinatesEquiv <$> ($ᵗ HashOutput : ProbComp HashOutput)) >>=
          (fun coordinates =>
            continuation (hashOutputCoordinatesEquiv.symm coordinates)) =
        ($ᵗ HashOutput : ProbComp HashOutput) >>= continuation := by
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [← hcomputation, evalSPMF_bind, hmap, ← evalSPMF_bind]

set_option maxRecDepth 100000 in
theorem evalDist_randomOracle_fresh_bind_coordinates {Result : Type}
    (input : HashInput) (cache : QueryCache HashSpec) (hcache : cache input = none)
    (continuation : HashOutput × QueryCache HashSpec → ProbComp Result) :
    𝒮[(randomOracle input).run cache >>= continuation] =
      𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
        fun coordinates =>
          let output := hashOutputCoordinatesEquiv.symm coordinates
          continuation (output, cache.cacheQuery input output)] := by
  rw [OracleSpec.randomOracle, QueryImpl.withCaching_run_none _ hcache]
  change 𝒮[((fun output : HashOutput => (output, cache.cacheQuery input output)) <$>
      ($ᵗ HashOutput : ProbComp HashOutput)) >>= continuation] = _
  have hcomputation :
      ((fun output : HashOutput => (output, cache.cacheQuery input output)) <$>
          ($ᵗ HashOutput : ProbComp HashOutput)) >>= continuation =
        ($ᵗ HashOutput : ProbComp HashOutput) >>= fun output =>
          continuation (output, cache.cacheQuery input output) := by
    simp [map_eq_bind_pure_comp, bind_assoc]
  rw [hcomputation]
  exact evalDist_uniformHashOutput_bind_coordinates fun output =>
    continuation (output, cache.cacheQuery input output)

def signAttemptResultOfOutput (output : HashOutput) :
    Option (Index × (IndexGroup → FtsLeaf)) :=
  let digest := truncateMessageDigest output
  if Admissible digest then some (digestIndex digest, digestLeaves digest) else none

theorem hashOutputCoordinatesEquiv_symm_digestCoordinates
    (coordinates : HashOutputCoordinates) :
    digestCoordinates (truncateMessageDigest (hashOutputCoordinatesEquiv.symm coordinates)) =
      coordinates.1 := by
  have heq := hashOutputCoordinatesEquiv.apply_symm_apply coordinates
  rw [hashOutputCoordinatesEquiv_apply] at heq
  exact congrArg Prod.fst heq

theorem hashOutputCoordinatesEquiv_symm_view (coordinates : HashOutputCoordinates) :
    hashOutputFewTimeView (hashOutputCoordinatesEquiv.symm coordinates) = coordinates.1.1 := by
  change (digestCoordinates
    (truncateMessageDigest (hashOutputCoordinatesEquiv.symm coordinates))).1 = coordinates.1.1
  exact congrArg Prod.fst (hashOutputCoordinatesEquiv_symm_digestCoordinates coordinates)

theorem signAttemptResultOfOutput_ne_none_iff (output : HashOutput) :
    signAttemptResultOfOutput output ≠ none ↔
      Admissible (truncateMessageDigest output) := by
  simp only [signAttemptResultOfOutput]
  split <;> simp_all

theorem admissible_iff_view (output : HashOutput) :
    Admissible (truncateMessageDigest output) ↔ AdmissibleLeaves (hashOutputFewTimeView output).2 := Iff.rfl

theorem signAttemptResultOfOutput_coordinates_ne_none_iff
    (coordinates : HashOutputCoordinates) :
    signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates) ≠ none ↔
      AdmissibleLeaves coordinates.1.1.2 := by
  rw [signAttemptResultOfOutput_ne_none_iff, admissible_iff_view, hashOutputCoordinatesEquiv_symm_view]

theorem signAttemptResultOfOutput_coordinates_view
    (coordinates : HashOutputCoordinates) (index : Index)
    (leaves : IndexGroup → FtsLeaf)
    (hresult : signAttemptResultOfOutput (hashOutputCoordinatesEquiv.symm coordinates) =
      some (index, leaves)) :
    (index, leaves) = coordinates.1.1 := by
  let output := hashOutputCoordinatesEquiv.symm coordinates
  simp only [signAttemptResultOfOutput] at hresult
  split at hresult
  · have hpair := Option.some.inj hresult
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpair
    exact hashOutputCoordinatesEquiv_symm_view coordinates
  · simp at hresult

theorem signAttemptResultOfOutput_view (output : HashOutput) (index : Index)
    (leaves : IndexGroup → FtsLeaf)
    (hresult : signAttemptResultOfOutput output = some (index, leaves)) :
    (index, leaves) = hashOutputFewTimeView output := by
  let coordinates := hashOutputCoordinatesEquiv output
  calc
    (index, leaves) = coordinates.1.1 := by
      apply signAttemptResultOfOutput_coordinates_view coordinates index leaves
      simpa [coordinates] using hresult
    _ = hashOutputFewTimeView output := by
      dsimp only [coordinates]
      rw [hashOutputCoordinatesEquiv_apply]

theorem simulateQ_signAttempt_run_eq (secretKey : SecretKey) (message : Message)
    (randomness : Randomness) (cache : QueryCache HashSpec) :
    (simulateQ (randomOracle : QueryImpl HashSpec _)
      (signAttempt secretKey message randomness)).run cache =
        (randomOracle (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness))).run cache >>=
            fun result => pure (signAttemptResultOfOutput result.1, result.2) := by
  have hquery :
      simulateQ (randomOracle : QueryImpl HashSpec _)
          (oracleHash (tweakableHashInput secretKey.parameter .message
            (messageDigestPayload secretKey.root message randomness)) :
              OracleComp HashSpec HashOutput) =
        randomOracle (tweakableHashInput secretKey.parameter .message
          (messageDigestPayload secretKey.root message randomness)) := by
    change simulateQ (randomOracle : QueryImpl HashSpec _)
      (liftM (HashSpec.query (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness)))) = _
    exact simulateQ_spec_query
      (impl := (randomOracle : QueryImpl HashSpec
        (StateT (QueryCache HashSpec) ProbComp)))
      (tweakableHashInput secretKey.parameter .message
        (messageDigestPayload secretKey.root message randomness))
  rw [signAttempt, simulateQ_bind, StateT.run_bind, messageDigest,
    simulateQ_bind, StateT.run_bind, hquery]
  simp only [signAttemptResultOfOutput, simulateQ_pure, StateT.run_pure]
  simp only [bind_assoc, pure_bind]
  apply bind_congr
  intro result
  split <;> rfl

set_option maxRecDepth 100000 in
theorem evalDist_signAttempt_fresh_bind_coordinates {Result : Type}
    (secretKey : SecretKey) (message : Message) (randomness : Randomness)
    (cache : QueryCache HashSpec)
    (hcache : cache (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) = none)
    (continuation :
      Option (Index × (IndexGroup → FtsLeaf)) × QueryCache HashSpec →
        ProbComp Result) :
    𝒮[(simulateQ (randomOracle : QueryImpl HashSpec _)
        (signAttempt secretKey message randomness)).run cache >>= continuation] =
      𝒮[($ᵗ HashOutputCoordinates : ProbComp HashOutputCoordinates) >>=
        fun coordinates =>
          let output := hashOutputCoordinatesEquiv.symm coordinates
          continuation (signAttemptResultOfOutput output,
            cache.cacheQuery
              (tweakableHashInput secretKey.parameter .message
                (messageDigestPayload secretKey.root message randomness)) output)] := by
  rw [simulateQ_signAttempt_run_eq]
  simp only [bind_assoc, pure_bind]
  exact evalDist_randomOracle_fresh_bind_coordinates
    (tweakableHashInput secretKey.parameter .message
      (messageDigestPayload secretKey.root message randomness)) cache hcache
    (fun result => continuation (signAttemptResultOfOutput result.1, result.2))

end Concrete

end SphincsSecurity
