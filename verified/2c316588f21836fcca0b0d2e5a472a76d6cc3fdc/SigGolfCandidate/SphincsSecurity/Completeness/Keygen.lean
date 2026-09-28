import SigGolfCandidate.SphincsSecurity.Completeness.Digest
import SigGolfCandidate.SphincsSecurity.Completeness.Recovery

/-!
# What key generation leaves uncached

Key generation builds the top tree, with `P = 0`: derivation inputs and chain, leaf and node
tweaks; then it derives the masks (derivation inputs under tag `13`) and makes one MAC query (tag
`14`). The searches that follow hash under the randomizer, message and encoding tweaks, which none of
those produce, so their inputs are all still missing from the cache when signing begins. The MAC query,
on the other hand, is in the cache, with the tag key generation returned: the signer's check repeats it.
-/

open OracleComp OracleSpec

namespace SphincsSecurity.Completeness

open Concrete

/-- Key generation avoids any input that none of its hash calls can produce. -/
theorem Avoids.keygen_of (seed : MasterSeed) (target : HashInput)
    (hkey : ∀ (parameter : PublicParameter) (domain : KeygenDomain),
      keygenHashInput parameter domain seed ≠ target)
    (hchain : ∀ (parameter : PublicParameter) (tree : TreeIndex) (leaf : LeafIndex)
      (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain topLayer tree leaf chainIdx step) payload ≠ target)
    (hleaf : ∀ (parameter : PublicParameter) (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput),
      tweakableHashInput parameter (.leaf topLayer tree leaf) payload ≠ target)
    (hnode : ∀ (parameter : PublicParameter) (tree : TreeIndex) (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.node topLayer tree level nodeIdx) payload ≠ target)
    (hmac : ∀ (parameter : PublicParameter) (region : TopRegion), macHashInput parameter seed region ≠ target)
    (f : QueryImpl HashSpec Id) : Avoids f target (Seeded.keygenFromSeed seed) :=
  Avoids.keygenFromSeed f target seed (fun _ _ _ _ => hchain _ _ _ _ _ _)
    (fun _ _ => hleaf _ _ _ _) (fun _ _ _ => hnode _ _ _ _ _) (fun _ => hkey _ _) (fun _ => hmac _ _)

/-- The MAC input differs from every input whose tweak tag is not `14`. -/
theorem macHashInput_ne_of_tag_ne (parameter parameter' : PublicParameter) (seed : MasterSeed)
    (region : TopRegion) {fields : TweakFields} (htag : fields.tag ≠ 14#8) (payload : HashInput) :
    macHashInput parameter seed region ≠ fieldBytes fields ++ bytesLE 16 parameter' ++ payload := by
  intro h
  exact fieldInput_ne_of_tag_ne' parameter parameter' (fields1 := ⟨14#8, 0#8, 0#40, 0#32, 0#32⟩)
    (fields2 := fields) (fun h' => htag h'.symm) (bytesLE 32 seed ++ regionBytes region) payload
    (by simpa only [macHashInput, List.append_assoc] using h)

theorem keygenDomain_tag_ne (domain : KeygenDomain) (tag : Nat) (htag : tag = 4 ∨ tag = 7 ∨ tag = 12) :
    (keygenDomainFields domain).tag ≠ BitVec.ofNat 8 tag := by
  rcases htag with rfl | rfl | rfl <;> cases domain <;> simp [keygenDomainFields, tweakFields]

/-- After key generation, nothing the randomizer search, the message digest or a counter search hashes is cached. -/
theorem keygen_fresh (seed : MasterSeed)
    (r : (PublicKey × TopCache × Seeded.SecretKey) × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.keygenFromSeed seed)).run ∅))
    (message : Message) :
    (∀ s, r.2 (randInput r.1.2.2 message s) = none)
      ∧ (∀ ρ, r.2 (msgInput r.1.2.2 message ρ) = none)
      ∧ EncodingFresh r.1.2.2.parameter (fun _ => True) r.2 := by
  refine ⟨fun s => cache_none_of_avoids _ ∅ r hr _ rfl (Avoids.keygen_of seed _ ?_ ?_ ?_ ?_ ?_),
    fun ρ => cache_none_of_avoids _ ∅ r hr _ rfl (Avoids.keygen_of seed _ ?_ ?_ ?_ ?_ ?_),
    fun lay _ tree leaf payload => cache_none_of_avoids _ ∅ r hr _ rfl
      (Avoids.keygen_of seed _ ?_ ?_ ?_ ?_ ?_)⟩
  · intro parameter domain h
    exact fieldInput_ne_of_tag_ne' parameter r.1.2.2.parameter
      (fields1 := keygenDomainFields domain) (fields2 := ⟨7#8, 0#8, 0#40, BitVec.ofNat 32 s, 0#32⟩)
      (keygenDomain_tag_ne domain 7 (by simp)) _ _
      (by simpa only [keygenHashInput, randInput, randomizerHashInput, List.append_assoc] using h)
  · intro parameter tree leaf chainIdx step payload h
    exact fieldInput_ne_of_tag_ne' parameter r.1.2.2.parameter
      (fields1 := hashDomainFields (.chain topLayer tree leaf chainIdx step))
      (fields2 := ⟨7#8, 0#8, 0#40, BitVec.ofNat 32 s, 0#32⟩)
      (by simp [hashDomainFields, tweakFields]) _ _
      (by simpa only [tweakableHashInput, tweakBytes, randInput, randomizerHashInput,
        List.append_assoc] using h)
  · intro parameter tree leaf payload h
    exact fieldInput_ne_of_tag_ne' parameter r.1.2.2.parameter
      (fields1 := hashDomainFields (.leaf topLayer tree leaf))
      (fields2 := ⟨7#8, 0#8, 0#40, BitVec.ofNat 32 s, 0#32⟩)
      (by simp [hashDomainFields, tweakFields]) _ _
      (by simpa only [tweakableHashInput, tweakBytes, randInput, randomizerHashInput,
        List.append_assoc] using h)
  · intro parameter tree level nodeIdx payload h
    exact fieldInput_ne_of_tag_ne' parameter r.1.2.2.parameter
      (fields1 := hashDomainFields (.node topLayer tree level nodeIdx))
      (fields2 := ⟨7#8, 0#8, 0#40, BitVec.ofNat 32 s, 0#32⟩)
      (by simp [hashDomainFields, tweakFields]) _ _
      (by simpa only [tweakableHashInput, tweakBytes, randInput, randomizerHashInput,
        List.append_assoc] using h)
  · intro parameter region h
    exact macHashInput_ne_of_tag_ne parameter r.1.2.2.parameter seed region
      (fields := ⟨7#8, 0#8, 0#40, BitVec.ofNat 32 s, 0#32⟩)
      (show (7#8 : BitVec 8) ≠ 14#8 by decide) _
      (by simpa only [randInput, randomizerHashInput, List.append_assoc] using h)
  · intro parameter domain
    exact keygenHashInput_ne_tweakableHashInput parameter _ domain _ seed _
  · intro parameter tree leaf chainIdx step payload
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree leaf payload
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree level nodeIdx payload
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter region h
    exact macHashInput_ne_of_tag_ne parameter r.1.2.2.parameter seed region
      (fields := hashDomainFields .message) (by simp [hashDomainFields, tweakFields]) _
      (by simpa only [msgInput, tweakableHashInput, tweakBytes, List.append_assoc] using h)
  · intro parameter domain
    exact keygenHashInput_ne_tweakableHashInput parameter _ domain _ seed _
  · intro parameter tree' leaf' chainIdx step payload'
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree' leaf' payload'
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter tree' level nodeIdx payload'
    exact tweakableHashInput_ne_of_tag_ne' parameter _ (by simp [hashDomainFields, tweakFields]) _ _
  · intro parameter region h
    exact macHashInput_ne_of_tag_ne parameter r.1.2.2.parameter seed region
      (fields := hashDomainFields (.encoding lay tree leaf)) (by simp [hashDomainFields, tweakFields]) _
      (by simpa only [tweakableHashInput, tweakBytes, List.append_assoc] using h)

/-- Key generation's MAC query is on its replay path. -/
theorem mac_mem_queriedInputs_keygen (f : QueryImpl HashSpec Id) (seed : MasterSeed) :
    macHashInput 0 seed (keygenRegionValue f seed) ∈ queriedInputs f (Seeded.keygenFromSeed seed) := by
  rw [Seeded.keygenFromSeed]
  apply queriedInputs_mono_bind_right
  rw [keygenRegionValue_def, keygenTableValue_def]
  split
  next leaves table h =>
    rw [h]
    apply queriedInputs_mono_bind_right
    apply queriedInputs_mono_bind_left
    rw [queriedInputs_oracleHash, List.mem_singleton]

/-- After key generation, the MAC of the cache it returned is cached, with the tag it returned: the
signer's check is a cache hit that passes. -/
theorem keygen_mac_cached (seed : MasterSeed)
    (r : (PublicKey × TopCache × Seeded.SecretKey) × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _)
      (Seeded.keygenFromSeed seed)).run ∅)) :
    r.2 (macHashInput r.1.2.2.parameter r.1.2.2.seed r.1.2.1.region) = some r.1.2.1.tag := by
  obtain ⟨keys, cache⟩ := r
  obtain ⟨_, f, hf, heval, hqueries⟩ := exists_answerFn_replay_of_mem_support _ ∅ keys cache hr
  rw [eval_keygenFromSeed] at heval
  subst heval
  obtain ⟨answer, hanswer⟩ :=
    Option.ne_none_iff_exists'.mp (hqueries _ (mac_mem_queriedInputs_keygen f seed))
  dsimp only
  rw [hanswer, hf hanswer]

end SphincsSecurity.Completeness
