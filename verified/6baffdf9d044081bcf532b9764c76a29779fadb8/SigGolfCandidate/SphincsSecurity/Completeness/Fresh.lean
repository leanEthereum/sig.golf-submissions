import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Support
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Bytes
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.KeyDerivation

/-!
# Inputs a computation leaves alone

The search bound of `Search.lean` needs its trials to be uncached when the search starts. What
supplies that is domain separation: key generation and the rest of signing hash under structural
tweaks and under the derivation domains, never under the encoding tweak a counter search uses, so
those inputs are still absent from the cache when the search reaches them.

`Avoids f target oa` is that fact for one input, and it composes along the computation.
-/

open OracleComp OracleSpec

namespace SphincsSecurity.Completeness

open Concrete

/-- Two hash inputs whose tweak fields differ in the tag differ, whatever their payloads. -/
theorem fieldInput_ne_of_tag_ne (parameter : PublicParameter) {fields1 fields2 : TweakFields}
    (htag : fields1.tag ≠ fields2.tag) (payload1 payload2 : HashInput) :
    fieldBytes fields1 ++ bytesLE 16 parameter ++ payload1
      ≠ fieldBytes fields2 ++ bytesLE 16 parameter ++ payload2 := by
  intro h
  apply htag
  obtain ⟨hprefix, _⟩ := List.append_inj h (by
    simp [fieldBytes, bytesLE_length])
  obtain ⟨hfields, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  rw [SphincsSecurity.fieldBytes_injective hfields]

/-- Two tweakable inputs with different tweak tags differ, whatever their payloads. -/
theorem tweakableHashInput_ne_of_tag_ne (parameter : PublicParameter) {d1 d2 : HashDomain}
    (htag : (hashDomainFields d1).tag ≠ (hashDomainFields d2).tag)
    (payload1 payload2 : HashInput) :
    tweakableHashInput parameter d1 payload1 ≠ tweakableHashInput parameter d2 payload2 := by
  intro h
  apply htag
  simp only [tweakableHashInput] at h
  obtain ⟨hprefix, _⟩ := List.append_inj h (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  rw [SphincsSecurity.tweakBytes_eq_iff.mp htweak]

/-- The tag byte precedes the parameter, so inputs under different tags differ even across parameters. -/
theorem fieldInput_ne_of_tag_ne' (parameter parameter' : PublicParameter)
    {fields1 fields2 : TweakFields} (htag : fields1.tag ≠ fields2.tag) (payload1 payload2 : HashInput) :
    fieldBytes fields1 ++ bytesLE 16 parameter ++ payload1
      ≠ fieldBytes fields2 ++ bytesLE 16 parameter' ++ payload2 := by
  intro h
  apply htag
  obtain ⟨hprefix, _⟩ := List.append_inj h (by simp [fieldBytes, bytesLE_length]; exact (bytesLE_length 16 _).trans (bytesLE_length 16 _).symm)
  obtain ⟨hfields, _⟩ := List.append_inj' hprefix ((bytesLE_length 16 _).trans (bytesLE_length 16 _).symm)
  rw [SphincsSecurity.fieldBytes_injective hfields]

theorem tweakableHashInput_ne_of_tag_ne' (parameter parameter' : PublicParameter)
    {d1 d2 : HashDomain} (htag : (hashDomainFields d1).tag ≠ (hashDomainFields d2).tag)
    (payload1 payload2 : HashInput) :
    tweakableHashInput parameter d1 payload1 ≠ tweakableHashInput parameter' d2 payload2 :=
  fieldInput_ne_of_tag_ne' parameter parameter' htag payload1 payload2

variable (f : QueryImpl HashSpec Id) (target : HashInput)

/-- The computation never queries `target`. -/
def Avoids {α : Type} (oa : OracleComp HashSpec α) : Prop := target ∉ queriedInputs f oa

theorem Avoids.pure' {α : Type} (value : α) : Avoids f target (Pure.pure value) := by
  simp [Avoids]

theorem Avoids.bind {α β : Type} {oa : OracleComp HashSpec α}
    {next : α → OracleComp HashSpec β} (hleft : Avoids f target oa)
    (hright : Avoids f target (next (evalWithAnswerFn f oa))) :
    Avoids f target (oa >>= next) := by
  intro hmem
  rw [queriedInputs_bind] at hmem
  rcases List.mem_append.mp hmem with hmem | hmem
  · exact hleft hmem
  · exact hright hmem

theorem Avoids.tweakableHash (parameter : PublicParameter) (domain : HashDomain)
    (payload : HashInput) (hne : tweakableHashInput parameter domain payload ≠ target) :
    Avoids f target (Concrete.tweakableHash parameter domain payload) := by
  intro hmem
  simp only [queriedInputs_tweakableHash, List.mem_singleton] at hmem
  exact hne hmem.symm

theorem Avoids.sequenceFin {α : Type} {n : Nat} (computation : Fin n → OracleComp HashSpec α)
    (h : ∀ index, Avoids f target (computation index)) :
    Avoids f target (sequenceFin computation) := by
  induction n with
  | zero => exact Avoids.pure' f target _
  | succ n ih =>
      rw [Concrete.sequenceFin]
      refine Avoids.bind f target (h 0) ?_
      exact Avoids.bind f target (ih _ (fun index => h index.succ)) (Avoids.pure' f target _)

theorem queriedInputs_deriveKey (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) :
    queriedInputs f (deriveKey parameter domain seed : OracleComp HashSpec Digest)
      = [keygenHashInput parameter domain seed] := rfl

theorem Avoids.deriveKey (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed)
    (hne : keygenHashInput parameter domain seed ≠ target) :
    Avoids f target (deriveKey parameter domain seed : OracleComp HashSpec Digest) := by
  intro hmem
  rw [queriedInputs_deriveKey, List.mem_singleton] at hmem
  exact hne hmem.symm

theorem Avoids.chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex)
    (hne : ∀ (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target) :
    ∀ (start steps : Nat) (value : Digest),
      Avoids f target (Concrete.chainWalk parameter lay tree leaf chainIdx start steps value
        : OracleComp HashSpec Digest) := by
  intro start steps
  induction steps with
  | zero => intro value; exact Avoids.pure' f target _
  | succ steps ih =>
      intro value
      rw [Concrete.chainWalk]
      refine Avoids.bind f target (ih value) ?_
      split
      · exact Avoids.tweakableHash f target parameter _ _ (hne _ _)
      · exact Avoids.pure' f target _


theorem Avoids.leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (endpoints : ChainIndex → Digest)
    (hne : ∀ payload : HashInput, tweakableHashInput parameter (.leaf lay tree leaf) payload ≠ target) :
    Avoids f target (Concrete.leafHash parameter lay tree leaf endpoints
      : OracleComp HashSpec Digest) :=
  Avoids.tweakableHash f target parameter _ _ (hne _)

/-! ## Building trees

A builder hashes the leaves it is handed through its secret derivation, then the levels through its
node hash; it avoids whatever all of those avoid. -/

theorem Avoids.buildLevel (hashNode : Nat → Digest → Digest → OracleComp HashSpec Digest)
    (width : Nat) (below : Nat → Digest)
    (hnode : ∀ nodeIdx left right, Avoids f target (hashNode nodeIdx left right)) :
    Avoids f target (Concrete.buildLevel hashNode width below) := by
  rw [Concrete.buildLevel]
  exact Avoids.bind f target (Avoids.sequenceFin f target _ fun _ => hnode _ _ _)
    (Avoids.pure' f target _)

theorem Avoids.buildLevels (hashNode : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (height : Nat) (leaves : Nat → Digest)
    (hnode : ∀ level nodeIdx left right, Avoids f target (hashNode level nodeIdx left right)) :
    ∀ levels, Avoids f target (Concrete.buildLevels hashNode height leaves levels) := by
  intro levels
  induction levels with
  | zero => exact Avoids.pure' f target _
  | succ levels ih =>
      rw [Concrete.buildLevels]
      exact Avoids.bind f target ih (Avoids.bind f target
        (Avoids.buildLevel f target _ _ _ (hnode _)) (Avoids.pure' f target _))

theorem Avoids.buildChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : OracleComp HashSpec Digest) (digit : Nat)
    (hsecret : Avoids f target secret)
    (hchain : ∀ (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target) :
    Avoids f target (Concrete.buildChain parameter lay tree leaf chainIdx secret digit) := by
  rw [Concrete.buildChain]
  exact Avoids.bind f target hsecret
    (Avoids.bind f target (Avoids.chainWalk f target parameter lay tree leaf chainIdx hchain _ _ _)
      (Avoids.bind f target (Avoids.chainWalk f target parameter lay tree leaf chainIdx hchain _ _ _)
        (Avoids.pure' f target _)))

theorem Avoids.buildLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (secret : ChainIndex → OracleComp HashSpec Digest) (digits : Encoding)
    (hsecret : ∀ chainIdx, Avoids f target (secret chainIdx))
    (hchain : ∀ (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target)
    (hleaf : ∀ payload : HashInput,
      tweakableHashInput parameter (.leaf lay tree leaf) payload ≠ target) :
    Avoids f target (Concrete.buildLeaf parameter lay tree leaf secret digits) := by
  rw [Concrete.buildLeaf]
  exact Avoids.bind f target
    (Avoids.sequenceFin f target _ fun chainIdx =>
      Avoids.buildChain f target parameter lay tree leaf chainIdx _ _ (hsecret chainIdx)
        (hchain chainIdx))
    (Avoids.bind f target (Avoids.leafHash f target parameter lay tree leaf _ hleaf)
      (Avoids.pure' f target _))

/-- Building a layer's tree avoids every input outside that tree's chain, leaf and node tweaks and
its secrets. -/
theorem Avoids.buildLayerTree (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (digits : Encoding)
    (hsecret : ∀ leaf chainIdx, Avoids f target (secret leaf chainIdx))
    (hchain : ∀ (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target)
    (hleaf : ∀ (leaf : LeafIndex) (payload : HashInput),
      tweakableHashInput parameter (.leaf lay tree leaf) payload ≠ target)
    (hnode : ∀ (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.node lay tree level nodeIdx) payload ≠ target) :
    Avoids f target (Concrete.buildLayerTree parameter lay tree secret leaf digits) := by
  rw [Concrete.buildLayerTree]
  refine Avoids.bind f target (Avoids.sequenceFin f target _ fun _ =>
    Avoids.buildLeaf f target parameter lay tree _ _ _ (hsecret _) (hchain _) (hleaf _)) ?_
  exact Avoids.bind f target
    (Avoids.buildLevels f target _ _ _
      (fun _ _ _ _ => Avoids.tweakableHash f target parameter _ _ (hnode _ _ _)) _)
    (Avoids.pure' f target _)

theorem Avoids.buildFtsTree (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → OracleComp HashSpec Digest) (leaf : FtsLeaf)
    (hsecret : ∀ leaf, Avoids f target (secret leaf))
    (hleafHash : ∀ (leaf : FtsLeaf) (payload : HashInput),
      tweakableHashInput parameter (.ftsLeaf index tree leaf) payload ≠ target)
    (hnode : ∀ (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.ftsNode index tree level nodeIdx) payload ≠ target) :
    Avoids f target (Concrete.buildFtsTree parameter index tree secret leaf) := by
  rw [Concrete.buildFtsTree]
  refine Avoids.bind f target (Avoids.sequenceFin f target _ fun leafIdx =>
    Avoids.bind f target (hsecret leafIdx) (Avoids.bind f target
      (Avoids.tweakableHash f target parameter _ _ (hleafHash _ _)) (Avoids.pure' f target _))) ?_
  exact Avoids.bind f target
    (Avoids.buildLevels f target _ _ _
      (fun _ _ _ _ => Avoids.tweakableHash f target parameter _ _ (hnode _ _ _)) _)
    (Avoids.pure' f target _)

theorem Avoids.buildForest (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → OracleComp HashSpec Digest) (leaves : IndexGroup → FtsLeaf)
    (hsecret : ∀ tree leaf, Avoids f target (secret tree leaf))
    (hleafHash : ∀ (tree : FtsTree) (leaf : FtsLeaf) (payload : HashInput),
      tweakableHashInput parameter (.ftsLeaf index tree leaf) payload ≠ target)
    (hnode : ∀ (tree : FtsTree) (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.ftsNode index tree level nodeIdx) payload ≠ target)
    (hroots : ∀ payload : HashInput,
      tweakableHashInput parameter (.ftsRoots index) payload ≠ target) :
    Avoids f target (Concrete.buildForest parameter index secret leaves) := by
  rw [Concrete.buildForest]
  exact Avoids.bind f target (Avoids.sequenceFin f target _ fun tree =>
    Avoids.buildFtsTree f target parameter index tree _ _ (hsecret tree) (hleafHash tree)
      (hnode tree))
    (Avoids.bind f target (Avoids.tweakableHash f target parameter _ _ (hroots _))
      (Avoids.pure' f target _))

/-- Building a layer's table avoids what building its tree avoids: the same queries. -/
theorem Avoids.buildLayerTable (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex)
    (digits : Encoding)
    (hsecret : ∀ leaf chainIdx, Avoids f target (secret leaf chainIdx))
    (hchain : ∀ (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target)
    (hleaf : ∀ (leaf : LeafIndex) (payload : HashInput),
      tweakableHashInput parameter (.leaf lay tree leaf) payload ≠ target)
    (hnode : ∀ (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput parameter (.node lay tree level nodeIdx) payload ≠ target) :
    Avoids f target (Concrete.buildLayerTable parameter lay tree secret leaf digits) := by
  rw [Concrete.buildLayerTable]
  refine Avoids.bind f target (Avoids.sequenceFin f target _ fun _ =>
    Avoids.buildLeaf f target parameter lay tree _ _ _ (hsecret _) (hchain _) (hleaf _)) ?_
  exact Avoids.bind f target
    (Avoids.buildLevels f target _ _ _
      (fun _ _ _ _ => Avoids.tweakableHash f target parameter _ _ (hnode _ _ _)) _)
    (Avoids.pure' f target _)

theorem queriedInputs_oracleHash (input : HashInput) :
    queriedInputs f (oracleHash input : OracleComp HashSpec HashOutput) = [input] := rfl

theorem Avoids.oracleHash (input : HashInput) (hne : input ≠ target) :
    Avoids f target (oracleHash input : OracleComp HashSpec HashOutput) := by
  intro hmem
  rw [queriedInputs_oracleHash, List.mem_singleton] at hmem
  exact hne hmem.symm

/-- Masking the top tree derives the masks and nothing else. -/
theorem Avoids.maskRegion (parameter : PublicParameter) (seed : MasterSeed)
    (table : Nat → Nat → Digest)
    (hmask : ∀ level nodeIdx : Nat, keygenHashInput parameter (Seeded.maskDomain level nodeIdx) seed ≠ target) :
    Avoids f target (Seeded.maskRegion parameter seed table : OracleComp HashSpec TopRegion) := by
  rw [Seeded.maskRegion]
  refine Avoids.bind f target (Avoids.sequenceFin f target _ fun level => ?_) (Avoids.pure' f target _)
  refine Avoids.bind f target (Avoids.sequenceFin f target _ fun nodeIdx => ?_) (Avoids.pure' f target _)
  exact Avoids.bind f target (Avoids.deriveKey f target parameter _ seed (hmask _ _))
    (Avoids.pure' f target _)

/-- Key generation builds the top tree from its derived secrets, masks it with derived masks, and
authenticates the masked region with one MAC query, and nothing else. -/
theorem Avoids.keygenFromSeed (seed : MasterSeed)
    (hchain : ∀ (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep) (payload : HashInput),
      tweakableHashInput 0 (.chain topLayer rootTree leaf chainIdx step) payload ≠ target)
    (hleaf : ∀ (leaf : LeafIndex) (payload : HashInput),
      tweakableHashInput 0 (.leaf topLayer rootTree leaf) payload ≠ target)
    (hnode : ∀ (level nodeIdx : Nat) (payload : HashInput),
      tweakableHashInput 0 (.node topLayer rootTree level nodeIdx) payload ≠ target)
    (hderive : ∀ domain : KeygenDomain, keygenHashInput 0 domain seed ≠ target)
    (hmac : ∀ region : TopRegion, macHashInput 0 seed region ≠ target) :
    Avoids f target (Seeded.keygenFromSeed seed) := by
  rw [Seeded.keygenFromSeed]
  refine Avoids.bind f target
    (Avoids.buildLayerTable f target 0 topLayer rootTree _ _ _
      (fun leaf chainIdx => Avoids.deriveKey f target 0 _ seed (hderive _))
      hchain hleaf hnode) ?_
  -- `split` keeps the tree build opaque; unifying with the `match` on it makes the kernel run the
  -- whole build
  split
  exact Avoids.bind f target (Avoids.maskRegion f target 0 seed _ fun _ _ => hderive _)
    (Avoids.bind f target (Avoids.oracleHash f target _ (hmac _)) (Avoids.pure' f target _))

/-! ## The signing side

The digest loop hashes under the randomizer tweak and the message tweak, never under the encoding
tweak a counter search walks. -/

theorem queriedInputs_deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) :
    queriedInputs f (deriveRandomizer parameter seed message trial
        : OracleComp HashSpec Randomness)
      = [randomizerHashInput parameter seed message trial] := rfl

theorem Avoids.deriveRandomizer (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32)
    (hne : randomizerHashInput parameter seed message trial ≠ target) :
    Avoids f target (SphincsSecurity.deriveRandomizer parameter seed message trial
      : OracleComp HashSpec Randomness) := by
  intro hmem
  rw [queriedInputs_deriveRandomizer, List.mem_singleton] at hmem
  exact hne hmem.symm

theorem queriedInputs_messageDigest (parameter : PublicParameter) (root : Digest)
    (message : Message) (randomness : Randomness) :
    queriedInputs f (Concrete.messageDigest parameter root message randomness
        : OracleComp HashSpec MessageDigest)
      = [tweakableHashInput parameter .message
          (Concrete.messageDigestPayload root message randomness)] := rfl

theorem Avoids.messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness)
    (hne : tweakableHashInput parameter .message
      (Concrete.messageDigestPayload root message randomness) ≠ target) :
    Avoids f target (Concrete.messageDigest parameter root message randomness
      : OracleComp HashSpec MessageDigest) := by
  intro hmem
  rw [queriedInputs_messageDigest, List.mem_singleton] at hmem
  exact hne hmem.symm

theorem Avoids.signAttempt (secretKey : Seeded.SecretKey) (message : Message)
    (randomness : Randomness)
    (hne : tweakableHashInput secretKey.parameter .message
      (Concrete.messageDigestPayload secretKey.root message randomness) ≠ target) :
    Avoids f target (Seeded.signAttempt secretKey message randomness
      : OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) := by
  rw [Seeded.signAttempt]
  refine Avoids.bind f target (Avoids.messageDigest f target _ _ _ _ hne) ?_
  split <;> exact Avoids.pure' f target _

theorem Avoids.signDigestLoop (secretKey : Seeded.SecretKey) (message : Message)
    (hrand : ∀ trial : BitVec 32,
      randomizerHashInput secretKey.parameter secretKey.seed message trial ≠ target)
    (hmsg : ∀ randomness : Randomness, tweakableHashInput secretKey.parameter .message
      (Concrete.messageDigestPayload secretKey.root message randomness) ≠ target) :
    ∀ (attempts trial : Nat),
      Avoids f target (Seeded.signDigestLoop secretKey message attempts trial
        : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf)))) := by
  intro attempts
  induction attempts with
  | zero => intro trial; exact Avoids.pure' f target _
  | succ attempts ih =>
      intro trial
      rw [Seeded.signDigestLoop]
      refine Avoids.bind f target (Avoids.deriveRandomizer f target _ _ _ _ (hrand _)) ?_
      refine Avoids.bind f target (Avoids.signAttempt f target _ _ _ (hmsg _)) ?_
      split
      · exact Avoids.pure' f target _
      · exact ih _


/-! ## A layer

A layer's own work is its counter search, under its encoding tweak, and its tree. -/

theorem Avoids.encodingSearch (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest)
    (hencode : ∀ payload : HashInput,
      tweakableHashInput parameter (.encoding lay tree leaf) payload ≠ target) :
    ∀ (attempts start : Nat),
      Avoids f target (Concrete.encodingSearch parameter lay tree leaf message attempts start
        : OracleComp HashSpec (Option (Counter × Encoding))) := by
  intro attempts
  induction attempts with
  | zero => intro start; exact Avoids.pure' f target _
  | succ attempts ih =>
      intro start
      rw [Concrete.encodingSearch]
      refine Avoids.bind f target ?_ ?_
      · rw [Concrete.encode]
        exact Avoids.bind f target
          (Avoids.tweakableHash f target parameter _ _ (hencode _)) (Avoids.pure' f target _)
      · split
        · exact Avoids.pure' f target _
        · exact ih _

/-- Different layers' counter searches hash under different layer fields, so none of them caches another's inputs. -/
theorem encodingInput_ne_of_layer_ne (parameter : PublicParameter) {lay lay' : Layer}
    (hlay : lay ≠ lay') (tree tree' : TreeIndex) (leaf leaf' : LeafIndex)
    (payload payload' : HashInput) :
    tweakableHashInput parameter (.encoding lay tree leaf) payload
      ≠ tweakableHashInput parameter (.encoding lay' tree' leaf') payload' := by
  intro h
  apply hlay
  simp only [tweakableHashInput] at h
  obtain ⟨hprefix, _⟩ := List.append_inj h (by simp [tweakBytes_length, bytesLE_length])
  obtain ⟨htweak, _⟩ := List.append_inj' hprefix (by simp [bytesLE_length])
  have hfields := SphincsSecurity.tweakBytes_eq_iff.mp htweak
  simp only [hashDomainFields, tweakFields, TweakFields.mk.injEq] at hfields
  have hv := congrArg BitVec.toNat hfields.2.1
  simp only [BitVec.toNat_ofNat] at hv
  have hl : lay.val < 2 ^ 8 := by have := lay.isLt; simp only [numLayers] at this; omega
  have hl' : lay'.val < 2 ^ 8 := by have := lay'.isLt; simp only [numLayers] at this; omega
  rw [Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hl'] at hv
  exact Fin.ext hv

/-! ## Packaging

Every hypothesis above says the same thing: the target is not the input some honest step hashes. For
an encoding input all of them hold at once, by the tag alone, so it is worth naming the bundle. -/

/-- The target is none of the inputs the honest algorithms hash under a structural or derivation tweak. -/
structure Structural (parameter : PublicParameter) (seed : MasterSeed) (target : HashInput) : Prop where
  chain : ∀ (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    (step : ChainStep) (payload : HashInput),
    tweakableHashInput parameter (.chain lay tree leaf chainIdx step) payload ≠ target
  leafHash : ∀ (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput),
    tweakableHashInput parameter (.leaf lay tree leaf) payload ≠ target
  node : ∀ (lay : Layer) (tree : TreeIndex) (level nodeIdx : Nat) (payload : HashInput),
    tweakableHashInput parameter (.node lay tree level nodeIdx) payload ≠ target
  ftsLeaf : ∀ (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (payload : HashInput),
    tweakableHashInput parameter (.ftsLeaf index tree leaf) payload ≠ target
  ftsNodeHash : ∀ (index : Index) (tree : FtsTree) (level nodeIdx : Nat) (payload : HashInput),
    tweakableHashInput parameter (.ftsNode index tree level nodeIdx) payload ≠ target
  ftsRoots : ∀ (index : Index) (payload : HashInput),
    tweakableHashInput parameter (.ftsRoots index) payload ≠ target
  msg : ∀ payload : HashInput, tweakableHashInput parameter .message payload ≠ target
  randomizer : ∀ (message : Message) (trial : BitVec 32),
    randomizerHashInput parameter seed message trial ≠ target
  derive : ∀ domain : KeygenDomain, keygenHashInput parameter domain seed ≠ target

/-- An encoding input is structural for no honest step: its tag is `4`, which none of them use, and the derivation domains are a different byte layout. -/
theorem structural_encoding (parameter : PublicParameter) (seed : MasterSeed) (lay' : Layer)
    (tree' : TreeIndex) (leaf' : LeafIndex) (payload' : HashInput) :
    Structural parameter seed (tweakableHashInput parameter (.encoding lay' tree' leaf') payload') where
  chain _ _ _ _ _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields]) _ _
  leafHash _ _ _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields]) _ _
  node _ _ _ _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields]) _ _
  ftsLeaf _ _ _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields]) _ _
  ftsNodeHash _ _ _ _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields]) _ _
  ftsRoots _ _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields]) _ _
  msg _ := tweakableHashInput_ne_of_tag_ne parameter
    (by simp [hashDomainFields, tweakFields]) _ _
  randomizer _ _ := fieldInput_ne_of_tag_ne parameter (by simp [hashDomainFields, tweakFields]) _ _
  derive _ := keygenHashInput_ne_tweakableHashInput parameter parameter _ _ seed _

/-! ## What the bundle gives

With the bundle, each honest step's avoidance needs no further argument. -/

theorem Avoids.signDigestLoop_of_structural (secretKey : Seeded.SecretKey) (message : Message)
    (hstruct : Structural secretKey.parameter secretKey.seed target) :
    ∀ (attempts trial : Nat),
      Avoids f target (Seeded.signDigestLoop secretKey message attempts trial
        : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf)))) :=
  Avoids.signDigestLoop f target secretKey message
    (fun trial => hstruct.randomizer message trial) (fun _ => hstruct.msg _)

theorem Avoids.buildForest_of_structural (parameter : PublicParameter) (index : Index)
    (seed : MasterSeed) (leaves : IndexGroup → FtsLeaf) (hstruct : Structural parameter seed target) :
    Avoids f target (Concrete.buildForest parameter index (Seeded.ftsSecret parameter seed index) leaves
      : OracleComp HashSpec _) :=
  Avoids.buildForest f target parameter index _ leaves
    (fun _ _ => Avoids.deriveKey f target parameter _ seed (hstruct.derive _))
    (fun tree leaf payload => hstruct.ftsLeaf index tree leaf payload)
    (fun tree level nodeIdx payload => hstruct.ftsNodeHash index tree level nodeIdx payload)
    (fun payload => hstruct.ftsRoots index payload)

theorem Avoids.buildLayerTree_of_structural (parameter : PublicParameter) (seed : MasterSeed)
    (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (digits : Encoding)
    (hstruct : Structural parameter seed target) :
    Avoids f target (Concrete.buildLayerTree parameter lay tree (Seeded.otsSecret parameter seed lay tree)
      leaf digits : OracleComp HashSpec _) :=
  Avoids.buildLayerTree f target parameter lay tree _ leaf digits
    (fun _ _ => Avoids.deriveKey f target parameter _ seed (hstruct.derive _))
    (fun leaf chainIdx step payload => hstruct.chain lay tree leaf chainIdx step payload)
    (fun leaf payload => hstruct.leafHash lay tree leaf payload)
    (fun level nodeIdx payload => hstruct.node lay tree level nodeIdx payload)

/-! ## The invariant a signature keeps

Signing runs its six counter searches one after another. Before each, no encoding input of a
layer still to come is cached: key generation and every earlier step avoid them. -/

/-- A computation that avoids an input, run from a cache missing it, leaves it missing. -/
theorem cache_none_of_avoids {α : Type} (oa : OracleComp HashSpec α) (cache : QueryCache HashSpec)
    (r : α × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache))
    (target : HashInput) (hnone : cache target = none)
    (havoid : ∀ f : QueryImpl HashSpec Id, Avoids f target oa) : r.2 target = none := by
  obtain ⟨f, hf⟩ := QueryCache.exists_agreesWithFn (spec := HashSpec) r.2
  exact cache_eq_none_of_not_mem_queriedInputs oa cache r.1 r.2 hr f hf target hnone (havoid f)

/-- No encoding input of a layer in `pending` is cached. -/
def EncodingFresh (parameter : PublicParameter) (pending : Layer → Prop)
    (cache : QueryCache HashSpec) : Prop :=
  ∀ lay, pending lay → ∀ (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput),
    cache (tweakableHashInput parameter (.encoding lay tree leaf) payload) = none

theorem EncodingFresh.step {α : Type} {parameter : PublicParameter} {pending : Layer → Prop}
    {cache : QueryCache HashSpec} (hfresh : EncodingFresh parameter pending cache)
    (oa : OracleComp HashSpec α) (r : α × QueryCache HashSpec)
    (hr : r ∈ support ((simulateQ (randomOracle : QueryImpl HashSpec _) oa).run cache))
    (havoid : ∀ (f : QueryImpl HashSpec Id) (lay : Layer), pending lay →
      ∀ (tree : TreeIndex) (leaf : LeafIndex) (payload : HashInput),
        Avoids f (tweakableHashInput parameter (.encoding lay tree leaf) payload) oa) :
    EncodingFresh parameter pending r.2 := fun lay hlay tree leaf payload =>
  cache_none_of_avoids oa cache r hr _ (hfresh lay hlay tree leaf payload)
    (fun f => havoid f lay hlay tree leaf payload)

end SphincsSecurity.Completeness
