import SigGolfCandidate.Equiv.Basic

/-!
# Honest hash inputs

`Honest x`: `x` starts with the protocol byte `1`, and its length is the one fixed by its tag
(byte 1). Zero padding (`padQ`) is injective on honest inputs, and every query of the abstract key
generation, signer and verifier is honest (for all inputs and all oracle answers).
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolf (Byte Bytes Query)
open SigGolfCandidate.Bridge (AllQ allQ_pure allQ_bind allQ_query allQ_map)
open SphincsSecurity (Digest Layer TreeIndex LeafIndex ChainIndex Encoding MasterSeed Index FtsTree
  FtsLeaf IndexGroup Message Signature)
open SphincsSecurity.Concrete (sequenceFin)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-- The input length of each tag. -/
def tagLen : Nat → Nat
  | 0 => 64 | 1 => 48 | 2 => 704 | 3 => 64 | 4 => 52 | 7 => 96 | 8 => 64 | 9 => 48 | 10 => 64
  | 11 => 256 | 12 => 96 | _ => 0

/-- An honest hash input: protocol byte `1`, and the length fixed by the tag byte. -/
def Honest (x : List UInt8) : Prop :=
  x.head? = some 1 ∧ x.length = tagLen (x.getD 1 0).toNat

theorem honest_head (x : List UInt8) (h : Honest x) : x.head? = some 1 := h.1

/-! ## Zero padding is injective on honest inputs -/

/-- The bytes of a query. -/
def qbytes (q : Query) : List Byte := Ref.toList q.2

theorem length_padTo64 (z : List Byte) : (Ref.padTo64 z).length = 64 * (Ref.padBlocks z.length + 1) := by
  unfold Ref.padTo64 Ref.padBlocks
  simp only [List.length_append, Ref.length_zeros]
  omega

theorem qbytes_pad64 (z : List Byte) : qbytes (Ref.pad64 z) = Ref.padTo64 z :=
  Ref.toList_ofList _ _ (length_padTo64 z)

theorem getD_toB (x : List UInt8) (i : Nat) : (toB x).getD i 0 = (x.getD i 0).toBitVec := by
  simp only [toB, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases x[i]? <;> rfl

theorem tagLen_cases (n : Nat) : tagLen n = 0 ∨ 48 ≤ tagLen n := by
  unfold tagLen; split <;> simp

theorem honest_length (x : List UInt8) (h : Honest x) : 48 ≤ x.length := by
  rcases tagLen_cases (x.getD 1 0).toNat with h0 | h0
  · have hl : x.length = 0 := h.2.trans h0
    have hh := h.1
    rw [List.length_eq_zero_iff.mp hl] at hh
    simp at hh
  · rw [h.2]; exact h0

theorem getD_append_left' {β : Type} (l₁ l₂ : List β) (i : Nat) (d : β) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem padQ_injOn : Set.InjOn padQ Honest := by
  intro x hx y hy hxy
  have h1 : Ref.padTo64 (toB x) = Ref.padTo64 (toB y) := by
    rw [← qbytes_pad64, ← qbytes_pad64]; exact congrArg qbytes hxy
  have hx2 := honest_length x hx
  have hy2 := honest_length y hy
  have ht : x.getD 1 0 = y.getD 1 0 := by
    have := congrArg (fun l => l.getD 1 0) h1
    simp only [Ref.padTo64] at this
    rw [getD_append_left' _ _ _ _ (by simp; omega), getD_append_left' _ _ _ _ (by simp; omega),
      getD_toB, getD_toB] at this
    exact UInt8.toBitVec_inj.mp this
  have hlen : x.length = y.length := by rw [hx.2, hy.2, ht]
  apply toB_injective
  have := congrArg (fun l => l.take x.length) h1
  simp only [Ref.padTo64] at this
  rw [List.take_append_of_le_length (by simp), List.take_append_of_le_length (by simp; omega)] at this
  rw [List.take_of_length_le (by simp), hlen, List.take_of_length_le (by simp)] at this
  exact this

/-! ## Honest inputs -/

theorem length_bytesLE (n : Nat) (v : BitVec (8 * n)) : (SphincsSecurity.bytesLE n v).length = n := by
  simp [SphincsSecurity.bytesLE]

theorem length_fieldBytes (f : SphincsSecurity.TweakFields) : (SphincsSecurity.fieldBytes f).length = 16 := by
  simp [SphincsSecurity.fieldBytes, length_bytesLE]

theorem honest_fieldBytes (f : SphincsSecurity.TweakFields) (rest : List UInt8)
    (h : 16 + rest.length = tagLen f.tag.toNat) : Honest (SphincsSecurity.fieldBytes f ++ rest) := by
  refine ⟨by simp [SphincsSecurity.fieldBytes, SphincsSecurity.protocolDomainSep], ?_⟩
  rw [List.length_append, length_fieldBytes, h]
  congr 1
  simp only [SphincsSecurity.fieldBytes, SphincsSecurity.bytesLE, List.append_assoc]
  simp [List.getD_eq_getElem?_getD]

theorem honest_th (P : SphincsSecurity.PublicParameter) (dom : SphincsSecurity.HashDomain)
    (payload : List UInt8)
    (h : 32 + payload.length = tagLen (SphincsSecurity.hashDomainFields dom).tag.toNat) :
    Honest (SphincsSecurity.tweakableHashInput P dom payload) := by
  unfold SphincsSecurity.tweakableHashInput SphincsSecurity.tweakBytes
  rw [List.append_assoc]
  apply honest_fieldBytes
  rw [List.length_append, length_bytesLE]; omega

/-! ## Every abstract query is honest -/

/-- Every query of an abstract computation is honest. -/
abbrev HQ {α : Type} (oa : AComp α) : Prop :=
  AllQ (ι := List UInt8) (R := SphincsSecurity.HashOutput) Honest oa

theorem hq_pure {α : Type} (a : α) : HQ (pure a : AComp α) := trivial

theorem hq_bind {α β : Type} {oa : AComp α} {ob : α → AComp β} (h : HQ oa) (h' : ∀ x, HQ (ob x)) :
    HQ (oa >>= ob) := allQ_bind Honest h h'

theorem hq_oracleHash (x : List UInt8) (h : Honest x) :
    HQ (SphincsSecurity.Concrete.oracleHash (m := AComp) x) :=
  (allQ_query (R := SphincsSecurity.HashOutput) Honest x).mpr h

theorem hq_th (P : SphincsSecurity.PublicParameter) (dom : SphincsSecurity.HashDomain)
    (payload : List UInt8)
    (h : 32 + payload.length = tagLen (SphincsSecurity.hashDomainFields dom).tag.toNat) :
    HQ (SphincsSecurity.Concrete.tweakableHash (m := AComp) P dom payload) :=
  hq_bind (hq_oracleHash _ (honest_th P dom payload h)) fun _ => hq_pure _

theorem hq_sequenceFin {α : Type} {n : Nat} (c : Fin n → AComp α) (h : ∀ j, HQ (c j)) :
    HQ (sequenceFin c) := by
  induction n with
  | zero => exact hq_pure _
  | succ n ih =>
    exact hq_bind (h 0) fun _ => hq_bind (ih _ fun j => h j.succ) fun _ => hq_pure _

macro "hq" : tactic => `(tactic| repeat (first
  | exact hq_pure _
  | refine hq_bind ?_ (fun _ => ?_)
  | refine hq_sequenceFin _ (fun _ => ?_)
  | split))

/-! ### Hash calls -/

section calls

open SphincsSecurity.Concrete

variable (P : SphincsSecurity.PublicParameter)

theorem length_flatMap16 (l : List Digest) :
    (l.flatMap (SphincsSecurity.bytesLE 16)).length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [List.flatMap_cons, length_bytesLE, ih]; ring

theorem hq_chainWalk (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (c : ChainIndex)
    (start steps : Nat) (v : Digest) : HQ (chainWalk (m := AComp) P lay tree leaf c start steps v) := by
  induction steps with
  | zero => exact hq_pure _
  | succ n ih =>
    refine hq_bind ih fun prev => ?_
    split
    · exact hq_th _ _ _ (by simp [SphincsSecurity.hashDomainFields, SphincsSecurity.tweakFields,
        tagLen, length_bytesLE])
    · exact hq_pure _

theorem hq_leafHash (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (ends : ChainIndex → Digest) :
    HQ (leafHash (m := AComp) P lay tree leaf ends) :=
  hq_th _ _ _ (by
    rw [leafPayload, length_flatMap16, List.length_ofFn]
    simp [SphincsSecurity.hashDomainFields, SphincsSecurity.tweakFields, tagLen, SphincsSecurity.numChains])

theorem hq_node (lay : Layer) (tree : TreeIndex) (lam j : Nat) (l r : Digest) :
    HQ (tweakableHash (m := AComp) P (.node lay tree lam j) (nodePayload l r)) :=
  hq_th _ _ _ (by simp [SphincsSecurity.hashDomainFields, SphincsSecurity.tweakFields, tagLen,
    nodePayload, length_bytesLE])

theorem hq_ftsNode (index : Index) (tree : FtsTree) (lam j : Nat) (l r : Digest) :
    HQ (tweakableHash (m := AComp) P (.ftsNode index tree lam j) (nodePayload l r)) :=
  hq_th _ _ _ (by simp [SphincsSecurity.hashDomainFields, SphincsSecurity.tweakFields, tagLen,
    nodePayload, length_bytesLE])

theorem hq_encode (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (M : Digest)
    (c : SphincsSecurity.Counter) : HQ (encode (m := AComp) P lay tree leaf M c) :=
  hq_bind (hq_th _ _ _ (by simp [SphincsSecurity.hashDomainFields, SphincsSecurity.tweakFields,
    tagLen, length_bytesLE])) fun _ => hq_pure _

theorem hq_ftsLeafHash (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (s : Digest) :
    HQ (ftsLeafHash (m := AComp) P index tree leaf s) :=
  hq_th _ _ _ (by simp [SphincsSecurity.hashDomainFields, SphincsSecurity.tweakFields, tagLen,
    length_bytesLE])

theorem hq_ftsRoots (index : Index) (roots : FtsTree → Digest) :
    HQ (tweakableHash (m := AComp) P (.ftsRoots index) (ftsRootsPayload roots)) :=
  hq_th _ _ _ (by
    rw [ftsRootsPayload, length_flatMap16, List.length_ofFn]
    simp [SphincsSecurity.hashDomainFields, SphincsSecurity.tweakFields, tagLen, SphincsSecurity.ftsTrees])

theorem hq_messageDigest (root : Digest) (m : Message) (rho : Digest) :
    HQ (messageDigest (m := AComp) P root m rho) :=
  hq_bind (hq_oracleHash _ (honest_th _ _ _ (by
    simp [SphincsSecurity.hashDomainFields, SphincsSecurity.tweakFields, tagLen,
      messageDigestPayload, length_bytesLE]))) fun _ => hq_pure _

theorem hq_deriveKey (dom : SphincsSecurity.KeygenDomain) (seed : MasterSeed) :
    HQ (SphincsSecurity.deriveKey (m := AComp) P dom seed) := by
  refine hq_bind (hq_oracleHash _ ?_) fun _ => hq_pure _
  unfold SphincsSecurity.keygenHashInput
  rw [List.append_assoc]
  apply honest_fieldBytes
  cases dom <;> simp [SphincsSecurity.keygenDomainFields, SphincsSecurity.tweakFields, tagLen,
    length_bytesLE]

theorem hq_deriveRandomizer (seed : MasterSeed) (m : Message) (trial : BitVec 32) :
    HQ (SphincsSecurity.deriveRandomizer (m := AComp) P seed m trial) := by
  refine hq_bind (hq_oracleHash _ ?_) fun _ => hq_pure _
  unfold SphincsSecurity.randomizerHashInput
  rw [List.append_assoc, List.append_assoc]
  apply honest_fieldBytes
  simp [tagLen, length_bytesLE]

end calls

macro "hqs" : tactic => `(tactic| repeat (first
  | exact hq_pure _
  | apply hq_chainWalk | apply hq_leafHash | apply hq_node | apply hq_ftsNode | apply hq_encode
  | apply hq_ftsLeafHash | apply hq_ftsRoots | apply hq_messageDigest | apply hq_deriveKey
  | apply hq_deriveRandomizer
  | refine hq_bind ?_ (fun _ => ?_)
  | refine hq_sequenceFin _ (fun _ => ?_)
  | split))

section algs

open SphincsSecurity.Concrete

variable (P : SphincsSecurity.PublicParameter)

/-! ### Verification -/

theorem hq_otsLeaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (M : Digest)
    (c : SphincsSecurity.Counter) (values : ChainIndex → Digest) :
    HQ (otsLeaf (m := AComp) P lay tree leaf M c values) := by
  unfold otsLeaf
  refine hq_bind (hq_encode _ _ _ _ _ _) fun r => ?_
  split
  · exact hq_bind (hq_sequenceFin _ fun c => hq_chainWalk _ _ _ _ _ _ _ _) fun _ =>
      hq_bind (hq_leafHash _ _ _ _ _) fun _ => hq_pure _
  · exact hq_pure _

theorem hq_treeFold (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (path : Nat → Digest)
    (n : Nat) (v : Digest) : HQ (treeFold (m := AComp) P lay tree leaf path n v) := by
  induction n with
  | zero => exact hq_pure _
  | succ n ih =>
    refine hq_bind ih fun _ => ?_
    dsimp only
    split <;> apply hq_node

theorem hq_ftsFold (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (path : Fin SphincsSecurity.ftsTreeHeight → Digest) (n : Nat) (v : Digest) :
    HQ (ftsFold (m := AComp) P index tree leaf path n v) := by
  induction n with
  | zero => exact hq_pure _
  | succ n ih =>
    refine hq_bind ih fun _ => ?_
    dsimp only
    split <;> apply hq_ftsNode

theorem hq_ftsRecover (index : Index) (leaves : IndexGroup → FtsLeaf) (secrets : FtsTree → Digest)
    (paths : FtsTree → Fin SphincsSecurity.ftsTreeHeight → Digest) :
    HQ (ftsRecover (m := AComp) P index leaves secrets paths) := by
  unfold ftsRecover
  refine hq_bind (hq_sequenceFin _ fun t => hq_bind (hq_ftsLeafHash _ _ _ _ _) fun _ =>
    hq_ftsFold _ _ _ _ _ _ _) fun _ => hq_ftsRoots _ _ _

theorem hq_verifyLayers (index : Index) (σ : Signature) (n : Nat) (M : Digest) :
    HQ (verifyLayers (m := AComp) P index σ n M) := by
  induction n generalizing M with
  | zero => exact hq_pure _
  | succ n ih =>
    unfold verifyLayers
    split
    · refine hq_bind (hq_otsLeaf _ _ _ _ _ _ _) fun r => ?_
      split
      · exact hq_bind (hq_treeFold _ _ _ _ _ _ _) fun _ => ih _
      · exact hq_pure _
    · exact hq_pure _

/-- **verify** makes only honest queries. -/
theorem hq_verify (pk : SphincsSecurity.PublicKey) (m : Message) (σ : Signature) :
    HQ (verify (m := AComp) pk m σ) := by
  unfold verify verifyCore
  split
  · refine hq_bind (hq_messageDigest _ _ _ _) fun d => ?_
    split
    · exact hq_pure _
    · refine hq_bind (hq_ftsRecover _ _ _ _ _) fun _ => hq_bind (hq_verifyLayers _ _ _ _ _) fun r => ?_
      split <;> exact hq_pure _
  · exact hq_pure _

/-! ### Tree building and signing -/

theorem hq_buildLevel (hashNode : Nat → Digest → Digest → AComp Digest)
    (h : ∀ j l r, HQ (hashNode j l r)) (width : Nat) (below : Nat → Digest) :
    HQ (buildLevel hashNode width below) :=
  hq_bind (hq_sequenceFin _ fun _ => h _ _ _) fun _ => hq_pure _

theorem hq_buildLevels (hashNode : Nat → Nat → Digest → Digest → AComp Digest)
    (h : ∀ lam j l r, HQ (hashNode lam j l r)) (height : Nat) (leaves : Nat → Digest) (n : Nat) :
    HQ (buildLevels hashNode height leaves n) := by
  induction n with
  | zero => exact hq_pure _
  | succ n ih =>
    exact hq_bind ih fun _ => hq_bind (hq_buildLevel _ (fun j l r => h _ j l r) _ _) fun _ => hq_pure _

theorem hq_buildChain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (c : ChainIndex)
    (secret : AComp Digest) (hs : HQ secret) (d : Nat) :
    HQ (buildChain P lay tree leaf c secret d) :=
  hq_bind hs fun _ => hq_bind (hq_chainWalk _ _ _ _ _ _ _ _) fun _ =>
    hq_bind (hq_chainWalk _ _ _ _ _ _ _ _) fun _ => hq_pure _

theorem hq_buildLeaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → AComp Digest) (hs : ∀ c, HQ (secret c)) (digits : Encoding) :
    HQ (buildLeaf P lay tree leaf secret digits) :=
  hq_bind (hq_sequenceFin _ fun c => hq_buildChain _ _ _ _ _ _ (hs c) _) fun _ =>
    hq_bind (hq_leafHash _ _ _ _ _) fun _ => hq_pure _

theorem hq_buildLayerTree (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → AComp Digest) (hs : ∀ e c, HQ (secret e c))
    (leaf : LeafIndex) (digits : Encoding) :
    HQ (buildLayerTree P lay tree secret leaf digits) :=
  hq_bind (hq_sequenceFin _ fun _ => hq_buildLeaf _ _ _ _ _ (hs _) _) fun _ =>
    hq_bind (hq_buildLevels _ (fun _ _ _ _ => hq_node _ _ _ _ _ _ _) _ _ _) fun _ => hq_pure _

theorem hq_buildFtsTree (index : Index) (tree : FtsTree) (secret : FtsLeaf → AComp Digest)
    (hs : ∀ j, HQ (secret j)) (leaf : FtsLeaf) :
    HQ (buildFtsTree P index tree secret leaf) :=
  hq_bind (hq_sequenceFin _ fun j => hq_bind (hs j) fun _ =>
      hq_bind (hq_ftsLeafHash _ _ _ _ _) fun _ => hq_pure _) fun _ =>
    hq_bind (hq_buildLevels _ (fun _ _ _ _ => hq_ftsNode _ _ _ _ _ _ _) _ _ _) fun _ => hq_pure _

theorem hq_buildForest (index : Index) (secret : FtsTree → FtsLeaf → AComp Digest)
    (hs : ∀ t j, HQ (secret t j)) (leaves : IndexGroup → FtsLeaf) :
    HQ (buildForest P index secret leaves) :=
  hq_bind (hq_sequenceFin _ fun t => hq_buildFtsTree _ _ _ _ (hs t) _) fun _ =>
    hq_bind (hq_ftsRoots _ _ _) fun _ => hq_pure _

theorem hq_encodingSearch (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (M : Digest)
    (attempts counter : Nat) : HQ (encodingSearch (m := AComp) P lay tree leaf M attempts counter) := by
  induction attempts generalizing counter with
  | zero => exact hq_pure _
  | succ n ih =>
    unfold encodingSearch
    refine hq_bind (hq_encode _ _ _ _ _ _) fun r => ?_
    split
    · exact hq_pure _
    · exact ih _

theorem hq_signLayers (index : Index) (secret : Layer → TreeIndex → LeafIndex → ChainIndex → AComp Digest)
    (hs : ∀ a b c d, HQ (secret a b c d)) (n : Nat) (M : Digest) :
    HQ (signLayers P index secret n M) := by
  induction n generalizing M with
  | zero => exact hq_pure _
  | succ n ih =>
    unfold signLayers
    split
    · refine hq_bind (hq_encodingSearch _ _ _ _ _ _ _) fun r => ?_
      split
      · refine hq_bind (hq_buildLayerTree _ _ _ _ (hs _ _) _ _) fun _ => hq_bind (ih _) fun r' => ?_
        split <;> exact hq_pure _
      · exact hq_pure _
    · exact hq_pure _

theorem hq_signFrom (index : Index) (ftsSecret : FtsTree → FtsLeaf → AComp Digest)
    (hf : ∀ t j, HQ (ftsSecret t j))
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → AComp Digest)
    (ho : ∀ a b c d, HQ (otsSecret a b c d)) (randomness : Digest) (leaves : IndexGroup → FtsLeaf) :
    HQ (signFrom P index ftsSecret otsSecret randomness leaves) := by
  unfold signFrom
  refine hq_bind (hq_buildForest _ _ _ hf _) fun _ => hq_bind (hq_signLayers _ _ _ ho _ _) fun r => ?_
  split <;> exact hq_pure _

end algs

/-- **sign** makes only honest queries. -/
theorem hq_sign (sk : SphincsSecurity.Seeded.SecretKey) (m : Message) :
    HQ (SphincsSecurity.Seeded.sign (m := AComp) sk m) := by
  unfold SphincsSecurity.Seeded.sign
  refine hq_bind ?_ fun r => ?_
  · generalize SphincsSecurity.digestAttemptLimit = n
    generalize (0 : Nat) = a
    induction n generalizing a with
    | zero => exact hq_pure _
    | succ n ih =>
      unfold SphincsSecurity.Seeded.signDigestLoop SphincsSecurity.Seeded.signAttempt
      refine hq_bind (hq_deriveRandomizer _ _ _ _) fun _ => ?_
      refine hq_bind (hq_bind (hq_messageDigest _ _ _ _) fun _ => by split <;> exact hq_pure _) fun r => ?_
      split
      · exact hq_pure _
      · exact ih _
  · split
    · exact hq_signFrom _ _ _ (fun _ _ => hq_deriveKey _ _ _) _ (fun _ _ _ _ => hq_deriveKey _ _ _) _ _
    · exact hq_pure _

/-- **keygen** makes only honest queries. -/
theorem hq_keygen (seed : MasterSeed) : HQ (SphincsSecurity.Seeded.keygenFromSeed seed) := by
  unfold SphincsSecurity.Seeded.keygenFromSeed
  exact hq_bind (hq_buildLayerTree _ _ _ _ (fun _ _ => hq_deriveKey _ _ _) _ _) fun _ => hq_pure _

end SigGolfCandidate.Equiv
