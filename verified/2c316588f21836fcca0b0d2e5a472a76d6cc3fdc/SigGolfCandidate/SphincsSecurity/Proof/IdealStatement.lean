import SigGolfCandidate.SphincsSecurity.Proof.RandomizedStatement

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

/-- The key of the specification: the public parameter (always `0`), the layer-`0` root, and every sampled secret. `Gen` samples them independently and uniformly, at every position of the index types, so positions a layer does not have hold secrets nothing reads; the seed derivation of the specification is an implementation of this key, not this key. -/
structure SecretKey where
  parameter : PublicParameter
  root : Digest
  otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest
  ftsSecret : Index → FtsTree → FtsLeaf → Digest
  /-- The top tree's node table `(level, nodeIdx) ↦ X_{level, nodeIdx}`, built by key generation. The
  signer reads the top layer's authentication path from it instead of rebuilding the top tree. -/
  top : Nat → Nat → Digest

namespace Concrete

noncomputable opaque randomnessSampleableType : SampleableType Randomness :=
  SampleableType.ofFintype Randomness

noncomputable local instance : SampleableType Randomness := randomnessSampleableType

noncomputable def sampleRandomness : ProbComp Randomness :=
  $ᵗ Randomness

attribute [irreducible] sampleRandomness


variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

noncomputable local instance : SampleableType PublicParameter :=
  SampleableType.ofFintype PublicParameter

noncomputable opaque otsSecretsSampleableType :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  SampleableType.ofFintype (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)

noncomputable local instance :
    SampleableType (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  otsSecretsSampleableType

noncomputable opaque ftsSecretsSampleableType :
    SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
  SampleableType.ofFintype (Index → FtsTree → FtsLeaf → Digest)

noncomputable local instance : SampleableType (Index → FtsTree → FtsLeaf → Digest) :=
  ftsSecretsSampleableType

/-- `pk_i = Chain(P, 0, 2^w - 1, sk_i)` for every chain. -/
def oneTimePublicKey (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (secret : ChainIndex → Digest) : m (ChainIndex → Digest) :=
  sequenceFin fun chainIdx =>
    chainWalk parameter lay tree leaf chainIdx 0 (chainLength - 1) (secret chainIdx)

/-- `OtsSign`: the least admissible counter, and the chain values it dictates. The search starts at `0` and stops after `encodingAttemptLimit` counters. -/
def otsSignFrom (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    Nat → Nat → m (Option (Counter × (ChainIndex → Digest)))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encodeAttempt parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => do
          let values ← sequenceFin fun chainIdx =>
            chainWalk parameter lay tree leaf chainIdx 0 (encoding chainIdx).val (secret chainIdx)
          return some (BitVec.ofNat counterBits counter, values)
      | none => otsSignFrom parameter lay tree leaf secret message attempts (counter + 1)

def otsSign (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (message : Digest) :
    m (Option (Counter × (ChainIndex → Digest))) :=
  otsSignFrom parameter lay tree leaf secret message encodingAttemptLimit 0

/-- `X^{lay,tau}_{level,nodeIdx}`, the Merkle tree over the layer's one-time leaves. -/
def treeNode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := leafOfNat nodeIdx
      let endpoints ← oneTimePublicKey parameter lay tree leaf (secret leaf)
      leafHash parameter lay tree leaf endpoints
  | level + 1, nodeIdx => do
      let left ← treeNode parameter lay tree secret level (2 * nodeIdx)
      let right ← treeNode parameter lay tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)

/-- `TreeRoot(P, lay, tau) = X^{lay,tau}_{h_lay, 0}`. -/
def treeRoot (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) : m Digest :=
  treeNode parameter lay tree secret (layerHeight lay) 0

/-- `TreePath`: `A_level = X^{lay,tau}_{level, floor(e / 2^level) xor 1}` for the layer's own `h_lay` levels, and nothing above them. -/
def treePath (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) : m (Fin maxLayerHeight → Digest) :=
  sequenceFin fun level =>
    if level.val < layerHeight lay then
      treeNode parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level.val) 1)
    else
      pure 0

/-- `Y^{idx}_{level,nodeIdx}`, the PORS tree of an instance; node `(level, nodeIdx)` is hashed under its heap
index `2^(14 - level) + nodeIdx`. -/
def ftsNode (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) : Nat → Nat → m Digest
  | 0, nodeIdx => do
      let leaf := ftsLeafOfNat nodeIdx
      ftsLeafHash parameter index tree leaf.val (secret leaf)
  | level + 1, nodeIdx => do
      let left ← ftsNode parameter index tree secret level (2 * nodeIdx)
      let right ← ftsNode parameter index tree secret level (2 * nodeIdx + 1)
      tweakableHash parameter (.ftsNode index tree (ftsHeapIndex (level + 1) nodeIdx))
        (nodePayload left right)

/-- `FtsKey(P, idx)`, the root of the instance's PORS tree. -/
def ftsKey (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) : m Digest :=
  ftsNode parameter index porsTree (secret porsTree) ftsTreeHeight 0

/-- `FtsOpen`: the PORS signature of the leaves: the slots in leaf order, the opened secrets, and the honest
schedule's segments, each authentication node computed at its read position. -/
def ftsOpen (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secret : FtsTree → FtsLeaf → Digest) : m FtsSignature := do
  let slots := sortedSlots leaves
  let plan := schedule (sortedLeaves leaves)
  let segments ← sequenceFin fun j : Fin ftsSegments => do
    let segment := plan.getD j.val default
    let nodes ← sequenceFin (n := segment.folds.val) fun i =>
      let position := segment.reads.getD i.val (0, 0)
      ftsNode parameter index porsTree (secret porsTree) position.1 position.2
    return segment.toSegment nodes
  return { perm := fun s => (slots.getD s.val ⟨0, by decide⟩).castSucc
           secrets := fun s => secret porsTree (leaves (slots.getD s.val ⟨0, by decide⟩))
           segments := segments }

/-- The public parameter is the constant `P = 0`. -/
noncomputable def sampleParameter : ProbComp PublicParameter :=
  pure 0

noncomputable def sampleOtsSecrets :
    ProbComp (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) :=
  $ᵗ (Layer → TreeIndex → LeafIndex → ChainIndex → Digest)

noncomputable def sampleFtsSecrets : ProbComp (Index → FtsTree → FtsLeaf → Digest) :=
  $ᵗ (Index → FtsTree → FtsLeaf → Digest)

/-- Key generation's tree: layer `0`'s tree built once from table secrets, exactly as the seeded key generation builds it. -/
def keygenRoot (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) : m Digest := do
  let (_, _, root) ← buildLayerTree parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  return root

/-- Key generation's tree kept whole: layer `0`'s node table, built once from table secrets with exactly
the queries of `keygenRoot`. -/
def keygenTable (parameter : PublicParameter) (secret : LeafIndex → ChainIndex → Digest) :
    m (Nat → Nat → Digest) := do
  let (_, table) ← buildLayerTable parameter topLayer rootTree
    (fun leaf chainIdx => pure (secret leaf chainIdx)) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  return table

/-- `Gen`: take the parameter `P = 0`, sample every secret, and build layer `0`'s tree, keeping its node
table for the signer and its root for the public key. The trees below it are built when a signature needs
them, so nothing else is computed here. -/
noncomputable def keygen : OracleComp OracleWorld (PublicKey × SecretKey) := do
  let parameter ← liftM sampleParameter
  let otsSecret ← liftM sampleOtsSecrets
  let ftsSecret ← liftM sampleFtsSecrets
  let top ← liftM
    (keygenTable parameter (otsSecret topLayer rootTree) : OracleComp HashSpec (Nat → Nat → Digest))
  let root := top (layerHeight topLayer) 0
  return (⟨root, parameter⟩, ⟨parameter, root, otsSecret, ftsSecret, top⟩)

/-- One digest attempt: one hash, keeping the index and the leaf indices if the digest is admissible. -/
def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  if Admissible digest then
    return some (digestIndex digest, digestLeaves digest)
  else
    return none

/-- The digest loop: at most `digestAttemptLimit` attempts, each sampling a fresh randomizer, stopping at the first admissible digest (about `2^9.76` attempts on average). -/
noncomputable def signDigestLoop : Nat → SecretKey → Message →
    OracleComp OracleWorld (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _secretKey, _message => pure none
  | attempts + 1, secretKey, message => do
      let randomness ← liftM sampleRandomness
      let attempt ← liftM
        (signAttempt secretKey message randomness :
          OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))
      match attempt with
      | some (index, leaves) => pure (some (randomness, index, leaves))
      | none => signDigestLoop attempts secretKey message

/-- The message layer `lay` signs: the root of the tree below it, or the PORS root at the bottom. Every layer's message is fixed by the index alone, which is what makes the layers independent. -/
def layerMessage (secretKey : SecretKey) (index : Index) (lay : Layer) : m Digest :=
  if hbelow : lay.val + 1 < numLayers then
    let below : Layer := ⟨lay.val + 1, hbelow⟩
    treeRoot secretKey.parameter below (treeIndexAt index below)
      (secretKey.otsSecret below (treeIndexAt index below))
  else
    ftsKey secretKey.parameter index (secretKey.ftsSecret index)

/-- One layer's contribution: its counter, its chain values, and its authentication path. -/
def signLayer (secretKey : SecretKey) (index : Index) (lay : Layer) :
    m (Option (Counter × (ChainIndex → Digest) × (Fin maxLayerHeight → Digest))) := do
  let tree := treeIndexAt index lay
  let leaf := leafIndexAt index lay
  let message ← layerMessage secretKey index lay
  match ← otsSign secretKey.parameter lay tree leaf (secretKey.otsSecret lay tree leaf) message with
  | none => return none
  | some (counter, values) => do
      let path ← treePath secretKey.parameter lay tree (secretKey.otsSecret lay tree) leaf
      return some (counter, values, path)

/-- `Sig` after the digest loop, from table secrets: the PORS tree built once, then the layers from the bottom up, each a counter search and its tree built once, and the top layer's path read from the key's node table. This mirrors `Seeded.signChecked` query for query, except for the secret and mask derivations. -/
def signAfterDigest (secretKey : SecretKey) (randomness : Randomness) (index : Index)
    (leaves : IndexGroup → FtsLeaf) : OracleComp HashSpec (Option Signature) :=
  signFrom secretKey.parameter index (fun tree leaf => pure (secretKey.ftsSecret index tree leaf))
    (fun lay tree leaf chainIdx => pure (secretKey.otsSecret lay tree leaf chainIdx))
    (fun level nodeIdx => pure (secretKey.top level nodeIdx)) randomness leaves

/-- `Sig(sk, m)`: the digest loop, then the PORS tree and the layers, or nothing as soon as one search fails. -/
noncomputable def sign (secretKey : SecretKey) (message : Message) :
    OracleComp OracleWorld (Option Signature) := do
  match ← signDigestLoop digestAttemptLimit secretKey message with
  | none => return none
  | some (randomness, index, leaves) =>
      liftM (signAfterDigest secretKey randomness index leaves : OracleComp HashSpec (Option Signature))

attribute [irreducible] treeNode ftsNode sampleParameter sampleOtsSecrets sampleFtsSecrets keygen sign
  keygenRoot keygenTable signAfterDigest

end Concrete

/-- The concrete SPHINCS scheme: key generation, the stateless randomized signer, and the verifier defined above. -/
noncomputable def Concrete.scheme : Scheme SecretKey where
  keygen := Concrete.keygen
  sign := Concrete.sign
  verify := fun publicKey message signature =>
    liftM (Concrete.verify publicKey message signature : OracleComp HashSpec Bool)

/-- The security claim: `127` bits of classical strong unforgeability in the random-oracle model, at `2^32` signing requests per key pair. -/
abbrev IndependentSecurityStatement : Prop :=
  HasClassicalSecurityBits Concrete.scheme 127

end SphincsSecurity
