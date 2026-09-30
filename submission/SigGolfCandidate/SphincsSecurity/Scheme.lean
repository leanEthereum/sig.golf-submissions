import SigGolfCandidate.SphincsSecurity.Compat
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# SPHINCS+ scheme

Parameters, serialized hash inputs, key generation, signing, and verification for the instance defined in `doc/sphincs/main.tex`, with the changes of the SPHINCS-golf variant: five layers of heights `(11,6,6,6,5)`, target sum `183`, paired secret derivations (one query yields two secrets), a top tree cached by key generation (masked, and authenticated by a MAC keyed with the master seed), no public-parameter derivation (`P = 0`), a message digest that does not bind the root, a verifier that rejects counters at or above `C_max`, and a signer that builds every tree it touches exactly once, in the query order of the reference implementation.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity

/-! ## The instance: parameters, types, and hash-input layout -/

def digestBits : Nat := 128
def hashOutputBits : Nat := 256
def messageBits : Nat := 256
def publicParameterBits : Nat := 128
def randomnessBits : Nat := 128
def counterBits : Nat := 32
def winternitzBits : Nat := 3
def chainLength : Nat := 2 ^ winternitzBits
def numChains : Nat := 42
def targetSum : Nat := 183
def numLayers : Nat := 5
def totalHeight : Nat := 34
/-- The tallest layer, the top one, `h_0 = 11`, which bounds every layer's leaf index. -/
def maxLayerHeight : Nat := 11
def ftsTreeHeight : Nat := 10
/-- The `k` index groups a digest carries. The forest holds `k - 1` trees, the last group being pinned to zero. -/
def ftsTrees : Nat := 15
/-- Signatures allowed per key pair, `q_s`. -/
def signatureLimit : Nat := 2 ^ 32
/-- Digest attempts per signature, `A_max`. -/
def digestAttemptLimit : Nat := 2 ^ 20
/-- Encoding counters tried per layer, `C_max`. -/
def encodingAttemptLimit : Nat := 2 ^ 22

abbrev MasterSeed := BitVec 256

abbrev Digest := BitVec digestBits
abbrev HashOutput := BitVec hashOutputBits
abbrev Message := BitVec messageBits
abbrev PublicParameter := BitVec publicParameterBits
abbrev Randomness := Digest
abbrev Counter := BitVec counterBits
abbrev Layer := Fin numLayers
/-- `idx`, which few-time key signs. -/
abbrev Index := Fin (2 ^ totalHeight)
/-- `tau`, a tree of any layer. Layer `lay` only uses the values below `2^(sum_{j < lay} h_j)`. -/
abbrev TreeIndex := Fin (2 ^ totalHeight)
/-- `e`, a leaf of any layer. Layer `lay` only uses the values below `2^h_lay`. -/
abbrev LeafIndex := Fin (2 ^ maxLayerHeight)
abbrev ChainIndex := Fin numChains
abbrev Digit := Fin chainLength
abbrev ChainStep := Fin (chainLength - 1)
/-- A tree of the few-time forest, `kappa < k - 1`. -/
abbrev FtsTree := Fin (ftsTrees - 1)
/-- An index group of the message digest, `kappa < k`. The first `k - 1` select a tree's leaf; the last is pinned to zero. -/
abbrev IndexGroup := Fin ftsTrees
abbrev FtsLeaf := Fin (2 ^ ftsTreeHeight)
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8
/-- A pair of chains `(2k, 2k + 1)` of a one-time key, whose secrets one derivation query yields. -/
abbrev ChainPair := Fin (numChains / 2)
/-- A pair of leaves `(2k, 2k + 1)` of a few-time tree, whose secrets one derivation query yields. -/
abbrev FtsPair := Fin (2 ^ (ftsTreeHeight - 1))

/-- Chain `2k`. -/
def evenChain (pair : ChainPair) : ChainIndex := ⟨2 * pair.val, by have := pair.isLt; unfold numChains at *; omega⟩
/-- Chain `2k + 1`. -/
def oddChain (pair : ChainPair) : ChainIndex := ⟨2 * pair.val + 1, by have := pair.isLt; unfold numChains at *; omega⟩
/-- The pair of a chain. -/
def chainPairOf (chainIdx : ChainIndex) : ChainPair := ⟨chainIdx.val / 2, by have := chainIdx.isLt; unfold numChains at *; omega⟩

/-- Leaf `2k`. -/
def evenFtsLeaf (pair : FtsPair) : FtsLeaf := ⟨2 * pair.val, by have := pair.isLt; unfold ftsTreeHeight at *; omega⟩
/-- Leaf `2k + 1`. -/
def oddFtsLeaf (pair : FtsPair) : FtsLeaf := ⟨2 * pair.val + 1, by have := pair.isLt; unfold ftsTreeHeight at *; omega⟩
/-- The pair of a leaf. -/
def ftsPairOf (leaf : FtsLeaf) : FtsPair := ⟨leaf.val / 2, by have := leaf.isLt; unfold ftsTreeHeight at *; omega⟩

/-- Spread per-pair values back to the members: even members take the first component. -/
def unpairChains {α : Type} (pairs : ChainPair → α × α) (chainIdx : ChainIndex) : α :=
  if chainIdx.val % 2 = 0 then (pairs (chainPairOf chainIdx)).1 else (pairs (chainPairOf chainIdx)).2

/-- Spread per-pair values back to the members: even leaves take the first component. -/
def unpairFtsLeaves {α : Type} (pairs : FtsPair → α × α) (leaf : FtsLeaf) : α :=
  if leaf.val % 2 = 0 then (pairs (ftsPairOf leaf)).1 else (pairs (ftsPairOf leaf)).2

/-- The `d` Merkle heights, `(h_0, ..., h_4) = (11, 6, 6, 6, 5)`. Layer `0` carries the public key; its
tree is built by key generation and cached. -/
def layerHeight (lay : Layer) : Nat := if lay.val = 0 then maxLayerHeight else if lay.val < 4 then 6 else 5

def topLayer : Layer := ⟨0, by decide⟩
def bottomLayer : Layer := ⟨numLayers - 1, by decide⟩

/-- `sum_{j < lay} h_j`, the index bits above layer `lay`. -/
def heightAbove (lay : Layer) : Nat := ∑ j : Layer, if j.val < lay.val then layerHeight j else 0

/-- `sum_{j > lay} h_j`, the index bits below layer `lay`. -/
def heightBelow (lay : Layer) : Nat := totalHeight - heightAbove lay - layerHeight lay

/-- Keep the first 128 output bits, the low bits of the little-endian bit vector. -/
def truncateHash (output : HashOutput) : Digest :=
  output.extractLsb' 0 digestBits

/-- The message digest is `h + k * a = 184` bits, an index and `k` leaf indices. -/
def messageDigestBits : Nat := totalHeight + ftsTrees * ftsTreeHeight

abbrev MessageDigest := BitVec messageDigestBits

/-- Keep the first `h + k * a` output bits. -/
def truncateMessageDigest (output : HashOutput) : MessageDigest :=
  output.extractLsb' 0 messageDigestBits

/-- `pk = (root, P)`. The parameter is always `P = 0`, so the published key is the root alone. -/
structure PublicKey where
  root : Digest
  parameter : PublicParameter
deriving DecidableEq

/-- One layer's WOTS signature and authentication path. -/
structure LayerSignature (lay : Layer) where
  counter : Counter
  chainValues : ChainIndex → Digest
  path : Fin (layerHeight lay) → Digest
deriving DecidableEq

/-- The randomizer, FORS openings, and five layer signatures, totaling 6404 bytes. -/
structure Signature where
  randomness : Randomness
  ftsSecret : FtsTree → Digest
  ftsPath : FtsTree → Fin ftsTreeHeight → Digest
  layers : (lay : Layer) → LayerSignature lay
deriving DecidableEq

/-- Serialize a bit vector into a fixed number of bytes, least significant byte first. -/
def bytesLE (byteCount : Nat) (value : BitVec (8 * byteCount)) : List UInt8 :=
  List.ofFn fun index : Fin byteCount =>
    UInt8.ofBitVec (value.extractLsb' (8 * index.val) 8)

/-- The five fields of the specification's `enc(t, lay, tau, p, j)`. The tree field is 40 bits wide: few-time tweaks carry the 34-bit index there. -/
structure TweakFields where
  tag : BitVec 8
  layer : BitVec 8
  tree : BitVec 40
  position : BitVec 32
  index : BitVec 32
deriving DecidableEq

/-- The protocol domain separator. -/
def protocolDomainSep : UInt8 := 1

/-- The specification's 16 tweak bytes `protocol_domain_sep || tag || layer || tree >> 32 || position || tree mod 2^32 || index`, each field serialized least significant byte first: byte 3 carries bits 32..39 of the tree field. -/
def fieldBytes (fields : TweakFields) : HashInput :=
  [protocolDomainSep] ++ bytesLE 1 fields.tag ++ bytesLE 1 fields.layer ++
    bytesLE 1 (fields.tree.extractLsb' 32 8) ++
    bytesLE 4 fields.position ++ bytesLE 4 (fields.tree.extractLsb' 0 32) ++ bytesLE 4 fields.index

/-- Convert the specification's five integer fields to their fixed widths. -/
def tweakFields (tag layer tree position index : Nat) : TweakFields :=
  ⟨BitVec.ofNat 8 tag, BitVec.ofNat 8 layer, BitVec.ofNat 40 tree,
    BitVec.ofNat 32 position, BitVec.ofNat 32 index⟩

/-- The verification hash domains. Seed derivation uses `KeygenDomain`. -/
inductive HashDomain where
  | chain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) (step : ChainStep)
  | leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | node (lay : Layer) (tree : TreeIndex) (level : Nat) (nodeIdx : Nat)
  | encoding (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
  | ftsLeaf (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
  | ftsNode (index : Index) (tree : FtsTree) (level : Nat) (nodeIdx : Nat)
  | ftsRoots (index : Index)
  | message
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of a tweak. Inside the hypertree the layer field is the layer and the tree field the tree; inside a few-time key they are the tree of the forest and the index that selects the instance. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay tree leaf chainIdx step => tweakFields 1 lay tree (chainLength * chainIdx + step) leaf
  | .leaf lay tree leaf => tweakFields 2 lay tree 0 leaf
  | .node lay tree level nodeIdx => tweakFields 3 lay tree level nodeIdx
  | .encoding lay tree leaf => tweakFields 4 lay tree 0 leaf
  | .ftsLeaf index tree leaf => tweakFields 9 tree index 0 leaf
  | .ftsNode index tree level nodeIdx => tweakFields 10 tree index level nodeIdx
  | .ftsRoots index => tweakFields 11 0 index 0 0
  | .message => tweakFields 12 0 0 0 0

/-- The exact 16 bytes supplied by the specification as a hash tweak. -/
def tweakBytes (domain : HashDomain) : HashInput :=
  fieldBytes (hashDomainFields domain)

/-- The random-oracle input `tweak || parameter || message` used by every tweakable hash call and by the message digest. -/
def tweakableHashInput (parameter : PublicParameter) (domain : HashDomain)
    (message : HashInput) : HashInput :=
  tweakBytes domain ++ bytesLE 16 parameter ++ message

/-- `tweak(7, 0, 0, trial, 0) || P || S || m`. -/
def randomizerHashInput (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) : HashInput :=
  fieldBytes ⟨7#8, 0#8, 0#40, trial, 0#32⟩ ++
    bytesLE 16 parameter ++ bytesLE 32 seed ++ bytesLE 32 message

inductive KeygenDomain where
  /-- The secrets of chains `2k` and `2k + 1` of a one-time key. -/
  | ots (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (pair : ChainPair)
  /-- The secrets of leaves `2k` and `2k + 1` of a few-time tree. -/
  | fts (index : Index) (tree : FtsTree) (pair : FtsPair)
  /-- The mask of the cached top-tree node `(level, nodeIdx)`. -/
  | mask (level : Fin maxLayerHeight) (nodeIdx : Fin (2 ^ maxLayerHeight))
deriving DecidableEq

def keygenDomainFields : KeygenDomain → TweakFields
  | .ots lay tree leaf pair => tweakFields 0 lay tree pair leaf
  | .fts index tree pair => tweakFields 8 tree index 0 pair
  | .mask level nodeIdx => tweakFields 13 0 0 level nodeIdx

/-- `tweak || P || S`. -/
def keygenHashInput (parameter : PublicParameter) (domain : KeygenDomain)
    (seed : MasterSeed) : HashInput :=
  fieldBytes (keygenDomainFields domain) ++ bytesLE 16 parameter ++ bytesLE 32 seed

/-! ### The cache

Key generation publishes a 128 KiB cache: the 32-byte MAC tag, then the masked nodes of the top tree at
levels `0, ..., 10` (level ascending, index ascending within a level). The root is not stored; it is the
public key. The signer reads the top layer's authentication path from the cache after checking the tag. -/

/-- The masked nodes of the top tree below its root: level `l < 11` holds `2^(11 - l)` nodes. -/
abbrev TopRegion := (level : Fin maxLayerHeight) → Fin (2 ^ (maxLayerHeight - level.val)) → Digest

/-- The cache: the MAC tag (the full 256-bit hash answer) and the masked-node region. Unused bytes of the
128 KiB buffer are zero and not part of the abstract cache. -/
structure TopCache where
  tag : HashOutput
  region : TopRegion
deriving DecidableEq

/-- The masked node `(level, nodeIdx)`, or zero outside the region. -/
def TopCache.node (cache : TopCache) (level nodeIdx : Nat) : Digest :=
  if hlevel : level < maxLayerHeight then
    if hnode : nodeIdx < 2 ^ (maxLayerHeight - level) then cache.region ⟨level, hlevel⟩ ⟨nodeIdx, hnode⟩
    else 0
  else 0

/-- The region's bytes: level by level, each node as 16 bytes, `65504` bytes in all. -/
def regionBytes (region : TopRegion) : HashInput :=
  (List.ofFn fun level : Fin maxLayerHeight => (List.ofFn (region level)).flatMap (bytesLE 16)).flatten

/-- `tweak(14, 0, 0, 0, 0) || P || S || region`: the MAC over the region, keyed by the master seed. -/
def macHashInput (parameter : PublicParameter) (seed : MasterSeed) (region : TopRegion) : HashInput :=
  fieldBytes ⟨14#8, 0#8, 0#40, 0#32, 0#32⟩ ++ bytesLE 16 parameter ++ bytesLE 32 seed ++ regionBytes region

/-! ### The target-sum code

`v = 42` chunks of `w = 3` bits, 21 in each half of the digest, one pinned bit per half, and the code is the words of digit sum `T = 183`. Two distinct words of equal sum are incomparable, which is what removes the Winternitz checksum and the reason why we need the counter. -/

namespace TargetSum

/-- The digit sum of a word. -/
def sum (x : Encoding) : Nat := ∑ i, (x i).val

/-- Membership in the code `C`: digit sum `T`. -/
def Valid (x : Encoding) : Prop := sum x = targetSum

instance : DecidablePred Valid :=
  fun x => inferInstanceAs (Decidable (sum x = targetSum))

/-- `v / 2 = 21` digits in each half of the digest. -/
def digitsPerHalf : Nat := numChains / 2

/-- Offset of a three-bit digit, skipping padding bits 63 and 127. -/
def digitOffset (i : ChainIndex) : Nat :=
  winternitzBits * i.val + if i.val < digitsPerHalf then 0 else 1

/-- `x_i`, the three bits of the digest at the digit's offset. -/
def digestEncoding (digest : Digest) : Encoding :=
  fun i => (digest.extractLsb' (digitOffset i) winternitzBits).toFin

/-- Decode the concrete little-endian layout: 21 three-bit digits, padding bit 63, 21 digits, and padding bit 127. A digest decodes exactly when both padding bits are clear and the digits reach the target sum. -/
def decodeDigest (digest : Digest) : Option Encoding :=
  if digest.getLsbD 63 = false ∧ digest.getLsbD 127 = false ∧ Valid (digestEncoding digest)
  then some (digestEncoding digest) else none

end TargetSum

/-! ## The algorithms

`Concrete` contains the hash and verification routines; `Seeded` contains key generation and signing. Hashing routines work in any monad with access to `HashSpec`. The experiment samples the master seed and charges every hash call, including repeated calls. Out-of-range branches only make the definitions total; honest algorithms never reach them. -/

/-- A hash query takes an arbitrary byte string and returns 32 bytes. -/
abbrev HashSpec := HashInput →ₒ HashOutput

/-- Private uniform sampling and the shared hash oracle. Only hash calls count toward the query budget. -/
abbrev OracleWorld := unifSpec + HashSpec

namespace Concrete

/-- Run the `n` computations in index order and collect their results. -/
def sequenceFin {m : Type → Type} [Monad m] {α : Type} {n : Nat}
    (computation : Fin n → m α) : m (Fin n → α) :=
  match n with
  | 0 => pure Fin.elim0
  | n + 1 => do
      let head ← computation 0
      let tail ← sequenceFin fun index : Fin n => computation index.succ
      return Fin.cases head tail

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- One query to the random oracle `H`. -/
def oracleHash (input : HashInput) : m HashOutput :=
  HasQuery.query (spec := HashSpec) (m := m) input

/-- `Th(P, tw, M) = Truncate_n(H(tw || P || M))`. -/
def tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    m Digest := do
  let output ← oracleHash (tweakableHashInput parameter domain payload)
  return truncateHash output

/-! ### The index -/

/-- `tau_lay = floor(idx / 2^(sum_{j >= lay} h_j))`. -/
def treeIndexAt (index : Index) (lay : Layer) : TreeIndex :=
  ⟨index.val / 2 ^ (totalHeight - heightAbove lay),
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) index.isLt⟩

/-- `e_lay = floor(idx / 2^(sum_{j > lay} h_j)) mod 2^h_lay`. -/
def leafIndexAt (index : Index) (lay : Layer) : LeafIndex :=
  ⟨index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay,
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.pow_le_pow_right (by omega) (by
      unfold layerHeight maxLayerHeight; split <;> (try split) <;> omega))⟩

/-! ### The one-time signature -/

/-- A node index at level `0` read as a leaf index. -/
def leafOfNat (value : Nat) : LeafIndex :=
  ⟨value % 2 ^ maxLayerHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- `Chain_{lay,tau,e,i}(P, start, steps, value)`: the step onto position `start + steps + 1` carries tweak position `2^w * i + start + steps`. -/
def chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) : Nat → Nat → Digest → m Digest
  | _, 0, value => pure value
  | start, steps + 1, value => do
      let previous ← chainWalk parameter lay tree leaf chainIdx start steps value
      if hstep : start + steps < chainLength - 1 then
        tweakableHash parameter (.chain lay tree leaf chainIdx ⟨start + steps, hstep⟩)
          (bytesLE 16 previous)
      else
        pure 0

/-- The verifier's half of a chain: walk the remaining `2^w - 1 - x_i` steps. -/
def recoverChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (digit : Digit) (value : Digest) : m Digest :=
  chainWalk parameter lay tree leaf chainIdx digit.val (chainLength - 1 - digit.val) value

/-- `pk_0 || ... || pk_{v-1}`. -/
def leafPayload (endpoints : ChainIndex → Digest) : HashInput :=
  (List.ofFn endpoints).flatMap (bytesLE 16)

/-- `X^{lay,tau}_{0,e}`, the one-time leaf: the hash of the `v` public values. -/
def leafHash (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (endpoints : ChainIndex → Digest) : m Digest :=
  tweakableHash parameter (.leaf lay tree leaf) (leafPayload endpoints)

/-- `Enc(P, lay, tau, e, M, c)`: hash the message with the counter under the leaf's encoding tweak, and decode. -/
def encode (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) : m (Option Encoding) := do
  let digest ← tweakableHash parameter (.encoding lay tree leaf)
    (bytesLE 16 message ++ bytesLE 4 counter)
  return TargetSum.decodeDigest digest

/-- `OtsLeaf`: the verifier's leaf, or nothing if the counter does not encode the message. -/
def otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) : m (Option Digest) := do
  let some encoding ← encode parameter lay tree leaf message counter | return none
  let endpoints ← sequenceFin fun chainIdx =>
    recoverChain parameter lay tree leaf chainIdx (encoding chainIdx) (values chainIdx)
  let value ← leafHash parameter lay tree leaf endpoints
  return some value

/-! ### A layer -/

/-- The two children of a Merkle node. -/
def nodePayload (left right : Digest) : HashInput :=
  bytesLE 16 left ++ bytesLE 16 right

/-- `TreeFold`: fold a leaf and a path into the layer's root. -/
def treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← treeFold parameter lay tree leaf path levels value
      let sibling := path levels
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload sibling current)
      else
        tweakableHash parameter (.node lay tree (levels + 1) nodeIdx) (nodePayload current sibling)

/-! ### The few-time signature -/

/-- A node index at level `0` read as a leaf index. -/
def ftsLeafOfNat (value : Nat) : FtsLeaf :=
  ⟨value % 2 ^ ftsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The index group of the digest that selects this tree's leaf. -/
def ftsIndexOf (tree : FtsTree) : IndexGroup :=
  tree.castLE (Nat.sub_le ftsTrees 1)

/-- The last index group, the one the digest is resampled to zero and the verifier checks. Its tree is the dropped one. -/
def lastIndexGroup : IndexGroup := ⟨ftsTrees - 1, by decide⟩

/-- `Y^{idx,kappa}_{0,j}`, the hash of one few-time secret. -/
def ftsLeafHash (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (secret : Digest) : m Digest :=
  tweakableHash parameter (.ftsLeaf index tree leaf) (bytesLE 16 secret)

/-- The `k - 1` roots of the forest. -/
def ftsRootsPayload (roots : FtsTree → Digest) : HashInput :=
  (List.ofFn roots).flatMap (bytesLE 16)

/-- The verifier's half of one few-time tree. -/
def ftsFold (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : FtsLeaf)
    (path : Fin ftsTreeHeight → Digest) : Nat → Digest → m Digest
  | 0, value => pure value
  | levels + 1, value => do
      let current ← ftsFold parameter index tree leaf path levels value
      let sibling := if hlevel : levels < ftsTreeHeight then path ⟨levels, hlevel⟩ else 0
      let nodeIdx := leaf.val / 2 ^ (levels + 1)
      if leaf.val.testBit levels then
        tweakableHash parameter (.ftsNode index tree (levels + 1) nodeIdx)
          (nodePayload sibling current)
      else
        tweakableHash parameter (.ftsNode index tree (levels + 1) nodeIdx)
          (nodePayload current sibling)

/-- `FtsRec`: recover the few-time public key from the opened secrets and paths. -/
def ftsRecover (parameter : PublicParameter) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (secrets : FtsTree → Digest) (paths : FtsTree → Fin ftsTreeHeight → Digest) : m Digest := do
  let roots ← sequenceFin fun tree => do
    let leaf := leaves (ftsIndexOf tree)
    let value ← ftsLeafHash parameter index tree leaf (secrets tree)
    ftsFold parameter index tree leaf (paths tree) ftsTreeHeight value
  tweakableHash parameter (.ftsRoots index) (ftsRootsPayload roots)

/-! ### The message digest -/

/-- `rho || 0^16 || m`, what the message digest hashes after the tweak and the parameter. The root slot is zero, so the digest does not bind the root and the signer does not need it; the argument is kept for the shape of the statement and ignored. -/
def messageDigestPayload (_root : Digest) (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 16 randomness ++ bytesLE 16 (0 : Digest) ++ bytesLE 32 message

/-- `Digest(P, m, rho)`, truncated to `h + k * a` bits. -/
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let output ← oracleHash
    (tweakableHashInput parameter .message (messageDigestPayload root message randomness))
  return truncateMessageDigest output

/-- `idx = N mod 2^h`. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin

/-- `u_kappa = floor(N / 2^(h + kappa * a)) mod 2^a`. -/
def digestLeaves (digest : MessageDigest) : IndexGroup → FtsLeaf :=
  fun tree => (digest.extractLsb' (totalHeight + ftsTreeHeight * tree.val) ftsTreeHeight).toFin

/-- A digest is admissible exactly when its last index group is zero. -/
def Admissible (digest : MessageDigest) : Prop := digestLeaves digest lastIndexGroup = 0

instance (digest : MessageDigest) : Decidable (Admissible digest) :=
  inferInstanceAs (Decidable (digestLeaves digest lastIndexGroup = 0))

/-! ### Verification -/

/-- Read a layer's path, returning zero outside its height. -/
def signaturePath (signature : Signature) (lay : Layer) (level : Nat) : Digest :=
  if hlevel : level < layerHeight lay then (signature.layers lay).path ⟨level, hlevel⟩ else 0

/-- The hypertree walk, from the bottom layer up: `remaining + 1` enters at layer `remaining`, and layer `0`'s fold returns the value compared against the public root. -/
def verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature) :
    Nat → Digest → m (Option Digest)
  | 0, message => pure (some message)
  | remaining + 1, message => do
      if hlayer : remaining < numLayers then
        let lay : Layer := ⟨remaining, hlayer⟩
        let tree := treeIndexAt index lay
        let leaf := leafIndexAt index lay
        let part := signature.layers lay
        let some value ← otsLeaf parameter lay tree leaf message part.counter part.chainValues
          | return none
        let root ← treeFold parameter lay tree leaf (signaturePath signature lay) (layerHeight lay) value
        verifyLayers parameter index signature remaining root
      else
        pure none

/-- Every layer's counter is below `C_max`. The verifier checks this first, without a query. -/
def CountersInRange (signature : Signature) : Prop :=
  ∀ lay, (signature.layers lay).counter.toNat < encodingAttemptLimit

instance (signature : Signature) : Decidable (CountersInRange signature) :=
  inferInstanceAs (Decidable (∀ lay, (signature.layers lay).counter.toNat < encodingAttemptLimit))

/-- `Ver` after the counter check: recompute the digest, recover the few-time key, walk the layers and compare with the root. -/
def verifyCore (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  if ¬ Admissible digest then return false
  else
    let index := digestIndex digest
    let ftsPublicKey ← ftsRecover publicKey.parameter index (digestLeaves digest)
      signature.ftsSecret signature.ftsPath
    let some root ← verifyLayers publicKey.parameter index signature numLayers ftsPublicKey | return false
    return decide (root = publicKey.root)

/-- `Ver(pk, m, sigma)`: reject any counter at or above `C_max`, then verify. -/
def verify (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool :=
  if CountersInRange signature then verifyCore publicKey message signature else pure false

/-! ### Building trees

The signer builds every tree it touches exactly once: all leaves in order, then the levels bottom-up,
each left to right. The builders take the secret derivation as an argument, so that the seeded signer
and the proof's table signer share them. -/

/-- Layer `0` holds one tree, at index `0`. -/
def rootTree : TreeIndex := ⟨0, Nat.two_pow_pos _⟩

/-- One level of a Merkle tree, `width` nodes left to right, from the level below. Indices outside
the level read zero. -/
def buildLevel (hashNode : Nat → Digest → Digest → m Digest) (width : Nat) (below : Nat → Digest) :
    m (Nat → Digest) := do
  let row ← sequenceFin (n := width) fun nodeIdx =>
    hashNode nodeIdx.val (below (2 * nodeIdx.val)) (below (2 * nodeIdx.val + 1))
  return fun nodeIdx => if h : nodeIdx < width then row ⟨nodeIdx, h⟩ else 0

/-- Levels `1, ..., levels` of a tree of height `height` over `leaves`, bottom-up. The result maps a
level and a node index to the node; level `0` is the leaves. -/
def buildLevels (hashNode : Nat → Nat → Digest → Digest → m Digest) (height : Nat)
    (leaves : Nat → Digest) : Nat → m (Nat → Nat → Digest)
  | 0 => pure fun _ nodeIdx => leaves nodeIdx
  | levels + 1 => do
      let table ← buildLevels hashNode height leaves levels
      let row ← buildLevel (hashNode (levels + 1)) (2 ^ (height - (levels + 1))) (table levels)
      return fun level nodeIdx => if level = levels + 1 then row nodeIdx else table level nodeIdx

/-- The word of all-zero digits: a leaf built with it keeps its secrets. -/
def zeroEncoding : Encoding := fun _ => ⟨0, by decide⟩

/-- One chain of a one-time key: its secret, then all `2^w - 1` steps. Returns the value after
`digit` steps and the endpoint. -/
def buildChain (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (secret : m Digest) (digit : Nat) : m (Digest × Digest) := do
  let start ← secret
  let value ← chainWalk parameter lay tree leaf chainIdx 0 digit start
  let endpoint ← chainWalk parameter lay tree leaf chainIdx digit (chainLength - 1 - digit) value
  return (value, endpoint)

/-- One leaf of a layer tree: chains `0, ..., v - 1` in order, then the leaf hash. Returns the chain
values at `digits` and the leaf. -/
def buildLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → m Digest) (digits : Encoding) : m ((ChainIndex → Digest) × Digest) := do
  let chains ← sequenceFin fun chainIdx =>
    buildChain parameter lay tree leaf chainIdx (secret chainIdx) (digits chainIdx).val
  let value ← leafHash parameter lay tree leaf fun chainIdx => (chains chainIdx).2
  return (fun chainIdx => (chains chainIdx).1, value)

/-- Build the tree `(lay, tau)` once, keeping everything: the leaves (each with the chain values at
its digits: `digits` for `leaf`, zero elsewhere) and the node table. `buildLayerTree` reads its result off
this table; key generation keeps the top tree's whole table for the cache. -/
def buildLayerTable (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    m ((Fin (2 ^ layerHeight lay) → (ChainIndex → Digest) × Digest) × (Nat → Nat → Digest)) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeaf parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  return (leaves, table)

/-- Build the tree `(lay, tau)` once. Returns the chain values of leaf `leaf` at `digits`, the
authentication path of `leaf` (level `l` holds `X_{l, floor(e / 2^l) xor 1}`) and the root. -/
def buildLayerTree (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    m ((ChainIndex → Digest) × (Nat → Digest) × Digest) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeaf parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  let values := if h : leaf.val < 2 ^ layerHeight lay then (leaves ⟨leaf.val, h⟩).1 else fun _ => 0
  return (values, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table (layerHeight lay) 0)

/-- Build one few-time tree once: leaves `j = 0, ..., 2^a - 1` (secret, then leaf hash), then the
levels. Returns the secret of `leaf`, its authentication path, and the root. -/
def buildFtsTree (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → m Digest) (leaf : FtsLeaf) : m (Digest × (Nat → Digest) × Digest) := do
  let leaves ← sequenceFin fun leafIdx : FtsLeaf => do
    let value ← secret leafIdx
    let hashed ← ftsLeafHash parameter index tree leafIdx value
    return (value, hashed)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.ftsNode index tree level nodeIdx) (nodePayload left right))
    ftsTreeHeight
    (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then (leaves ⟨nodeIdx, h⟩).2 else 0)
    ftsTreeHeight
  return ((leaves leaf).1, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table ftsTreeHeight 0)

/-- Build the forest `kappa = 0, ..., k - 2` in order, then hash the roots into the few-time public
key. Returns the opened secrets, the paths and the key. -/
def buildForest (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → m Digest) (leaves : IndexGroup → FtsLeaf) :
    m ((FtsTree → Digest) × (FtsTree → Fin ftsTreeHeight → Digest) × Digest) := do
  let trees ← sequenceFin fun tree =>
    buildFtsTree parameter index tree (secret tree) (leaves (ftsIndexOf tree))
  let key ← tweakableHash parameter (.ftsRoots index) (ftsRootsPayload fun tree => (trees tree).2.2)
  return (fun tree => (trees tree).1, fun tree level => (trees tree).2.1 level.val, key)

/-- `OtsSign`'s counter search: the least counter from `counter` on whose encoding decodes, trying at
most `attempts` counters. -/
def encodingSearch (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) : Nat → Nat → m (Option (Counter × Encoding))
  | 0, _ => pure none
  | attempts + 1, counter => do
      match ← encode parameter lay tree leaf message (BitVec.ofNat counterBits counter) with
      | some encoding => return some (BitVec.ofNat counterBits counter, encoding)
      | none => encodingSearch parameter lay tree leaf message attempts (counter + 1)

/-- One layer's signature before its path is cut to the layer's height: counter, chain values, path. -/
abbrev LayerOutput := Counter × (ChainIndex → Digest) × (Nat → Digest)

/-- The top layer's signature, from the cache: the counter search on `message`, the chain values of
leaf `leaf` (per chain, its secret and then its first `x_i` steps), and the authentication path read
through `topNode` (level `l` holds node `(l, floor(e / 2^l) xor 1)`). The top tree is not rebuilt. -/
def signTopLayer (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainIndex → m Digest) (topNode : Nat → Nat → m Digest) (message : Digest) :
    m (Option LayerOutput) := do
  let tree := treeIndexAt index topLayer
  let leaf := leafIndexAt index topLayer
  let some (counter, encoding) ←
      encodingSearch parameter topLayer tree leaf message encodingAttemptLimit 0
    | return none
  let values ← sequenceFin fun chainIdx => do
    let start ← secret leaf chainIdx
    chainWalk parameter topLayer tree leaf chainIdx 0 (encoding chainIdx).val start
  let path ← sequenceFin (n := maxLayerHeight) fun level =>
    topNode level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return some (counter, values, fun level => if h : level < maxLayerHeight then path ⟨level, h⟩ else 0)

/-- The hypertree, from the bottom layer up: `remaining + 1` signs `message` at layer `remaining`
(counter search, then the tree built once), and its root is the message of layer `remaining - 1`. The
top layer (`remaining = 0`) is signed from the cache by `signTopLayer`. -/
def signLayers (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest) (topNode : Nat → Nat → m Digest) :
    Nat → Digest → m (Option (Layer → LayerOutput))
  | 0, _ => pure (some fun _ => (0, fun _ => 0, fun _ => 0))
  | remaining + 1, message =>
      if hlayer : remaining < numLayers then
        if remaining = 0 then do
          let some output ← signTopLayer parameter index (secret topLayer (treeIndexAt index topLayer))
              topNode message
            | return none
          return some fun other => if other = topLayer then output else (0, fun _ => 0, fun _ => 0)
        else do
          let lay : Layer := ⟨remaining, hlayer⟩
          let tree := treeIndexAt index lay
          let leaf := leafIndexAt index lay
          let some (counter, encoding) ←
              encodingSearch parameter lay tree leaf message encodingAttemptLimit 0
            | return none
          let (values, path, root) ← buildLayerTree parameter lay tree (secret lay tree) leaf encoding
          let some rest ← signLayers parameter index secret topNode remaining root | return none
          return some fun other => if other = lay then (counter, values, path) else rest other
      else
        pure none

/-- Cut a layer's output to the layer's height. -/
def LayerOutput.toSignature (lay : Layer) (output : LayerOutput) : LayerSignature lay :=
  ⟨output.1, output.2.1, fun level => output.2.2 level.val⟩

/-- `Sig` after the digest loop, with the secret derivations and the top tree's nodes as arguments:
build the forest once, then sign the layers from the bottom up. -/
def signFrom (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsLeaf → m Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest)
    (topNode : Nat → Nat → m Digest)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) : m (Option Signature) := do
  let (secrets, ftsPath, ftsPublicKey) ← buildForest parameter index ftsSecret leaves
  let some parts ← signLayers parameter index otsSecret topNode numLayers ftsPublicKey
    | return none
  return some ⟨randomness, secrets, ftsPath, fun lay => LayerOutput.toSignature lay (parts lay)⟩

attribute [irreducible] verify

/-! ### The builders with paired secrets

The seeded signer derives the secrets of a pair of chains (or of few-time leaves) with one query. These
builders take a getter per pair and walk the pair's two members after it; with table secrets they make
exactly the queries of the per-secret builders above (`Proof/Scheme/PairedEval.lean`). -/

/-- One leaf of a layer tree, with pair getters: per pair, its secrets, chain `2k`, chain `2k + 1`; then the
leaf hash. -/
def buildLeafPaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainPair → m (Digest × Digest)) (digits : Encoding) : m ((ChainIndex → Digest) × Digest) := do
  let pairs ← sequenceFin fun pair : ChainPair => do
    let secrets ← secret pair
    let first ← buildChain parameter lay tree leaf (evenChain pair) (pure secrets.1) (digits (evenChain pair)).val
    let second ← buildChain parameter lay tree leaf (oddChain pair) (pure secrets.2) (digits (oddChain pair)).val
    return (first, second)
  let chains := unpairChains pairs
  let value ← leafHash parameter lay tree leaf fun chainIdx => (chains chainIdx).2
  return (fun chainIdx => (chains chainIdx).1, value)

/-- `buildLayerTable` with pair getters. -/
def buildLayerTablePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (leaf : LeafIndex) (digits : Encoding) :
    m ((Fin (2 ^ layerHeight lay) → (ChainIndex → Digest) × Digest) × (Nat → Nat → Digest)) := do
  let leaves ← sequenceFin (n := 2 ^ layerHeight lay) fun leafNat =>
    buildLeafPaired parameter lay tree (leafOfNat leafNat.val) (secret (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.node lay tree level nodeIdx) (nodePayload left right))
    (layerHeight lay)
    (fun nodeIdx => if h : nodeIdx < 2 ^ layerHeight lay then (leaves ⟨nodeIdx, h⟩).2 else 0)
    (layerHeight lay)
  return (leaves, table)

/-- `buildLayerTree` with pair getters. -/
def buildLayerTreePaired (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (leaf : LeafIndex) (digits : Encoding) :
    m ((ChainIndex → Digest) × (Nat → Digest) × Digest) := do
  let (leaves, table) ← buildLayerTablePaired parameter lay tree secret leaf digits
  let values := if h : leaf.val < 2 ^ layerHeight lay then (leaves ⟨leaf.val, h⟩).1 else fun _ => 0
  return (values, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table (layerHeight lay) 0)

/-- `buildFtsTree` with pair getters: per pair, its secrets, the leaf hash of `2k`, of `2k + 1`; then the
levels. -/
def buildFtsTreePaired (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsPair → m (Digest × Digest)) (leaf : FtsLeaf) : m (Digest × (Nat → Digest) × Digest) := do
  let pairs ← sequenceFin fun pair : FtsPair => do
    let secrets ← secret pair
    let first ← ftsLeafHash parameter index tree (evenFtsLeaf pair) secrets.1
    let second ← ftsLeafHash parameter index tree (oddFtsLeaf pair) secrets.2
    return ((secrets.1, first), (secrets.2, second))
  let leaves := unpairFtsLeaves pairs
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.ftsNode index tree level nodeIdx) (nodePayload left right))
    ftsTreeHeight
    (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then (leaves ⟨nodeIdx, h⟩).2 else 0)
    ftsTreeHeight
  return ((leaves leaf).1, fun level => table level (Nat.xor (leaf.val / 2 ^ level) 1),
    table ftsTreeHeight 0)

/-- `buildForest` with pair getters. -/
def buildForestPaired (parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsPair → m (Digest × Digest)) (leaves : IndexGroup → FtsLeaf) :
    m ((FtsTree → Digest) × (FtsTree → Fin ftsTreeHeight → Digest) × Digest) := do
  let trees ← sequenceFin fun tree =>
    buildFtsTreePaired parameter index tree (secret tree) (leaves (ftsIndexOf tree))
  let key ← tweakableHash parameter (.ftsRoots index) (ftsRootsPayload fun tree => (trees tree).2.2)
  return (fun tree => (trees tree).1, fun tree level => (trees tree).2.1 level.val, key)

/-- `signTopLayer` with pair getters: per pair, its secrets, the first `x_{2k}` steps of chain `2k`, the
first `x_{2k+1}` steps of chain `2k + 1`. -/
def signTopLayerPaired (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (topNode : Nat → Nat → m Digest) (message : Digest) :
    m (Option LayerOutput) := do
  let tree := treeIndexAt index topLayer
  let leaf := leafIndexAt index topLayer
  let some (counter, encoding) ←
      encodingSearch parameter topLayer tree leaf message encodingAttemptLimit 0
    | return none
  let pairs ← sequenceFin fun pair : ChainPair => do
    let secrets ← secret leaf pair
    let first ← chainWalk parameter topLayer tree leaf (evenChain pair) 0 (encoding (evenChain pair)).val secrets.1
    let second ← chainWalk parameter topLayer tree leaf (oddChain pair) 0 (encoding (oddChain pair)).val secrets.2
    return (first, second)
  let values := unpairChains pairs
  let path ← sequenceFin (n := maxLayerHeight) fun level =>
    topNode level.val (Nat.xor (leaf.val / 2 ^ level.val) 1)
  return some (counter, values, fun level => if h : level < maxLayerHeight then path ⟨level, h⟩ else 0)

/-- `signLayers` with pair getters. -/
def signLayersPaired (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainPair → m (Digest × Digest)) (topNode : Nat → Nat → m Digest) :
    Nat → Digest → m (Option (Layer → LayerOutput))
  | 0, _ => pure (some fun _ => (0, fun _ => 0, fun _ => 0))
  | remaining + 1, message =>
      if hlayer : remaining < numLayers then
        if remaining = 0 then do
          let some output ← signTopLayerPaired parameter index (secret topLayer (treeIndexAt index topLayer))
              topNode message
            | return none
          return some fun other => if other = topLayer then output else (0, fun _ => 0, fun _ => 0)
        else do
          let lay : Layer := ⟨remaining, hlayer⟩
          let tree := treeIndexAt index lay
          let leaf := leafIndexAt index lay
          let some (counter, encoding) ←
              encodingSearch parameter lay tree leaf message encodingAttemptLimit 0
            | return none
          let (values, path, root) ← buildLayerTreePaired parameter lay tree (secret lay tree) leaf encoding
          let some rest ← signLayersPaired parameter index secret topNode remaining root | return none
          return some fun other => if other = lay then (counter, values, path) else rest other
      else
        pure none

/-- `signFrom` with pair getters. -/
def signFromPaired (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsPair → m (Digest × Digest))
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainPair → m (Digest × Digest))
    (topNode : Nat → Nat → m Digest)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) : m (Option Signature) := do
  let (secrets, ftsPath, ftsPublicKey) ← buildForestPaired parameter index ftsSecret leaves
  let some parts ← signLayersPaired parameter index otsSecret topNode numLayers ftsPublicKey
    | return none
  return some ⟨randomness, secrets, ftsPath, fun lay => LayerOutput.toSignature lay (parts lay)⟩

end Concrete

def deriveKey {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (domain : KeygenDomain) (seed : MasterSeed) : m Digest := do
  return truncateHash (← Concrete.oracleHash (keygenHashInput parameter domain seed))

def deriveRandomizer {m : Type → Type} [Monad m] [HasQuery HashSpec m]
    (parameter : PublicParameter) (seed : MasterSeed)
    (message : Message) (trial : BitVec 32) : m Randomness := do
  return truncateHash (← Concrete.oracleHash (randomizerHashInput parameter seed message trial))

noncomputable def sampleMasterSeed : ProbComp MasterSeed :=
  letI := SampleableType.ofFintype MasterSeed
  $ᵗ MasterSeed

namespace Seeded

open Concrete

structure SecretKey where
  seed : MasterSeed
  parameter : PublicParameter
  root : Digest

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- The two secrets of one derivation answer: its low and its high 16 bytes. -/
def splitSecrets (output : HashOutput) : Digest × Digest :=
  (truncateHash output, output.extractLsb' digestBits digestBits)

/-- `sk_{lay,tau,e,2k}` and `sk_{lay,tau,e,2k+1}`, derived from the seed with one query. -/
def otsSecret (parameter : PublicParameter) (seed : MasterSeed) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (pair : ChainPair) : m (Digest × Digest) := do
  return splitSecrets (← Concrete.oracleHash (keygenHashInput parameter (.ots lay tree leaf pair) seed))

/-- `s^{idx,kappa}_{2k}` and `s^{idx,kappa}_{2k+1}`, derived from the seed with one query. -/
def ftsSecret (parameter : PublicParameter) (seed : MasterSeed) (index : Index) (tree : FtsTree)
    (pair : FtsPair) : m (Digest × Digest) := do
  return splitSecrets (← Concrete.oracleHash (keygenHashInput parameter (.fts index tree pair) seed))

/-- The mask domain of node `(l, j)`. The signer only asks for nodes of the cached region, where the
reductions are the identity. -/
def maskDomain (level nodeIdx : Nat) : KeygenDomain :=
  .mask ⟨level % maxLayerHeight, Nat.mod_lt _ (by decide)⟩ ⟨nodeIdx % 2 ^ maxLayerHeight, Nat.mod_lt _ (by decide)⟩

/-- `mask(l, j)`, the mask of the cached top-tree node `(l, j)`, derived from the seed. -/
def maskSecret (parameter : PublicParameter) (seed : MasterSeed) (level nodeIdx : Nat) : m Digest :=
  deriveKey parameter (maskDomain level nodeIdx) seed

/-- Mask the top tree's node table below the root, level by level and left to right, deriving each mask
in turn. -/
def maskRegion (parameter : PublicParameter) (seed : MasterSeed) (table : Nat → Nat → Digest) :
    m TopRegion :=
  do
  let rows ← sequenceFin fun level : Fin maxLayerHeight => do
    let row ← sequenceFin fun nodeIdx : Fin (2 ^ (maxLayerHeight - level.val)) => do
      let mask ← maskSecret parameter seed level.val nodeIdx.val
      return table level.val nodeIdx.val ^^^ mask
    return fun nodeIdx : Nat => if h : nodeIdx < 2 ^ (maxLayerHeight - level.val) then row ⟨nodeIdx, h⟩ else 0
  return fun level nodeIdx => rows level nodeIdx.val

/-- The top tree's node `(l, j)` as the signer reads it: the cached masked node, unmasked with a freshly
derived mask. -/
def cachedTopNode (parameter : PublicParameter) (seed : MasterSeed) (cache : TopCache) (level nodeIdx : Nat) :
    m Digest := do
  let mask ← maskSecret parameter seed level nodeIdx
  return cache.node level nodeIdx ^^^ mask

/-- Build the top tree from the supplied seed (its root is the public key), mask its nodes below the root,
and authenticate the masked region with the MAC. There is no parameter derivation: `P = 0`. -/
def keygenFromSeed (seed : MasterSeed) : OracleComp HashSpec (PublicKey × TopCache × SecretKey) := do
  let (_, table) ← buildLayerTablePaired 0 topLayer rootTree (otsSecret 0 seed topLayer rootTree)
    ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  let root := table (layerHeight topLayer) 0
  let region ← maskRegion 0 seed table
  let tag ← oracleHash (macHashInput 0 seed region)
  return (⟨root, 0⟩, ⟨tag, region⟩, ⟨seed, 0, root⟩)

def signAttempt (secretKey : SecretKey) (message : Message) (randomness : Randomness) :
    m (Option (Index × (IndexGroup → FtsLeaf))) := do
  let digest ← messageDigest secretKey.parameter secretKey.root message randomness
  if Admissible digest then
    return some (digestIndex digest, digestLeaves digest)
  else
    return none

/-- Derive trials in increasing order, stopping at the first admissible digest. -/
def signDigestLoop (secretKey : SecretKey) (message : Message) : Nat → Nat →
    m (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness ← deriveRandomizer secretKey.parameter secretKey.seed message (BitVec.ofNat 32 trial)
      match ← signAttempt secretKey message randomness with
      | some (index, leaves) => return some (randomness, index, leaves)
      | none => signDigestLoop secretKey message attempts (trial + 1)

/-- `Sig(sk, m)` after the MAC check: the digest loop, the forest built once, then the layers from the
bottom up, each a counter search followed by its tree built once, and the top layer from the cache. -/
def signChecked (secretKey : SecretKey) (cache : TopCache) (message : Message) : m (Option Signature) := do
  let some (randomness, index, leaves) ← signDigestLoop secretKey message digestAttemptLimit 0
    | return none
  signFromPaired secretKey.parameter index (ftsSecret secretKey.parameter secretKey.seed index)
    (otsSecret secretKey.parameter secretKey.seed)
    (cachedTopNode secretKey.parameter secretKey.seed cache) randomness leaves

/-- `Sig(sk, cache, m)`: check the cache's MAC first (one query; a mismatch fails), then sign. -/
def sign (secretKey : SecretKey) (cache : TopCache) (message : Message) : m (Option Signature) := do
  let tag ← oracleHash (macHashInput secretKey.parameter secretKey.seed cache.region)
  if tag = cache.tag then signChecked secretKey cache message else return none

end Seeded

end SphincsSecurity
