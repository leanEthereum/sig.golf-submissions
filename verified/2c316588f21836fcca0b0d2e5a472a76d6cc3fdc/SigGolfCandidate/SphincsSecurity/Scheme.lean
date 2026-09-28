import SigGolfCandidate.SphincsSecurity.Compat
import VCVio.OracleComp.QueryTracking.LoggingOracle
import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation

/-!
# SPHINCS+ scheme

Parameters, serialized hash inputs, key generation, signing, and verification for the instance defined in `doc/sphincs/main.tex`, with the changes of the SPHINCS-golf variant: five layers of heights `(11,6,6,6,5)`, target sum `182`, paired secret derivations (one query yields two secrets), a top tree cached by key generation (masked, and authenticated by a MAC keyed with the master seed), no public-parameter derivation (`P = 0`), a message digest that does not bind the root, a verifier that rejects counters at or above `C_max`, and a signer that builds every tree it touches exactly once, in the query order of the reference implementation.

The few-time signature is PORS+FP (`work/design/SPEC-pors.md`, reference `work/py-pors/ref.py`): one Merkle
tree of height `14` per instance `idx`, the full 256-bit digest split into `idx` (34 bits) and `k = 15`
leaf indices, admissible when the indices are distinct and their octopus (the pruned authentication set)
has at most `120` nodes. The signature is *witness-shaped*: the sorted leaves' digest slots, their secrets,
and the stack-machine segments of the verifier with the authentication nodes they fold. The verifier is the
stack machine of `ref.pors_root`, and the tree root is the bottom layer's message. Tree nodes are hashed
under their heap index (tag `10`, position `0`), the relabeled form of `ref.py`'s node tweaks.
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
def targetSum : Nat := 182
def numLayers : Nat := 5
def totalHeight : Nat := 34
/-- The tallest layer, the top one, `h_0 = 11`, which bounds every layer's leaf index. -/
def maxLayerHeight : Nat := 11
/-- The height of the PORS tree of an instance: `2^14` leaves. -/
def ftsTreeHeight : Nat := 14
/-- `k`, the leaf indices a digest carries (its slots) and the leaves a signature opens. -/
def ftsOpenings : Nat := 15
/-- The authentication-node budget: an admissible digest's octopus has at most `120` nodes, and the verifier
accepts at most `120` folds. -/
def ftsAuthCapacity : Nat := 120
/-- The verifier's segments: one per opened leaf and one per merge, `2k - 1 = 29`. -/
def ftsSegments : Nat := 2 * ftsOpenings - 1
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
/-- The tree of a few-time instance. PORS has a single tree per instance, so this type is a unit; it is kept
so that the secret table `Index → FtsTree → FtsLeaf → Digest`, the key-derivation domain and the hash
domains keep their shape. Its only value is `porsTree`. -/
abbrev FtsTree := Fin 1
/-- A slot of the message digest, `r < k`: slot `r` carries the leaf index `v_r`. -/
abbrev IndexGroup := Fin ftsOpenings
/-- A slot code of the signature's permutation: a digest slot `r < k`, or `k = 15`, the out-of-range
sentinel whose value is `2^14`. -/
abbrev SlotCode := Fin (ftsOpenings + 1)
abbrev FtsLeaf := Fin (2 ^ ftsTreeHeight)
abbrev Encoding := ChainIndex → Digit
abbrev HashInput := List UInt8
/-- A pair of chains `(2k, 2k + 1)` of a one-time key, whose secrets one derivation query yields. -/
abbrev ChainPair := Fin (numChains / 2)
/-- A pair of leaves `(2q, 2q + 1)` of the PORS tree, whose secrets one derivation query yields. -/
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

/-- The message digest is the full 256-bit answer: the index (`h = 34` bits), the `k = 15` leaf indices of
`14` bits each, and `12` unused bits. -/
def messageDigestBits : Nat := hashOutputBits

abbrev MessageDigest := BitVec messageDigestBits

/-- The message digest of an answer: all of its bits. -/
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

/-- One segment of the PORS stack machine: `folds` authentication nodes to fold into the pending node, then a
merge with the node on top of the stack (`merge = true`) or the end of the current leaf (`merge = false`).
`parity` is bit `0` of the heap index at the segment's start; it orders the first fold's children. It is
read only when `folds > 0`, and is normalised to `false` otherwise, so that an accepted signature carries no
unread data. A segment with `folds = 15` is rejected by the verifier before any node is read. -/
structure Segment where
  folds : Fin 16
  merge : Bool
  parity : Bool
  nodes : Fin folds.val → Digest
  parity_normal : folds.val = 0 → parity = false
deriving DecidableEq

/-- A segment with `parity` normalised: kept when there is a fold, `false` otherwise. -/
def Segment.normalized (folds : Fin 16) (merge parity : Bool) (nodes : Fin folds.val → Digest) : Segment :=
  ⟨folds, merge, parity && decide (folds.val ≠ 0), nodes, fun h => by simp [h]⟩

instance : Inhabited Segment := ⟨⟨0, false, false, fun index => index.elim0, fun _ => rfl⟩⟩

/-- The node `i` of a segment, or zero past its folds. -/
def Segment.node (segment : Segment) (i : Nat) : Digest :=
  if h : i < segment.folds.val then segment.nodes ⟨i, h⟩ else 0

/-- The few-time (PORS) part of a signature, in the shape the verifier reads it: for the `s`-th smallest
opened leaf, `perm s` is its digest slot and `secrets s` its secret; `segments` is the stack machine's
program, `2k - 1 = 29` segments carrying the authentication nodes in read order. -/
structure FtsSignature where
  perm : Fin ftsOpenings → SlotCode
  secrets : Fin ftsOpenings → Digest
  segments : Fin ftsSegments → Segment
deriving DecidableEq

/-- The randomizer, the PORS opening and five layer signatures. -/
structure Signature where
  randomness : Randomness
  fts : FtsSignature
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
  /-- The PORS leaf `j` (tag `9`). The verifier may hash the sentinel value `j = 2^14` before rejecting,
  so the leaf is a natural number; honest leaves are below `2^14`. -/
  | ftsLeaf (index : Index) (tree : FtsTree) (leaf : Nat)
  /-- The PORS node with heap index `heapIdx` (tag `10`, position `0`): node `(level, nodeIdx)` of the tree
  has heap index `2^(14 - level) + nodeIdx`. The verifier's queries have heap indices below `2^14`,
  including `0`, which no tree node has. -/
  | ftsNode (index : Index) (tree : FtsTree) (heapIdx : Nat)
  | message
deriving DecidableEq

/-- Serialize a typed hash domain into the fields of a tweak. Inside the hypertree the layer field is the layer and the tree field the tree; inside a few-time key they are the (only) tree, `0`, and the index that selects the instance. -/
def hashDomainFields : HashDomain → TweakFields
  | .chain lay tree leaf chainIdx step => tweakFields 1 lay tree (chainLength * chainIdx + step) leaf
  | .leaf lay tree leaf => tweakFields 2 lay tree 0 leaf
  | .node lay tree level nodeIdx => tweakFields 3 lay tree level nodeIdx
  | .encoding lay tree leaf => tweakFields 4 lay tree 0 leaf
  | .ftsLeaf index tree leaf => tweakFields 9 tree index 0 leaf
  | .ftsNode index tree heapIdx => tweakFields 10 tree index 0 heapIdx
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
  /-- The secrets of leaves `2q` and `2q + 1` of the PORS tree of instance `index`. -/
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

`v = 42` chunks of `w = 3` bits, 21 in each half of the digest, one pinned bit per half, and the code is the words of digit sum `T = 182`. Two distinct words of equal sum are incomparable, which is what removes the Winternitz checksum and the reason why we need the counter. -/

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

/-! ### The few-time signature (PORS) -/

/-- The only tree of an instance. -/
def porsTree : FtsTree := ⟨0, by decide⟩

/-- A node index at level `0` read as a leaf index. -/
def ftsLeafOfNat (value : Nat) : FtsLeaf :=
  ⟨value % 2 ^ ftsTreeHeight, Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The heap index of node `(level, nodeIdx)` of the PORS tree: `2^(14 - level) + nodeIdx` (the root is `1`,
leaf `j` is `2^14 + j`). -/
def ftsHeapIndex (level nodeIdx : Nat) : Nat := 2 ^ (ftsTreeHeight - level) + nodeIdx

/-- `Y^{idx}_{0,j}`, the hash of one few-time secret. -/
def ftsLeafHash (parameter : PublicParameter) (index : Index) (tree : FtsTree) (leaf : Nat)
    (secret : Digest) : m Digest :=
  tweakableHash parameter (.ftsLeaf index tree leaf) (bytesLE 16 secret)

/-- The children in the order a fold hashes them: the sibling first when the current node is a right
child. -/
def foldPayload (right : Bool) (sibling current : Digest) : HashInput :=
  if right then nodePayload sibling current else nodePayload current sibling

/-- The `remaining` folds of a segment from its fold `position` on, starting from `current` at heap index
`heap`: fold `i` hashes `current` with the segment's node `i` into the node with heap index `heap / 2`. The
first fold's child order is the segment's `parity`, later folds use bit `0` of `heap`. Returns the node and
its heap index. -/
def foldSegment (parameter : PublicParameter) (index : Index) (segment : Segment) :
    Nat → Nat → Digest → Nat → m (Digest × Nat)
  | 0, _, current, heap => pure (current, heap)
  | remaining + 1, position, current, heap => do
      let right := if position = 0 then segment.parity else decide (heap % 2 = 1)
      let parent ← tweakableHash parameter (.ftsNode index porsTree (heap / 2))
        (foldPayload right (segment.node position) current)
      foldSegment parameter index segment remaining (position + 1) parent (heap / 2)

/-- The hash a segment performs before its folds: the leaf hash of the leaf's value and secret (the leaf's
first segment), or the merge of the node `left` popped from the stack with the current node into the node
with heap index `heapIdx`. -/
inductive PendingHash where
  | leaf (value : Nat) (secret : Digest)
  | merge (heapIdx : Nat) (left : Digest)

/-- The stack machine's state: the current node and its heap index, the stack of pending nodes with the heap
index of the sibling they wait for (top first), the folds so far, and the next segment. -/
structure RecoverState where
  node : Digest
  heap : Nat
  stack : List (Digest × Nat)
  folds : Nat
  segment : Nat

/-- The start state. -/
def RecoverState.initial : RecoverState := ⟨0, 0, [], 0, 0⟩

/-- Run one leaf's segments, `ref.pors_root`'s inner loop, with at most `fuel` segments. Per segment: reject
`folds > 14`; reject a segment with folds whose parity bit `t` is not bit `0` of the current heap index
(`t` orders the first fold's children, so an unchecked `t` would let a hash computed at heap index `E` stand
for the sibling `E xor 1`); the pending hash; the folds; then either the leaf ends (`merge = false`) or the
stack's top is popped (reject if the stack is empty or its sibling heap index is not the current one) and
becomes the next segment's pending merge, one level up. -/
def recoverSegments (parameter : PublicParameter) (index : Index) (segments : Fin ftsSegments → Segment) :
    Nat → PendingHash → RecoverState → m (Option RecoverState)
  | 0, _, _ => pure none
  | fuel + 1, pending, state => do
      if hsegment : state.segment < ftsSegments then
        let segment := segments ⟨state.segment, hsegment⟩
        if ftsTreeHeight < segment.folds.val then
          return none
        else if segment.folds.val ≠ 0 ∧ segment.parity ≠ decide (state.heap % 2 = 1) then
          return none
        else
          let start ← match pending with
            | .leaf value secret => ftsLeafHash parameter index porsTree value secret
            | .merge heapIdx left =>
                tweakableHash parameter (.ftsNode index porsTree heapIdx) (nodePayload left state.node)
          let (node, heap) ← foldSegment parameter index segment segment.folds.val 0 start state.heap
          let state : RecoverState :=
            { state with node := node, heap := heap, folds := state.folds + segment.folds.val,
                         segment := state.segment + 1 }
          if segment.merge then
            match state.stack with
            | [] => return none
            | (left, sibling) :: rest =>
                if sibling = heap then
                  recoverSegments parameter index segments fuel (.merge (heap / 2) left)
                    { state with stack := rest, heap := heap / 2 }
                else
                  return none
          else
            return some state
      else
        return none

/-- Run the leaves from the `position`-th smallest on, `ref.pors_root`'s outer loop: the leaf's value is
`values (perm position)`; reject unless the values increase strictly and the last one is below `2^14`;
start at heap index `2^14 | value` with the leaf hash pending, run its segments, and push the node with its
sibling's heap index unless it is the last leaf. -/
def recoverLeaves (parameter : PublicParameter) (index : Index) (values : SlotCode → Nat)
    (fts : FtsSignature) : Nat → Nat → Nat → RecoverState → m (Option RecoverState)
  | 0, _, _, state => pure (some state)
  | remaining + 1, position, previous, state => do
      if hposition : position < ftsOpenings then
        let value := values (fts.perm ⟨position, hposition⟩)
        if 0 < position ∧ ¬ previous < value then
          return none
        else if position + 1 = ftsOpenings ∧ ¬ value < 2 ^ ftsTreeHeight then
          return none
        else
          let some state ← recoverSegments parameter index fts.segments ftsSegments
              (.leaf value (fts.secrets ⟨position, hposition⟩))
              { state with heap := 2 ^ ftsTreeHeight ||| value }
            | return none
          let state := if position + 1 < ftsOpenings then
              { state with stack := (state.node, state.heap ^^^ 1) :: state.stack } else state
          recoverLeaves parameter index values fts remaining (position + 1) value state
      else
        return none

/-- `FtsRec`, the stack machine of `ref.pors_root`: run the `k` leaves, then accept the node as the PORS root
if there were at most `120` folds, the node is the root (heap index `1`) and the stack is empty. -/
def ftsRecover (parameter : PublicParameter) (index : Index) (values : SlotCode → Nat)
    (fts : FtsSignature) : m (Option Digest) := do
  let some state ← recoverLeaves parameter index values fts ftsOpenings 0 0 RecoverState.initial
    | return none
  if state.folds ≤ ftsAuthCapacity ∧ state.heap = 1 ∧ state.stack = [] then
    return some state.node
  else
    return none

/-! ### The message digest -/

/-- `rho || 0^16 || m`, what the message digest hashes after the tweak and the parameter. The root slot is zero, so the digest does not bind the root and the signer does not need it; the argument is kept for the shape of the statement and ignored. -/
def messageDigestPayload (_root : Digest) (message : Message) (randomness : Randomness) : HashInput :=
  bytesLE 16 randomness ++ bytesLE 16 (0 : Digest) ++ bytesLE 32 message

/-- `Digest(P, m, rho)`, the full answer. -/
def messageDigest (parameter : PublicParameter) (root : Digest) (message : Message)
    (randomness : Randomness) : m MessageDigest := do
  let output ← oracleHash
    (tweakableHashInput parameter .message (messageDigestPayload root message randomness))
  return truncateMessageDigest output

/-- `idx = N mod 2^h`. -/
def digestIndex (digest : MessageDigest) : Index :=
  (digest.extractLsb' 0 totalHeight).toFin

/-- `v_r = floor(N / 2^(h + 14 r)) mod 2^14`, the leaf index in slot `r`. -/
def digestLeaves (digest : MessageDigest) : IndexGroup → FtsLeaf :=
  fun slot => (digest.extractLsb' (totalHeight + ftsTreeHeight * slot.val) ftsTreeHeight).toFin

/-- The value of a slot code as the verifier reads it: the slot's leaf index, or `2^14` for the sentinel
code `k`. -/
def slotValue (leaves : IndexGroup → FtsLeaf) (code : SlotCode) : Nat :=
  if h : code.val < ftsOpenings then (leaves ⟨code.val, h⟩).val else 2 ^ ftsTreeHeight

/-! ### Octopus and schedule

The pure combinatorics of `ref.octopus_size` and `ref.schedule` on the sorted leaf indices. -/

/-- Python's `int.bit_length`: `0` for `0`, else `floor(log2 x) + 1`. -/
def bitLength (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-- The size of the octopus (the pruned authentication set) of the sorted distinct leaves `sorted`:
`14 + sum_{s >= 1} bitlen(v_{s-1} xor v_s) - 2 (|sorted| - 1)`, written as `14 + 2 + sum - 2 |sorted|`
(the same value for every nonempty list; on sorted distinct lists the subtraction never truncates). -/
def octopusSize (sorted : List Nat) : Nat :=
  ftsTreeHeight + 2 + (List.zipWith (fun a b => bitLength (a ^^^ b)) sorted sorted.tail).sum -
    2 * sorted.length

/-- The slots ordered by their leaf indices (stable: equal indices keep their slot order). -/
def sortedSlots (leaves : IndexGroup → FtsLeaf) : List IndexGroup :=
  (List.finRange ftsOpenings).insertionSort fun r r' => (leaves r).val ≤ (leaves r').val

/-- The leaf indices, sorted. -/
def sortedLeaves (leaves : IndexGroup → FtsLeaf) : List Nat :=
  (sortedSlots leaves).map fun r => (leaves r).val

/-- The signer's (and the verifier's) condition on a digest's leaf indices: pairwise distinct, and an
octopus of at most `120` nodes. -/
def AdmissibleLeaves (leaves : IndexGroup → FtsLeaf) : Prop :=
  Function.Injective leaves ∧ octopusSize (sortedLeaves leaves) ≤ ftsAuthCapacity

instance (leaves : IndexGroup → FtsLeaf) : Decidable (AdmissibleLeaves leaves) :=
  inferInstanceAs (Decidable (Function.Injective leaves ∧ _))

/-- A digest is admissible exactly when its leaf indices are. -/
def Admissible (digest : MessageDigest) : Prop := AdmissibleLeaves (digestLeaves digest)

instance (digest : MessageDigest) : Decidable (Admissible digest) :=
  inferInstanceAs (Decidable (AdmissibleLeaves (digestLeaves digest)))

/-- One segment of the honest schedule: whether it ends in a merge, the parity bit `t` of its start (not yet
normalised), and the positions `(height, nodeIdx)` of the nodes it folds, in read order. -/
structure ScheduleSegment where
  merge : Bool
  parity : Bool
  reads : List (Nat × Nat)
deriving DecidableEq, Inhabited

/-- The schedule's state: the finished segments, the stack of sibling heap indices the pending nodes wait
for (top first), the current heap index, and the open segment's parity and reads. -/
structure ScheduleState where
  done : List ScheduleSegment
  stack : List Nat
  heap : Nat
  parity : Bool
  reads : List (Nat × Nat)

/-- One height of a leaf's climb: merge if the stack's top waits for the current node (the open segment
ends with a merge, and the next one starts one level up), else fold with the witness sibling. -/
def scheduleStep (state : ScheduleState) (height : Nat) : ScheduleState :=
  let fold : ScheduleState :=
    { state with reads := state.reads ++ [(height, (state.heap ^^^ 1) - 2 ^ (ftsTreeHeight - height))],
                 heap := state.heap / 2 }
  match state.stack with
  | top :: rest =>
      if top = state.heap then
        { state with done := state.done ++ [⟨true, state.parity, state.reads⟩], stack := rest,
                     heap := state.heap / 2, parity := decide (state.heap / 2 % 2 = 1), reads := [] }
      else fold
  | [] => fold

/-- The leaves from `v` on: climb from `2^14 | v` through the heights below the level where `v` meets the
next leaf (all `14` heights for the last leaf), close the leaf's last segment, and push the sibling of the
node reached unless it is the last leaf. -/
def scheduleLeaves : List Nat → ScheduleState → ScheduleState
  | [], state => state
  | v :: rest, state =>
      let heap := 2 ^ ftsTreeHeight ||| v
      let top := match rest with
        | [] => ftsTreeHeight
        | w :: _ => bitLength (v ^^^ w) - 1
      let state := (List.range top).foldl scheduleStep
        { state with heap := heap, parity := decide (heap % 2 = 1), reads := [] }
      let state := { state with done := state.done ++ [⟨false, state.parity, state.reads⟩] }
      scheduleLeaves rest (match rest with
        | [] => state
        | _ :: _ => { state with stack := (state.heap ^^^ 1) :: state.stack })

/-- `ref.schedule`: the honest segments of the sorted leaves. For an admissible digest there are `29` of
them, each with at most `14` reads, and `octopusSize` reads in all. -/
def schedule (sorted : List Nat) : List ScheduleSegment :=
  (scheduleLeaves sorted ⟨[], [], 0, false, []⟩).done

/-- The number of folds of a schedule segment, as a segment field. -/
def ScheduleSegment.folds (segment : ScheduleSegment) : Fin 16 :=
  ⟨segment.reads.length % 16, Nat.mod_lt _ (by decide)⟩

/-- `ref.schedule`'s segment byte `a | 16 merge | 32 t` (before normalisation). -/
def ScheduleSegment.byte (segment : ScheduleSegment) : Nat :=
  segment.reads.length + 16 * (if segment.merge then 1 else 0) + 32 * (if segment.parity then 1 else 0)

/-- The segment with the given nodes, its parity normalised. -/
def ScheduleSegment.toSegment (segment : ScheduleSegment) (nodes : Fin segment.folds.val → Digest) :
    Segment :=
  Segment.normalized segment.folds segment.merge segment.parity nodes

/-- The honest PORS signature of the digest's leaves: the slots in the order of their leaves, the leaves'
secrets, and the schedule's segments with the tree's nodes (`node level nodeIdx`) at their read positions. -/
def honestFts (leaves : IndexGroup → FtsLeaf) (secret : FtsLeaf → Digest) (node : Nat → Nat → Digest) :
    FtsSignature :=
  let slots := sortedSlots leaves
  let segments := schedule (sortedLeaves leaves)
  { perm := fun s => (slots.getD s.val ⟨0, by decide⟩).castSucc
    secrets := fun s => secret (leaves (slots.getD s.val ⟨0, by decide⟩))
    segments := fun j =>
      let segment := segments.getD j.val default
      segment.toSegment fun i =>
        let position := segment.reads.getD i.val (0, 0)
        node position.1 position.2 }

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

/-- `Ver` after the counter check: recompute the digest, recover the PORS root with the stack machine (which
enforces admissibility: strictly increasing leaves, at most `120` folds), walk the layers and compare with
the root. -/
def verifyCore (publicKey : PublicKey) (message : Message) (signature : Signature) : m Bool := do
  let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
  let index := digestIndex digest
  let some ftsPublicKey ← ftsRecover publicKey.parameter index (slotValue (digestLeaves digest))
      signature.fts
    | return false
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

/-- Build the PORS tree of instance `index` once: leaves `j = 0, ..., 2^14 - 1` (secret, then leaf hash),
then the levels bottom-up, each left to right, node `(level, nodeIdx)` under its heap index. Returns the
secrets and the node table (level `0` holds the leaves, level `14` the root). -/
def buildFtsTree (parameter : PublicParameter) (index : Index) (secret : FtsLeaf → m Digest) :
    m ((FtsLeaf → Digest) × (Nat → Nat → Digest)) := do
  let leaves ← sequenceFin fun leafIdx : FtsLeaf => do
    let value ← secret leafIdx
    let hashed ← ftsLeafHash parameter index porsTree leafIdx.val value
    return (value, hashed)
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.ftsNode index porsTree (ftsHeapIndex level nodeIdx)) (nodePayload left right))
    ftsTreeHeight
    (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then (leaves ⟨nodeIdx, h⟩).2 else 0)
    ftsTreeHeight
  return (fun leafIdx => (leaves leafIdx).1, table)

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
build the PORS tree once, read the opening off it, then sign the layers from the bottom up, the tree's root
being the bottom layer's message. -/
def signFrom (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsLeaf → m Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest)
    (topNode : Nat → Nat → m Digest)
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) : m (Option Signature) := do
  let (secrets, table) ← buildFtsTree parameter index (ftsSecret porsTree)
  let some parts ← signLayers parameter index otsSecret topNode numLayers (table ftsTreeHeight 0)
    | return none
  return some ⟨randomness, honestFts leaves secrets table,
    fun lay => LayerOutput.toSignature lay (parts lay)⟩

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

/-- `buildFtsTree` with pair getters: per pair, its secrets, the leaf hash of `2q`, of `2q + 1`; then the
levels. -/
def buildFtsTreePaired (parameter : PublicParameter) (index : Index)
    (secret : FtsPair → m (Digest × Digest)) : m ((FtsLeaf → Digest) × (Nat → Nat → Digest)) := do
  let pairs ← sequenceFin fun pair : FtsPair => do
    let secrets ← secret pair
    let first ← ftsLeafHash parameter index porsTree (evenFtsLeaf pair).val secrets.1
    let second ← ftsLeafHash parameter index porsTree (oddFtsLeaf pair).val secrets.2
    return ((secrets.1, first), (secrets.2, second))
  let leaves := unpairFtsLeaves pairs
  let table ← buildLevels
    (fun level nodeIdx left right =>
      tweakableHash parameter (.ftsNode index porsTree (ftsHeapIndex level nodeIdx)) (nodePayload left right))
    ftsTreeHeight
    (fun nodeIdx => if h : nodeIdx < 2 ^ ftsTreeHeight then (leaves ⟨nodeIdx, h⟩).2 else 0)
    ftsTreeHeight
  return (fun leafIdx => (leaves leafIdx).1, table)

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
  let (secrets, table) ← buildFtsTreePaired parameter index (ftsSecret porsTree)
  let some parts ← signLayersPaired parameter index otsSecret topNode numLayers (table ftsTreeHeight 0)
    | return none
  return some ⟨randomness, honestFts leaves secrets table,
    fun lay => LayerOutput.toSignature lay (parts lay)⟩

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

/-- `s^{idx}_{2q}` and `s^{idx}_{2q+1}`, derived from the seed with one query. -/
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

/-- `Sig(sk, m)` after the MAC check: the digest loop, the PORS tree built once, then the layers from the
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
