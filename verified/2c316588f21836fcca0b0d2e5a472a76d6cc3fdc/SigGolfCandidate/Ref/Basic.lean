import SigGolfCandidate.Legacy
import SigGolfCandidate.CacheBytes
import Mathlib.Data.List.Sort

/-!
# SPHINCS-golf reference specification: primitives

Byte-level primitives of the reference specification (PORS+FP variant: `work/py-pors/ref.py`,
`work/design/SPEC-pors.md`, `work/py-pors/PROGRAMS.md`):

* byte encodings (little endian) and conversions between `List Byte` and `Bytes n`;
* the parameters;
* the 16-byte tweak;
* `pad64` (zero padding to whole 64-byte blocks), the oracle input format `fmt` (chain inputs
  `tw || P || v` become `tw' || 0^32 || v` with the split position `p'`; hypertree node inputs
  (tag 3) get the heap index `2^(h - lam) + j`; the digest input becomes `tw || rho || m`;
  everything else `pad64`), and the hash wrappers `H`, `hash16`, `th`;
* every per-hash input format (`*Input`), the exact byte list *before* padding;
* digest split (`idxOf`, `leafOf`, `leavesOf`), the PORS index functions (`bitLen`,
  `octopusSize`, `sortLeaves`, `admissible`, `schedule`), routing (`route`), digit decoding
  (`decodeDigits`).

**PORS nodes (tag 10) are written directly in their real block form** `enc(10, 0, idx, 0, H) ||
P || L || R` with the heap index `H` in the `j` field (`porsNodeInput idx H l r`), so `fmt` is the
identity (zero padding of a 64-byte input) on them: `ref.f_query` relabels the signer's
`tw(10, 0, idx, lam, j)` to exactly this block with `H = 2^(14 - lam) + j`, and `ref.node_query`
queries it for every `H` (also `H = 0`, out of the honest range). Only tag 3 is relabeled.

All values (secrets, chain values, nodes, roots, `rho`) are `Val = List Byte` of length 16.
Byte `i` of a `Bytes n` (a `BitVec (8 n)`) is bits `8 i .. 8 i + 7` (as `SigGolfCandidate.Legacy.bytes`), so
all conversions are little endian, exactly like the RISC-V memory.
-/

namespace SigGolfCandidate.Ref
open SigGolfCandidate.Legacy OracleComp OracleSpec

/-! ## Bytes -/

/-- A 16-byte value (hash output truncated to 128 bits, secret, node, ...). -/
abbrev Val := List Byte

/-- The byte `n mod 256`. -/
def byte (n : Nat) : Byte := BitVec.ofNat 8 n

/-- `k`-byte little-endian encoding of `v mod 256^k`. -/
def leBytes (k v : Nat) : List Byte := (List.range k).map fun i => byte (v / 256 ^ i)

/-- `LE32`. -/
def le32 (v : Nat) : List Byte := leBytes 4 v

/-- Little-endian value of a byte list. -/
def leNat : List Byte → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNat bs

/-- `0^k` (bytes). -/
def zeros (k : Nat) : List Byte := List.replicate k 0

/-- The bytes of a `Bytes n` value (`= SigGolfCandidate.Legacy.bytes`, the loader's byte order). -/
def toList {n : Nat} (x : Bytes n) : List Byte := SigGolfCandidate.Legacy.bytes x

/-- The `Bytes n` value of a byte list (little endian; extra bytes are dropped). -/
def ofList (n : Nat) (l : List Byte) : Bytes n := BitVec.ofNat (8 * n) (leNat l)

/-- The first `k` bytes of a hash answer. -/
def answerBytes (k : Nat) (a : BitVec 256) : List Byte :=
  (List.range k).map fun i => a.extractLsb' (8 * i) 8

/-- `l[off .. off + len)`. -/
def slice (l : List Byte) (off len : Nat) : List Byte := (l.drop off).take len

/-! ## Parameters (SPEC-pors.md) -/

def nChains : Nat := 42
/-- The WOTS target sum (the 42 3-bit digits of an accepted encoding sum to it). -/
def targetSum : Nat := 182
/-- Old name of `targetSum`. -/
abbrev target : Nat := targetSum
/-- The number of hypertree layers `d`. -/
def nLayers : Nat := 5
/-- The layer heights, layer 0 (the cached top tree) first. -/
def heights : List Nat := [11, 6, 6, 6, 5]
def totalH : Nat := 34
/-- PORS tree height (`POR_H`). -/
def porsH : Nat := 14
/-- Opened PORS leaves per signature (`POR_K`). -/
def porsK : Nat := 15
/-- PORS leaves (`POR_T = 2^14`). -/
def porsT : Nat := 2 ^ porsH
/-- Authentication-node slots (`POR_M`, the octopus bound). -/
def porsM : Nat := 120
/-- Schedule segments (`POR_SEGS = 2 k - 1`: one per leaf start, one per merge). -/
def porsSegs : Nat := 2 * porsK - 1
/-- Digest trials `A_max`. -/
def aMax : Nat := 2 ^ 20
/-- The counter limit `C_max`: the signer tries `c < cMax`, the verifier rejects `c ≥ cMax`. -/
def cMax : Nat := 2 ^ 22
/-- Signature bytes `S`. -/
def sigBytes : Nat := 6100
/-- Witness bytes `W`. -/
def witBytes : Nat := 6348

/-- Height of hypertree layer `lay` (layer 0 = top): `heights[lay]`. -/
def height (lay : Nat) : Nat := heights.getD lay 0

/-- `sum_{j > lay} h_j`, the position of `e_lay` in `idx`. -/
def shiftBelow (lay : Nat) : Nat := ((List.range nLayers).filter (lay < ·)).foldr (height · + ·) 0

/-- `(e_lay, tau_lay)`: the leaf index in and the index of the tree of layer `lay`. -/
def route (idx lay : Nat) : Nat × Nat :=
  (idx / 2 ^ shiftBelow lay % 2 ^ height lay, idx / 2 ^ (shiftBelow lay + height lay))

/-! ### The cached top tree (layer 0) -/

/-- Height of the top tree (`h_0 = 11`). -/
abbrev topH : Nat := height 0

/-- `N_l = sum_{k < l} 2^(topH - k)`: the index of the first node of level `l` in the region. -/
def topN (l : Nat) : Nat := ((List.range l).map fun k => 2 ^ (topH - k)).sum

/-- Bytes of the masked-node region (levels `0 .. topH - 1`): `16 * N_topH = 65504`. -/
def regionBytes : Nat := 16 * topN topH

/-- The cache: tag (32) | region | zeros, `CACHE_BYTES = 2^17` in total. -/
def cacheBytes : Nat := CACHE_BYTES

/-- Offset of the masked top-tree node `(l, j)` in the cache. -/
def cacheNodeOff (l j : Nat) : Nat := 32 + 16 * (topN l + j)

/-- The masked top-tree node `(l, j)` of a cache. -/
def cacheNode (cache : List Byte) (l j : Nat) : Val := slice cache (cacheNodeOff l j) 16

/-- The cache's MAC tag (bytes `0 .. 32`). -/
def cacheTag (cache : List Byte) : List Byte := slice cache 0 32

/-- The cache's masked-node region (bytes `32 .. 32 + regionBytes`). -/
def cacheRegion (cache : List Byte) : List Byte := slice cache 32 regionBytes

/-- Bytewise XOR (the shorter length). -/
def xorBytes (a b : List Byte) : List Byte := List.zipWith (· ^^^ ·) a b

/-! ## Tweaks and hashing -/

/-- `enc(t, lay, tau, p, j) = 1 || t || lay || tau >> 32 || LE32 p || LE32 (tau mod 2^32) || LE32 j`
(`word0 = 1 | t<<8 | lay<<16 | (tau>>32)<<24 | p<<32`, `word1 = (tau mod 2^32) | j<<32`). -/
def tweak (t lay tau p j : Nat) : List Byte :=
  [byte 1, byte t, byte lay, byte (tau / 2 ^ 32)] ++ le32 p ++ le32 (tau % 2 ^ 32) ++ le32 j

/-- The public parameter `P = 0^128`. -/
def P : List Byte := zeros 16

/-- `tw || P || payload`, the unpadded input of `Th(P, tw, payload)`. -/
def thInput (tw payload : List Byte) : List Byte := tw ++ P ++ payload

/-- `n` such that `pad64 x` has `n + 1` blocks: `max 1 ⌈len/64⌉ - 1`. -/
def padBlocks (len : Nat) : Nat := (len + 63) / 64 - 1

/-- `x` followed by zero bytes up to `64 * (padBlocks |x| + 1)` bytes. -/
def padTo64 (x : List Byte) : List Byte :=
  x ++ zeros (64 * (padBlocks x.length + 1) - x.length)

/-- The oracle query of `x`: `x` zero padded to a nonzero multiple of 64 bytes. -/
def pad64 (x : List Byte) : Query := ⟨padBlocks x.length, ofList _ (padTo64 x)⟩

/-- WOTS chain inputs (`PROGRAMS.md`, FORMAT): 48 bytes with tag byte (byte 1) `1`. -/
def IsChainFmt (x : List Byte) : Prop := x.length = 48 ∧ x.getD 1 0 = byte 1

instance (x : List Byte) : Decidable (IsChainFmt x) :=
  inferInstanceAs (Decidable (x.length = 48 ∧ x.getD 1 0 = byte 1))

/-- Hypertree node inputs: 64 bytes with tag byte `3`. (PORS nodes, tag 10, are not relabeled:
their inputs already carry the heap index, see `porsNodeInput`.) -/
def IsNodeFmt (x : List Byte) : Prop := x.length = 64 ∧ x.getD 1 0 = byte 3

instance (x : List Byte) : Decidable (IsNodeFmt x) :=
  inferInstanceAs (Decidable (x.length = 64 ∧ x.getD 1 0 = byte 3))

/-- Message digest inputs: 96 bytes with tag byte `12`. -/
def IsDigestFmt (x : List Byte) : Prop := x.length = 96 ∧ x.getD 1 0 = byte 12

instance (x : List Byte) : Decidable (IsDigestFmt x) :=
  inferInstanceAs (Decidable (x.length = 96 ∧ x.getD 1 0 = byte 12))

/-- The split chain position `p' = (p mod 8) | (p div 8) << 8` (byte 4 = `mu - 1`, byte 5 = `i`
for `p = 8 i + mu - 1`). -/
def splitP (p : Nat) : Nat := p % 8 + 256 * (p / 8)

/-- The heap index `2^(h - lam) + j` of node `j` of level `lam` of a tree of height `h`. -/
def heapIndex (h lam j : Nat) : Nat := 2 ^ (h - lam) + j

/-- The height of the tree of a (tag 3) node input: `height lay`, `lay` = byte 2. -/
def nodeHeight (x : List Byte) : Nat := height (x.getD 2 0).toNat

/-- The 64-byte block of a chain input `x = tw || P || v`: `tw' || 0^32 || v`, `tw'` = `tw` with
the `p` field (bytes 4..8) replaced by `splitP p`. -/
def chainBlock (x : List Byte) : List Byte :=
  x.take 4 ++ le32 (splitP (leNat (slice x 4 4))) ++ slice x 8 8 ++ zeros 32 ++ x.drop 32

/-- The block of a node input `enc(t, lay, tau, lam, j) || P || L || R`:
`enc(t, lay, tau, 0, heapIndex h lam j) || P || L || R`. -/
def nodeBlock (x : List Byte) : List Byte :=
  x.take 4 ++ le32 0 ++ slice x 8 4 ++
    le32 (heapIndex (nodeHeight x) (leNat (slice x 4 4)) (leNat (slice x 12 4))) ++ x.drop 16

/-- The block of a digest input `tw || P || rho || 0^16 || m`: `tw || rho || m`. -/
def digestBlock (x : List Byte) : List Byte := x.take 16 ++ slice x 32 16 ++ x.drop 64

/-- **The oracle input format** `f` (`PROGRAMS.md`, FORMAT; `ref.f_query`): chain inputs, hypertree
node inputs (tag 3) and digest inputs become the one-block `chainBlock`, `nodeBlock`,
`digestBlock`; every other input is zero padded (`pad64`). PORS node inputs (tag 10) are built
in their relabeled form already (`porsNodeInput`), so zero padding (the identity on 64 bytes)
is exactly `ref.f_query` on the signer's tag-10 inputs and `ref.node_query`'s raw blocks. -/
def fmt (x : List Byte) : Query :=
  if IsChainFmt x then ⟨0, ofList _ (chainBlock x)⟩
  else if IsNodeFmt x then ⟨0, ofList _ (nodeBlock x)⟩
  else if IsDigestFmt x then ⟨0, ofList _ (digestBlock x)⟩
  else pad64 x

/-- The bytes of `fmt x` (`toList_fmt`). -/
def fmtList (x : List Byte) : List Byte :=
  if IsChainFmt x then chainBlock x
  else if IsNodeFmt x then nodeBlock x
  else if IsDigestFmt x then digestBlock x
  else padTo64 x

/-- One oracle call on `fmt x`. -/
def H (x : List Byte) : OracleComp HashSpec (BitVec 256) := HashSpec.query (fmt x)

/-- One paired seed derivation: the full 32-byte answer on `fmt x` as two 16-byte secrets
(low half, high half). -/
def prf2 (x : List Byte) : OracleComp HashSpec (Val × Val) := do
  let a ← H x
  pure ((answerBytes 32 a).take 16, (answerBytes 32 a).drop 16)

/-- One oracle call on `fmt x`, truncated to its first 16 bytes. -/
def hash16 (x : List Byte) : OracleComp HashSpec Val := do
  let a ← H x
  pure (answerBytes 16 a)

/-- `Th(P, tw, payload)`: the first 16 bytes of `H(fmt(tw || 0^16 || payload))`. -/
def th (tw payload : List Byte) : OracleComp HashSpec Val := hash16 (thInput tw payload)

/-! ## Hash input formats (exact byte lists before padding)

Hypertree formats take `(lay, tau, e)` = (layer, tree, leaf) first; PORS formats take the
instance `idx` first. -/

/-- WOTS secrets of chain pair `i` (chains `2i`, `2i+1`) of leaf `e`: `tw(0, lay, tau, i, e) || P || S`
(64 bytes; queried with `prf2`). -/
def prfInput (S : List Byte) (lay tau e i : Nat) : List Byte := thInput (tweak 0 lay tau i e) S

/-- Chain step `mu ∈ 1..7` of chain `i`: `tw(1, lay, tau, 8i + mu - 1, e) || P || v` (48 bytes). -/
def chainInput (lay tau e i mu : Nat) (v : Val) : List Byte :=
  thInput (tweak 1 lay tau (8 * i + mu - 1) e) v

/-- OTS leaf of leaf `e`: `tw(2, lay, tau, 0, e) || P || pk_0 .. pk_41` (704 bytes). -/
def leafInput (lay tau e : Nat) (ends : List Val) : List Byte :=
  thInput (tweak 2 lay tau 0 e) ends.flatten

/-- Tree node `j` of level `lam`: `tw(3, lay, tau, lam, j) || P || l || r` (64 bytes). -/
def nodeInput (lay tau lam j : Nat) (l r : Val) : List Byte :=
  thInput (tweak 3 lay tau lam j) (l ++ r)

/-- Encoding of `M` with counter `c`: `tw(4, lay, tau, 0, e) || P || M || LE32 c` (52 bytes). -/
def encInput (lay tau e : Nat) (M : Val) (c : Nat) : List Byte :=
  thInput (tweak 4 lay tau 0 e) (M ++ le32 c)

/-- Randomizer trial `a`: `tw(7, 0, 0, a, 0) || P || S || m` (96 bytes). -/
def rndInput (S m : List Byte) (a : Nat) : List Byte := thInput (tweak 7 0 0 a 0) (S ++ m)

/-- PORS secrets of leaf pair `q` (leaves `2q`, `2q+1`): `tw(8, 0, idx, 0, q) || P || S`
(64 bytes; queried with `prf2`). -/
def porsPrfInput (S : List Byte) (idx q : Nat) : List Byte := thInput (tweak 8 0 idx 0 q) S

/-- PORS leaf `j`: `tw(9, 0, idx, 0, j) || P || s` (48 bytes, zero padded, not relabeled). -/
def porsLeafInput (idx j : Nat) (s : Val) : List Byte := thInput (tweak 9 0 idx 0 j) s

/-- PORS node with heap index `H`: `enc(10, 0, idx, 0, H) || P || l || r` (64 bytes). This is the
real block of `ref.node_query` (for every `H`; `le32` keeps `H mod 2^32`), and of the signer's
node `(lam, j)` after `ref.f_query` for `H = 2^(14 - lam) + j`. -/
def porsNodeInput (idx H : Nat) (l r : Val) : List Byte := thInput (tweak 10 0 idx 0 H) (l ++ r)

/-- Message digest: `tw(12, 0, 0, 0, 0) || P || rho || 0^16 || m` (96 bytes). -/
def digestInput (rho m : List Byte) : List Byte := thInput (tweak 12 0 0 0 0) (rho ++ zeros 16 ++ m)

/-- Mask of top-tree node `(l, j)`: `tw(13, 0, 0, l, j) || P || S` (64 bytes). -/
def maskInput (S : List Byte) (l j : Nat) : List Byte := thInput (tweak 13 0 0 l j) S

/-- The cache MAC: `tw(14, 0, 0, 0, 0) || P || S || region` (65568 bytes); the full 32-byte
answer is the tag. -/
def macInput (S region : List Byte) : List Byte := thInput (tweak 14 0 0 0 0) (S ++ region)

/-! ## Digest, index split, digit decoding -/

/-- `N` = the full 256-bit answer of `H(digestInput rho m)` (little endian, `ref.message_digest`). -/
def digest (rho m : List Byte) : OracleComp HashSpec Nat := do
  let a ← H (digestInput rho m)
  pure a.toNat

/-- `idx = N mod 2^34`. -/
def idxOf (N : Nat) : Nat := N % 2 ^ totalH

/-- Leaf index `r` (digest slot `r < 15`): `v_r = floor(N / 2^(34 + 14 r)) mod 2^14`. -/
def leafOf (N r : Nat) : Nat := N / 2 ^ (totalH + porsH * r) % 2 ^ porsH

/-- The 15 leaf indices `v_0 .. v_14` of a digest, in digest-slot order (`ref.split_digest`). -/
def leavesOf (N : Nat) : List Nat := (List.range porsK).map (leafOf N)

/-- Python's `int.bit_length`: `0` for `0`, else `floor(log2 x) + 1`. -/
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-- `ref.octopus_size vs = 14 + sum_{s ≥ 1} bitlen(vs[s-1] xor vs[s]) - 2 (|vs| - 1)`, written as
`14 + 2 + sum - 2 |vs|` (equal whenever Python's value is `≥ 0`, which it always is on sorted
distinct lists; the Nat truncation to `0` does not change any comparison `≤ 120` either). -/
def octopusSize (vs : List Nat) : Nat :=
  porsH + 2 + (List.zipWith (fun a b => bitLen (a ^^^ b)) vs vs.tail).sum - 2 * vs.length

/-- `sorted(v)` (ascending). -/
def sortLeaves (v : List Nat) : List Nat := v.insertionSort (· ≤ ·)

/-- `ref.admissible`: the 15 leaf indices of `N` are pairwise distinct and their octopus (in
sorted order) has at most `porsM = 120` nodes. -/
def admissible (N : Nat) : Bool :=
  decide (leavesOf N).Nodup && decide (octopusSize (sortLeaves (leavesOf N)) ≤ porsM)

/-! ### The honest stack-machine schedule (`ref.schedule`) -/

/-- State of `ref.schedule`: segment bytes, read positions `(height, node index)`, and the stack
of pending sibling heap indices (head = top, i.e. Python's `stack[-1]`). -/
structure SchedState where
  segs : List Nat
  reads : List (Nat × Nat)
  stack : List Nat
deriving DecidableEq, Repr

/-- One height `h` of the inner `while h < top` loop of leaf processing; state
`(st, E, cnt, t)`. If the stack top equals `E`: emit the segment `cnt | 16 | 32 t`, pop, go up
(`t` = bit 0 of the new `E`); else record the witness sibling `(h, (E xor 1) - 2^14 / 2^h)`,
count it, go up. -/
def schedStep (x : SchedState × Nat × Nat × Nat) (h : Nat) : SchedState × Nat × Nat × Nat :=
  let (st, E, cnt, t) := x
  match st.stack with
  | Q :: rest =>
    if Q = E then ({ st with segs := st.segs ++ [cnt ||| 16 ||| 32 * t], stack := rest },
      E / 2, 0, E / 2 % 2)
    else ({ st with reads := st.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)] }, E / 2, cnt + 1, t)
  | [] => ({ st with reads := st.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)] }, E / 2, cnt + 1, t)

/-- Leaf `s` of the sorted leaves `vs` (`k = |vs|`): `E = 2^14 | vs[s]`, heights
`0 .. top - 1` with `top = bitlen(vs[s] xor vs[s+1]) - 1` (`s + 1 < k`) or `14`; then the leaf's
last segment `cnt | 32 t`; push `E xor 1` unless `s` is the last leaf. -/
def schedLeaf (vs : List Nat) (st : SchedState) (s : Nat) : SchedState :=
  let k := vs.length
  let E := porsT ||| vs.getD s 0
  let top := if s + 1 < k then bitLen (vs.getD s 0 ^^^ vs.getD (s + 1) 0) - 1 else porsH
  let (st, E, cnt, t) := (List.range top).foldl schedStep (st, E, 0, E % 2)
  let st := { st with segs := st.segs ++ [cnt ||| 32 * t] }
  if s + 1 < k then { st with stack := (E ^^^ 1) :: st.stack } else st

/-- `ref.schedule vs`: (segment bytes, read positions) of the sorted leaves `vs`. -/
def schedule (vs : List Nat) : List Nat × List (Nat × Nat) :=
  let st := (List.range vs.length).foldl (schedLeaf vs) ⟨[], [], []⟩
  (st.segs, st.reads)

/-- The 21 3-bit digits of a 64-bit word: `(d >> 3r) & 7`, `r = 0..20`. -/
def digitsOfWord (d : Nat) : List Nat := (List.range 21).map fun r => d / 8 ^ r % 8

/-- TargetSum decoding of an encoding output `v` (first 16 bytes): `d0`, `d1` = the two LE 64-bit
halves; reject if bit 63 of `d0` or of `d1` is set, else the 42 digits (21 of `d0`, then 21 of
`d1`) if they sum to `targetSum`. -/
def decodeDigits (v : Val) : Option (List Nat) :=
  let d0 := leNat (slice v 0 8)
  let d1 := leNat (slice v 8 8)
  if d0 < 2 ^ 63 ∧ d1 < 2 ^ 63 then
    let x := digitsOfWord d0 ++ digitsOfWord d1
    if x.sum = targetSum then some x else none
  else none

end SigGolfCandidate.Ref
