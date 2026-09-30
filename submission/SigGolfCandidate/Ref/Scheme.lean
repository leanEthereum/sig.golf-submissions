import SigGolfCandidate.Ref.Basic

/-!
# SPHINCS-golf reference specification: keygen, sign, expand, verify

Mirrors `work/py-pors/ref.py` (PORS+FP, SPEC-pors.md) query for query. Every loop is a
`List.foldlM` over an index range (`List.range n` = `0, 1, .., n-1`, `List.range' a n` =
`a, .., a+n-1`) or, for the loops that may stop early (searches, layers, the PORS stack machine),
a structural recursion on a fuel / layer count / list.
Accumulated lists grow at the end (`acc ++ [v]`), so after processing `j` indices the
accumulator holds exactly the first `j` results.

Pure bookkeeping (captures of signature parts, path siblings) is interleaved exactly where the
bytecode does it, but it never affects the queries.
-/

namespace SigGolfCandidate.Ref
open SigGolf OracleComp OracleSpec

/-- A tree node format: `node lam j l r` is the input of node `j` of level `lam`. -/
abbrev NodeFmt := Nat → Nat → Val → Val → List Byte

/-! ## Tree building (sign, keygen) -/

/-- One level of a tree: nodes `j = 0 .. |level|/2 - 1` from left to right,
`hash16 (node lam j level[2j] level[2j+1])`. -/
def buildLevel (node : NodeFmt) (lam : Nat) (level : List Val) :
    OracleComp HashSpec (List Val) :=
  (List.range (level.length / 2)).foldlM (fun acc j => do
    let v ← hash16 (node lam j (level.getD (2 * j) []) (level.getD (2 * j + 1) []))
    pure (acc ++ [v])) []

/-- One step of `buildLevels` (level `lam`): record the authentication-path sibling
`level[(cap >> (lam-1)) xor 1]` of leaf `cap`, then build level `lam`. State `(level, path)`. -/
def levelStep (node : NodeFmt) (cap : Nat) (st : List Val × List Val) (lam : Nat) :
    OracleComp HashSpec (List Val × List Val) := do
  let path := st.2 ++ [st.1.getD ((cap / 2 ^ (lam - 1)) ^^^ 1) []]
  let level ← buildLevel node lam st.1
  pure (level, path)

/-- Levels `lam = 1 .. h` bottom-up from `leaves`. Returns `(root, path of leaf cap)`. -/
def buildLevels (node : NodeFmt) (cap h : Nat) (leaves : List Val) :
    OracleComp HashSpec (Val × List Val) := do
  let st ← (List.range' 1 h).foldlM (levelStep node cap) (leaves, [])
  pure (st.1.getD 0 [], st.2)

/-- Chain `i` of leaf `e` of tree `(lay, tau)` from its secret `v`: steps `mu = 1 .. 7`.
Returns `(chain end, value at position x)` (position 0 = the secret). -/
def chainSteps (lay tau e i x : Nat) (v : Val) : OracleComp HashSpec (Val × Val) :=
  (List.range' 1 7).foldlM (fun (st : Val × Val) mu => do
    let v ← hash16 (chainInput lay tau e i mu st.1)
    pure (v, if mu = x then v else st.2)) (v, v)

/-- OTS leaf `e`: for chain pairs `k = 0 .. 20`, the paired secret query, then chain `2k`'s steps,
then chain `2k+1`'s (digits `x`); then the leaf hash.
Returns `(leaf, [value of chain i at position x_i])`. -/
def buildLeaf (S : List Byte) (lay tau e : Nat) (x : List Nat) :
    OracleComp HashSpec (Val × List Val) := do
  let st ← (List.range (nChains / 2)).foldlM (fun (st : List Val × List Val) k => do
    let (s0, s1) ← prf2 (prfInput S lay tau e k)
    let (v0, c0) ← chainSteps lay tau e (2 * k) (x.getD (2 * k) 0) s0
    let (v1, c1) ← chainSteps lay tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
    pure (st.1 ++ [v0, v1], st.2 ++ [c0, c1])) ([], [])
  let leaf ← hash16 (leafInput lay tau e st.1)
  pure (leaf, st.2)

/-- Leaves `e = 0 .. 2^h - 1` in order. Returns `(leaves, chain values of leaf cap)`. -/
def buildLeaves (S : List Byte) (lay tau h cap : Nat) (x : List Nat) :
    OracleComp HashSpec (List Val × List Val) :=
  (List.range (2 ^ h)).foldlM (fun (st : List Val × List Val) e => do
    let (leaf, c) ← buildLeaf S lay tau e x
    pure (st.1 ++ [leaf], if e = cap then c else st.2)) ([], [])

/-- Tree `(lay, tau)` of height `h`, built once (`ref.build_tree`): leaves, then levels.
Returns `(root, chain values x of leaf cap, path of leaf cap)`. -/
def buildTree (S : List Byte) (lay tau h cap : Nat) (x : List Nat) :
    OracleComp HashSpec (Val × List Val × List Val) := do
  let (leaves, vals) ← buildLeaves S lay tau h cap x
  let (root, path) ← buildLevels (nodeInput lay tau) cap h leaves
  pure (root, vals, path)

/-! ## keygen -/

/-- All levels `0 .. h` of a tree over `leaves` (level 0 = the leaves), built bottom-up, each level
left to right: the queries of `buildLevels`, keeping every level. -/
def buildAllLevels (node : NodeFmt) (h : Nat) (leaves : List Val) :
    OracleComp HashSpec (List (List Val)) :=
  (List.range' 1 h).foldlM (fun (levels : List (List Val)) lam => do
    let level ← buildLevel node lam (levels.getD (lam - 1) [])
    pure (levels ++ [level])) [leaves]

/-- Level `l` of the top tree masked node by node: `mask(l, j)` for `j` in order, then
`X_{l,j} xor mask(l, j)`. -/
def maskLevel (S : List Byte) (l : Nat) (level : List Val) : OracleComp HashSpec (List Val) :=
  (List.range level.length).foldlM (fun acc j => do
    let mk ← hash16 (maskInput S l j)
    pure (acc ++ [xorBytes (level.getD j []) mk])) []

/-- `ref.keygen`: build the top tree (layer 0, tau 0, height `topH`, as `buildTree`), mask its
levels `0 .. topH - 1` into the region, MAC the region. Returns `(pk = root, cache bytes)`. -/
def keygenList (S : List Byte) : OracleComp HashSpec (Val × List Byte) := do
  let (leaves, _) ← buildLeaves S 0 0 topH 0 []
  let levels ← buildAllLevels (nodeInput 0 0) topH leaves
  let masked ← (List.range topH).foldlM (fun (acc : List Val) l => do
    let ml ← maskLevel S l (levels.getD l [])
    pure (acc ++ ml)) []
  let region := masked.flatten
  let tag ← H (macInput S region)
  pure ((levels.getD topH []).getD 0 [],
    toList (n := 32) tag ++ region ++ zeros (cacheBytes - 32 - regionBytes))

def keygenRef (sk : Bytes 32) : OracleComp HashSpec (Bytes 16 × Cache) := do
  let (root, cache) ← keygenList (toList sk)
  pure (ofList 16 root, ofList CACHE_BYTES cache)

/-! ## sign -/

/-- Digest search from trial `a` with `fuel` trials left: `rho = Th(tw(7,0,0,a,0), S||m)`,
`N = digest rho m`; stop at the first admissible `N`. -/
def searchDigest (S m : List Byte) (a : Nat) : Nat → OracleComp HashSpec (Option (Val × Nat))
  | 0 => pure none
  | fuel + 1 => do
    let rho ← hash16 (rndInput S m a)
    let N ← digest rho m
    if admissible N then pure (some (rho, N)) else searchDigest S m (a + 1) fuel

/-- PORS leaves of instance `idx` (`ref.sign` step 2): for pairs `q = 0 .. 2^13 - 1`, the paired
secret query `prf2 (tw(8, 0, idx, 0, q) || P || S)`, then leaf `2q`, then leaf `2q+1` (tag 9).
Returns `(leaves, secrets)` (both of length `2^14`, index = leaf index). -/
def buildPorsLeaves (S : List Byte) (idx : Nat) : OracleComp HashSpec (List Val × List Val) :=
  (List.range (porsT / 2)).foldlM (fun (st : List Val × List Val) q => do
    let (s0, s1) ← prf2 (porsPrfInput S idx q)
    let l0 ← hash16 (porsLeafInput idx (2 * q) s0)
    let l1 ← hash16 (porsLeafInput idx (2 * q + 1) s1)
    pure (st.1 ++ [l0, l1], st.2 ++ [s0, s1])) ([], [])

/-- The PORS node format for `buildLevel`: node `j` of level `lam` is queried as
`porsNodeInput idx (2^(14 - lam) + j)` (= `ref.f_query` of `tw(10, 0, idx, lam, j) || P || L || R`). -/
def porsNodeFmt (idx : Nat) : NodeFmt := fun lam j l r => porsNodeInput idx (heapIndex porsH lam j) l r

/-- The PORS tree of instance `idx`: leaves (`buildPorsLeaves`), then levels `lam = 1 .. 14`
bottom-up, each left to right. Returns `(levels 0 .. 14, secrets)`. -/
def buildPorsTree (S : List Byte) (idx : Nat) :
    OracleComp HashSpec (List (List Val) × List Val) := do
  let (leaves, secrets) ← buildPorsLeaves S idx
  let levels ← buildAllLevels (porsNodeFmt idx) porsH leaves
  pure (levels, secrets)

/-- The FTS part of the signature (135 items of 16 bytes): the secrets of the sorted leaves
`vs`, the authentication nodes `levels[h][j]` in schedule read order, zero items up to
`porsK + porsM`. -/
def porsOpening (vs : List Nat) (levels : List (List Val)) (secrets : List Val) : List Val :=
  let fts := vs.map (fun x => secrets.getD x []) ++
    (schedule vs).2.map (fun hj => (levels.getD hj.1 []).getD hj.2 [])
  fts ++ List.replicate (porsK + porsM - fts.length) (zeros 16)

/-- Counter search for layer `lay` from counter `c` with `fuel` trials left: the first `c` whose
encoding `Th(tw(4,lay,tau,0,e), M || LE32 c)` decodes. Returns `(c, digits)`. -/
def searchCounter (lay tau e : Nat) (M : Val) (c : Nat) :
    Nat → OracleComp HashSpec (Option (Nat × List Nat))
  | 0 => pure none
  | fuel + 1 => do
    let d ← hash16 (encInput lay tau e M c)
    match decodeDigits d with
    | some x => pure (some (c, x))
    | none => searchCounter lay tau e M (c + 1) fuel

/-- A signed layer: counter, 42 chain values, authentication path. -/
abbrev LayerSig := Nat × List Val × List Val

/-- Chain `i` of leaf `e` up to position `x` only, from its secret `v`: steps `1 .. x`. -/
def chainTo (lay tau e i x : Nat) (v : Val) : OracleComp HashSpec Val :=
  (List.range' 1 x).foldlM (fun v mu => hash16 (chainInput lay tau e i mu v)) v

/-- The top-tree path of leaf `e` from the cache: for `l = 0 .. topH - 1`, sibling
`s = (e >> l) xor 1`, query `mask(l, s)`, path node = cache node `(l, s)` xor mask. -/
def topPath (S cache : List Byte) (e : Nat) : OracleComp HashSpec (List Val) :=
  (List.range topH).foldlM (fun acc l => do
    let s := (e / 2 ^ l) ^^^ 1
    let mk ← hash16 (maskInput S l s)
    pure (acc ++ [xorBytes (cacheNode cache l s) mk])) []

/-- Layer 0 (the cached top tree): counter search on `M`, the WOTS signature of leaf `e_0`
(for each chain pair, the paired secret query, then chains `2k` and `2k+1` up to their digits), the path from the cache. The top tree is not built. -/
def signTop (S cache : List Byte) (idx : Nat) (M : Val) :
    OracleComp HashSpec (Option (List LayerSig)) := do
  let (e, tau) := route idx 0
  match ← searchCounter 0 tau e M 0 cMax with
  | none => pure none
  | some (c, x) =>
    let vals ← (List.range (nChains / 2)).foldlM (fun acc k => do
      let (s0, s1) ← prf2 (prfInput S 0 tau e k)
      let v0 ← chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) s0
      let v1 ← chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
      pure (acc ++ [v0, v1])) []
    let path ← topPath S cache e
    pure (some [(c, vals, path)])

/-- Layers `lay, lay-1, .., 1` (`M` = the message of layer `lay`): counter search, then the tree
with capture; its root is the message of the layer below; then the top layer (`signTop`).
Called with `lay = nLayers - 1`. Returns the layers in order `0 .. lay`. -/
def signLayers (S cache : List Byte) (idx : Nat) :
    Nat → Val → OracleComp HashSpec (Option (List LayerSig))
  | 0, M => signTop S cache idx M
  | lay + 1, M => do
    let (e, tau) := route idx (lay + 1)
    match ← searchCounter (lay + 1) tau e M 0 cMax with
    | none => pure none
    | some (c, x) =>
      let (root, vals, path) ← buildTree S (lay + 1) tau (height (lay + 1)) e x
      match ← signLayers S cache idx lay root with
      | none => pure none
      | some rest => pure (some (rest ++ [(c, vals, path)]))

/-- Signature bytes: `rho | FTS items (135 × 16) | (LE32 c, vals, path)_{lay=0..4}`. -/
def serialize (rho : Val) (fts : List Val) (lays : List LayerSig) : List Byte :=
  rho ++ fts.flatten ++
    (lays.map fun l => le32 l.1 ++ l.2.1.flatten ++ l.2.2.flatten).flatten

/-- `ref.sign`: the MAC check of the cache (one query; `none` on a mismatch), the digest search,
the PORS tree of `idx` (its root is the message of the bottom layer), the layers `4 .. 0`. -/
def signList (S cache m : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  let tag ← H (macInput S (cacheRegion cache))
  if toList (n := 32) tag = cacheTag cache then
    match ← searchDigest S m 0 aMax with
    | none => pure none
    | some (rho, N) =>
      let (levels, secrets) ← buildPorsTree S (idxOf N)
      let M := (levels.getD porsH []).getD 0 []
      let fts := porsOpening (sortLeaves (leavesOf N)) levels secrets
      match ← signLayers S cache (idxOf N) (nLayers - 1) M with
      | none => pure none
      | some lays => pure (some (serialize rho fts lays))
  else pure none

def signRef (sk : Bytes 32) (cache : Cache) (m : Bytes 32) :
    OracleComp HashSpec (Option (Bytes 6100)) := do
  let r ← signList (toList sk) (toList cache) (toList m)
  pure (r.map (ofList 6100))

/-! ## Signature and witness layout -/

/-- Bytes of layer `lay` in the signature: `LE32 c`, 42 chain values, `h_lay` siblings. -/
def sigLayerBytes (lay : Nat) : Nat := 4 + 16 * nChains + 16 * height lay
/-- Bytes before the layers (`ref.LAYER0`): `rho` and the 135 FTS items (2176). -/
def headBytes : Nat := 16 + 16 * (porsK + porsM)
/-- Offset of layer `lay` in the signature (`ref.sig_layer_offset`). -/
def sigLayerOff (lay : Nat) : Nat := headBytes + ((List.range lay).map sigLayerBytes).sum

/-- Signature fields (`ref.parse`): `rho`, FTS item `i < 135` (secrets `i < 15`, then auth slots). -/
def sigRho (sig : List Byte) : Val := slice sig 0 16
def sigItem (sig : List Byte) (i : Nat) : Val := slice sig (16 + 16 * i) 16
def sigAuth (sig : List Byte) (i : Nat) : Val := sigItem sig (porsK + i)
/-- The counter bytes and the body (chain values, path) of layer `lay` in the signature. -/
def sigCounterBytes (sig : List Byte) (lay : Nat) : List Byte := slice sig (sigLayerOff lay) 4
def sigLayerBody (sig : List Byte) (lay : Nat) : List Byte :=
  slice sig (sigLayerOff lay + 4) (sigLayerBytes lay - 4)

/-- Witness offsets: `pi` (`W_PI`), sorted secrets (`W_SEC`), segment stream (`W_STREAM`), its
size (`STREAM_BYTES = 8 * 29 + 16 * 120`), layer bodies (`W_LAYERS`). -/
def wPi : Nat := 16
def wSec : Nat := 32
def wStream : Nat := wSec + 16 * porsK
def streamBytes : Nat := 8 * porsSegs + 16 * porsM
def wLayers : Nat := wStream + streamBytes
/-- Offset of layer `lay`'s body (chain values, path) in the witness (`ref.wit_layer_offset`). -/
def witLayerOff (lay : Nat) : Nat := wLayers + ((List.range lay).map fun l => sigLayerBytes l - 4).sum
/-- Offset of the counters in the witness (`ref.WIT_COUNTERS = 6328`). -/
def witCounters : Nat := witLayerOff nLayers

/-! ## expand (`ref.expand`: one digest query, may fail) -/

/-- The segment stream of `ref.expand`: for each segment byte `b` (with `a = b mod 16`), the
8-byte header `b, 0^7`, then the next `a` auth items of the signature (read order). State
`(bytes, r)` with `r` the number of auth items used so far. -/
def streamStep (sig : List Byte) (st : List Byte × Nat) (b : Nat) : List Byte × Nat :=
  (st.1 ++ [byte b] ++ zeros 7 ++ ((List.range (b % 16)).map fun i => sigAuth sig (st.2 + i)).flatten,
    st.2 + b % 16)

def segStream (sig : List Byte) (segs : List Nat) : List Byte := (segs.foldl (streamStep sig) ([], 0)).1

/-- The witness bytes built by `ref.expand` (after its checks), from the signature, the leaf
indices `v` (digest-slot order), their sorted list `vs`, and the segment bytes `segs`:
`rho | pi (byte s = 8 * slot of vs[s] in v) | 0 | secrets | stream, zero padded to STREAM_BYTES |
layer bodies 0..4 | counters 0..4`. (On every input `ref.expand` accepts the stream has at most
`STREAM_BYTES` bytes; the `take` only fixes the length otherwise, where `ref.expand` would fail
its assertion.) -/
def witnessList (sig : List Byte) (v vs segs : List Nat) : List Byte :=
  sigRho sig ++ vs.map (fun x => byte (8 * v.idxOf x)) ++ zeros (wSec - wPi - porsK) ++
    ((List.range porsK).map (sigItem sig)).flatten ++
    (segStream sig segs ++ zeros streamBytes).take streamBytes ++
    ((List.range nLayers).map (sigLayerBody sig)).flatten ++
    ((List.range nLayers).map (sigCounterBytes sig)).flatten

/-- The part of `ref.expand` after the digest query (no queries): `none` unless the 15 leaf
indices of `N` are distinct, their octopus has `≤ 120` nodes and the unused auth slots
`n .. 119` (`n` = the octopus size = the number of reads) are zero; else the witness. -/
def expandOf (sig : List Byte) (N : Nat) : Option (List Byte) :=
  let v := leavesOf N
  if !decide v.Nodup then none
  else
    let vs := sortLeaves v
    if octopusSize vs > porsM then none
    else
      let (segs, reads) := schedule vs
      let n := reads.length
      if !(List.range' n (porsM - n)).all (fun i => sigAuth sig i == zeros 16) then none
      else some (witnessList sig v vs segs)

/-- `ref.expand` on byte lists: the digest of `rho` and `m` (the only query), then `expandOf`. -/
def expandList (m sig : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  let N ← digest (sigRho sig) m
  pure (expandOf sig N)

/-- `ref.expand(pk, m, sig)` (the public key is unused). -/
def expandRef (m : Bytes 32) (_pk : Bytes 16) (sig : Bytes 6100) :
    OracleComp HashSpec (Option (Bytes 6348)) := do
  let r ← expandList (toList m) (toList sig)
  pure (r.map (ofList 6348))

/-! ## verify (on the witness, in the bytecode's order) -/

/-- Witness fields. `wbyte` / `wbytes` read zero beyond the witness (`ref.wbyte`). -/
def witRho (w : List Byte) : Val := slice w 0 16
def witPi (w : List Byte) (s : Nat) : Nat := (w.getD (wPi + s) 0).toNat
def witSecret (w : List Byte) (s : Nat) : Val := slice w (wSec + 16 * s) 16
def wbyte (w : List Byte) (off : Nat) : Nat := (w.getD off 0).toNat
def wbytes (w : List Byte) (off n : Nat) : Val := (List.range n).map fun i => w.getD (off + i) 0
def witChain (w : List Byte) (lay i : Nat) : Val := slice w (witLayerOff lay + 16 * i) 16
def witSib (w : List Byte) (lay l : Nat) : Val := slice w (witLayerOff lay + 672 + 16 * l) 16
def witPath (w : List Byte) (lay : Nat) : List Val := (List.range (height lay)).map (witSib w lay)
def witCounter (w : List Byte) (lay : Nat) : Nat := leNat (slice w (witCounters + 4 * lay) 4)

/-- The counter range check: every `c_lay < 2^20`. -/
def countersOk (w : List Byte) : Bool := (List.range nLayers).all fun lay => witCounter w lay < cMax

/-- `ref.fold` (TreeFold / FtsFold): levels `lam = 0 .. |path|-1` with node
`(lam + 1, leaf >> (lam + 1))`; the current value goes left iff bit `lam` of `leaf` is 0. -/
def foldPath (node : NodeFmt) (leaf : Nat) (v : Val) (path : List Val) : OracleComp HashSpec Val :=
  (List.range path.length).foldlM (fun v lam =>
    let sib := path.getD lam []
    let j := leaf / 2 ^ (lam + 1)
    if leaf / 2 ^ lam % 2 = 1 then hash16 (node (lam + 1) j sib v)
    else hash16 (node (lam + 1) j v sib)) v

/-! ### The PORS stack machine (`ref.pors_root`) -/

/-- The pending hash of a segment: the leaf hash of leaf `x` with secret `s` (a leaf's first
segment), or the merge hash `node(H, l | current node)`. -/
inductive Pending where
  | leaf (x : Nat) (s : Val)
  | merge (H : Nat) (l : Val)

/-- Perform the pending hash (`node` = the current node). -/
def pendingHash (idx : Nat) (node : Val) : Pending → OracleComp HashSpec Val
  | .leaf x s => hash16 (porsLeafInput idx x s)
  | .merge H l => hash16 (porsNodeInput idx H l node)

/-- The `a` folds of a segment whose header is at `ptr`: fold `i` reads the sibling
`wbytes w (ptr + 8 + 16 i) 16`, puts the current node on the right iff bit 0 of `E` is 1, hashes
with heap index `E / 2`, and goes up. State `(node, E)`. -/
def segFolds (idx : Nat) (w : List Byte) (ptr a : Nat) (node : Val) (E : Nat) :
    OracleComp HashSpec (Val × Nat) :=
  (List.range a).foldlM (fun (st : Val × Nat) i =>
    let sib := wbytes w (ptr + 8 + 16 * i) 16
    if st.2 % 2 = 1 then do
      let v ← hash16 (porsNodeInput idx (st.2 / 2) sib st.1)
      pure (v, st.2 / 2)
    else do
      let v ← hash16 (porsNodeInput idx (st.2 / 2) st.1 sib)
      pure (v, st.2 / 2)) (node, E)

/-- One segment of the stack machine (header at `ptr`): read the header byte `b = wbyte w ptr`
(`a = b mod 16`, `merge` = bit 4, `t` = bit 5, bits 6..7 ignored); reject (`none`, no query) if
`a > 14`, or if `a > 0` and `t` differs from bit 0 of `E` (the heap index at the segment's start);
the pending hash; the `a` folds (`segFolds`). Returns `(ptr + 8 + 16 a, E, folds + a, node, merge = 1)`. -/
def segment (idx : Nat) (w : List Byte) (ptr E folds : Nat) (pending : Pending) (node : Val) :
    OracleComp HashSpec (Option (Nat × Nat × Nat × Val × Bool)) := do
  let b := wbyte w ptr
  let a := b % 16
  let merge := b / 16 % 2
  let t := b / 32 % 2
  if a > porsH then pure none
  else if 0 < a ∧ t ≠ E % 2 then pure none
  else
    let node ← pendingHash idx node pending
    let (node, E) ← segFolds idx w ptr a node E
    pure (some (ptr + 8 + 16 * a, E, folds + a, node, merge = 1))

/-- The segments of one leaf (the inner `while True` of `ref.pors_root`), by structural recursion
on the stack (head = top): a `segment`; without merge the leaf is done, returning
`(ptr, E, folds, node, stack)`; with merge: reject on an empty stack or if the popped `Q ≠ E`,
else the next segment's pending hash is the merge `node(E / 2, popped node | node)` and
`E := E / 2`. (The stack is matched before the segment only to make the recursion structural;
the segment's queries come first in both branches, as in `ref.pors_root`.) -/
def segLoop (idx : Nat) (w : List Byte) :
    Nat → Nat → Nat → Pending → Val → List (Val × Nat) →
      OracleComp HashSpec (Option (Nat × Nat × Nat × Val × List (Val × Nat)))
  | ptr, E, folds, pending, node, [] => do
    match ← segment idx w ptr E folds pending node with
    | none => pure none
    | some (ptr, E, folds, node, merge) =>
      if merge then pure none else pure (some (ptr, E, folds, node, []))
  | ptr, E, folds, pending, node, (pnode, Q) :: rest => do
    match ← segment idx w ptr E folds pending node with
    | none => pure none
    | some (ptr, E, folds, node, merge) =>
      if !merge then pure (some (ptr, E, folds, node, (pnode, Q) :: rest))
      else if Q ≠ E then pure none
      else segLoop idx w ptr (E / 2) folds (.merge (E / 2) pnode) node rest

/-- State of the leaf loop of `ref.pors_root`. -/
structure PorsState where
  ptr : Nat
  prev : Nat
  E : Nat
  folds : Nat
  node : Val
  stack : List (Val × Nat)

/-- The leaf loop of `ref.pors_root` over the slots `s` of the list (called with
`List.range 15`): `x = IND[(pi_s & 0x78) >> 3]` with `IND = v ++ [2^14]`; reject unless
`prev < x` (`s ≥ 1`) and, for the last leaf, `x < 2^14`; `E = 2^14 | x`; the leaf's segments
(pending = the leaf hash of `x` with secret `s`); push `(node, E xor 1)` unless `s` is the last
leaf. -/
def porsLeaves (idx : Nat) (v : List Nat) (w : List Byte) :
    List Nat → PorsState → OracleComp HashSpec (Option PorsState)
  | [], st => pure (some st)
  | s :: rest, st => do
    let x := (v ++ [porsT]).getD (witPi w s / 8 % 16) 0
    if s ≠ 0 ∧ ¬ st.prev < x then pure none
    else if s = porsK - 1 ∧ ¬ x < porsT then pure none
    else
      match ← segLoop idx w st.ptr (porsT ||| x) st.folds (.leaf x (witSecret w s)) st.node
          st.stack with
      | none => pure none
      | some (ptr, E, folds, node, stack) =>
        let stack := if s < porsK - 1 then (node, E ^^^ 1) :: stack else stack
        porsLeaves idx v w rest ⟨ptr, x, E, folds, node, stack⟩

/-- `ref.pors_root`: the stack machine over the 15 leaves from `ptr = W_STREAM`; then reject
unless `folds ≤ 120`, `E = 1` and the stack is empty. Returns the PORS root. -/
def porsRoot (idx : Nat) (v : List Nat) (w : List Byte) : OracleComp HashSpec (Option Val) := do
  match ← porsLeaves idx v w (List.range porsK) ⟨wStream, 0, 0, 0, [], []⟩ with
  | none => pure none
  | some st =>
    if st.folds > porsM ∨ st.E ≠ 1 ∨ st.stack ≠ [] then pure none else pure (some st.node)

/-- Chain `i` of leaf `e` from the value `v` at position `x`: steps `mu = x+1 .. 7`. -/
def chainFrom (lay tau e i x : Nat) (v : Val) : OracleComp HashSpec Val :=
  (List.range' (x + 1) (7 - x)).foldlM (fun v mu => hash16 (chainInput lay tau e i mu v)) v

/-- OTS leaf from the chain values of layer `lay` and the digits `x`: chains `i = 0 .. 41`,
then the leaf hash. -/
def verifyLeaf (w : List Byte) (lay tau e : Nat) (x : List Nat) : OracleComp HashSpec Val := do
  let ends ← (List.range nChains).foldlM (fun ends i => do
    let v ← chainFrom lay tau e i (x.getD i 0) (witChain w lay i)
    pure (ends ++ [v])) []
  hash16 (leafInput lay tau e ends)

/-- Layers `n-1, .., 0` from the message `M` of layer `n-1`: encoding (reject = `none`),
chains, leaf, folds. Returns the top root. -/
def verifyLayers (w : List Byte) (idx : Nat) : Nat → Val → OracleComp HashSpec (Option Val)
  | 0, M => pure (some M)
  | lay + 1, M => do
    let (e, tau) := route idx lay
    let d ← hash16 (encInput lay tau e M (witCounter w lay))
    match decodeDigits d with
    | none => pure none
    | some x =>
      let leaf ← verifyLeaf w lay tau e x
      let root ← foldPath (nodeInput lay tau) e leaf (witPath w lay)
      verifyLayers w idx lay root

/-- Verification of a witness (byte list; `ref.verify_witness` without its length check,
which `verifyRef` makes vacuous): the counter range check (no queries), the digest, the PORS
root (the message of the bottom layer), the layers `4 .. 0`, the comparison with `pk`. -/
def verifyList (m pk w : List Byte) : OracleComp HashSpec Bool := do
  if !countersOk w then return false
  let N ← digest (witRho w) m
  match ← porsRoot (idxOf N) (leavesOf N) w with
  | none => pure false
  | some M =>
    match ← verifyLayers w (idxOf N) nLayers M with
    | none => pure false
    | some root => pure (root == pk)

def verifyRef (m : Bytes 32) (pk : Bytes 16) (w : Bytes 6348) : OracleComp HashSpec Bool :=
  verifyList (toList m) (toList pk) (toList w)

/-- `ref.verify`: expand, then verify the witness (`false` if expand fails). -/
def verifySigRef (m : Bytes 32) (pk : Bytes 16) (sig : Bytes 6100) : OracleComp HashSpec Bool := do
  match ← expandRef m pk sig with
  | none => pure false
  | some w => verifyRef m pk w

end SigGolfCandidate.Ref
