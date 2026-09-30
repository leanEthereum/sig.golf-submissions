import SigGolfCandidate.Ref.Basic

/-!
# SPHINCS-golf reference specification: keygen, sign, expand, verify

Mirrors `work/py/ref.py` query for query. Every loop is a `List.foldlM` over an index range
(`List.range n` = `0, 1, .., n-1`, `List.range' a n` = `a, .., a+n-1`) or, for the searches and
the layer loops (which may stop early), a structural recursion on a fuel / layer count.
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

/-- Chain `i` of leaf `e` of tree `(lay, tau)`: the secret `prf`, then steps `mu = 1 .. 7`.
Returns `(chain end, value at position x)` (position 0 = the secret). -/
def buildChain (S : List Byte) (lay tau e i x : Nat) : OracleComp HashSpec (Val × Val) := do
  let v ← hash16 (prfInput S lay tau e i)
  (List.range' 1 7).foldlM (fun (st : Val × Val) mu => do
    let v ← hash16 (chainInput lay tau e i mu st.1)
    pure (v, if mu = x then v else st.2)) (v, v)

/-- OTS leaf `e`: chains `i = 0 .. 41` (digits `x`), then the leaf hash.
Returns `(leaf, [value of chain i at position x_i])`. -/
def buildLeaf (S : List Byte) (lay tau e : Nat) (x : List Nat) :
    OracleComp HashSpec (Val × List Val) := do
  let st ← (List.range nChains).foldlM (fun (st : List Val × List Val) i => do
    let (v, c) ← buildChain S lay tau e i (x.getD i 0)
    pure (st.1 ++ [v], st.2 ++ [c])) ([], [])
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

/-- Public key = root of tree `(0, 0)` (height 5). (The capture arguments are irrelevant.) -/
def keygenList (S : List Byte) : OracleComp HashSpec Val := do
  let (root, _, _) ← buildTree S 0 0 (height 0) 0 []
  pure root

def keygenRef (sk : Bytes 32) : OracleComp HashSpec (Bytes 16) := do
  let root ← keygenList (toList sk)
  pure (ofList 16 root)

/-! ## sign -/

/-- Digest search from trial `a` with `fuel` trials left: `rho = Th(tw(7,0,0,a,0), S||m)`,
`N = digest rho m`; stop at the first admissible `N`. -/
def searchDigest (S m : List Byte) (a : Nat) : Nat → OracleComp HashSpec (Option (Val × Nat))
  | 0 => pure none
  | fuel + 1 => do
    let rho ← hash16 (rndInput S m a)
    let N ← digest rho m
    if admissible N then pure (some (rho, N)) else searchDigest S m (a + 1) fuel

/-- FORS leaves `j = 0 .. 2^a - 1` of tree `k`: secret, then leaf.
Returns `(leaves, secret u)`. -/
def buildFtsLeaves (S : List Byte) (k idx a u : Nat) : OracleComp HashSpec (List Val × Val) :=
  (List.range (2 ^ a)).foldlM (fun (st : List Val × Val) j => do
    let s ← hash16 (ftsPrfInput S k idx j)
    let leaf ← hash16 (ftsLeafInput k idx j s)
    pure (st.1 ++ [leaf], if j = u then s else st.2)) ([], [])

/-- FORS tree `k` of instance `idx` (height `a`), opened at leaf `u`.
Returns `(secret, path, root)`. -/
def buildFtsTree (S : List Byte) (k idx a u : Nat) :
    OracleComp HashSpec (Val × List Val × Val) := do
  let (leaves, s) ← buildFtsLeaves S k idx a u
  let (root, path) ← buildLevels (ftsNodeInput k idx) u a leaves
  pure (s, path, root)

/-- FORS trees `k = 0 .. 13` (height 10) opened at `u_k`.
Returns `(openings (s, path), roots)`. -/
def signFors (S : List Byte) (N : Nat) :
    OracleComp HashSpec (List (Val × List Val) × List Val) :=
  (List.range ftsTrees).foldlM (fun (st : List (Val × List Val) × List Val) k => do
    let (s, path, root) ← buildFtsTree S k (idxOf N) ftsA (uOf N k)
    pure (st.1 ++ [(s, path)], st.2 ++ [root])) ([], [])

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

/-- Layers `n-1, n-2, .., 0` (`M` = the message of layer `n-1`): counter search, then the tree
with capture; its root is the message of the layer below. Returns the layers in order
`0 .. n-1`. -/
def signLayers (S : List Byte) (idx : Nat) : Nat → Val → OracleComp HashSpec (Option (List LayerSig))
  | 0, _ => pure (some [])
  | lay + 1, M => do
    let (e, tau) := route idx lay
    match ← searchCounter lay tau e M 0 cMax with
    | none => pure none
    | some (c, x) =>
      let (root, vals, path) ← buildTree S lay tau (height lay) e x
      match ← signLayers S idx lay root with
      | none => pure none
      | some rest => pure (some (rest ++ [(c, vals, path)]))

/-- Signature bytes: `rho | (s_k, path_k)_{k=0..13} | (LE32 c, vals, path)_{lay=0..6}`. -/
def serialize (rho : Val) (fors : List (Val × List Val)) (lays : List LayerSig) : List Byte :=
  rho ++ (fors.map fun o => o.1 ++ o.2.flatten).flatten ++
    (lays.map fun l => le32 l.1 ++ l.2.1.flatten ++ l.2.2.flatten).flatten

def signList (S m : List Byte) : OracleComp HashSpec (Option (List Byte)) := do
  match ← searchDigest S m 0 aMax with
  | none => pure none
  | some (rho, N) =>
    let (fors, roots) ← signFors S N
    let M ← hash16 (rootsInput (idxOf N) roots)
    match ← signLayers S (idxOf N) nLayers M with
    | none => pure none
    | some lays => pure (some (serialize rho fors lays))

def signRef (sk : Bytes 32) (m : Bytes 32) : OracleComp HashSpec (Option (Bytes 7756)) := do
  let r ← signList (toList sk) (toList m)
  pure (r.map (ofList 7756))

/-! ## expand (the byte permutation `ref.to_witness`) -/

/-- Offset of layer `lay` in the signature: `2480 + 756 lay`. -/
def sigLayerOff (lay : Nat) : Nat := 2480 + 756 * lay
/-- Offset of layer `lay`'s body (chain values, path) in the witness: `2480 + 752 lay`. -/
def witLayerOff (lay : Nat) : Nat := 2480 + 752 * lay
/-- Offset of the counters in the witness. -/
def witCounters : Nat := 7728

/-- Signature position of witness byte `i`: head (rho, FORS) in place; layer bodies without
their counters; the seven counters at the end. -/
def witnessSrc (i : Nat) : Nat :=
  if i < 2480 then i
  else if i < witCounters then
    sigLayerOff ((i - 2480) / 752) + 4 + (i - witLayerOff ((i - 2480) / 752))
  else
    sigLayerOff ((i - witCounters) / 4) + (i - witCounters) % 4

/-- Witness position of signature byte `i` (inverse of `witnessSrc`): with
`lay = (i - 2480) / 756`, `r = (i - 2480) % 756`, the counter byte `r < 4` goes to
`7728 + 4 lay + r`, the body byte to `witLayerOff lay + r - 4`. -/
def signatureSrc (i : Nat) : Nat :=
  if i < 2480 then i
  else if (i - 2480) % 756 < 4 then witCounters + 4 * ((i - 2480) / 756) + (i - 2480) % 756
  else witLayerOff ((i - 2480) / 756) + ((i - 2480) % 756 - 4)

/-- `ref.to_witness` on byte lists. -/
def toWitness (sig : List Byte) : List Byte :=
  (List.range sigBytes).map fun i => sig.getD (witnessSrc i) 0

/-- `ref.from_witness` on byte lists. -/
def fromWitness (w : List Byte) : List Byte :=
  (List.range sigBytes).map fun i => w.getD (signatureSrc i) 0

def expandRef (sig : Bytes 7756) : Bytes 7756 := ofList 7756 (toWitness (toList sig))

def unexpandRef (w : Bytes 7756) : Bytes 7756 := ofList 7756 (fromWitness (toList w))

/-! ## verify (on the witness, in the bytecode's order) -/

/-- Witness fields (PROGRAMS.md, witness `perm`). -/
def witRho (w : List Byte) : Val := slice w 0 16
def witFtsSecret (w : List Byte) (k : Nat) : Val := slice w (16 + 176 * k) 16
def witFtsSib (w : List Byte) (k l : Nat) : Val := slice w (32 + 176 * k + 16 * l) 16
def witFtsPath (w : List Byte) (k : Nat) : List Val := (List.range ftsA).map (witFtsSib w k)
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

/-- FORS root of tree `k` from the opening `(s, path)` at leaf `u`: leaf hash, then `a` folds. -/
def ftsRoot (k idx u : Nat) (s : Val) (path : List Val) : OracleComp HashSpec Val := do
  let v ← hash16 (ftsLeafInput k idx u s)
  foldPath (ftsNodeInput k idx) u v path

/-- The FORS roots `k = 0 .. 13`. -/
def verifyFors (w : List Byte) (N : Nat) : OracleComp HashSpec (List Val) :=
  (List.range ftsTrees).foldlM (fun roots k => do
    let r ← ftsRoot k (idxOf N) (uOf N k) (witFtsSecret w k) (witFtsPath w k)
    pure (roots ++ [r])) []

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

/-- Verification of a witness (byte list). -/
def verifyList (m pk w : List Byte) : OracleComp HashSpec Bool := do
  if !countersOk w then return false
  let N ← digest (witRho w) m
  if !admissible N then return false
  let roots ← verifyFors w N
  let M ← hash16 (rootsInput (idxOf N) roots)
  match ← verifyLayers w (idxOf N) nLayers M with
  | none => pure false
  | some root => pure (root == pk)

def verifyRef (m : Bytes 32) (pk : Bytes 16) (w : Bytes 7756) : OracleComp HashSpec Bool :=
  verifyList (toList m) (toList pk) (toList w)

/-- Verification of a signature: verify its witness. -/
def verifySigRef (m : Bytes 32) (pk : Bytes 16) (sig : Bytes 7756) : OracleComp HashSpec Bool :=
  verifyRef m pk (expandRef sig)

end SigGolfCandidate.Ref
