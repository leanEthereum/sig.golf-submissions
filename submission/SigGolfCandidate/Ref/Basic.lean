import SigGolf

/-!
# SPHINCS-golf reference specification: primitives

Byte-level primitives of the reference specification (`work/py/ref.py`, `work/design/SPEC.md`,
`work/py/PROGRAMS.md`):

* byte encodings (little endian) and conversions between `List Byte` and `Bytes n`;
* the parameters;
* the 16-byte tweak;
* `pad64` (zero padding to whole 64-byte blocks) and the hash wrappers `H`, `hash16`, `th`;
* every per-hash input format (`*Input`), the exact byte list *before* padding;
* digest split (`idxOf`, `uOf`, `admissible`), routing (`route`), digit decoding
  (`decodeDigits`).

All values (secrets, chain values, nodes, roots, `rho`) are `Val = List Byte` of length 16.
Byte `i` of a `Bytes n` (a `BitVec (8 n)`) is bits `8 i .. 8 i + 7` (as `SigGolf.bytes`), so
all conversions are little endian, exactly like the RISC-V memory.
-/

namespace SigGolfCandidate.Ref
open SigGolf OracleComp OracleSpec

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

/-- The bytes of a `Bytes n` value (`= SigGolf.bytes`, the loader's byte order). -/
def toList {n : Nat} (x : Bytes n) : List Byte := SigGolf.bytes x

/-- The `Bytes n` value of a byte list (little endian; extra bytes are dropped). -/
def ofList (n : Nat) (l : List Byte) : Bytes n := BitVec.ofNat (8 * n) (leNat l)

/-- The first `k` bytes of a hash answer. -/
def answerBytes (k : Nat) (a : BitVec 256) : List Byte :=
  (List.range k).map fun i => a.extractLsb' (8 * i) 8

/-- `l[off .. off + len)`. -/
def slice (l : List Byte) (off len : Nat) : List Byte := (l.drop off).take len

/-! ## Parameters (SPEC.md) -/

def nChains : Nat := 42
def target : Nat := 170
def nLayers : Nat := 7
def totalH : Nat := 34
def ftsA : Nat := 10
/-- Number of opened FORS trees (`k - 1`; tree 14 is the pinned group `u_14 = 0`). -/
def ftsTrees : Nat := 14
def aMax : Nat := 2 ^ 20
def cMax : Nat := 2 ^ 20
def sigBytes : Nat := 7756

/-- Height of hypertree layer `lay` (layer 0 = top): `(5,5,5,5,5,5,4)`. -/
def height (lay : Nat) : Nat := if lay = 6 then 4 else 5

/-- `sum_{j > lay} h_j`, the position of `e_lay` in `idx`. -/
def shiftBelow (lay : Nat) : Nat := ((List.range nLayers).filter (lay < ·)).foldr (height · + ·) 0

/-- `(e_lay, tau_lay)`: the leaf index in and the index of the tree of layer `lay`. -/
def route (idx lay : Nat) : Nat × Nat :=
  (idx / 2 ^ shiftBelow lay % 2 ^ height lay, idx / 2 ^ (shiftBelow lay + height lay))

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

/-- One oracle call on `pad64 x`. -/
def H (x : List Byte) : OracleComp HashSpec (BitVec 256) := HashSpec.query (pad64 x)

/-- One oracle call on `pad64 x`, truncated to its first 16 bytes. -/
def hash16 (x : List Byte) : OracleComp HashSpec Val := do
  let a ← H x
  pure (answerBytes 16 a)

/-- `Th(P, tw, payload)`: the first 16 bytes of `H(pad64(tw || 0^16 || payload))`. -/
def th (tw payload : List Byte) : OracleComp HashSpec Val := hash16 (thInput tw payload)

/-! ## Hash input formats (exact byte lists before padding)

Hypertree formats take `(lay, tau, e)` = (layer, tree, leaf) first; FORS formats take
`(k, idx)` = (tree kappa, instance). -/

/-- WOTS secret (chain start) `i` of leaf `e`: `tw(0, lay, tau, i, e) || P || S` (64 bytes). -/
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

/-- FORS secret `j` of tree `k`: `tw(8, k, idx, 0, j) || P || S` (64 bytes). -/
def ftsPrfInput (S : List Byte) (k idx j : Nat) : List Byte := thInput (tweak 8 k idx 0 j) S

/-- FORS leaf `j` of tree `k`: `tw(9, k, idx, 0, j) || P || s` (48 bytes). -/
def ftsLeafInput (k idx j : Nat) (s : Val) : List Byte := thInput (tweak 9 k idx 0 j) s

/-- FORS node `j` of level `lam`: `tw(10, k, idx, lam, j) || P || l || r` (64 bytes). -/
def ftsNodeInput (k idx lam j : Nat) (l r : Val) : List Byte :=
  thInput (tweak 10 k idx lam j) (l ++ r)

/-- FORS key: `tw(11, 0, idx, 0, 0) || P || root_0 .. root_13` (256 bytes). -/
def rootsInput (idx : Nat) (roots : List Val) : List Byte :=
  thInput (tweak 11 0 idx 0 0) roots.flatten

/-- Message digest: `tw(12, 0, 0, 0, 0) || P || rho || 0^16 || m` (96 bytes). -/
def digestInput (rho m : List Byte) : List Byte := thInput (tweak 12 0 0 0 0) (rho ++ zeros 16 ++ m)

/-! ## Digest, index split, digit decoding -/

/-- `N = Truncate_184(H(digestInput rho m))` (the first 23 bytes, little endian). -/
def digest (rho m : List Byte) : OracleComp HashSpec Nat := do
  let a ← H (digestInput rho m)
  pure (a.toNat % 2 ^ 184)

/-- `idx = N mod 2^34`. -/
def idxOf (N : Nat) : Nat := N % 2 ^ totalH

/-- `u_k = floor(N / 2^(34 + 10k)) mod 2^10`. -/
def uOf (N k : Nat) : Nat := N / 2 ^ (totalH + ftsA * k) % 2 ^ ftsA

/-- Admissible iff `u_14 = 0`. -/
def admissible (N : Nat) : Bool := uOf N 14 == 0

/-- The 21 3-bit digits of a 64-bit word: `(d >> 3r) & 7`, `r = 0..20`. -/
def digitsOfWord (d : Nat) : List Nat := (List.range 21).map fun r => d / 8 ^ r % 8

/-- TargetSum decoding of an encoding output `v` (first 16 bytes): `d0`, `d1` = the two LE 64-bit
halves; reject if bit 63 of `d0` or of `d1` is set, else the 42 digits (21 of `d0`, then 21 of
`d1`) if they sum to 170. -/
def decodeDigits (v : Val) : Option (List Nat) :=
  let d0 := leNat (slice v 0 8)
  let d1 := leNat (slice v 8 8)
  if d0 < 2 ^ 63 ∧ d1 < 2 ^ 63 then
    let x := digitsOfWord d0 ++ digitsOfWord d1
    if x.sum = target then some x else none
  else none

end SigGolfCandidate.Ref
