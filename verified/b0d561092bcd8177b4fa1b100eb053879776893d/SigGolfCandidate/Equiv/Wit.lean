import SigGolfCandidate.Equiv.Slices

/-!
# The witness decoder, the compact signature, and the abstract expansion (PORS+FP)

The abstract `Signature` is witness-shaped (`SphincsSecurity.FtsSignature`: slot codes, secrets and the
29 stack-machine segments). This file fixes the three maps the Bridge needs (design:
`work/design/WS7a-SCHEME.md` §3):

* `witSig : List Byte → Signature` / `witDec : Bytes 6348 → Signature` parse a witness exactly as the
  verifier (`Ref.verifyList`) reads it: `rho` at `0`, the slot code of the `s`-th leaf
  `(pi_s & 0x78) >> 3` from byte `16 + s`, the secrets at `32 + 16 s`, the segment stream from
  `Ref.wStream = 272` by a pointer (header byte `b`: `a = b mod 16`, merge = bit 4, `t` = bit 5,
  normalised when `a = 0`; the `a` nodes at `ptr + 8 + 16 i`; next header at `ptr + 8 + 16 a`), bytes
  beyond the witness read as zero, the layer bodies and the counters.
* `compressList` / `compress : Signature → Bytes 6100`: `rho | secrets | the nodes of segments
  0..28 concatenated, zero padded (or cut) to 120 nodes | per layer LE32 counter, chain values, path`.
* `aExpand m pk σ`: the digest query of `rho = σ[0..16)` and `m` through the abstract hash, then the
  pure reconstruction `Ref.expandOf` of the reference.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolf (Byte Bytes)
open SphincsSecurity (Digest Signature Layer ChainIndex Segment FtsSignature LayerSignature Message
  PublicKey)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-! ## The witness decoder -/

/-- The 16 witness bytes at `o` as a digest (bytes beyond the witness read as zero, `Ref.wbytes`). -/
def wdig (w : List Byte) (o : Nat) : Digest := Ref.ofList 16 (Ref.wbytes w o 16)

/-- The segment whose header is at `p`: `a = b mod 16`, merge = bit 4, `t` = bit 5 of the header byte
`b = Ref.wbyte w p` (normalised to `false` when `a = 0`), node `i` at `p + 8 + 16 i`. -/
def segAt (w : List Byte) (p : Nat) : Segment :=
  Segment.normalized ⟨Ref.wbyte w p % 16, Nat.mod_lt _ (by decide)⟩
    (decide (Ref.wbyte w p / 16 % 2 = 1)) (decide (Ref.wbyte w p / 32 % 2 = 1))
    (fun i => wdig w (p + 8 + 16 * i.val))

/-- The header position of segment `j`: `Ref.wStream`, then `+ 8 + 16 a` per segment. -/
def segPtr (w : List Byte) : Nat → Nat
  | 0 => Ref.wStream
  | j + 1 => segPtr w j + 8 + 16 * (Ref.wbyte w (segPtr w j) % 16)

/-- The PORS part of a witness. -/
def witFts (w : List Byte) : FtsSignature where
  perm s := ⟨Ref.witPi w s.val / 8 % 16, by
    have := Nat.mod_lt (Ref.witPi w s.val / 8) (show 0 < 16 by decide)
    simp only [SphincsSecurity.ftsOpenings]; omega⟩
  secrets s := Ref.ofList 16 (Ref.witSecret w s.val)
  segments j := segAt w (segPtr w j.val)

/-- Layer `lay` of a witness: its counter (at `Ref.witCounters + 4 lay`), chain values and path. -/
def witLayer (w : List Byte) (lay : Layer) : LayerSignature lay :=
  ⟨Ref.ofList 4 (Ref.slice w (Ref.witCounters + 4 * lay.val) 4),
    fun i => Ref.ofList 16 (Ref.witChain w lay.val i.val),
    fun l => Ref.ofList 16 (Ref.witSib w lay.val l.val)⟩

/-- **The witness decoder** on byte lists. -/
def witSig (w : List Byte) : Signature :=
  ⟨Ref.ofList 16 (Ref.witRho w), witFts w, witLayer w⟩

/-- **The witness decoder**. -/
def witDec (w : Bytes 6348) : Signature := witSig (Ref.toList w)

/-! ## The compact signature -/

/-- The authentication nodes of a signature: the nodes of segments `0 .. 28`, concatenated. -/
def authNodes (σ : Signature) : List Digest :=
  (List.ofFn fun j => List.ofFn (σ.fts.segments j).nodes).flatten

/-- One layer: `LE32 c`, the 42 chain values and the path. -/
def layerBytes (σ : Signature) (lay : Layer) : List Byte :=
  Ref.toList (n := 4) (σ.layers lay).counter ++
    (List.ofFn fun i => dv ((σ.layers lay).chainValues i)).flatten ++
    (List.ofFn fun j => dv ((σ.layers lay).path j)).flatten

/-- **The compact signature bytes**: `rho | 15 secrets | 120 authentication-node slots (the segments'
nodes in order, zero padded, cut at 120) | layers 0..4`. -/
def compressList (σ : Signature) : List Byte :=
  dv σ.randomness ++ (List.ofFn fun s => dv (σ.fts.secrets s)).flatten ++
    (((authNodes σ).map dv).flatten ++ Ref.zeros (16 * Ref.porsM)).take (16 * Ref.porsM) ++
    (List.ofFn (layerBytes σ)).flatten

/-- **The compact signature**. -/
def compress (σ : Signature) : Bytes 6100 := Ref.ofList 6100 (compressList σ)

/-! ## The abstract expansion -/

/-- **The abstract expansion**: the digest of `rho = σ[0..16)` and the message (one abstract query),
then the reference's pure reconstruction `Ref.expandOf` (which fails on malformed signatures). -/
def aExpand (m : Message) (pk : PublicKey) (σ : Bytes 6100) : AComp (Option (Bytes 6348)) := do
  let d ← SphincsSecurity.Concrete.messageDigest (m := AComp) 0 pk.root m
    (Ref.ofList 16 (Ref.sigRho (Ref.toList σ)))
  pure ((Ref.expandOf (Ref.toList σ) d.toNat).map (Ref.ofList 6348))

/-! ## Basic facts -/

theorem length_wbytes (w : List Byte) (o n : Nat) : (Ref.wbytes w o n).length = n := by
  simp [Ref.wbytes]

theorem dv_wdig (w : List Byte) (o : Nat) : dv (wdig w o) = Ref.wbytes w o 16 :=
  Ref.toList_ofList 16 _ (length_wbytes w o 16)

theorem length_layerBytes (σ : Signature) (lay : Layer) :
    (layerBytes σ lay).length = Ref.sigLayerBytes lay.val := by
  simp only [layerBytes, List.length_append, Ref.length_toList]
  rw [length_flatten_ofFn _ 16 (fun j => length_dv _), length_flatten_ofFn _ 16 (fun j => length_dv _)]
  fin_cases lay <;> rfl

theorem length_compressList (σ : Signature) : (compressList σ).length = 6100 := by
  simp only [compressList, List.length_append, length_dv, List.length_take, Ref.zeros,
    List.length_replicate]
  rw [length_flatten_ofFn _ 16 (fun j => length_dv _)]
  have hl : (List.ofFn (layerBytes σ)).flatten.length = 3924 := by
    rw [List.length_flatten, List.map_ofFn]
    simp only [Function.comp_def, length_layerBytes, List.sum_ofFn]
    decide
  rw [hl]
  simp only [SphincsSecurity.ftsOpenings, Ref.porsM]
  omega

theorem toList_compress (σ : Signature) : Ref.toList (compress σ) = compressList σ :=
  Ref.toList_ofList 6100 _ (length_compressList σ)

end SigGolfCandidate.Equiv
