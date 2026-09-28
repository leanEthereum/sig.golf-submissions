import SigGolfCandidate.Equiv.Tree
import SigGolfCandidate.Equiv.Digits
import SigGolfCandidate.Equiv.Wit
import SigGolfCandidate.Equiv.Cache

/-!
# Shared hash-call relations: hypertree layers, digest, PORS hash inputs

The counter search, the layer loop (with the cached top layer), the message digest (the full
256-bit answer), and the three PORS hash inputs (paired secrets, leaves, heap-indexed nodes): each
reference routine is `f <$> relabel fmtQ A` for the abstract routine `A`. Used by the signer
(`Sign.lean`), the verifier (`Verify.lean`) and the expansion (`Expand.lean`).
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolfCandidate.Legacy (Byte Bytes Query)
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map relabel_query)
open SphincsSecurity (Digest Layer TreeIndex LeafIndex ChainIndex Encoding MasterSeed Index FtsTree
  FtsLeaf IndexGroup Message)
open SphincsSecurity.Concrete (sequenceFin)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-! ## The counter search -/

theorem hash16_enc (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (M : Digest) (c : Nat) :
    Ref.hash16 (Ref.encInput lay tree leaf (dv M) c) =
      dv <$> relabel fmtQ (SphincsSecurity.Concrete.tweakableHash (m := AComp) 0
        (.encoding lay tree leaf)
        (SphincsSecurity.bytesLE 16 M ++ SphincsSecurity.bytesLE 4 (BitVec.ofNat SphincsSecurity.counterBits c))) := by
  apply hash16_tweakable
  rw [toB_tweakableHashInput]
  simp only [SphincsSecurity.tweakBytes, SphincsSecurity.hashDomainFields, toB_tweakFields,
    toB_append, toB_dv, Ref.encInput, Ref.thInput, List.append_assoc]
  rw [show (BitVec.ofNat SphincsSecurity.counterBits c) = BitVec.ofNat (8 * 4) c from rfl,
    toB_bytesLE_ofNat]
  rfl

theorem searchCounter_eq (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (M : Digest)
    (fuel c : Nat) (h : c + fuel ≤ 2 ^ 32) :
    Ref.searchCounter lay tree leaf (dv M) c fuel =
      Option.map (fun r => (r.1.toNat, List.ofFn fun i => (r.2 i).val)) <$>
        relabel fmtQ (SphincsSecurity.Concrete.encodingSearch (m := AComp) 0 lay tree leaf M fuel c) := by
  induction fuel generalizing c with
  | zero => simp [Ref.searchCounter, SphincsSecurity.Concrete.encodingSearch]
  | succ fuel ih =>
    unfold Ref.searchCounter SphincsSecurity.Concrete.encodingSearch SphincsSecurity.Concrete.encode
    rw [hash16_enc]
    simp only [relabel_bind, relabel_pure, bind_map_left, map_bind, bind_assoc, pure_bind]
    refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun d => ?_
    rw [decodeDigits_dv]
    cases hd : SphincsSecurity.TargetSum.decodeDigest d with
    | none =>
      simp only [Option.map_none]
      rw [ih (c + 1) (by omega)]
    | some enc =>
      simp only [Option.map_some, relabel_pure, map_pure]
      congr 2
      simp only [BitVec.toNat_ofNat, SphincsSecurity.counterBits]
      rw [Nat.mod_eq_of_lt (by omega)]

/-! ## The layers -/

theorem layer_tables : ∀ lay : Layer, Ref.shiftBelow lay.val = SphincsSecurity.heightBelow lay ∧
    Ref.height lay.val = SphincsSecurity.layerHeight lay ∧
    Ref.shiftBelow lay.val + Ref.height lay.val =
      SphincsSecurity.totalHeight - SphincsSecurity.heightAbove lay := by
  decide

theorem route_eq (index : Index) (lay : Layer) :
    Ref.route index lay = ((SphincsSecurity.Concrete.leafIndexAt index lay).val,
      (SphincsSecurity.Concrete.treeIndexAt index lay).val) := by
  obtain ⟨h1, h2, h3⟩ := layer_tables lay
  simp only [Ref.route, SphincsSecurity.Concrete.leafIndexAt, SphincsSecurity.Concrete.treeIndexAt]
  rw [← h3, h1, h2]

theorem height_eq (lay : Layer) : Ref.height lay.val = SphincsSecurity.layerHeight lay :=
  (layer_tables lay).2.1

theorem leafIndexAt_lt (index : Index) (lay : Layer) :
    (SphincsSecurity.Concrete.leafIndexAt index lay).val < 2 ^ SphincsSecurity.layerHeight lay := by
  simp only [SphincsSecurity.Concrete.leafIndexAt]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

/-- A layer's output as the reference's `(counter, chain values, path)`. -/
def layerRef (lay : Layer) (o : SphincsSecurity.Concrete.LayerOutput) : Ref.LayerSig :=
  (o.1.toNat, List.ofFn (fun i => dv (o.2.1 i)),
    (List.range (SphincsSecurity.layerHeight lay)).map fun l => dv (o.2.2 l))

/-! ### The top layer (from the cache) -/

theorem dv_xor (a b : Digest) : dv (a ^^^ b) = Ref.xorBytes (dv a) (dv b) := by
  simp only [dv, Ref.toList, SigGolfCandidate.Legacy.bytes, Ref.xorBytes, List.zipWith_map, List.zipWith_self]
  apply List.map_congr_left
  intro i hi
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_xor, hk]

theorem hash16_mask (seed : MasterSeed) (l s : Nat) (hl : l < SphincsSecurity.maxLayerHeight)
    (hs : s < 2 ^ SphincsSecurity.maxLayerHeight) :
    Ref.hash16 (Ref.maskInput (Ref.toList (n := 32) seed) l s) =
      dv <$> relabel fmtQ (SphincsSecurity.Seeded.maskSecret (m := AComp) 0 seed l s) := by
  apply hash16_derive
  simp only [SphincsSecurity.keygenHashInput, SphincsSecurity.Seeded.maskDomain,
    SphincsSecurity.keygenDomainFields, Nat.mod_eq_of_lt hl, Nat.mod_eq_of_lt hs]
  simp [toB_tweakFields, toB_seed, Ref.maskInput, Ref.thInput]

theorem chainTo_eq (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (c : ChainIndex) (x : Nat) (hx : x ≤ 7) (v : Digest) :
    Ref.chainTo lay tree leaf c x (dv v) =
      dv <$> relabel fmtQ (SphincsSecurity.Concrete.chainWalk (m := AComp) 0 lay tree leaf c 0 x v) := by
  unfold Ref.chainTo
  have h := chainFold_eq lay tree leaf c 0 x (by omega) v
  rw [Nat.zero_add] at h
  exact h

/-- The cached top node `(l, s)` as the signer reads it. -/
abbrev absTopNode (seed : MasterSeed) (b : SigGolfCandidate.Cache) :=
  SphincsSecurity.Seeded.cachedTopNode (m := AComp) 0 seed (cacheDec b)

theorem topPath_eq (seed : MasterSeed) (b : SigGolfCandidate.Cache) (e : Nat)
    (he : e < 2 ^ SphincsSecurity.maxLayerHeight) :
    Ref.topPath (Ref.toList (n := 32) seed) (Ref.toList b) e =
      (fun path : Fin SphincsSecurity.maxLayerHeight → Digest => List.ofFn fun l => dv (path l)) <$>
        relabel fmtQ (sequenceFin (m := AComp) (n := SphincsSecurity.maxLayerHeight) fun level =>
          absTopNode seed b level.val (Nat.xor (e / 2 ^ level.val) 1)) := by
  unfold Ref.topPath
  rw [show Ref.topH = SphincsSecurity.maxLayerHeight from rfl, relabel_sequenceFin]
  have hbody : (fun (acc : List Ref.Val) (l : Nat) => do
      let mk ← Ref.hash16 (Ref.maskInput (Ref.toList (n := 32) seed) l ((e / 2 ^ l) ^^^ 1))
      pure (acc ++ [Ref.xorBytes (Ref.cacheNode (Ref.toList b) l ((e / 2 ^ l) ^^^ 1)) mk])) =
      fun acc l => (do
        let mk ← Ref.hash16 (Ref.maskInput (Ref.toList (n := 32) seed) l ((e / 2 ^ l) ^^^ 1))
        pure (Ref.xorBytes (Ref.cacheNode (Ref.toList b) l ((e / 2 ^ l) ^^^ 1)) mk)) >>= fun v =>
          pure (acc ++ [v]) := by
    funext acc l; simp only [bind_assoc, pure_bind]
  rw [hbody]
  rw [foldlM_range_seq (fun level : Fin SphincsSecurity.maxLayerHeight => relabel fmtQ
      (absTopNode seed b level.val (Nat.xor (e / 2 ^ level.val) 1))) _ dv (fun l hl => by
    have hs : (e / 2 ^ l) ^^^ 1 < 2 ^ (SphincsSecurity.maxLayerHeight - l) := by
      have h1 : e / 2 ^ l < 2 ^ (SphincsSecurity.maxLayerHeight - l) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add,
          show SphincsSecurity.maxLayerHeight - l + l = SphincsSecurity.maxLayerHeight by omega]
        exact he
      exact Nat.xor_lt_two_pow h1 (Nat.one_lt_two_pow (by omega))
    have hs' : (e / 2 ^ l) ^^^ 1 < 2 ^ SphincsSecurity.maxLayerHeight :=
      lt_of_lt_of_le hs (Nat.pow_le_pow_right (by omega) (by omega))
    simp only [absTopNode, SphincsSecurity.Seeded.cachedTopNode, relabel_bind, relabel_pure]
    rw [hash16_mask seed l _ hl hs', bind_map_left, map_bind]
    refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun mk => ?_
    simp only [map_pure]
    rw [dv_xor]
    exact congrArg (fun x => pure (Ref.xorBytes x (dv mk))) (dv_cacheDec_node b l _ hl hs).symm)]
  refine congrArg (· <$> _) ?_
  funext f
  rw [foldl_finRange_append, List.nil_append]

theorem signTop_eq (seed : MasterSeed) (b : SigGolfCandidate.Cache) (index : Index) (M : Digest) :
    Ref.signTop (Ref.toList (n := 32) seed) (Ref.toList b) index (dv M) =
      Option.map (fun o => [layerRef SphincsSecurity.topLayer o]) <$> relabel fmtQ
        (SphincsSecurity.Concrete.signTopLayerPaired (m := AComp) 0 index
          (SphincsSecurity.Seeded.otsSecret 0 seed SphincsSecurity.topLayer
            (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer))
          (absTopNode seed b) M) := by
  have hr := route_eq index SphincsSecurity.topLayer
  unfold Ref.signTop SphincsSecurity.Concrete.signTopLayerPaired
  rw [show ((SphincsSecurity.topLayer : Layer) : Nat) = 0 from rfl] at hr
  simp only [hr]
  have hsc := searchCounter_eq SphincsSecurity.topLayer
    (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
    (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer) M Ref.cMax 0
    (by simp [Ref.cMax])
  rw [show ((SphincsSecurity.topLayer : Layer) : Nat) = 0 from rfl] at hsc
  rw [hsc, show Ref.cMax = SphincsSecurity.encodingAttemptLimit from rfl]
  simp only [relabel_bind, relabel_pure, bind_map_left, map_bind]
  refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun r => ?_
  rcases r with _ | ⟨counter, enc⟩
  · simp
  · simp only [Option.map_some]
    rw [show Ref.nChains / 2 = SphincsSecurity.numChains / 2 from rfl]
    have hbody : (fun (acc : List Ref.Val) (k : Nat) => do
        let (s0, s1) ← Ref.prf2 (Ref.prfInput (Ref.toList (n := 32) seed) 0
          (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
          (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer) k)
        let v0 ← Ref.chainTo 0 (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
          (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer) (2 * k)
          ((List.ofFn fun i => (enc i).val).getD (2 * k) 0) s0
        let v1 ← Ref.chainTo 0 (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
          (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer) (2 * k + 1)
          ((List.ofFn fun i => (enc i).val).getD (2 * k + 1) 0) s1
        pure (acc ++ [v0, v1])) = fun acc k =>
        (Ref.prf2 (Ref.prfInput (Ref.toList (n := 32) seed) 0
          (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
          (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer) k) >>= fun s =>
          Ref.chainTo 0 (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
            (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer) (2 * k)
            ((List.ofFn fun i => (enc i).val).getD (2 * k) 0) s.1 >>= fun v0 =>
          Ref.chainTo 0 (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
            (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer) (2 * k + 1)
            ((List.ofFn fun i => (enc i).val).getD (2 * k + 1) 0) s.2 >>= fun v1 =>
            pure (v0, v1)) >>= fun r => pure (acc ++ [r.1, r.2]) := by
      funext acc k; simp only [bind_assoc, pure_bind]
    rw [hbody]
    rw [foldlM_range_seq (fun pair : SphincsSecurity.ChainPair => relabel fmtQ (do
        let secrets ← SphincsSecurity.Seeded.otsSecret (m := AComp) 0 seed SphincsSecurity.topLayer
          (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
          (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer) pair
        let first ← SphincsSecurity.Concrete.chainWalk 0 SphincsSecurity.topLayer
          (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
          (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer)
          (SphincsSecurity.evenChain pair) 0 (enc (SphincsSecurity.evenChain pair)).val secrets.1
        let second ← SphincsSecurity.Concrete.chainWalk 0 SphincsSecurity.topLayer
          (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
          (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer)
          (SphincsSecurity.oddChain pair) 0 (enc (SphincsSecurity.oddChain pair)).val secrets.2
        return (first, second)))
      _ (fun r => (dv r.1, dv r.2)) (fun j hj => by
        have e2 : 2 * j = (SphincsSecurity.evenChain ⟨j, hj⟩).val := rfl
        have e3 : 2 * j + 1 = (SphincsSecurity.oddChain ⟨j, hj⟩).val := rfl
        rw [show (0 : Nat) = ((SphincsSecurity.topLayer : Layer) : Nat) from rfl,
          prf2_ots seed _ _ _ ⟨j, hj⟩, e3, e2, getD_ofFn, getD_ofFn,
          dif_pos (SphincsSecurity.evenChain ⟨j, hj⟩).isLt,
          dif_pos (SphincsSecurity.oddChain ⟨j, hj⟩).isLt, bind_map_left]
        simp only [relabel_bind, relabel_pure, map_bind, bind_assoc]
        refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun sec => ?_
        rw [chainTo_eq _ _ _ _ _ (digit_le enc _) sec.1, bind_map_left]
        refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun v0 => ?_
        rw [chainTo_eq _ _ _ _ _ (digit_le enc _) sec.2, bind_map_left]
        rfl)]
    simp only [relabel_bind, relabel_sequenceFin, map_bind, bind_map_left, relabel_pure]
    refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun vals => ?_
    have hlt := leafIndexAt_lt index SphincsSecurity.topLayer
    rw [topPath_eq seed b _ hlt, bind_map_left, relabel_sequenceFin]
    refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun path => ?_
    simp only [map_pure, Option.map_some]
    rw [foldl_finRange_appendList, List.nil_append]
    refine congrArg (fun x => pure (some [x])) ?_
    simp only [layerRef]
    rw [flatten_unpairChains vals dv]
    congr 2

/-! ### All layers -/

theorem signLayers_eq (seed : MasterSeed) (b : SigGolfCandidate.Cache) (index : Index) (n : Nat)
    (hn : n + 1 ≤ SphincsSecurity.numLayers) (M : Digest) :
    Ref.signLayers (Ref.toList (n := 32) seed) (Ref.toList b) index n (dv M) =
      Option.map (fun parts => List.ofFn fun l : Fin (n + 1) =>
          layerRef (Fin.castLE hn l) (parts (Fin.castLE hn l))) <$>
        relabel fmtQ (SphincsSecurity.Concrete.signLayersPaired (m := AComp) 0 index
          (SphincsSecurity.Seeded.otsSecret 0 seed) (absTopNode seed b) (n + 1) M) := by
  induction n generalizing M with
  | zero =>
    unfold Ref.signLayers SphincsSecurity.Concrete.signLayersPaired
    rw [dif_pos (by decide), if_pos rfl, signTop_eq]
    simp only [relabel_bind, relabel_pure, map_bind, bind_map_left]
    rw [map_eq_bind_pure_comp]
    refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun r => ?_
    rcases r with _ | o
    · rfl
    · simp only [Option.map_some, map_pure]
      rfl
  | succ n ih =>
    let lay : Layer := ⟨n + 1, by omega⟩
    have hr := route_eq index lay
    have hh := height_eq lay
    simp only [lay] at hr hh
    unfold Ref.signLayers SphincsSecurity.Concrete.signLayersPaired
    rw [dif_pos (show n + 1 < SphincsSecurity.numLayers by omega), if_neg (by omega)]
    simp only [hr, hh]
    rw [searchCounter_eq lay (SphincsSecurity.Concrete.treeIndexAt index lay)
      (SphincsSecurity.Concrete.leafIndexAt index lay) M Ref.cMax 0 (by simp [Ref.cMax])]
    rw [show Ref.cMax = SphincsSecurity.encodingAttemptLimit from rfl]
    simp only [relabel_bind, relabel_pure, bind_map_left, map_bind]
    refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun r => ?_
    rcases r with _ | ⟨counter, enc⟩
    · simp
    · simp only [Option.map_some]
      rw [buildTree_eq seed lay (SphincsSecurity.Concrete.treeIndexAt index lay)
        (SphincsSecurity.Concrete.leafIndexAt index lay) (leafIndexAt_lt index lay) enc
        (List.ofFn fun i => (enc i).val) (fun i => by rw [getD_ofFn, dif_pos i.isLt])]
      simp only [relabel_bind, relabel_pure, bind_map_left, map_bind]
      refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun T => ?_
      rw [ih (by omega), bind_map_left]
      refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun r => ?_
      rcases r with _ | rest
      · simp
      · simp only [Option.map_some, relabel_pure, map_pure]
        congr 2
        rw [List.ofFn_succ_last (n := n + 1)]
        congr 1
        · congr 1; funext l
          split_ifs with h
          · have := congrArg Fin.val h
            have h2 : l.val = n + 1 := this
            exact absurd h2 (by have := l.isLt; omega)
          · rfl
        · split_ifs with h
          · rfl
          · exact absurd rfl h

/-! ## The digest search -/

theorem toB_msg (m : Message) :
    toB (SphincsSecurity.bytesLE 32 m) = Ref.toList (n := 32) m := toB_bytesLE 32 m

theorem hash16_rnd (seed : MasterSeed) (m : Message) (a : Nat) :
    Ref.hash16 (Ref.rndInput (Ref.toList (n := 32) seed) (Ref.toList (n := 32) m) a) =
      dv <$> relabel fmtQ (SphincsSecurity.deriveRandomizer (m := AComp) 0 seed m (BitVec.ofNat 32 a)) := by
  apply hash16_derive
  simp only [SphincsSecurity.randomizerHashInput, toB_append, toB_P, toB_seed, toB_msg,
    Ref.rndInput, Ref.thInput, List.append_assoc]
  rw [show (⟨7#8, 0#8, 0#40, BitVec.ofNat 32 a, 0#32⟩ : SphincsSecurity.TweakFields) =
    SphincsSecurity.tweakFields 7 0 0 a 0 from rfl, toB_tweakFields]

theorem digest_eq (root rho : Digest) (m : Message) :
    Ref.digest (dv rho) (Ref.toList (n := 32) m) =
      (fun d => d.toNat) <$> relabel fmtQ
        (SphincsSecurity.Concrete.messageDigest (m := AComp) 0 root m rho) := by
  unfold Ref.digest SphincsSecurity.Concrete.messageDigest
  simp only [relabel_bind, relabel_oracleHash, relabel_pure, map_bind, map_pure]
  have hin : toB (SphincsSecurity.tweakableHashInput 0 .message
      (SphincsSecurity.Concrete.messageDigestPayload root m rho)) = Ref.digestInput (dv rho) (Ref.toList (n := 32) m) := by
    rw [toB_tweakableHashInput]
    simp only [SphincsSecurity.tweakBytes, SphincsSecurity.hashDomainFields, toB_tweakFields,
      SphincsSecurity.Concrete.messageDigestPayload, toB_append, toB_dv, toB_msg, Ref.digestInput,
      Ref.thInput, List.append_assoc]
    rw [show dv 0 = Ref.zeros 16 from toList_zero 16]
  rw [hin]
  refine bind_congr (m := OracleComp SigGolfCandidate.Legacy.HashSpec) fun a => ?_
  rw [truncateMessageDigest_toNat]

/-! ## PORS hash inputs -/

theorem prf2_pors (seed : MasterSeed) (index : Index) (pair : SphincsSecurity.FtsPair) :
    Ref.prf2 (Ref.porsPrfInput (Ref.toList (n := 32) seed) index pair) =
      (fun p => (dv p.1, dv p.2)) <$>
        relabel fmtQ (SphincsSecurity.Seeded.ftsSecret (m := AComp) 0 seed index
          SphincsSecurity.Concrete.porsTree pair) := by
  apply prf2_eq
  simp [SphincsSecurity.keygenHashInput, SphincsSecurity.keygenDomainFields, toB_tweakFields,
    toB_seed, Ref.porsPrfInput, Ref.thInput, SphincsSecurity.Concrete.porsTree]

/-- A PORS leaf hash (any leaf value `j`, also the sentinel `2^14`). -/
theorem hash16_porsLeaf (index : Index) (j : Nat) (s : Digest) :
    Ref.hash16 (Ref.porsLeafInput index j (dv s)) =
      dv <$> relabel fmtQ (SphincsSecurity.Concrete.ftsLeafHash (m := AComp) 0 index
        SphincsSecurity.Concrete.porsTree j s) := by
  apply hash16_tweakable
  rw [toB_tweakableHashInput]
  simp only [SphincsSecurity.tweakBytes, SphincsSecurity.hashDomainFields, toB_tweakFields,
    toB_dv, Ref.porsLeafInput, Ref.thInput, List.append_assoc, SphincsSecurity.Concrete.porsTree]

/-- A PORS node hash under heap index `H` (any `H`). -/
theorem hash16_porsNode (index : Index) (H : Nat) (l r : Digest) :
    Ref.hash16 (Ref.porsNodeInput index H (dv l) (dv r)) =
      dv <$> relabel fmtQ (SphincsSecurity.Concrete.tweakableHash (m := AComp) 0
        (.ftsNode index SphincsSecurity.Concrete.porsTree H) (SphincsSecurity.Concrete.nodePayload l r)) := by
  apply hash16_tweakable
  rw [toB_tweakableHashInput]
  simp only [SphincsSecurity.tweakBytes, SphincsSecurity.hashDomainFields, toB_tweakFields,
    SphincsSecurity.Concrete.nodePayload, toB_append, toB_dv, Ref.porsNodeInput, Ref.thInput,
    List.append_assoc, SphincsSecurity.Concrete.porsTree]

end SigGolfCandidate.Equiv
