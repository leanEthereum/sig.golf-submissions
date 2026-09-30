import SigGolfCandidate.Equiv.Tree
import SigGolfCandidate.Equiv.Digits
import SigGolfCandidate.Equiv.Codec
import SigGolfCandidate.Equiv.Cache

/-!
# Signing

The few-time forest, the digest search, the counter search, the layer loop and the whole signer:
each reference routine is `f <$> relabel fmtQ A` for the abstract routine `A`.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolf (Byte Bytes Query)
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map relabel_query)
open SphincsSecurity (Digest Layer TreeIndex LeafIndex ChainIndex Encoding MasterSeed Index FtsTree
  FtsLeaf IndexGroup Message)
open SphincsSecurity.Concrete (sequenceFin)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-! ## Hash inputs of the forest and the digest -/

theorem hash16_ftsPrf (seed : MasterSeed) (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    Ref.hash16 (Ref.ftsPrfInput (Ref.toList (n := 32) seed) tree index leaf) =
      dv <$> relabel fmtQ (SphincsSecurity.Seeded.ftsSecret (m := AComp) 0 seed index tree leaf) := by
  apply hash16_derive
  simp [SphincsSecurity.keygenHashInput, SphincsSecurity.keygenDomainFields, toB_tweakFields,
    toB_seed, Ref.ftsPrfInput, Ref.thInput]

theorem hash16_ftsLeaf (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (s : Digest) :
    Ref.hash16 (Ref.ftsLeafInput tree index leaf (dv s)) =
      dv <$> relabel fmtQ (SphincsSecurity.Concrete.ftsLeafHash (m := AComp) 0 index tree leaf s) := by
  apply hash16_tweakable
  rw [toB_tweakableHashInput]
  simp only [SphincsSecurity.tweakBytes, SphincsSecurity.hashDomainFields, toB_tweakFields,
    toB_dv, Ref.ftsLeafInput, Ref.thInput, List.append_assoc]

theorem hash16_ftsNode (index : Index) (tree : FtsTree) (lam j : Nat) (l r : Digest) :
    Ref.hash16 (Ref.ftsNodeInput tree index lam j (dv l) (dv r)) =
      dv <$> relabel fmtQ (SphincsSecurity.Concrete.tweakableHash (m := AComp) 0
        (.ftsNode index tree lam j) (SphincsSecurity.Concrete.nodePayload l r)) := by
  apply hash16_tweakable
  rw [toB_tweakableHashInput]
  simp only [SphincsSecurity.tweakBytes, SphincsSecurity.hashDomainFields, toB_tweakFields,
    SphincsSecurity.Concrete.nodePayload, toB_append, toB_dv, Ref.ftsNodeInput, Ref.thInput,
    List.append_assoc]

theorem hash16_roots (index : Index) (roots : FtsTree → Digest) :
    Ref.hash16 (Ref.rootsInput index (List.ofFn fun k => dv (roots k))) =
      dv <$> relabel fmtQ (SphincsSecurity.Concrete.tweakableHash (m := AComp) 0
        (.ftsRoots index) (SphincsSecurity.Concrete.ftsRootsPayload roots)) := by
  apply hash16_tweakable
  rw [toB_tweakableHashInput]
  simp only [SphincsSecurity.tweakBytes, SphincsSecurity.hashDomainFields, toB_tweakFields,
    SphincsSecurity.Concrete.ftsRootsPayload, toB_flatMap_dv, Ref.rootsInput, Ref.thInput,
    List.map_ofFn, List.append_assoc]
  rfl

/-! ## One few-time tree -/

/-- The abstract leaves of a few-time tree. -/
abbrev absFtsLeaves (seed : MasterSeed) (index : Index) (tree : FtsTree) :=
  sequenceFin (m := AComp) fun leafIdx : FtsLeaf => do
    let value ← SphincsSecurity.Seeded.ftsSecret 0 seed index tree leafIdx
    let hashed ← SphincsSecurity.Concrete.ftsLeafHash 0 index tree leafIdx value
    return (value, hashed)

theorem buildFtsLeaves_eq (seed : MasterSeed) (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    Ref.buildFtsLeaves (Ref.toList (n := 32) seed) tree index Ref.ftsA leaf =
      (fun f => (List.ofFn fun j => dv (f j).2, dv (f leaf).1)) <$>
        relabel fmtQ (absFtsLeaves seed index tree) := by
  unfold Ref.buildFtsLeaves
  have hbody : (fun (st : List Ref.Val × Ref.Val) (j : Nat) => do
      let s ← Ref.hash16 (Ref.ftsPrfInput (Ref.toList (n := 32) seed) tree index j)
      let l ← Ref.hash16 (Ref.ftsLeafInput tree index j s)
      pure (st.1 ++ [l], if j = leaf.val then s else st.2)) = fun st j =>
      (Ref.hash16 (Ref.ftsPrfInput (Ref.toList (n := 32) seed) tree index j) >>= fun s =>
        Ref.hash16 (Ref.ftsLeafInput tree index j s) >>= fun l => pure (s, l)) >>= fun r =>
        pure (st.1 ++ [r.2], if j = leaf.val then r.1 else st.2) := by
    funext st j; simp only [bind_assoc, pure_bind]
  rw [hbody, show Ref.ftsA = SphincsSecurity.ftsTreeHeight from rfl, absFtsLeaves,
    relabel_sequenceFin]
  rw [foldlM_range_seq (fun leafIdx : FtsLeaf => relabel fmtQ (do
      let value ← SphincsSecurity.Seeded.ftsSecret (m := AComp) 0 seed index tree leafIdx
      let hashed ← SphincsSecurity.Concrete.ftsLeafHash (m := AComp) 0 index tree leafIdx value
      return (value, hashed))) _ (fun r : Digest × Digest => (dv r.1, dv r.2)) (fun j hj => by
    have h1 := hash16_ftsPrf seed index tree ⟨j, hj⟩
    simp only [relabel_bind, relabel_pure]
    rw [h1, bind_map_left]
    simp only [map_bind, map_pure]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun s => ?_
    rw [hash16_ftsLeaf index tree ⟨j, hj⟩ s, bind_map_left])]
  refine congrArg (· <$> _) ?_
  funext f
  rw [foldl_prod _ (fun acc j => acc ++ [dv (f j).2])
      (fun acc (j : Fin (2 ^ SphincsSecurity.ftsTreeHeight)) =>
        if j.val = leaf.val then dv (f j).1 else acc),
    foldl_finRange_append, foldl_finRange_capture, dif_pos leaf.isLt, List.nil_append]

theorem buildFtsTree_eq (seed : MasterSeed) (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    Ref.buildFtsTree (Ref.toList (n := 32) seed) tree index Ref.ftsA leaf =
      (fun r => (dv r.1, (List.range SphincsSecurity.ftsTreeHeight).map (fun l => dv (r.2.1 l)),
          dv r.2.2)) <$>
        relabel fmtQ (SphincsSecurity.Concrete.buildFtsTree (m := AComp) 0 index tree
          (SphincsSecurity.Seeded.ftsSecret 0 seed index tree) leaf) := by
  unfold Ref.buildFtsTree SphincsSecurity.Concrete.buildFtsTree
  rw [buildFtsLeaves_eq seed index tree leaf]
  simp only [relabel_bind, relabel_pure, map_bind, bind_map_left, map_pure]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun f => ?_
  rw [ofFn_leaves f Prod.snd, show Ref.ftsA = SphincsSecurity.ftsTreeHeight from rfl]
  rw [buildLevels_eq (Ref.ftsNodeInput tree index) (fun level nodeIdx left right =>
      SphincsSecurity.Concrete.tweakableHash (m := AComp) 0 (.ftsNode index tree level nodeIdx)
        (SphincsSecurity.Concrete.nodePayload left right)) (hash16_ftsNode index tree) _ _ leaf.isLt
      (fun k => if h : k < 2 ^ SphincsSecurity.ftsTreeHeight then (f ⟨k, h⟩).2 else 0)]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]

/-! ## The forest -/

/-- `Ref.signFors` with the index and the leaf groups given separately. -/
def signForsU (S : List Byte) (idx : Nat) (u : Nat → Nat) :
    OracleComp SigGolf.HashSpec (List (Ref.Val × List Ref.Val) × List Ref.Val) :=
  (List.range Ref.ftsTrees).foldlM (fun (st : List (Ref.Val × List Ref.Val) × List Ref.Val) k => do
    let (s, path, root) ← Ref.buildFtsTree S k idx Ref.ftsA (u k)
    pure (st.1 ++ [(s, path)], st.2 ++ [root])) ([], [])

theorem signFors_eq_U (S : List Byte) (N : Nat) :
    Ref.signFors S N = signForsU S (Ref.idxOf N) (Ref.uOf N) := rfl

/-- The abstract forest trees. -/
abbrev absTrees (seed : MasterSeed) (index : Index) (leaves : IndexGroup → FtsLeaf) :=
  sequenceFin (m := AComp) fun tree : FtsTree =>
    SphincsSecurity.Concrete.buildFtsTree 0 index tree (SphincsSecurity.Seeded.ftsSecret 0 seed index tree)
      (leaves (SphincsSecurity.Concrete.ftsIndexOf tree))

theorem signForsU_eq (seed : MasterSeed) (index : Index) (leaves : IndexGroup → FtsLeaf) :
    signForsU (Ref.toList (n := 32) seed) index (uFun leaves) =
      (fun trees : FtsTree → Digest × (Nat → Digest) × Digest =>
        (List.ofFn fun k => (dv (trees k).1,
            (List.range SphincsSecurity.ftsTreeHeight).map (fun l => dv ((trees k).2.1 l))),
          List.ofFn fun k => dv (trees k).2.2)) <$>
        relabel fmtQ (absTrees seed index leaves) := by
  unfold signForsU
  have hbody : (fun (st : List (Ref.Val × List Ref.Val) × List Ref.Val) (k : Nat) =>
      Ref.buildFtsTree (Ref.toList (n := 32) seed) k index Ref.ftsA (uFun leaves k) >>= fun p =>
        match p with | (s, path, root) => pure (st.1 ++ [(s, path)], st.2 ++ [root])) =
      fun st k =>
      Ref.buildFtsTree (Ref.toList (n := 32) seed) k index Ref.ftsA (uFun leaves k) >>= fun r =>
        pure (st.1 ++ [(r.1, r.2.1)], st.2 ++ [r.2.2]) := rfl
  rw [hbody, show Ref.ftsTrees = SphincsSecurity.ftsTrees - 1 from rfl, absTrees, relabel_sequenceFin]
  rw [foldlM_range_seq (fun tree : FtsTree => relabel fmtQ
      (SphincsSecurity.Concrete.buildFtsTree (m := AComp) 0 index tree
        (SphincsSecurity.Seeded.ftsSecret 0 seed index tree)
        (leaves (SphincsSecurity.Concrete.ftsIndexOf tree)))) _
      (fun r => (dv r.1, (List.range SphincsSecurity.ftsTreeHeight).map (fun l => dv (r.2.1 l)),
          dv r.2.2)) (fun j hj => by
    have hu : uFun leaves j = (leaves (SphincsSecurity.Concrete.ftsIndexOf ⟨j, hj⟩)).val := by
      unfold uFun
      rw [dif_pos (by simp [SphincsSecurity.ftsTrees] at hj ⊢; omega)]
      rfl
    rw [hu]
    exact buildFtsTree_eq seed index ⟨j, hj⟩ _)]
  refine congrArg (· <$> _) ?_
  funext f
  rw [foldl_prod _ (fun acc j => acc ++ [(dv (f j).1,
      (List.range SphincsSecurity.ftsTreeHeight).map (fun l => dv ((f j).2.1 l)))])
      (fun acc j => acc ++ [dv (f j).2.2]),
    foldl_finRange_append, foldl_finRange_append, List.nil_append, List.nil_append]

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
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun d => ?_
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

theorem map_range_eq_ofFn {β : Type} (n : Nat) (f : Nat → β) :
    (List.range n).map f = List.ofFn fun j : Fin n => f j.val := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-! ### The top layer (from the cache) -/

theorem dv_xor (a b : Digest) : dv (a ^^^ b) = Ref.xorBytes (dv a) (dv b) := by
  simp only [dv, Ref.toList, SigGolf.bytes, Ref.xorBytes, List.zipWith_map, List.zipWith_self]
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

theorem chainTo_eq (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (c : ChainIndex) (x : Nat) (hx : x ≤ 7) :
    Ref.chainTo (Ref.toList (n := 32) seed) lay tree leaf c x =
      dv <$> relabel fmtQ (do
        let start ← SphincsSecurity.Seeded.otsSecret (m := AComp) 0 seed lay tree leaf c
        SphincsSecurity.Concrete.chainWalk 0 lay tree leaf c 0 x start) := by
  unfold Ref.chainTo
  rw [hash16_prf]
  simp only [relabel_bind, map_bind, bind_map_left]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun start => ?_
  have h := chainFold_eq lay tree leaf c 0 x (by omega) start
  rw [Nat.zero_add] at h
  exact h

/-- The cached top node `(l, s)` as the signer reads it. -/
abbrev absTopNode (seed : MasterSeed) (b : SigGolf.Cache) :=
  SphincsSecurity.Seeded.cachedTopNode (m := AComp) 0 seed (cacheDec b)

theorem topPath_eq (seed : MasterSeed) (b : SigGolf.Cache) (e : Nat)
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
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun mk => ?_
    simp only [map_pure]
    rw [dv_xor]
    exact congrArg (fun x => pure (Ref.xorBytes x (dv mk))) (dv_cacheDec_node b l _ hl hs).symm)]
  refine congrArg (· <$> _) ?_
  funext f
  rw [foldl_finRange_append, List.nil_append]

theorem signTop_eq (seed : MasterSeed) (b : SigGolf.Cache) (index : Index) (M : Digest) :
    Ref.signTop (Ref.toList (n := 32) seed) (Ref.toList b) index (dv M) =
      Option.map (fun o => [layerRef SphincsSecurity.topLayer o]) <$> relabel fmtQ
        (SphincsSecurity.Concrete.signTopLayer (m := AComp) 0 index
          (SphincsSecurity.Seeded.otsSecret 0 seed SphincsSecurity.topLayer
            (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer))
          (absTopNode seed b) M) := by
  have hr := route_eq index SphincsSecurity.topLayer
  unfold Ref.signTop SphincsSecurity.Concrete.signTopLayer
  rw [show ((SphincsSecurity.topLayer : Layer) : Nat) = 0 from rfl] at hr
  simp only [hr]
  have hsc := searchCounter_eq SphincsSecurity.topLayer
    (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
    (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer) M Ref.cMax 0
    (by simp [Ref.cMax])
  rw [show ((SphincsSecurity.topLayer : Layer) : Nat) = 0 from rfl] at hsc
  rw [hsc, show Ref.cMax = SphincsSecurity.encodingAttemptLimit from rfl]
  simp only [relabel_bind, relabel_pure, bind_map_left, map_bind]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
  rcases r with _ | ⟨counter, enc⟩
  · simp
  · simp only [Option.map_some]
    rw [show Ref.nChains = SphincsSecurity.numChains from rfl]
    rw [foldlM_range_seq (fun c : ChainIndex => relabel fmtQ (do
        let start ← SphincsSecurity.Seeded.otsSecret (m := AComp) 0 seed SphincsSecurity.topLayer
          (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
          (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer) c
        SphincsSecurity.Concrete.chainWalk 0 SphincsSecurity.topLayer
          (SphincsSecurity.Concrete.treeIndexAt index SphincsSecurity.topLayer)
          (SphincsSecurity.Concrete.leafIndexAt index SphincsSecurity.topLayer) c 0 (enc c).val start))
      _ dv (fun j hj => by
        rw [getD_ofFn, dif_pos hj]
        have hd : (enc ⟨j, hj⟩).val ≤ 7 := by
          have := (enc ⟨j, hj⟩).isLt
          simp [SphincsSecurity.chainLength, SphincsSecurity.winternitzBits] at this; omega
        exact chainTo_eq seed SphincsSecurity.topLayer _ _ ⟨j, hj⟩ _ hd)]
    simp only [relabel_bind, relabel_sequenceFin, map_bind, bind_map_left, relabel_pure]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun vals => ?_
    have hlt := leafIndexAt_lt index SphincsSecurity.topLayer
    rw [topPath_eq seed b _ hlt, bind_map_left, relabel_sequenceFin]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun path => ?_
    simp only [map_pure, Option.map_some]
    rw [foldl_finRange_append, List.nil_append]
    refine congrArg (fun x => pure (some [x])) ?_
    simp only [layerRef]
    congr 2

/-! ### All layers -/

theorem signLayers_eq (seed : MasterSeed) (b : SigGolf.Cache) (index : Index) (n : Nat)
    (hn : n + 1 ≤ SphincsSecurity.numLayers) (M : Digest) :
    Ref.signLayers (Ref.toList (n := 32) seed) (Ref.toList b) index n (dv M) =
      Option.map (fun parts => List.ofFn fun l : Fin (n + 1) =>
          layerRef (Fin.castLE hn l) (parts (Fin.castLE hn l))) <$>
        relabel fmtQ (SphincsSecurity.Concrete.signLayers (m := AComp) 0 index
          (SphincsSecurity.Seeded.otsSecret 0 seed) (absTopNode seed b) (n + 1) M) := by
  induction n generalizing M with
  | zero =>
    unfold Ref.signLayers SphincsSecurity.Concrete.signLayers
    rw [dif_pos (by decide), if_pos rfl, signTop_eq]
    simp only [relabel_bind, relabel_pure, map_bind, bind_map_left]
    rw [map_eq_bind_pure_comp]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
    rcases r with _ | o
    · rfl
    · simp only [Option.map_some, map_pure]
      rfl
  | succ n ih =>
    let lay : Layer := ⟨n + 1, by omega⟩
    have hr := route_eq index lay
    have hh := height_eq lay
    simp only [lay] at hr hh
    unfold Ref.signLayers SphincsSecurity.Concrete.signLayers
    rw [dif_pos (show n + 1 < SphincsSecurity.numLayers by omega), if_neg (by omega)]
    simp only [hr, hh]
    rw [searchCounter_eq lay (SphincsSecurity.Concrete.treeIndexAt index lay)
      (SphincsSecurity.Concrete.leafIndexAt index lay) M Ref.cMax 0 (by simp [Ref.cMax])]
    rw [show Ref.cMax = SphincsSecurity.encodingAttemptLimit from rfl]
    simp only [relabel_bind, relabel_pure, bind_map_left, map_bind]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
    rcases r with _ | ⟨counter, enc⟩
    · simp
    · simp only [Option.map_some]
      rw [buildTree_eq seed lay (SphincsSecurity.Concrete.treeIndexAt index lay)
        (SphincsSecurity.Concrete.leafIndexAt index lay) (leafIndexAt_lt index lay) enc
        (List.ofFn fun i => (enc i).val) (fun i => by rw [getD_ofFn, dif_pos i.isLt])]
      simp only [relabel_bind, relabel_pure, bind_map_left, map_bind]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun T => ?_
      rw [ih (by omega), bind_map_left]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
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
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun a => ?_
  rw [truncateMessageDigest_toNat]

/-- Project a reference digest-search result to what the rest of the signer reads. -/
def projN (r : Ref.Val × Nat) : Ref.Val × Nat × (Nat → Nat) := (r.1, Ref.idxOf r.2, Ref.uOf r.2)

/-- The same projection of an abstract digest-search result. -/
def projA (r : Digest × Index × (IndexGroup → FtsLeaf)) : Ref.Val × Nat × (Nat → Nat) :=
  (dv r.1, r.2.1.val, uFun r.2.2)

theorem searchDigest_eq (sk : SphincsSecurity.Seeded.SecretKey) (hP : sk.parameter = 0)
    (m : Message) (fuel a : Nat) :
    Option.map projN <$> Ref.searchDigest (Ref.toList (n := 32) sk.seed) (Ref.toList (n := 32) m) a fuel =
      Option.map projA <$> relabel fmtQ
        (SphincsSecurity.Seeded.signDigestLoop (m := AComp) sk m fuel a) := by
  induction fuel generalizing a with
  | zero => simp [Ref.searchDigest, SphincsSecurity.Seeded.signDigestLoop]
  | succ fuel ih =>
    unfold Ref.searchDigest SphincsSecurity.Seeded.signDigestLoop SphincsSecurity.Seeded.signAttempt
    rw [hash16_rnd, hP]
    simp only [relabel_bind, relabel_pure, bind_map_left, map_bind]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun rho => ?_
    rw [digest_eq sk.root rho m, bind_map_left]
    simp only [bind_assoc]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun d => ?_
    rw [admissible_eq]
    by_cases hd : SphincsSecurity.Concrete.Admissible d
    · simp only [hd, decide_true, if_true, pure_bind, relabel_pure, map_pure, Option.map_some]
      simp only [projN, projA, idxOf_eq, uOf_eq]
    · simp only [hd, decide_false, if_false, pure_bind, Bool.false_eq_true]
      exact ih (a + 1)

/-! ## The whole signer -/

/-- What the reference signer does after the MAC check and the digest search. -/
def signCont (S cache : List Byte) (rho : Ref.Val) (idx : Nat) (u : Nat → Nat) :
    OracleComp SigGolf.HashSpec (Option (List Byte)) := do
  let (fors, roots) ← signForsU S idx u
  let M ← Ref.hash16 (Ref.rootsInput idx roots)
  match ← Ref.signLayers S cache idx (Ref.nLayers - 1) M with
  | none => pure none
  | some lays => pure (some (Ref.serialize rho fors lays))

theorem signList_eq_cont (S cache m : List Byte) :
    Ref.signList S cache m = Ref.H (Ref.macInput S (Ref.cacheRegion cache)) >>= fun tag =>
      if Ref.toList (n := 32) tag = Ref.cacheTag cache then
        (Option.map projN <$> Ref.searchDigest S m 0 Ref.aMax) >>= fun r =>
          match r with
          | none => pure none
          | some (rho, idx, u) => signCont S cache rho idx u
      else pure none := by
  unfold Ref.signList
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun tag => ?_
  split_ifs
  · rw [bind_map_left]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
    rcases r with _ | ⟨rho, N⟩ <;> rfl
  · rfl

theorem serialize_eq (rho : Digest) (trees : FtsTree → Digest × (Nat → Digest) × Digest)
    (parts : Layer → SphincsSecurity.Concrete.LayerOutput) :
    Ref.serialize (dv rho)
      (List.ofFn fun k => (dv (trees k).1,
        (List.range SphincsSecurity.ftsTreeHeight).map (fun l => dv ((trees k).2.1 l))))
      (List.ofFn fun l : Fin (5 + 1) =>
        layerRef (Fin.castLE (le_refl 6) l) (parts (Fin.castLE (le_refl 6) l))) =
    sigToList ⟨rho, fun t => (trees t).1, fun t l => (trees t).2.1 l.val,
      fun lay => SphincsSecurity.Concrete.LayerOutput.toSignature lay (parts lay)⟩ := by
  unfold Ref.serialize sigToList
  simp only [List.map_ofFn]
  congr 1
  congr 2
  funext l
  simp only [Function.comp, layerPart, layerRef, map_range_eq_ofFn,
    SphincsSecurity.Concrete.LayerOutput.toSignature]
  rw [Ref.le32, leBytes_eq_toList]
  have e : ∀ c : SphincsSecurity.Counter,
      Ref.toList (n := 4) (BitVec.ofNat (8 * 4) c.toNat) = Ref.toList (n := 4) c := fun c => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [e]
  rfl

theorem signCont_eq (seed : MasterSeed) (b : SigGolf.Cache) (randomness : Digest) (index : Index)
    (leaves : IndexGroup → FtsLeaf) :
    signCont (Ref.toList (n := 32) seed) (Ref.toList b) (dv randomness) index (uFun leaves) =
      Option.map sigToList <$> relabel fmtQ
        (SphincsSecurity.Concrete.signFrom (m := AComp) 0 index
          (SphincsSecurity.Seeded.ftsSecret 0 seed index) (SphincsSecurity.Seeded.otsSecret 0 seed)
          (absTopNode seed b) randomness leaves) := by
  unfold signCont SphincsSecurity.Concrete.signFrom SphincsSecurity.Concrete.buildForest
  rw [signForsU_eq]
  simp only [relabel_bind, relabel_pure, bind_map_left, map_bind, bind_assoc, pure_bind]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun trees => ?_
  rw [hash16_roots, bind_map_left]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun key => ?_
  rw [show Ref.nLayers - 1 = 5 from rfl]
  rw [signLayers_eq seed b index 5 (le_refl 6) key, bind_map_left]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
  rcases r with _ | parts
  · simp
  · simp only [Option.map_some, relabel_pure, map_pure]
    exact congrArg (fun x => pure (some x)) (serialize_eq randomness trees parts)

theorem toB_macHashInput (seed : MasterSeed) (b : SigGolf.Cache) :
    toB (SphincsSecurity.macHashInput 0 seed (cacheDec b).region) =
      Ref.macInput (Ref.toList (n := 32) seed) (Ref.cacheRegion (Ref.toList b)) := by
  unfold SphincsSecurity.macHashInput
  simp only [toB_append, toB_P, toB_seed, toB_regionBytes_cacheDec, Ref.macInput, Ref.thInput,
    List.append_assoc]
  rw [show (⟨14#8, 0#8, 0#40, 0#32, 0#32⟩ : SphincsSecurity.TweakFields) =
    SphincsSecurity.tweakFields 14 0 0 0 0 from rfl, toB_tweakFields]

/-- **sign** (byte lists): the reference signer is the relabelled abstract signer on the decoded
cache, for any secret key with the parameter `0` (the root is ignored). -/
theorem signList_eq (sk : SphincsSecurity.Seeded.SecretKey) (hP : sk.parameter = 0)
    (b : SigGolf.Cache) (m : Message) :
    Ref.signList (Ref.toList (n := 32) sk.seed) (Ref.toList b) (Ref.toList (n := 32) m) =
      Option.map sigToList <$> relabel fmtQ
        (SphincsSecurity.Seeded.sign (m := AComp) sk (cacheDec b) m) := by
  rw [signList_eq_cont]
  unfold SphincsSecurity.Seeded.sign
  rw [hP, relabel_bind, relabel_oracleHash, toB_macHashInput, map_bind]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun tag => ?_
  by_cases ht : tag = (cacheDec b).tag
  · rw [if_pos ((cacheTag_iff b tag).mpr ht), if_pos ht]
    unfold SphincsSecurity.Seeded.signChecked
    rw [show Ref.aMax = SphincsSecurity.digestAttemptLimit from rfl]
    have hsd := searchDigest_eq sk hP m SphincsSecurity.digestAttemptLimit 0
    rw [hsd, bind_map_left]
    simp only [relabel_bind, relabel_pure, map_bind]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
    rcases r with _ | ⟨randomness, index, leaves⟩
    · simp
    · simp only [Option.map_some, projA]
      rw [signCont_eq, hP]
  · rw [if_neg (fun h => ht ((cacheTag_iff b tag).mp h)), if_neg ht]
    simp

/-- **sign**: `signRef` is the relabelled abstract signer on the decoded cache, decoded by the
signature codec. -/
theorem signRef_eq (sk : SphincsSecurity.Seeded.SecretKey) (hP : sk.parameter = 0)
    (b : SigGolf.Cache) (m : Bytes 32) :
    Ref.signRef sk.seed b m =
      Option.map sigCodec.symm <$> relabel fmtQ
        (SphincsSecurity.Seeded.sign (m := AComp) sk (cacheDec b) m) := by
  unfold Ref.signRef
  rw [signList_eq sk hP b m]
  simp only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
  rcases r with _ | σ <;> rfl

end SigGolfCandidate.Equiv
