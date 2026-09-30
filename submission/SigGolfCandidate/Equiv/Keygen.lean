import SigGolfCandidate.Equiv.Layers

/-!
# Key generation (the cached top tree)

`Ref.keygenList` builds the top tree (as every other tree), masks its levels `0 .. 10` into the
region and MACs the region; it is the relabelled abstract `Seeded.keygenFromSeed`, with the cache
bytes `cacheList` (`keygenRef_eq`: the published key and `cacheEnc` of the abstract cache).
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolf (Byte Bytes Query)
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map relabel_query)
open SphincsSecurity (Digest Layer TreeIndex LeafIndex ChainIndex Encoding MasterSeed TopCache
  TopRegion)
open SphincsSecurity.Concrete (sequenceFin)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-! ## All levels of a tree -/

/-- Level `L` of a node table as reference bytes (`2^(h-L)` nodes). -/
def levelList (T : Nat → Nat → Digest) (h L : Nat) : List Ref.Val :=
  List.ofFn fun j : Fin (2 ^ (h - L)) => dv (T L j)

theorem getD_map_range_list {β : Type} (n i : Nat) (f : Nat → List β) (hi : i < n) :
    ((List.range n).map f).getD i [] = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl

section levels

variable (node : Ref.NodeFmt) (hashNode : Nat → Nat → Digest → Digest → AComp Digest)
  (hnode : ∀ lam j l r, Ref.hash16 (node lam j (dv l) (dv r)) = dv <$> relabel fmtQ (hashNode lam j l r))

include hnode in
theorem buildAllLevels_steps (h : Nat) (leaves : Nat → Digest) (L : Nat) (hL : L ≤ h) :
    (List.range' 1 L).foldlM (fun (levels : List (List Ref.Val)) lam => do
        let level ← Ref.buildLevel node lam (levels.getD (lam - 1) [])
        pure (levels ++ [level])) [List.ofFn (fun j : Fin (2 ^ h) => dv (leaves j))] =
      (fun T => (List.range (L + 1)).map (levelList T h)) <$>
        relabel fmtQ (SphincsSecurity.Concrete.buildLevels hashNode h leaves L) := by
  induction L with
  | zero =>
    simp only [List.range'_zero, List.foldlM_nil, SphincsSecurity.Concrete.buildLevels, relabel_pure,
      map_pure]
    simp only [Nat.zero_add, List.range_one, List.map_cons, List.map_nil, levelList]
    rw [Nat.sub_zero]
  | succ L ih =>
    rw [List.range'_concat, List.foldlM_append, ih (by omega)]
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure, bind_map_left,
      SphincsSecurity.Concrete.buildLevels, relabel_bind, relabel_pure, map_bind]
    refine bind_congr fun T => ?_
    rw [show 1 + 1 * L - 1 = L by omega, getD_map_range_list _ _ _ (by omega)]
    unfold Ref.buildLevel SphincsSecurity.Concrete.buildLevel levelList
    simp only [Nat.one_mul, List.length_ofFn]
    have hw : 2 ^ (h - L) / 2 = 2 ^ (h - (L + 1)) := by
      rw [show h - L = (h - (L + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by omega)]
    rw [hw, show 1 + L = L + 1 by omega]
    have hpow : 2 ^ (h - L) = 2 * 2 ^ (h - (L + 1)) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hb : ∀ j (hj : j < 2 ^ (h - (L + 1))),
        Ref.hash16 (node (L + 1) j
          ((List.ofFn fun j : Fin (2 ^ (h - L)) => dv (T L j)).getD (2 * j) [])
          ((List.ofFn fun j : Fin (2 ^ (h - L)) => dv (T L j)).getD (2 * j + 1) [])) =
        dv <$> relabel fmtQ (hashNode (L + 1) j (T L (2 * j)) (T L (2 * j + 1))) := by
      intro j hj
      rw [getD_ofFn, getD_ofFn, dif_pos (by omega), dif_pos (by omega)]
      exact hnode _ _ _ _
    rw [foldlM_range_seq (fun j : Fin (2 ^ (h - (L + 1))) =>
        relabel fmtQ (hashNode (L + 1) j (T L (2 * j)) (T L (2 * j + 1)))) _ dv (fun j hj => hb j hj)]
    simp only [relabel_bind, relabel_pure, relabel_sequenceFin, map_bind, map_pure, Functor.map_map,
      bind_map_left, bind_assoc, pure_bind]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun row => ?_
    congr 1
    rw [foldl_finRange_append, List.nil_append, List.range_succ (n := L + 1), List.map_append]
    simp only [List.map_cons, List.map_nil]
    congr 1
    · apply List.map_congr_left
      intro l hl
      rw [List.mem_range] at hl
      simp [show l ≠ L + 1 by omega]
    · simp only [levelList, if_true]
      refine congrArg (fun x => [x]) (List.ofFn_inj.mpr (funext fun j => ?_))
      simp [j.isLt]

end levels

/-! ## The masked region -/

theorem maskLevel_eq (seed : MasterSeed) (l : Nat) (hl : l < SphincsSecurity.maxLayerHeight)
    (T : Nat → Nat → Digest) :
    Ref.maskLevel (Ref.toList (n := 32) seed) l (levelList T SphincsSecurity.maxLayerHeight l) =
      (fun row : Nat → Digest =>
          List.ofFn fun j : Fin (2 ^ (SphincsSecurity.maxLayerHeight - l)) => dv (row j)) <$>
        relabel fmtQ (do
          let row ← sequenceFin (m := AComp) fun nodeIdx : Fin (2 ^ (SphincsSecurity.maxLayerHeight - l)) => do
            let mask ← SphincsSecurity.Seeded.maskSecret 0 seed l nodeIdx.val
            return T l nodeIdx.val ^^^ mask
          return fun nodeIdx : Nat =>
            if h : nodeIdx < 2 ^ (SphincsSecurity.maxLayerHeight - l) then row ⟨nodeIdx, h⟩ else 0) := by
  unfold Ref.maskLevel levelList
  rw [List.length_ofFn]
  have hbody : (fun (acc : List Ref.Val) (j : Nat) => do
      let mk ← Ref.hash16 (Ref.maskInput (Ref.toList (n := 32) seed) l j)
      pure (acc ++ [Ref.xorBytes ((List.ofFn fun j : Fin (2 ^ (SphincsSecurity.maxLayerHeight - l)) =>
        dv (T l j)).getD j []) mk])) = fun acc j => (do
      let mk ← Ref.hash16 (Ref.maskInput (Ref.toList (n := 32) seed) l j)
      pure (Ref.xorBytes ((List.ofFn fun j : Fin (2 ^ (SphincsSecurity.maxLayerHeight - l)) =>
        dv (T l j)).getD j []) mk)) >>= fun v => pure (acc ++ [v]) := by
    funext acc j; simp only [bind_assoc, pure_bind]
  rw [hbody]
  rw [foldlM_range_seq (fun nodeIdx : Fin (2 ^ (SphincsSecurity.maxLayerHeight - l)) => relabel fmtQ (do
      let mask ← SphincsSecurity.Seeded.maskSecret (m := AComp) 0 seed l nodeIdx.val
      return T l nodeIdx.val ^^^ mask)) _ dv (fun j hj => by
    have hj' : j < 2 ^ SphincsSecurity.maxLayerHeight :=
      lt_of_lt_of_le hj (Nat.pow_le_pow_right (by omega) (by omega))
    rw [getD_ofFn, dif_pos hj, hash16_mask seed l j hl hj']
    simp only [relabel_bind, relabel_pure, bind_map_left, map_bind, map_pure]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun mk => ?_
    rw [dv_xor])]
  simp only [relabel_bind, relabel_pure, relabel_sequenceFin, map_bind, map_pure, Functor.map_map,
    bind_map_left, bind_assoc, pure_bind]
  rw [map_eq_bind_pure_comp]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun row => ?_
  simp only [Function.comp]
  rw [foldl_finRange_append, List.nil_append]
  congr 1
  refine List.ofFn_inj.mpr (funext fun j => ?_)
  simp [j.isLt]

theorem toB_regionBytes (region : TopRegion) :
    toB (SphincsSecurity.regionBytes region) =
      (List.ofFn fun lv : Fin SphincsSecurity.maxLayerHeight =>
        (List.ofFn fun j => dv (region lv j)).flatten).flatten := by
  unfold SphincsSecurity.regionBytes
  rw [show toB = List.map UInt8.toBitVec from rfl, List.map_flatten, List.map_ofFn]
  refine congrArg List.flatten (List.ofFn_inj.mpr (funext fun lv => ?_))
  simp only [Function.comp]
  rw [show List.map UInt8.toBitVec = toB from rfl, toB_flatMap_dv, List.map_ofFn]
  rfl

theorem toB_macHashInput' (seed : MasterSeed) (region : TopRegion) :
    toB (SphincsSecurity.macHashInput 0 seed region) =
      Ref.macInput (Ref.toList (n := 32) seed) (toB (SphincsSecurity.regionBytes region)) := by
  unfold SphincsSecurity.macHashInput
  simp only [toB_append, toB_P, toB_seed, Ref.macInput, Ref.thInput, List.append_assoc]
  rw [show (⟨14#8, 0#8, 0#40, 0#32, 0#32⟩ : SphincsSecurity.TweakFields) =
    SphincsSecurity.tweakFields 14 0 0 0 0 from rfl, toB_tweakFields]

/-! ## Key generation -/

theorem keygenList_eq (seed : MasterSeed) :
    Ref.keygenList (Ref.toList (n := 32) seed) =
      (fun r => (dv r.1.root, cacheList r.2.1)) <$>
        relabel fmtQ (SphincsSecurity.Seeded.keygenFromSeed seed) := by
  unfold Ref.keygenList SphincsSecurity.Seeded.keygenFromSeed SphincsSecurity.Concrete.buildLayerTablePaired
  have h := buildLeaves_eq seed SphincsSecurity.topLayer SphincsSecurity.Concrete.rootTree ⟨0, by decide⟩
    (by decide) SphincsSecurity.Concrete.zeroEncoding [] (fun i => rfl)
  have e1 : ((SphincsSecurity.topLayer : Layer) : Nat) = 0 := rfl
  have e2 : ((SphincsSecurity.Concrete.rootTree : TreeIndex) : Nat) = 0 := rfl
  rw [e1, e2] at h
  rw [show Ref.topH = SphincsSecurity.layerHeight SphincsSecurity.topLayer from rfl, h]
  simp only [relabel_bind, relabel_pure, map_bind, bind_map_left, bind_assoc, pure_bind]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun f => ?_
  rw [ofFn_leaves f Prod.snd]
  unfold Ref.buildAllLevels
  rw [buildAllLevels_steps (Ref.nodeInput 0 0) (fun level nodeIdx left right =>
      SphincsSecurity.Concrete.tweakableHash (m := AComp) 0
        (.node SphincsSecurity.topLayer SphincsSecurity.Concrete.rootTree level nodeIdx)
        (SphincsSecurity.Concrete.nodePayload left right))
      (hash16_node SphincsSecurity.topLayer SphincsSecurity.Concrete.rootTree) _
      (fun k => if h : k < 2 ^ SphincsSecurity.layerHeight SphincsSecurity.topLayer then (f ⟨k, h⟩).2 else 0)
      _ le_rfl]
  rw [bind_map_left]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun T => ?_
  unfold SphincsSecurity.Seeded.maskRegion
  simp only [relabel_bind, relabel_pure, relabel_sequenceFin, map_bind, bind_assoc, pure_bind]
  rw [show SphincsSecurity.layerHeight SphincsSecurity.topLayer = SphincsSecurity.maxLayerHeight from rfl]
  rw [foldlM_range_seq_dep (fun level : Fin SphincsSecurity.maxLayerHeight => (do
        let x ← sequenceFin fun j : Fin (2 ^ (SphincsSecurity.maxLayerHeight - level.val)) => do
          let x ← relabel fmtQ (SphincsSecurity.Seeded.maskSecret (m := AComp) 0 seed level.val j.val)
          pure (T level.val j.val ^^^ x)
        pure fun nodeIdx =>
          if h : nodeIdx < 2 ^ (SphincsSecurity.maxLayerHeight - level.val) then x ⟨nodeIdx, h⟩ else 0 :
        OracleComp SigGolf.HashSpec (Nat → Digest)))
      _ (fun level row =>
        List.ofFn fun j : Fin (2 ^ (SphincsSecurity.maxLayerHeight - level.val)) => dv (row j))
      (fun l hl => by
        rw [getD_map_range_list _ _ _ (by omega), maskLevel_eq seed l hl T]
        simp only [relabel_bind, relabel_sequenceFin, relabel_pure])]
  rw [bind_map_left]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun rows => ?_
  rw [foldl_finRange_appendList, List.nil_append, relabel_oracleHash, toB_macHashInput',
    toB_regionBytes]
  have hreg : ((List.ofFn fun l : Fin SphincsSecurity.maxLayerHeight =>
      List.ofFn fun j : Fin (2 ^ (SphincsSecurity.maxLayerHeight - l.val)) => dv (rows l j)).flatten).flatten =
      (List.ofFn fun lv : Fin SphincsSecurity.maxLayerHeight =>
        (List.ofFn fun j : Fin (2 ^ (SphincsSecurity.maxLayerHeight - lv.val)) =>
          dv ((fun level (nodeIdx : Fin (2 ^ (SphincsSecurity.maxLayerHeight - level.val))) =>
            rows level nodeIdx.val) lv j)).flatten).flatten := by
    rw [List.flatten_flatten, List.map_ofFn]; rfl
  rw [hreg]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun tag => ?_
  simp only [map_pure]
  refine congrArg pure ?_
  rw [getD_map_range_list _ _ _ (by omega), levelList, getD_ofFn, dif_pos (by simp)]
  rw [cacheList, toB_regionBytes]

/-- **keygen**: the reference key generation is the relabelled abstract key generation; the
public key is the root and the cache is `cacheEnc` of the abstract cache. -/
theorem keygenRef_eq (sk : Bytes 32) :
    Ref.keygenRef sk =
      (fun kp => ((kp.1.root : Bytes 16), cacheEnc kp.2.1)) <$>
        relabel fmtQ (SphincsSecurity.Seeded.keygenFromSeed sk) := by
  unfold Ref.keygenRef
  rw [keygenList_eq sk]
  simp only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun kp => ?_
  simp only [Function.comp_apply, pure_bind]
  refine congrArg pure (Prod.ext ?_ rfl)
  exact Ref.ofList_toList (n := 16) kp.1.root

end SigGolfCandidate.Equiv
