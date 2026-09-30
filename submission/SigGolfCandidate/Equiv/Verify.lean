import SigGolfCandidate.Equiv.Sign

/-!
# Verification

`verifyRef m pk w` is the relabelled abstract verifier on the decoded witness `witDec w` and the
public key `⟨pk, 0⟩`; `verifySigRef` likewise on `sigCodec σ`.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolf (Byte Bytes Query)
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map relabel_query)
open SphincsSecurity (Digest Layer TreeIndex LeafIndex ChainIndex Encoding MasterSeed Index FtsTree
  FtsLeaf IndexGroup Message Signature)
open SphincsSecurity.Concrete (sequenceFin)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-! ## Folding a path -/

theorem testBit_iff (a l : Nat) : (a / 2 ^ l % 2 = 1) ↔ a.testBit l = true := by
  rw [Nat.testBit_eq_decide_div_mod_eq]; simp

theorem foldlM_congr_mem {m : Type → Type} [Monad m] {α β : Type} (l : List β) (f g : α → β → m α)
    (h : ∀ a b, b ∈ l → f a b = g a b) (init : α) : l.foldlM f init = l.foldlM g init := by
  induction l generalizing init with
  | nil => rfl
  | cons x l ih =>
    simp only [List.foldlM_cons]
    rw [h init x List.mem_cons_self]
    congr 1; funext a
    exact ih (fun a b hb => h a b (List.mem_cons_of_mem _ hb)) a

section fold

variable (node : Ref.NodeFmt) (hashNode : Nat → Nat → Digest → Digest → AComp Digest)
  (hnode : ∀ lam j l r, Ref.hash16 (node lam j (dv l) (dv r)) = dv <$> relabel padQ (hashNode lam j l r))

include hnode in
theorem foldPath_aux (leaf : Nat) (sib : Nat → Digest) (G : Nat → Digest → AComp Digest)
    (hG0 : ∀ v, G 0 v = pure v)
    (hG : ∀ l v, G (l + 1) v = G l v >>= fun cur =>
      if leaf.testBit l then hashNode (l + 1) (leaf / 2 ^ (l + 1)) (sib l) cur
      else hashNode (l + 1) (leaf / 2 ^ (l + 1)) cur (sib l))
    (ps : List Ref.Val) (n : Nat) (hps : ∀ l < n, ps.getD l [] = dv (sib l)) (v : Digest) :
    (List.range n).foldlM (fun v lam =>
      if leaf / 2 ^ lam % 2 = 1 then Ref.hash16 (node (lam + 1) (leaf / 2 ^ (lam + 1)) (ps.getD lam []) v)
      else Ref.hash16 (node (lam + 1) (leaf / 2 ^ (lam + 1)) v (ps.getD lam []))) (dv v) =
      dv <$> relabel padQ (G n v) := by
  induction n with
  | zero => simp [hG0]
  | succ n ih =>
    rw [List.range_succ, List.foldlM_append, ih (fun l hl => hps l (by omega))]
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure, bind_map_left, hG, relabel_bind, map_bind]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun cur => ?_
    rw [hps n (by omega)]
    by_cases hb : leaf.testBit n = true
    · rw [if_pos ((testBit_iff _ _).mpr hb), if_pos hb, hnode]
    · rw [if_neg (fun h => hb ((testBit_iff _ _).mp h)), if_neg hb, hnode]

include hnode in
/-- `Ref.foldPath` against any abstract fold with the same recursion. -/
theorem foldPath_eq (leaf : Nat) (sib : Nat → Digest) (G : Nat → Digest → AComp Digest)
    (hG0 : ∀ v, G 0 v = pure v)
    (hG : ∀ l v, G (l + 1) v = G l v >>= fun cur =>
      if leaf.testBit l then hashNode (l + 1) (leaf / 2 ^ (l + 1)) (sib l) cur
      else hashNode (l + 1) (leaf / 2 ^ (l + 1)) cur (sib l))
    (n : Nat) (v : Digest) :
    Ref.foldPath node leaf (dv v) ((List.range n).map fun l => dv (sib l)) =
      dv <$> relabel padQ (G n v) := by
  unfold Ref.foldPath
  simp only [List.length_map, List.length_range]
  exact foldPath_aux node hashNode hnode leaf sib G hG0 hG _ n (fun l hl => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]; rfl) v

end fold

/-! ## Witness fields -/

section wit

variable (wl : List Byte) (hl : wl.length = 7756)

include hl

theorem witRho_eq : Ref.witRho wl = dv (sigOfWit wl).randomness :=
  (dv_ofList_slice _ _ (by omega)).symm

theorem witFtsSecret_eq (k : FtsTree) : Ref.witFtsSecret wl k = dv ((sigOfWit wl).ftsSecret k) :=
  (dv_ofList_slice _ _ (by have := fts_lt k; omega)).symm

theorem witFtsPath_eq (k : FtsTree) :
    Ref.witFtsPath wl k = (List.range SphincsSecurity.ftsTreeHeight).map fun l =>
      dv (if h : l < SphincsSecurity.ftsTreeHeight then (sigOfWit wl).ftsPath k ⟨l, h⟩ else 0) := by
  unfold Ref.witFtsPath
  apply List.map_congr_left
  intro l hl'
  have hl2 : l < SphincsSecurity.ftsTreeHeight := List.mem_range.mp hl'
  rw [dif_pos hl2]
  have hl3 : l < 10 := hl2
  exact (dv_ofList_slice _ _ (by have := fts_lt k; omega)).symm

theorem witChain_eq (lay : Layer) (i : ChainIndex) :
    Ref.witChain wl lay i = dv (((sigOfWit wl).layers lay).chainValues i) :=
  (dv_ofList_slice _ _ (by
    have := lay_lt lay; have := chain_lt i; unfold Ref.witLayerOff; omega)).symm

theorem witPath_eq (lay : Layer) :
    Ref.witPath wl lay = (List.range (SphincsSecurity.layerHeight lay)).map fun l =>
      dv (SphincsSecurity.Concrete.signaturePath (sigOfWit wl) lay l) := by
  unfold Ref.witPath
  rw [height_eq]
  apply List.map_congr_left
  intro l hl'
  have hl2 : l < SphincsSecurity.layerHeight lay := List.mem_range.mp hl'
  unfold SphincsSecurity.Concrete.signaturePath
  rw [dif_pos hl2]
  have hlay := lay_lt lay
  have hb : 752 * lay.val + 16 * l ≤ 4576 := by
    by_cases h6 : lay.val = 6
    · have h4 : SphincsSecurity.layerHeight lay = 4 := by
        unfold SphincsSecurity.layerHeight
        rw [if_neg (show ¬ (lay.val + 1 < SphincsSecurity.numLayers) from
          show ¬ (lay.val + 1 < 7) by omega)]
      omega
    · have := layerHeight_le lay; omega
  exact (dv_ofList_slice _ _ (by unfold Ref.witLayerOff; omega)).symm

omit hl in
theorem witCounter_eq (lay : Layer) :
    BitVec.ofNat SphincsSecurity.counterBits (Ref.witCounter wl lay) = ((sigOfWit wl).layers lay).counter :=
  rfl

theorem witCounter_toNat (lay : Layer) :
    ((sigOfWit wl).layers lay).counter.toNat = Ref.witCounter wl lay := by
  rw [← witCounter_eq wl lay]
  simp only [BitVec.toNat_ofNat, SphincsSecurity.counterBits]
  apply Nat.mod_eq_of_lt
  have := Ref.leNat_lt (Ref.slice wl (Ref.witCounters + 4 * lay.val) 4)
  rw [length_slice _ _ _ (by have := lay_lt lay; unfold Ref.witCounters; omega)] at this
  unfold Ref.witCounter; omega

theorem countersOk_eq :
    Ref.countersOk wl = decide (SphincsSecurity.Concrete.CountersInRange (sigOfWit wl)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  unfold Ref.countersOk SphincsSecurity.Concrete.CountersInRange
  rw [List.all_eq_true]
  constructor
  · intro h lay
    have := h lay.val (List.mem_range.mpr (lay_lt lay))
    rw [witCounter_toNat wl hl]
    simpa [Ref.cMax, SphincsSecurity.encodingAttemptLimit] using of_decide_eq_true this
  · intro h lay hlay
    have := h ⟨lay, List.mem_range.mp hlay⟩
    rw [witCounter_toNat wl hl] at this
    exact decide_eq_true (by simpa [Ref.cMax, SphincsSecurity.encodingAttemptLimit] using this)

end wit

/-! ## The few-time forest -/

theorem ftsRoot_eq (index : Index) (tree : FtsTree) (leaf : FtsLeaf) (secret : Digest)
    (path : Fin SphincsSecurity.ftsTreeHeight → Digest) :
    Ref.ftsRoot tree index leaf (dv secret) ((List.range SphincsSecurity.ftsTreeHeight).map fun l =>
        dv (if h : l < SphincsSecurity.ftsTreeHeight then path ⟨l, h⟩ else 0)) =
      dv <$> relabel padQ (do
        let value ← SphincsSecurity.Concrete.ftsLeafHash (m := AComp) 0 index tree leaf secret
        SphincsSecurity.Concrete.ftsFold 0 index tree leaf path SphincsSecurity.ftsTreeHeight value) := by
  unfold Ref.ftsRoot
  rw [hash16_ftsLeaf, relabel_bind, bind_map_left, map_bind]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun v => ?_
  exact foldPath_eq (Ref.ftsNodeInput tree index) (fun lam j l r =>
      SphincsSecurity.Concrete.tweakableHash (m := AComp) 0 (.ftsNode index tree lam j)
        (SphincsSecurity.Concrete.nodePayload l r)) (hash16_ftsNode index tree) leaf
    (fun l => if h : l < SphincsSecurity.ftsTreeHeight then path ⟨l, h⟩ else 0)
    (fun n v => SphincsSecurity.Concrete.ftsFold (m := AComp) 0 index tree leaf path n v)
    (fun v => rfl) (fun l v => rfl) _ v

theorem verifyFors_eq (wl : List Byte) (hl : wl.length = 7756) (d : SphincsSecurity.MessageDigest) :
    Ref.verifyFors wl d.toNat =
      (fun roots : FtsTree → Digest => List.ofFn fun k => dv (roots k)) <$> relabel padQ
        (sequenceFin (m := AComp) fun tree => do
          let leaf := SphincsSecurity.Concrete.digestLeaves d (SphincsSecurity.Concrete.ftsIndexOf tree)
          let value ← SphincsSecurity.Concrete.ftsLeafHash 0 (SphincsSecurity.Concrete.digestIndex d)
            tree leaf ((sigOfWit wl).ftsSecret tree)
          SphincsSecurity.Concrete.ftsFold 0 (SphincsSecurity.Concrete.digestIndex d) tree leaf
            ((sigOfWit wl).ftsPath tree) SphincsSecurity.ftsTreeHeight value) := by
  unfold Ref.verifyFors
  rw [relabel_sequenceFin, show Ref.ftsTrees = SphincsSecurity.ftsTrees - 1 from rfl]
  rw [foldlM_range_seq (fun tree : FtsTree => relabel padQ (do
      let leaf := SphincsSecurity.Concrete.digestLeaves d (SphincsSecurity.Concrete.ftsIndexOf tree)
      let value ← SphincsSecurity.Concrete.ftsLeafHash (m := AComp) 0
        (SphincsSecurity.Concrete.digestIndex d) tree leaf ((sigOfWit wl).ftsSecret tree)
      SphincsSecurity.Concrete.ftsFold 0 (SphincsSecurity.Concrete.digestIndex d) tree leaf
        ((sigOfWit wl).ftsPath tree) SphincsSecurity.ftsTreeHeight value)) _ dv (fun j hj => by
    have hu : Ref.uOf d.toNat j =
        (SphincsSecurity.Concrete.digestLeaves d (SphincsSecurity.Concrete.ftsIndexOf ⟨j, hj⟩)).val := by
      rw [uOf_eq]; unfold uFun
      rw [dif_pos (by simp [SphincsSecurity.ftsTrees] at hj ⊢; omega)]
      rfl
    rw [idxOf_eq, hu, witFtsSecret_eq wl hl ⟨j, hj⟩, witFtsPath_eq wl hl ⟨j, hj⟩]
    exact ftsRoot_eq _ ⟨j, hj⟩ _ _ _) (fun acc _ v => acc ++ [v])]
  refine congrArg (· <$> _) ?_
  funext f
  rw [foldl_finRange_append, List.nil_append]

/-! ## The layers -/

theorem verifyLeaf_eq (wl : List Byte) (hl : wl.length = 7756) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (enc : Encoding) :
    Ref.verifyLeaf wl lay tree leaf (List.ofFn fun i => (enc i).val) =
      dv <$> relabel padQ (do
        let endpoints ← sequenceFin (m := AComp) fun c =>
          SphincsSecurity.Concrete.recoverChain 0 lay tree leaf c (enc c)
            (((sigOfWit wl).layers lay).chainValues c)
        SphincsSecurity.Concrete.leafHash 0 lay tree leaf endpoints) := by
  unfold Ref.verifyLeaf
  rw [show Ref.nChains = SphincsSecurity.numChains from rfl]
  rw [foldlM_range_seq (fun c : ChainIndex => relabel padQ
      (SphincsSecurity.Concrete.recoverChain (m := AComp) 0 lay tree leaf c (enc c)
        (((sigOfWit wl).layers lay).chainValues c))) _ dv (fun j hj => by
    rw [getD_ofFn, dif_pos hj, witChain_eq wl hl lay ⟨j, hj⟩]
    have hd : (enc ⟨j, hj⟩).val ≤ 7 := by
      have := (enc ⟨j, hj⟩).isLt
      simp [SphincsSecurity.chainLength, SphincsSecurity.winternitzBits] at this; omega
    unfold Ref.chainFrom SphincsSecurity.Concrete.recoverChain
    rw [chainFold_eq lay tree leaf ⟨j, hj⟩ _ _ (by omega),
      show SphincsSecurity.chainLength - 1 - (enc ⟨j, hj⟩).val = 7 - (enc ⟨j, hj⟩).val by
        simp [SphincsSecurity.chainLength, SphincsSecurity.winternitzBits]]) (fun acc _ v => acc ++ [v])]
  simp only [relabel_bind, relabel_sequenceFin, map_bind, bind_map_left]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun f => ?_
  rw [foldl_finRange_append, List.nil_append, hash16_leaf]

theorem verifyLayers_eq (wl : List Byte) (hl : wl.length = 7756) (index : Index) (n : Nat)
    (hn : n ≤ 7) (M : Digest) :
    Ref.verifyLayers wl index n (dv M) =
      Option.map dv <$> relabel padQ
        (SphincsSecurity.Concrete.verifyLayers (m := AComp) 0 index (sigOfWit wl) n M) := by
  induction n generalizing M with
  | zero => simp [Ref.verifyLayers, SphincsSecurity.Concrete.verifyLayers]
  | succ n ih =>
    let lay : Layer := ⟨n, show n < 7 by omega⟩
    have hr := route_eq index lay
    simp only [lay] at hr
    unfold Ref.verifyLayers SphincsSecurity.Concrete.verifyLayers
    rw [dif_pos (show n < SphincsSecurity.numLayers by show n < 7; omega)]
    simp only [hr]
    unfold SphincsSecurity.Concrete.otsLeaf SphincsSecurity.Concrete.encode
    rw [hash16_enc lay, witCounter_eq wl lay]
    simp only [relabel_bind, relabel_pure, bind_map_left, map_bind, bind_assoc, pure_bind]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun d => ?_
    rw [decodeDigits_dv]
    cases hd : SphincsSecurity.TargetSum.decodeDigest d with
    | none => simp
    | some enc =>
      simp only [Option.map_some]
      rw [verifyLeaf_eq wl hl lay _ _ enc]
      simp only [relabel_bind, relabel_pure, bind_map_left, map_bind, bind_assoc, pure_bind]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun ends => ?_
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun v => ?_
      rw [witPath_eq wl hl lay]
      have hfold := foldPath_eq (Ref.nodeInput lay (SphincsSecurity.Concrete.treeIndexAt index lay))
        (fun lam j l r => SphincsSecurity.Concrete.tweakableHash (m := AComp) 0
          (.node lay (SphincsSecurity.Concrete.treeIndexAt index lay) lam j)
          (SphincsSecurity.Concrete.nodePayload l r))
        (hash16_node lay _) (SphincsSecurity.Concrete.leafIndexAt index lay)
        (SphincsSecurity.Concrete.signaturePath (sigOfWit wl) lay)
        (fun k v => SphincsSecurity.Concrete.treeFold (m := AComp) 0 lay
          (SphincsSecurity.Concrete.treeIndexAt index lay) (SphincsSecurity.Concrete.leafIndexAt index lay)
          (SphincsSecurity.Concrete.signaturePath (sigOfWit wl) lay) k v)
        (fun v => rfl) (fun l v => rfl) (SphincsSecurity.layerHeight lay) v
      rw [hfold, bind_map_left]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun root => ?_
      exact ih (by omega) root

/-! ## The verifier -/

/-- **verify**: `verifyRef m pk w` is the relabelled abstract verifier on the public key
`⟨pk, 0⟩` and the decoded witness. -/
theorem verifyRef_eq (m : Bytes 32) (pk : Bytes 16) (w : Bytes 7756) :
    Ref.verifyRef m pk w =
      relabel padQ (SphincsSecurity.Concrete.verify (m := AComp) ⟨pk, 0⟩ m (witDec w)) := by
  have hl : (Ref.toList w).length = 7756 := Ref.length_toList w
  unfold Ref.verifyRef Ref.verifyList SphincsSecurity.Concrete.verify SphincsSecurity.Concrete.verifyCore
  rw [countersOk_eq _ hl]
  unfold witDec
  by_cases hc : SphincsSecurity.Concrete.CountersInRange (sigOfWit (Ref.toList w))
  · simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]
    rw [witRho_eq _ hl, digest_eq pk _ m, relabel_bind, bind_map_left]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun d => ?_
    rw [admissible_eq]
    by_cases ha : SphincsSecurity.Concrete.Admissible d
    · simp only [ha, decide_true, Bool.not_true, Bool.false_eq_true, if_false, not_true_eq_false]
      unfold SphincsSecurity.Concrete.ftsRecover
      rw [verifyFors_eq _ hl d, idxOf_eq]
      simp only [relabel_bind, bind_map_left, bind_assoc]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun roots => ?_
      rw [hash16_roots, bind_map_left]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun key => ?_
      rw [show Ref.nLayers = SphincsSecurity.numLayers from rfl,
        verifyLayers_eq _ hl _ SphincsSecurity.numLayers (le_refl 7), bind_map_left]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
      rcases r with _ | root
      · rfl
      · simp only [Option.map_some, relabel_pure]
        refine congrArg pure ?_
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
        exact ⟨fun h => dv_injective h, fun h => by rw [h]; rfl⟩
    · simp only [ha, decide_false, Bool.not_false, if_true, not_false_eq_true, relabel_pure]
  · simp only [hc, decide_false, Bool.not_false, if_true, if_false, relabel_pure]

/-- **verify**, with the witness decoded through the signature codec. -/
theorem verifyRef_eq' (m : Bytes 32) (pk : Bytes 16) (w : Bytes 7756) :
    Ref.verifyRef m pk w =
      relabel padQ (SphincsSecurity.Concrete.verify (m := AComp) ⟨pk, 0⟩ m
        (sigCodec (Ref.unexpandRef w))) := by
  rw [verifyRef_eq, witDec_eq]

/-- **verify** on a signature (through `expandRef`). -/
theorem verifySigRef_eq (m : Bytes 32) (pk : Bytes 16) (σ : Bytes 7756) :
    Ref.verifySigRef m pk σ =
      relabel padQ (SphincsSecurity.Concrete.verify (m := AComp) ⟨pk, 0⟩ m (sigCodec σ)) := by
  rw [Ref.verifySigRef, verifyRef_eq, witDec_expandRef]

end SigGolfCandidate.Equiv
