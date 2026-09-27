import SigGolfCandidate.Equiv.Layers

/-!
# Verification (PORS+FP)

`verifyRef_eq`: for every witness, the reference verifier is the relabelled abstract verifier on
the public key `⟨pk, 0⟩` and the decoded witness `witDec w` (rejecting paths included).
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolf (Byte Bytes Query)
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map relabel_query)
open SphincsSecurity (Digest Layer TreeIndex LeafIndex ChainIndex Encoding MasterSeed Index FtsTree
  FtsLeaf IndexGroup Message Signature LayerSignature)
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
  (hnode : ∀ lam j l r, Ref.hash16 (node lam j (dv l) (dv r)) = dv <$> relabel fmtQ (hashNode lam j l r))

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
      dv <$> relabel fmtQ (G n v) := by
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
      dv <$> relabel fmtQ (G n v) := by
  unfold Ref.foldPath
  simp only [List.length_map, List.length_range]
  exact foldPath_aux node hashNode hnode leaf sib G hG0 hG _ n (fun l hl => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl]; rfl) v

end fold

/-! ## Witness fields -/

section wit

variable (wl : List Byte) (hl : wl.length = 6348)

theorem wit_bound (lay : Layer) :
    Ref.witLayerOff lay.val + 672 + 16 * SphincsSecurity.layerHeight lay ≤ Ref.witCounters := by
  fin_cases lay <;> decide

theorem lay_lt (lay : Layer) : lay.val < 5 := lay.isLt
theorem chain_lt (i : ChainIndex) : i.val < 42 := i.isLt

include hl

theorem witRho_eq : Ref.witRho wl = dv (witSig wl).randomness :=
  (dv_ofList_slice _ _ (by omega)).symm

theorem witSecret_eq (s : Nat) (hs : s < 15) :
    Ref.witSecret wl s = dv (Ref.ofList 16 (Ref.witSecret wl s)) :=
  (dv_ofList_slice _ _ (by unfold Ref.wSec; omega)).symm

theorem witChain_eq (lay : Layer) (i : ChainIndex) :
    Ref.witChain wl lay.val i.val = dv (((witSig wl).layers lay).chainValues i) :=
  (dv_ofList_slice _ _ (by
    have := wit_bound lay; have := chain_lt i; have := Ref.witCounters_eq
    omega)).symm

theorem witPath_eq (lay : Layer) :
    Ref.witPath wl lay.val = (List.range (SphincsSecurity.layerHeight lay)).map fun l =>
      dv (SphincsSecurity.Concrete.signaturePath (witSig wl) lay l) := by
  unfold Ref.witPath
  rw [height_eq]
  apply List.map_congr_left
  intro l hl'
  have hl2 : l < SphincsSecurity.layerHeight lay := List.mem_range.mp hl'
  unfold SphincsSecurity.Concrete.signaturePath
  rw [dif_pos hl2]
  have hb := wit_bound lay
  have hc := Ref.witCounters_eq
  exact (dv_ofList_slice _ _ (by omega)).symm

omit hl in
theorem witCounter_eq (lay : Layer) :
    BitVec.ofNat SphincsSecurity.counterBits (Ref.witCounter wl lay.val) = ((witSig wl).layers lay).counter :=
  rfl

theorem witCounter_toNat (lay : Layer) :
    ((witSig wl).layers lay).counter.toNat = Ref.witCounter wl lay.val := by
  rw [← witCounter_eq wl lay]
  simp only [BitVec.toNat_ofNat, SphincsSecurity.counterBits]
  apply Nat.mod_eq_of_lt
  have := Ref.leNat_lt (Ref.slice wl (Ref.witCounters + 4 * lay.val) 4)
  rw [length_slice _ _ _ (by have := lay_lt lay; have := Ref.witCounters_eq; omega)] at this
  unfold Ref.witCounter; omega

theorem countersOk_eq :
    Ref.countersOk wl = decide (SphincsSecurity.Concrete.CountersInRange (witSig wl)) := by
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

/-! ## The layers -/

theorem verifyLeaf_eq (wl : List Byte) (hl : wl.length = 6348) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (enc : Encoding) :
    Ref.verifyLeaf wl lay tree leaf (List.ofFn fun i => (enc i).val) =
      dv <$> relabel fmtQ (do
        let endpoints ← sequenceFin (m := AComp) fun c =>
          SphincsSecurity.Concrete.recoverChain 0 lay tree leaf c (enc c)
            (((witSig wl).layers lay).chainValues c)
        SphincsSecurity.Concrete.leafHash 0 lay tree leaf endpoints) := by
  unfold Ref.verifyLeaf
  rw [show Ref.nChains = SphincsSecurity.numChains from rfl]
  rw [foldlM_range_seq (fun c : ChainIndex => relabel fmtQ
      (SphincsSecurity.Concrete.recoverChain (m := AComp) 0 lay tree leaf c (enc c)
        (((witSig wl).layers lay).chainValues c))) _ dv (fun j hj => by
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

theorem verifyLayers_eq (wl : List Byte) (hl : wl.length = 6348) (index : Index) (n : Nat)
    (hn : n ≤ 5) (M : Digest) :
    Ref.verifyLayers wl index n (dv M) =
      Option.map dv <$> relabel fmtQ
        (SphincsSecurity.Concrete.verifyLayers (m := AComp) 0 index (witSig wl) n M) := by
  induction n generalizing M with
  | zero => simp [Ref.verifyLayers, SphincsSecurity.Concrete.verifyLayers]
  | succ n ih =>
    let lay : Layer := ⟨n, show n < 5 by omega⟩
    have hr := route_eq index lay
    simp only [lay] at hr
    unfold Ref.verifyLayers SphincsSecurity.Concrete.verifyLayers
    rw [dif_pos (show n < SphincsSecurity.numLayers by show n < 5; omega)]
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
        (SphincsSecurity.Concrete.signaturePath (witSig wl) lay)
        (fun k v => SphincsSecurity.Concrete.treeFold (m := AComp) 0 lay
          (SphincsSecurity.Concrete.treeIndexAt index lay) (SphincsSecurity.Concrete.leafIndexAt index lay)
          (SphincsSecurity.Concrete.signaturePath (witSig wl) lay) k v)
        (fun v => rfl) (fun l v => rfl) (SphincsSecurity.layerHeight lay) v
      rw [hfold, bind_map_left]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun root => ?_
      exact ih (by omega) root


/-! ## The PORS stack machine -/

open SphincsSecurity.Concrete (RecoverState PendingHash)

section pors

variable (index : Index) (wl : List Byte)

/-- A segment fold, as `Ref.segFolds` does it. -/
theorem segFolds_aux (seg : SphincsSecurity.Segment) (ptr : Nat)
    (hnodes : ∀ i (h : i < seg.folds.val), seg.nodes ⟨i, h⟩ = wdig wl (ptr + 8 + 16 * i)) :
    ∀ (r p : Nat) (cur : Digest) (E : Nat), p + r ≤ seg.folds.val →
      (p = 0 → 0 < r → seg.parity = decide (E % 2 = 1)) →
      (List.range' p r).foldlM (fun (st : Ref.Val × Nat) i =>
        let sib := Ref.wbytes wl (ptr + 8 + 16 * i) 16
        if st.2 % 2 = 1 then do
          let v ← Ref.hash16 (Ref.porsNodeInput index (st.2 / 2) sib st.1)
          pure (v, st.2 / 2)
        else do
          let v ← Ref.hash16 (Ref.porsNodeInput index (st.2 / 2) st.1 sib)
          pure (v, st.2 / 2)) (dv cur, E) =
      (fun q : Digest × Nat => (dv q.1, q.2)) <$> relabel fmtQ
        (SphincsSecurity.Concrete.foldSegment (m := AComp) 0 index seg r p cur E) := by
  intro r
  induction r with
  | zero => intro p cur E _ _; simp [SphincsSecurity.Concrete.foldSegment]
  | succ r ih =>
    intro p cur E hpr hpar
    rw [List.range'_succ, List.foldlM_cons]
    have hsib : Ref.wbytes wl (ptr + 8 + 16 * p) 16 = dv (seg.node p) := by
      unfold SphincsSecurity.Segment.node
      rw [dif_pos (by omega), hnodes p (by omega), dv_wdig]
    have hright : (if p = 0 then seg.parity else decide (E % 2 = 1)) = decide (E % 2 = 1) := by
      split_ifs with h0
      · exact hpar h0 (by omega)
      · rfl
    simp only [SphincsSecurity.Concrete.foldSegment, hright, hsib]
    by_cases hE : E % 2 = 1
    · simp only [hE, if_true, decide_true, SphincsSecurity.Concrete.foldPayload]
      rw [hash16_porsNode]
      simp only [relabel_bind, bind_map_left, map_bind, bind_assoc, pure_bind]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun v => ?_
      exact ih (p + 1) v (E / 2) (by omega) (fun h => absurd h (by omega))
    · simp only [hE, if_false, decide_false, SphincsSecurity.Concrete.foldPayload, Bool.false_eq_true]
      rw [hash16_porsNode]
      simp only [relabel_bind, bind_map_left, map_bind, bind_assoc, pure_bind]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun v => ?_
      exact ih (p + 1) v (E / 2) (by omega) (fun h => absurd h (by omega))

theorem segFolds_eq (seg : SphincsSecurity.Segment) (ptr : Nat)
    (hnodes : ∀ i (h : i < seg.folds.val), seg.nodes ⟨i, h⟩ = wdig wl (ptr + 8 + 16 * i))
    (a : Nat) (cur : Digest) (E : Nat) (ha : a = seg.folds.val)
    (hpar : 0 < a → seg.parity = decide (E % 2 = 1)) :
    Ref.segFolds index wl ptr a (dv cur) E =
      (fun q : Digest × Nat => (dv q.1, q.2)) <$> relabel fmtQ
        (SphincsSecurity.Concrete.foldSegment (m := AComp) 0 index seg a 0 cur E) := by
  unfold Ref.segFolds
  rw [List.range_eq_range']
  exact segFolds_aux index wl seg ptr hnodes a 0 cur E (by omega) (fun _ h => hpar h)

/-- The reference's stack of an abstract stack. -/
def encStack (s : List (Digest × Nat)) : List (Ref.Val × Nat) := s.map fun p => (dv p.1, p.2)

/-- The reference's pending hash of an abstract one. -/
def encP : PendingHash → Ref.Pending
  | .leaf v s => .leaf v (dv s)
  | .merge H l => .merge H (dv l)

/-- The reference's `segLoop` result of an abstract state. -/
def encR (st : RecoverState) : Nat × Nat × Nat × Ref.Val × List (Ref.Val × Nat) :=
  (segPtr wl st.segment, st.heap, st.folds, dv st.node, encStack st.stack)

/-- The hash a segment performs before its folds (abstract). -/
def pendA (ap : PendingHash) (cur : Digest) : AComp Digest :=
  match ap with
  | .leaf v s => SphincsSecurity.Concrete.ftsLeafHash 0 index SphincsSecurity.Concrete.porsTree v s
  | .merge H l => SphincsSecurity.Concrete.tweakableHash 0
      (.ftsNode index SphincsSecurity.Concrete.porsTree H) (SphincsSecurity.Concrete.nodePayload l cur)

theorem pend_eq (ap : PendingHash) (cur : Digest) :
    Ref.pendingHash index (dv cur) (encP ap) = dv <$> relabel fmtQ (pendA index ap cur) := by
  cases ap with
  | leaf v s => exact hash16_porsLeaf index v s
  | merge H l => exact hash16_porsNode index H l cur

/-- What `recoverSegments` does after a segment's folds. -/
def segCont (segments : Fin SphincsSecurity.ftsSegments → SphincsSecurity.Segment) (fuel : Nat)
    (st : RecoverState) (seg : SphincsSecurity.Segment) (x : Digest × Nat) : AComp (Option RecoverState) :=
  if seg.merge then
    match st.stack with
    | [] => pure none
    | (left, sibling) :: rest =>
      if sibling = x.2 then
        SphincsSecurity.Concrete.recoverSegments 0 index segments fuel (.merge (x.2 / 2) left)
          ⟨x.1, x.2 / 2, rest, st.folds + seg.folds.val, st.segment + 1⟩
      else pure none
  else pure (some ⟨x.1, x.2, st.stack, st.folds + seg.folds.val, st.segment + 1⟩)

theorem recoverSegments_step (segments : Fin SphincsSecurity.ftsSegments → SphincsSecurity.Segment)
    (fuel : Nat) (ap : PendingHash) (st : RecoverState) (h : st.segment < SphincsSecurity.ftsSegments) :
    SphincsSecurity.Concrete.recoverSegments (m := AComp) 0 index segments (fuel + 1) ap st =
      if SphincsSecurity.ftsTreeHeight < (segments ⟨st.segment, h⟩).folds.val then pure none
      else if (segments ⟨st.segment, h⟩).folds.val ≠ 0 ∧
          (segments ⟨st.segment, h⟩).parity ≠ decide (st.heap % 2 = 1) then pure none
      else
        pendA index ap st.node >>= fun start =>
        SphincsSecurity.Concrete.foldSegment 0 index (segments ⟨st.segment, h⟩)
          (segments ⟨st.segment, h⟩).folds.val 0 start st.heap >>= fun x =>
        segCont index segments fuel st (segments ⟨st.segment, h⟩) x := by
  rw [SphincsSecurity.Concrete.recoverSegments, dif_pos h]
  cases ap <;> rfl

theorem segAt_folds (p : Nat) : ((segAt wl p).folds.val) = Ref.wbyte wl p % 16 := rfl
theorem segAt_merge (p : Nat) : (segAt wl p).merge = decide (Ref.wbyte wl p / 16 % 2 = 1) := rfl
theorem segAt_parity (p : Nat) : (segAt wl p).parity =
    (decide (Ref.wbyte wl p / 32 % 2 = 1) && decide (Ref.wbyte wl p % 16 ≠ 0)) := rfl

theorem segment_eq (j E folds : Nat) (ap : PendingHash) (cur : Digest) :
    Ref.segment index wl (segPtr wl j) E folds (encP ap) (dv cur) =
      if 14 < (segAt wl (segPtr wl j)).folds.val then pure none
      else if (segAt wl (segPtr wl j)).folds.val ≠ 0 ∧
          (segAt wl (segPtr wl j)).parity ≠ decide (E % 2 = 1) then pure none
      else (fun x : Digest × Nat => some (segPtr wl (j + 1), x.2, folds + (segAt wl (segPtr wl j)).folds.val,
          dv x.1, (segAt wl (segPtr wl j)).merge)) <$>
        relabel fmtQ (pendA index ap cur >>= fun start =>
          SphincsSecurity.Concrete.foldSegment 0 index (segAt wl (segPtr wl j))
            (segAt wl (segPtr wl j)).folds.val 0 start E) := by
  rw [segAt_folds, segAt_merge, segAt_parity]
  unfold Ref.segment
  simp only [gt_iff_lt, Ref.porsH]
  generalize hb : Ref.wbyte wl (segPtr wl j) = b
  by_cases h1 : 14 < b % 16
  · simp [h1]
  · simp only [h1, if_false]
    have ht : b / 32 % 2 < 2 := Nat.mod_lt _ (by decide)
    have hE : E % 2 < 2 := Nat.mod_lt _ (by decide)
    by_cases h2 : 0 < b % 16 ∧ b / 32 % 2 ≠ E % 2
    · have h2' : b % 16 ≠ 0 ∧ (decide (b / 32 % 2 = 1) && decide (b % 16 ≠ 0)) ≠ decide (E % 2 = 1) := by
        refine ⟨by omega, ?_⟩
        have hne : b % 16 ≠ 0 := by omega
        simp only [hne, ne_eq, not_false_eq_true, decide_true, Bool.and_true]
        intro h
        have := congrArg (fun x : Bool => x = true) h
        simp only [decide_eq_true_eq, eq_iff_iff] at this
        omega
      rw [if_pos h2, if_pos h2']
    · have h2' : ¬ (b % 16 ≠ 0 ∧ (decide (b / 32 % 2 = 1) && decide (b % 16 ≠ 0)) ≠ decide (E % 2 = 1)) := by
        rintro ⟨hne, hpar⟩
        apply hpar
        simp only [hne, ne_eq, not_false_eq_true, decide_true, Bool.and_true]
        have : b / 32 % 2 = E % 2 := by omega
        rw [this]
      rw [if_neg h2, if_neg h2']
      have hpar : 0 < b % 16 → (segAt wl (segPtr wl j)).parity = decide (E % 2 = 1) := by
        intro ha
        rw [segAt_parity, hb]
        simp only [show b % 16 ≠ 0 by omega, ne_eq, not_false_eq_true, decide_true, Bool.and_true]
        have : b / 32 % 2 = E % 2 := by omega
        rw [this]
      rw [pend_eq, bind_map_left]
      simp only [relabel_bind, map_bind]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun start => ?_
      rw [segFolds_eq index wl (segAt wl (segPtr wl j)) (segPtr wl j) (fun i h => rfl) (b % 16) start E
        (by rw [segAt_folds, hb]) hpar]
      rw [bind_map_left, map_eq_bind_pure_comp]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun x => ?_
      have hp : segPtr wl (j + 1) = segPtr wl j + 8 + 16 * (b % 16) := by
        rw [segPtr, hb]
      simp only [Function.comp, hp]

theorem segLoop_bind {β : Type}
    (Kr : Option (Nat × Nat × Nat × Ref.Val × List (Ref.Val × Nat)) → OracleComp SigGolf.HashSpec β)
    (Ka : Option RecoverState → AComp β) :
    ∀ (astack : List (Digest × Nat)) (fuel : Nat) (ap : PendingHash) (st : RecoverState),
      st.stack = astack → st.segment + astack.length < 29 → astack.length < fuel →
      (∀ st' : RecoverState, st'.segment + st'.stack.length = st.segment + astack.length + 1 →
        Kr (some (encR wl st')) = relabel fmtQ (Ka (some st'))) →
      Kr none = relabel fmtQ (Ka none) →
      Ref.segLoop index wl (segPtr wl st.segment) st.heap st.folds (encP ap) (dv st.node)
          (encStack astack) >>= Kr =
        relabel fmtQ (SphincsSecurity.Concrete.recoverSegments (m := AComp) 0 index
          (witFts wl).segments fuel ap st >>= Ka) := by
  intro astack
  induction astack with
  | nil =>
    intro fuel ap st hst hseg hfuel hK hK0
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hj : st.segment < SphincsSecurity.ftsSegments := by
      simp at hseg; show st.segment < 29; omega
    rw [recoverSegments_step index _ fuel ap st hj]
    have hsg : (witFts wl).segments ⟨st.segment, hj⟩ = segAt wl (segPtr wl st.segment) := rfl
    rw [hsg]
    simp only [encStack, List.map_nil]
    rw [Ref.segLoop, segment_eq]
    by_cases h1 : SphincsSecurity.ftsTreeHeight < (segAt wl (segPtr wl st.segment)).folds.val
    · rw [if_pos h1, if_pos (show (14 : Nat) < _ from h1)]
      simp only [pure_bind, hK0]
    · rw [if_neg h1, if_neg (show ¬ (14 : Nat) < _ from h1)]
      by_cases h2 : (segAt wl (segPtr wl st.segment)).folds.val ≠ 0 ∧
          (segAt wl (segPtr wl st.segment)).parity ≠ decide (st.heap % 2 = 1)
      · simp only [if_pos h2, pure_bind, hK0]
      · rw [if_neg h2, if_neg h2]
        rw [bind_map_left]
        simp only [bind_assoc, relabel_bind]
        refine bind_congr (m := OracleComp SigGolf.HashSpec) fun start => ?_
        refine bind_congr (m := OracleComp SigGolf.HashSpec) fun x => ?_
        rw [← relabel_bind]
        unfold segCont
        rw [hst]
        by_cases hm : (segAt wl (segPtr wl st.segment)).merge = true
        · simp only [hm, if_true, pure_bind, hK0]
        · simp only [hm, Bool.false_eq_true, if_false, pure_bind]
          exact hK ⟨x.1, x.2, [], st.folds + (segAt wl (segPtr wl st.segment)).folds.val, st.segment + 1⟩
            (by simp)
  | cons top rest ih =>
    intro fuel ap st hst hseg hfuel hK hK0
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hj : st.segment < SphincsSecurity.ftsSegments := by
      simp at hseg; show st.segment < 29; omega
    rw [recoverSegments_step index _ fuel ap st hj]
    have hsg : (witFts wl).segments ⟨st.segment, hj⟩ = segAt wl (segPtr wl st.segment) := rfl
    rw [hsg]
    obtain ⟨left, sibling⟩ := top
    simp only [encStack, List.map_cons]
    rw [Ref.segLoop, segment_eq]
    by_cases h1 : SphincsSecurity.ftsTreeHeight < (segAt wl (segPtr wl st.segment)).folds.val
    · rw [if_pos h1, if_pos (show (14 : Nat) < _ from h1)]
      simp only [pure_bind, hK0]
    · rw [if_neg h1, if_neg (show ¬ (14 : Nat) < _ from h1)]
      by_cases h2 : (segAt wl (segPtr wl st.segment)).folds.val ≠ 0 ∧
          (segAt wl (segPtr wl st.segment)).parity ≠ decide (st.heap % 2 = 1)
      · simp only [if_pos h2, pure_bind, hK0]
      · rw [if_neg h2, if_neg h2]
        rw [bind_map_left]
        simp only [bind_assoc, relabel_bind]
        refine bind_congr (m := OracleComp SigGolf.HashSpec) fun start => ?_
        refine bind_congr (m := OracleComp SigGolf.HashSpec) fun x => ?_
        rw [← relabel_bind]
        unfold segCont
        rw [hst]
        by_cases hm : (segAt wl (segPtr wl st.segment)).merge = true
        · simp only [hm, if_true, Bool.not_true, Bool.false_eq_true]
          by_cases hq : sibling = x.2
          · simp only [hq, ne_eq, not_true_eq_false, if_false, if_true]
            have := ih fuel (.merge (x.2 / 2) left)
              ⟨x.1, x.2 / 2, rest, st.folds + (segAt wl (segPtr wl st.segment)).folds.val, st.segment + 1⟩
              rfl (by simp at hseg ⊢; omega) (by simp at hfuel ⊢; omega)
              (fun st' h' => hK st' (by simp at h' ⊢; omega)) hK0
            exact this
          · simp only [hq, ne_eq, not_false_eq_true, if_true, if_false, pure_bind, hK0]
        · simp only [hm, Bool.false_eq_true, if_false, Bool.not_false, if_true, pure_bind]
          exact hK ⟨x.1, x.2, (left, sibling) :: rest,
            st.folds + (segAt wl (segPtr wl st.segment)).folds.val, st.segment + 1⟩ (by simp; omega)

/-- What `porsRoot` reads off the reference's final state. -/
def projR (st : Ref.PorsState) : Nat × Nat × List (Ref.Val × Nat) × Ref.Val :=
  (st.folds, st.E, st.stack, st.node)

/-- The same of an abstract state. -/
def projRecA (st : RecoverState) : Nat × Nat × List (Ref.Val × Nat) × Ref.Val :=
  (st.folds, st.heap, encStack st.stack, dv st.node)

theorem porsLeaves_eq (hl : wl.length = 6348) (leaves : IndexGroup → FtsLeaf) :
    ∀ (rem pos prev : Nat) (ast : RecoverState), pos + rem = 15 →
      ast.segment + ast.stack.length ≤ 2 * pos →
      Option.map projR <$> Ref.porsLeaves index (List.ofFn fun r => (leaves r).val) wl
          (List.range' pos rem)
          ⟨segPtr wl ast.segment, prev, ast.heap, ast.folds, dv ast.node, encStack ast.stack⟩ =
        relabel fmtQ (Option.map projRecA <$> SphincsSecurity.Concrete.recoverLeaves (m := AComp) 0 index
          (SphincsSecurity.Concrete.slotValue leaves) (witFts wl) rem pos prev ast) := by
  intro rem
  induction rem with
  | zero =>
    intro pos prev ast _ _
    simp [Ref.porsLeaves, SphincsSecurity.Concrete.recoverLeaves, projR, projRecA]
  | succ rem ih =>
    intro pos prev ast hpr hinv
    have hpos : pos < SphincsSecurity.ftsOpenings := by show pos < 15; omega
    rw [List.range'_succ]
    simp only [Ref.porsLeaves, SphincsSecurity.Concrete.recoverLeaves, dif_pos hpos]
    have hx : ((List.ofFn fun r => (leaves r).val) ++ [Ref.porsT]).getD (Ref.witPi wl pos / 8 % 16) 0 =
        SphincsSecurity.Concrete.slotValue leaves ((witFts wl).perm ⟨pos, hpos⟩) :=
      slotValue_eq leaves ((witFts wl).perm ⟨pos, hpos⟩)
    rw [hx]
    generalize hxv : SphincsSecurity.Concrete.slotValue leaves ((witFts wl).perm ⟨pos, hpos⟩) = x
    have hsec : Ref.witSecret wl pos = dv ((witFts wl).secrets ⟨pos, hpos⟩) :=
      witSecret_eq wl hl pos (by simpa [SphincsSecurity.ftsOpenings] using hpos)
    rw [hsec]
    by_cases c1 : pos ≠ 0 ∧ ¬ prev < x
    · rw [if_pos c1, if_pos (show 0 < pos ∧ ¬ prev < x by omega)]
      simp
    · rw [if_neg c1, if_neg (show ¬ (0 < pos ∧ ¬ prev < x) by omega)]
      by_cases c2 : pos = Ref.porsK - 1 ∧ ¬ x < Ref.porsT
      · rw [if_pos c2, if_pos (show pos + 1 = SphincsSecurity.ftsOpenings ∧
            ¬ x < 2 ^ SphincsSecurity.ftsTreeHeight by
          simp only [Ref.porsK, Ref.porsT, Ref.porsH, SphincsSecurity.ftsOpenings,
            SphincsSecurity.ftsTreeHeight] at c2 ⊢; omega)]
        simp
      · rw [if_neg c2, if_neg (show ¬ (pos + 1 = SphincsSecurity.ftsOpenings ∧
            ¬ x < 2 ^ SphincsSecurity.ftsTreeHeight) by
          simp only [Ref.porsK, Ref.porsT, Ref.porsH, SphincsSecurity.ftsOpenings,
            SphincsSecurity.ftsTreeHeight] at c2 ⊢; omega)]
        rw [map_bind, map_bind]
        refine segLoop_bind index wl _ _ ast.stack SphincsSecurity.ftsSegments
          (.leaf x ((witFts wl).secrets ⟨pos, hpos⟩))
          { ast with heap := 2 ^ SphincsSecurity.ftsTreeHeight ||| x } rfl ?_ ?_ ?_ ?_
        · have : pos ≤ 14 := by simp [SphincsSecurity.ftsOpenings] at hpos; omega
          show ast.segment + ast.stack.length < 29
          omega
        · have : pos ≤ 14 := by simp [SphincsSecurity.ftsOpenings] at hpos; omega
          show ast.stack.length < 29
          omega
        · intro st' hst'
          simp only at hst'
          simp only [encR]
          have h15 : pos ≤ 14 := by simp [SphincsSecurity.ftsOpenings] at hpos; omega
          by_cases hp : pos < 14
          · rw [if_pos (show pos < Ref.porsK - 1 from hp),
              if_pos (show pos + 1 < SphincsSecurity.ftsOpenings by show pos + 1 < 15; omega)]
            exact ih (pos + 1) x ⟨st'.node, st'.heap, (st'.node, st'.heap ^^^ 1) :: st'.stack, st'.folds,
              st'.segment⟩ (by omega) (by simp; omega)
          · rw [if_neg (show ¬ pos < Ref.porsK - 1 from hp),
              if_neg (show ¬ pos + 1 < SphincsSecurity.ftsOpenings by show ¬ pos + 1 < 15; omega)]
            exact ih (pos + 1) x st' (by omega) (by omega)
        · simp

theorem segLoop_leaf_irrel (i : Nat) (w : List Byte) (p E f x : Nat) (sec n1 n2 : Ref.Val)
    (stk : List (Ref.Val × Nat)) :
    Ref.segLoop i w p E f (.leaf x sec) n1 stk = Ref.segLoop i w p E f (.leaf x sec) n2 stk := by
  cases stk <;> simp only [Ref.segLoop, Ref.segment, Ref.pendingHash]

theorem porsLeaves_node_irrel (i : Nat) (v : List Nat) (w : List Byte) (s : Nat) (rest : List Nat)
    (p pr E f : Nat) (n1 n2 : Ref.Val) (stk : List (Ref.Val × Nat)) :
    Ref.porsLeaves i v w (s :: rest) ⟨p, pr, E, f, n1, stk⟩ =
      Ref.porsLeaves i v w (s :: rest) ⟨p, pr, E, f, n2, stk⟩ := by
  simp only [Ref.porsLeaves]
  rw [segLoop_leaf_irrel i w p _ f _ _ n1 n2]

/-- The stack machine: `Ref.porsRoot` is the relabelled `ftsRecover` on the decoded witness. -/
theorem porsRoot_eq (hl : wl.length = 6348) (leaves : IndexGroup → FtsLeaf) :
    Ref.porsRoot index (List.ofFn fun r => (leaves r).val) wl =
      Option.map dv <$> relabel fmtQ (SphincsSecurity.Concrete.ftsRecover (m := AComp) 0 index
        (SphincsSecurity.Concrete.slotValue leaves) (witFts wl)) := by
  have hL := porsLeaves_eq index wl hl leaves 15 0 0 SphincsSecurity.Concrete.RecoverState.initial rfl
    (by simp [SphincsSecurity.Concrete.RecoverState.initial])
  have hr : List.range Ref.porsK = List.range' 0 15 := by rw [List.range_eq_range']; rfl
  unfold Ref.porsRoot SphincsSecurity.Concrete.ftsRecover
  rw [hr, show List.range' 0 15 = 0 :: List.range' 1 14 from rfl,
    porsLeaves_node_irrel _ _ _ 0 _ _ _ _ _ [] (dv 0)]
  rw [show (0 :: List.range' 1 14) = List.range' 0 15 from rfl]
  refine Eq.trans (b := (fun r => r.bind fun q : Nat × Nat × List (Ref.Val × Nat) × Ref.Val =>
      if q.1 > Ref.porsM ∨ q.2.1 ≠ 1 ∨ q.2.2.1 ≠ [] then none else some q.2.2.2) <$>
        (Option.map projR <$> Ref.porsLeaves (↑index) (List.ofFn fun r => (leaves r).val) wl
          (List.range' 0 15) ⟨Ref.wStream, 0, 0, 0, dv 0, []⟩)) ?_ ?_
  · rw [Functor.map_map, map_eq_bind_pure_comp]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
    rcases r with _ | st
    · rfl
    · simp only [Function.comp, Option.map_some, Option.bind_some, projR]
      split_ifs <;> rfl
  · simp only [SphincsSecurity.Concrete.RecoverState.initial] at hL
    rw [show (⟨Ref.wStream, 0, 0, 0, dv 0, []⟩ : Ref.PorsState) =
      ⟨segPtr wl 0, 0, 0, 0, dv 0, encStack []⟩ from rfl, hL]
    rw [← relabel_map, ← relabel_map, Functor.map_map, map_bind]
    congr 1
    rw [map_eq_bind_pure_comp]
    refine bind_congr (m := AComp) fun r => ?_
    rcases r with _ | st
    · rfl
    · simp only [Function.comp, Option.map_some, Option.bind_some, projRecA]
      split_ifs with h1 h2 h2 <;>
        simp_all [encStack, Ref.porsM, SphincsSecurity.ftsAuthCapacity] <;> omega

end pors


/-! ## The verifier -/

/-- **verify**: `verifyRef m pk w` is the relabelled abstract verifier on `⟨pk, 0⟩` and `witDec w`. -/
theorem verifyRef_eq (m : Bytes 32) (pk : Bytes 16) (w : Bytes 6348) :
    Ref.verifyRef m pk w =
      relabel fmtQ (SphincsSecurity.Concrete.verify (m := AComp) ⟨pk, 0⟩ m (witDec w)) := by
  have hl : (Ref.toList w).length = 6348 := Ref.length_toList w
  unfold Ref.verifyRef Ref.verifyList SphincsSecurity.Concrete.verify SphincsSecurity.Concrete.verifyCore
  rw [countersOk_eq _ hl]
  unfold witDec
  by_cases hc : SphincsSecurity.Concrete.CountersInRange (witSig (Ref.toList w))
  · simp only [hc, decide_true, Bool.not_true, Bool.false_eq_true, if_false, if_true]
    rw [witRho_eq _ hl, digest_eq pk _ m, relabel_bind, bind_map_left]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun d => ?_
    rw [idxOf_eq, leavesOf_eq, porsRoot_eq _ _ hl, bind_map_left]
    simp only [relabel_bind]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
    rcases r with _ | key
    · simp [relabel_pure]
    · simp only [Option.map_some]
      rw [show Ref.nLayers = SphincsSecurity.numLayers from rfl,
        verifyLayers_eq _ hl _ SphincsSecurity.numLayers (le_refl 5), bind_map_left, relabel_bind]
      refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
      rcases r with _ | root
      · simp [relabel_pure]
      · simp only [Option.map_some, relabel_pure]
        refine congrArg pure ?_
        rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
        exact ⟨fun h => dv_injective h, fun h => by rw [h]; rfl⟩
  · simp only [hc, decide_false, Bool.not_false, if_true, if_false, relabel_pure]

end SigGolfCandidate.Equiv
