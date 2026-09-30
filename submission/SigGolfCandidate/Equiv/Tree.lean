import SigGolfCandidate.Equiv.Basic

/-!
# Hypertree trees: chains, leaves, levels, whole trees, keygen

Every reference tree routine (`Ref.buildChain`, `Ref.buildLeaf`, `Ref.buildLeaves`,
`Ref.buildLevels`, `Ref.buildTree`, `Ref.keygenList`) is `f <$> relabel padQ A` for the
corresponding abstract routine `A`.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolf (Byte Bytes Query)
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map relabel_query)
open SphincsSecurity (Digest Layer TreeIndex LeafIndex ChainIndex Encoding MasterSeed)
open SphincsSecurity.Concrete (sequenceFin)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-! ## Hash inputs -/

@[simp] theorem toB_P : toB (SphincsSecurity.bytesLE 16 (0 : SphincsSecurity.PublicParameter)) = Ref.P := by
  rw [toB_bytesLE]; exact toList_zero 16

@[simp] theorem toB_P' :
    toB (SphincsSecurity.bytesLE 16 (0#SphincsSecurity.publicParameterBits)) = Ref.P := toB_P

theorem toB_dv (d : Digest) : toB (SphincsSecurity.bytesLE 16 d) = dv d := toB_bytesLE 16 d

theorem toB_seed (seed : MasterSeed) :
    toB (SphincsSecurity.bytesLE 32 seed) = Ref.toList (n := 32) seed := toB_bytesLE 32 seed

theorem toB_tweakableHashInput (dom : SphincsSecurity.HashDomain) (payload : List UInt8) :
    toB (SphincsSecurity.tweakableHashInput 0 dom payload) =
      toB (SphincsSecurity.tweakBytes dom) ++ Ref.P ++ toB payload := by
  simp [SphincsSecurity.tweakableHashInput]

/-- A reference hash of an arbitrary abstract input. -/
theorem hash16_derive (x : List UInt8) (y : List Byte) (hy : toB x = y) :
    Ref.hash16 y = dv <$> relabel padQ
      (do return SphincsSecurity.truncateHash (← SphincsSecurity.Concrete.oracleHash (m := AComp) x)) := by
  subst hy
  simp only [relabel_bind, relabel_oracleHash, hash16_eq, relabel_pure]
  rw [map_bind]
  simp only [map_pure]
  rw [map_eq_bind_pure_comp]; rfl

theorem hash16_prf (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (c : ChainIndex) :
    Ref.hash16 (Ref.prfInput (Ref.toList (n := 32) seed) lay tree leaf c) =
      dv <$> relabel padQ (SphincsSecurity.Seeded.otsSecret (m := AComp) 0 seed lay tree leaf c) := by
  apply hash16_derive
  simp [SphincsSecurity.keygenHashInput, SphincsSecurity.keygenDomainFields, toB_tweakFields,
    toB_seed, Ref.prfInput, Ref.thInput]

/-! ## Chains -/

section chain

variable (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (c : ChainIndex)

/-- The abstract chain walk is a fold over its positions. -/
theorem chainWalk_foldlM (P : SphincsSecurity.PublicParameter) (start steps : Nat) (v : Digest) :
    SphincsSecurity.Concrete.chainWalk (m := AComp) P lay tree leaf c start steps v =
      (List.range' start steps).foldlM (fun v p =>
        if hp : p < SphincsSecurity.chainLength - 1 then
          SphincsSecurity.Concrete.tweakableHash P (.chain lay tree leaf c ⟨p, hp⟩)
            (SphincsSecurity.bytesLE 16 v)
        else pure 0) v := by
  induction steps generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [List.range'_concat, List.foldlM_append, ← ih]
    simp only [SphincsSecurity.Concrete.chainWalk, Nat.one_mul, List.foldlM_cons, List.foldlM_nil,
      bind_pure]

theorem hash16_chain (P0 : SphincsSecurity.PublicParameter) (hP : P0 = 0) (p : Nat)
    (hp : p < SphincsSecurity.chainLength - 1) (v : Digest) :
    Ref.hash16 (Ref.chainInput lay tree leaf c (p + 1) (dv v)) =
      dv <$> relabel padQ (SphincsSecurity.Concrete.tweakableHash (m := AComp) P0
        (.chain lay tree leaf c ⟨p, hp⟩) (SphincsSecurity.bytesLE 16 v)) := by
  subst hP
  apply hash16_tweakable
  rw [toB_tweakableHashInput, toB_dv]
  simp only [SphincsSecurity.tweakBytes, SphincsSecurity.hashDomainFields, toB_tweakFields,
    Ref.chainInput, Ref.thInput, SphincsSecurity.chainLength, SphincsSecurity.winternitzBits]
  simp only [List.append_assoc]
  congr 3

/-- The reference chain fold from position `s` (steps `s+1 .. s+n`). -/
theorem chainFold_eq (s n : Nat) (hsn : s + n ≤ 7) (v : Digest) :
    (List.range' (s + 1) n).foldlM
        (fun v mu => Ref.hash16 (Ref.chainInput lay tree leaf c mu v)) (dv v) =
      dv <$> relabel padQ (SphincsSecurity.Concrete.chainWalk (m := AComp) 0 lay tree leaf c s n v) := by
  induction n with
  | zero => simp [SphincsSecurity.Concrete.chainWalk]
  | succ n ih =>
    rw [List.range'_concat, List.foldlM_append, ih (by omega)]
    simp only [SphincsSecurity.Concrete.chainWalk, relabel_bind, map_bind, bind_map_left,
      Nat.one_mul, List.foldlM_cons, List.foldlM_nil, bind_pure]
    congr 1; funext u
    have hp : s + n < SphincsSecurity.chainLength - 1 := by
      simp [SphincsSecurity.chainLength, SphincsSecurity.winternitzBits]; omega
    rw [dif_pos hp, show s + 1 + n = (s + n) + 1 by omega, hash16_chain lay tree leaf c 0 rfl]

/-- The capturing fold of `Ref.buildChain` when the capture position is not visited. -/
theorem capFold_notin {m : Type → Type} [Monad m] [LawfulMonad m] {V : Type}
    (step : Nat → V → m V) (x : Nat) (l : List Nat) (hx : x ∉ l) (a c : V) :
    l.foldlM (fun (st : V × V) mu => do
      let v ← step mu st.1
      pure (v, if mu = x then v else st.2)) (a, c) =
      (fun w => (w, c)) <$> l.foldlM (fun v mu => step mu v) a := by
  induction l generalizing a with
  | nil => simp
  | cons y l ih =>
    simp only [List.foldlM_cons, map_bind, bind_assoc, pure_bind]
    have hy : y ≠ x := fun h => hx (h ▸ List.mem_cons_self)
    congr 1; funext v
    rw [if_neg hy]
    exact ih (fun h => hx (List.mem_cons_of_mem _ h)) v

/-- `Ref.buildChain` with a capture position `x ≤ 7`: the value after `x` steps and the end. -/
theorem buildChain_split (S : List Byte) (lay tau e i x : Nat) (hx : x ≤ 7) :
    Ref.buildChain S lay tau e i x =
      Ref.hash16 (Ref.prfInput S lay tau e i) >>= fun v =>
      (List.range' 1 x).foldlM (fun v mu => Ref.hash16 (Ref.chainInput lay tau e i mu v)) v >>=
        fun w => (fun z => (z, w)) <$> (List.range' (x + 1) (7 - x)).foldlM
          (fun v mu => Ref.hash16 (Ref.chainInput lay tau e i mu v)) w := by
  unfold Ref.buildChain
  congr 1; funext v
  have hc := fun x l hx a c => capFold_notin
    (fun mu v => Ref.hash16 (Ref.chainInput lay tau e i mu v)) x l hx a c
  cases x with
  | zero =>
    rw [hc 0 _ (by simp)]
    simp
  | succ k =>
    have hsplit : List.range' 1 7 = List.range' 1 k ++ (1 + k) :: List.range' (1 + k + 1) (6 - k) := by
      rw [← List.range'_succ, show 6 - k + 1 = 7 - k by omega, List.range'_append_1]
      congr 1; omega
    rw [hsplit, List.foldlM_append, hc (k + 1) _ (by simp; omega)]
    simp only [map_bind, bind_map_left, List.foldlM_cons, bind_assoc, pure_bind]
    rw [show List.range' 1 (k + 1) = List.range' 1 k ++ [1 + k] by
      rw [List.range'_concat]; simp]
    simp only [List.foldlM_append, List.foldlM_cons, List.foldlM_nil, bind_assoc, bind_pure]
    congr 1; funext w; congr 1; funext z
    rw [if_pos (by omega), hc (k + 1) _ (by simp), show k + 1 + 1 = 1 + k + 1 by omega,
      show 7 - (k + 1) = 6 - k by omega]

theorem buildChain_eq (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (c : ChainIndex) (d : Nat) (hd : d ≤ 7) :
    Ref.buildChain (Ref.toList (n := 32) seed) lay tree leaf c d =
      (fun r => (dv r.2, dv r.1)) <$> relabel padQ
        (SphincsSecurity.Concrete.buildChain (m := AComp) 0 lay tree leaf c
          (SphincsSecurity.Seeded.otsSecret 0 seed lay tree leaf c) d) := by
  rw [buildChain_split _ _ _ _ _ _ hd, hash16_prf]
  unfold SphincsSecurity.Concrete.buildChain
  simp only [relabel_bind, relabel_pure, map_bind, bind_map_left, map_pure]
  congr 1; funext start
  have h1 := chainFold_eq lay tree leaf c 0 d (by omega) start
  rw [Nat.zero_add] at h1
  rw [h1, bind_map_left]
  congr 1; funext w
  have h2 := chainFold_eq lay tree leaf c d (7 - d) (by omega) w
  rw [h2, show SphincsSecurity.chainLength - 1 - d = 7 - d by
    simp [SphincsSecurity.chainLength, SphincsSecurity.winternitzBits]]
  simp only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  rfl

end chain

/-! ## Leaves -/

theorem toB_flatMap_dv (l : List Digest) :
    toB (l.flatMap (SphincsSecurity.bytesLE 16)) = (l.map dv).flatten := by
  induction l with
  | nil => rfl
  | cons d l ih => simp [List.flatMap_cons, toB_append, toB_dv, ih]

theorem hash16_leaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (ends : ChainIndex → Digest) :
    Ref.hash16 (Ref.leafInput lay tree leaf (List.ofFn fun i => dv (ends i))) =
      dv <$> relabel padQ (SphincsSecurity.Concrete.leafHash (m := AComp) 0 lay tree leaf ends) := by
  apply hash16_tweakable
  rw [toB_tweakableHashInput]
  simp only [SphincsSecurity.tweakBytes, SphincsSecurity.hashDomainFields, toB_tweakFields,
    SphincsSecurity.Concrete.leafPayload, toB_flatMap_dv, Ref.leafInput, Ref.thInput, List.map_ofFn,
    List.append_assoc]
  rfl

theorem buildLeaf_eq (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (enc : Encoding) (x : List Nat) (hx : ∀ i : ChainIndex, x.getD i 0 = (enc i).val) :
    Ref.buildLeaf (Ref.toList (n := 32) seed) lay tree leaf x =
      (fun r => (dv r.2, List.ofFn fun i => dv (r.1 i))) <$> relabel padQ
        (SphincsSecurity.Concrete.buildLeaf (m := AComp) 0 lay tree leaf
          (SphincsSecurity.Seeded.otsSecret 0 seed lay tree leaf) enc) := by
  unfold Ref.buildLeaf SphincsSecurity.Concrete.buildLeaf
  have hbody : (fun (st : List Ref.Val × List Ref.Val) (i : Nat) =>
      Ref.buildChain (Ref.toList (n := 32) seed) lay tree leaf i (x.getD i 0) >>= fun p =>
        match p with | (v, c) => pure (st.1 ++ [v], st.2 ++ [c])) = fun st i =>
      Ref.buildChain (Ref.toList (n := 32) seed) lay tree leaf i (x.getD i 0) >>= fun r =>
        pure (st.1 ++ [r.1], st.2 ++ [r.2]) := rfl
  rw [hbody, show Ref.nChains = SphincsSecurity.numChains from rfl]
  rw [foldlM_range_seq (fun i => relabel padQ (SphincsSecurity.Concrete.buildChain (m := AComp) 0
      lay tree leaf i (SphincsSecurity.Seeded.otsSecret 0 seed lay tree leaf i) (enc i).val))
      _ (fun r => (dv r.2, dv r.1))
      (fun j hj => by
        rw [hx ⟨j, hj⟩]
        exact buildChain_eq seed lay tree leaf ⟨j, hj⟩ _ (by have := (enc ⟨j, hj⟩).isLt; simp [SphincsSecurity.chainLength, SphincsSecurity.winternitzBits] at this; omega))]
  simp only [relabel_bind, relabel_sequenceFin, relabel_pure, map_bind, bind_map_left, map_pure]
  refine bind_congr fun f => ?_
  rw [foldl_prod _ (fun acc j => acc ++ [dv (f j).2]) (fun acc j => acc ++ [dv (f j).1]),
    foldl_finRange_append, foldl_finRange_append]
  simp only [List.nil_append]
  rw [hash16_leaf, bind_map_left]

/-! ## Leaves of a tree: the captured digits only change the captured values -/

theorem fst_buildChain (S : List Byte) (lay tau e i x : Nat) :
    Prod.fst <$> Ref.buildChain S lay tau e i x = Prod.fst <$> Ref.buildChain S lay tau e i 0 := by
  unfold Ref.buildChain
  simp only [map_bind]
  refine bind_congr fun v => ?_
  have h := fun y => map_fst_foldlM (m := OracleComp SigGolf.HashSpec) (List.range' 1 7)
    (fun (a : Ref.Val) mu => Ref.hash16 (Ref.chainInput lay tau e i mu a)) (fun _ _ r => r)
    (fun st mu r => if mu = y then r else st.2) (v, v)
  exact (h x).trans (h 0).symm

theorem fst_buildLeaf (S : List Byte) (lay tau e : Nat) (x y : List Nat) :
    Prod.fst <$> Ref.buildLeaf S lay tau e x = Prod.fst <$> Ref.buildLeaf S lay tau e y := by
  have key : ∀ z : List Nat, Prod.fst <$> Ref.buildLeaf S lay tau e z =
      ((List.range Ref.nChains).foldlM (fun (a : List Ref.Val) i =>
        (fun v => a ++ [v]) <$> (Prod.fst <$> Ref.buildChain S lay tau e i 0)) []) >>= fun ends =>
        Ref.hash16 (Ref.leafInput lay tau e ends) := by
    intro z
    unfold Ref.buildLeaf
    have hbody : (fun (st : List Ref.Val × List Ref.Val) (i : Nat) =>
        Ref.buildChain S lay tau e i (z.getD i 0) >>= fun p =>
          match p with | (v, c) => pure (st.1 ++ [v], st.2 ++ [c])) = fun st i =>
        Ref.buildChain S lay tau e i (z.getD i 0) >>= fun r =>
          pure (st.1 ++ [r.1], st.2 ++ [r.2]) := rfl
    rw [hbody]
    have h := map_fst_foldlM (m := OracleComp SigGolf.HashSpec) (List.range Ref.nChains)
      (fun (_ : List Ref.Val) i => Ref.buildChain S lay tau e i (z.getD i 0))
      (fun a _ r => a ++ [r.1]) (fun st _ r => st.2 ++ [r.2]) ([], [])
    simp only [map_bind, map_pure, bind_pure]
    rw [← bind_map_left (f := Prod.fst) (g := fun st => Ref.hash16 (Ref.leafInput lay tau e st)), h]
    refine congrArg (· >>= _) ?_
    refine congrArg (fun F => List.foldlM F _ _) ?_
    funext a i
    rw [← fst_buildChain S lay tau e i (z.getD i 0)]
    simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  rw [key x, key y]

/-- `Ref.buildLeaves` with the digits passed only to the captured leaf. -/
theorem buildLeaves_canon (S : List Byte) (lay tau h cap : Nat) (x : List Nat) :
    Ref.buildLeaves S lay tau h cap x =
      (List.range (2 ^ h)).foldlM (fun (st : List Ref.Val × List Ref.Val) e =>
        Ref.buildLeaf S lay tau e (if e = cap then x else []) >>= fun r =>
          pure (st.1 ++ [r.1], if e = cap then r.2 else st.2)) ([], []) := by
  unfold Ref.buildLeaves
  refine congrArg (fun F => List.foldlM F _ _) ?_
  funext st e
  by_cases he : e = cap
  · simp only [he, if_true]
  · simp only [he, if_false]
    have h1 : ∀ z, (Ref.buildLeaf S lay tau e z >>= fun p => pure (st.1 ++ [p.1], st.2)) =
        (fun l => (st.1 ++ [l], st.2)) <$> (Prod.fst <$> Ref.buildLeaf S lay tau e z) := by
      intro z; rw [Functor.map_map, map_eq_bind_pure_comp]; rfl
    rw [h1 x, h1 [], fst_buildLeaf S lay tau e x []]

theorem leafOfNat_val (j : Nat) (hj : j < 2 ^ SphincsSecurity.maxLayerHeight) :
    (SphincsSecurity.Concrete.leafOfNat j).val = j := by
  simp [SphincsSecurity.Concrete.leafOfNat, Nat.mod_eq_of_lt hj]

theorem layerHeight_le (lay : Layer) : SphincsSecurity.layerHeight lay ≤ 5 := by
  unfold SphincsSecurity.layerHeight SphincsSecurity.maxLayerHeight; split <;> omega

theorem pow_layerHeight_le (lay : Layer) :
    2 ^ SphincsSecurity.layerHeight lay ≤ 2 ^ SphincsSecurity.maxLayerHeight :=
  Nat.pow_le_pow_right (by omega) (layerHeight_le lay)

/-- The abstract leaves of a layer tree. -/
abbrev absLeaves (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (digits : Encoding) :=
  sequenceFin (m := AComp) (n := 2 ^ SphincsSecurity.layerHeight lay) fun leafNat =>
    SphincsSecurity.Concrete.buildLeaf 0 lay tree (SphincsSecurity.Concrete.leafOfNat leafNat.val)
      (SphincsSecurity.Seeded.otsSecret 0 seed lay tree (SphincsSecurity.Concrete.leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else SphincsSecurity.Concrete.zeroEncoding)

theorem buildLeaves_eq (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hcap : leaf.val < 2 ^ SphincsSecurity.layerHeight lay)
    (digits : Encoding) (x : List Nat) (hx : ∀ i : ChainIndex, x.getD i 0 = (digits i).val) :
    Ref.buildLeaves (Ref.toList (n := 32) seed) lay tree (SphincsSecurity.layerHeight lay) leaf x =
      (fun f => (List.ofFn fun j => dv (f j).2, List.ofFn fun i => dv ((f ⟨leaf.val, hcap⟩).1 i))) <$>
        relabel padQ (absLeaves seed lay tree leaf digits) := by
  rw [buildLeaves_canon, absLeaves, relabel_sequenceFin]
  have hb : ∀ j (hj : j < 2 ^ SphincsSecurity.layerHeight lay),
      Ref.buildLeaf (Ref.toList (n := 32) seed) lay tree j (if j = leaf.val then x else []) =
        (fun r => (dv r.2, List.ofFn fun i => dv (r.1 i))) <$> relabel padQ
          (SphincsSecurity.Concrete.buildLeaf (m := AComp) 0 lay tree
            (SphincsSecurity.Concrete.leafOfNat j)
            (SphincsSecurity.Seeded.otsSecret 0 seed lay tree (SphincsSecurity.Concrete.leafOfNat j))
            (if j = leaf.val then digits else SphincsSecurity.Concrete.zeroEncoding)) := by
    intro j hj
    have hv := leafOfNat_val j (lt_of_lt_of_le hj (pow_layerHeight_le lay))
    have := buildLeaf_eq seed lay tree (SphincsSecurity.Concrete.leafOfNat j)
      (if j = leaf.val then digits else SphincsSecurity.Concrete.zeroEncoding)
      (if j = leaf.val then x else []) (by
        intro i
        by_cases hj' : j = leaf.val
        · simp only [hj', if_true]; exact hx i
        · simp [hj', SphincsSecurity.Concrete.zeroEncoding])
    rw [hv] at this
    exact this
  rw [foldlM_range_seq (fun jf : Fin (2 ^ SphincsSecurity.layerHeight lay) => relabel padQ
      (SphincsSecurity.Concrete.buildLeaf (m := AComp) 0 lay tree
        (SphincsSecurity.Concrete.leafOfNat jf.val)
        (SphincsSecurity.Seeded.otsSecret 0 seed lay tree (SphincsSecurity.Concrete.leafOfNat jf.val))
        (if jf.val = leaf.val then digits else SphincsSecurity.Concrete.zeroEncoding)))
    _ (fun r => (dv r.2, List.ofFn fun i => dv (r.1 i))) (fun j hj => hb j hj)]
  simp only [Functor.map_map]
  refine congrArg (· <$> _) ?_
  funext f
  rw [foldl_prod _ (fun acc j => acc ++ [dv (f j).2])
      (fun acc (j : Fin (2 ^ SphincsSecurity.layerHeight lay)) =>
        if j.val = leaf.val then List.ofFn (fun i => dv ((f j).1 i)) else acc),
    foldl_finRange_append, foldl_finRange_capture, dif_pos hcap]
  rfl

/-! ## Levels (shared by hypertree and few-time trees) -/

theorem getD_ofFn {β : Type} {n : Nat} (f : Fin n → β) (i : Nat) (d : β) :
    (List.ofFn f).getD i d = if h : i < n then f ⟨i, h⟩ else d := by
  split_ifs with h
  · simp [List.getD_eq_getElem?_getD, h]
  · simp [List.getD_eq_getElem?_getD, h]

section levels

variable (node : Ref.NodeFmt) (hashNode : Nat → Nat → Digest → Digest → AComp Digest)
  (hnode : ∀ lam j l r, Ref.hash16 (node lam j (dv l) (dv r)) = dv <$> relabel padQ (hashNode lam j l r))

include hnode in
theorem buildLevels_steps (h cap : Nat) (hcap : cap < 2 ^ h) (leaves : Nat → Digest) (L : Nat)
    (hL : L ≤ h) :
    (List.range' 1 L).foldlM (Ref.levelStep node cap)
        (List.ofFn (fun j : Fin (2 ^ h) => dv (leaves j)), []) =
      (fun T => (List.ofFn (fun j : Fin (2 ^ (h - L)) => dv (T L j)),
          (List.range L).map (fun l => dv (T l (Nat.xor (cap / 2 ^ l) 1))))) <$>
        relabel padQ (SphincsSecurity.Concrete.buildLevels hashNode h leaves L) := by
  induction L with
  | zero =>
    simp only [List.range'_zero, List.foldlM_nil, SphincsSecurity.Concrete.buildLevels, relabel_pure,
      map_pure, List.range_zero, List.map_nil]
    rw [Nat.sub_zero]
  | succ L ih =>
    rw [List.range'_concat, List.foldlM_append, ih (by omega)]
    simp only [List.foldlM_cons, List.foldlM_nil, bind_pure, bind_map_left,
      SphincsSecurity.Concrete.buildLevels, relabel_bind, relabel_pure, map_bind]
    refine bind_congr fun T => ?_
    unfold Ref.levelStep Ref.buildLevel SphincsSecurity.Concrete.buildLevel
    simp only [Nat.one_mul, Nat.add_sub_cancel_left, List.length_ofFn]
    have hw : 2 ^ (h - L) / 2 = 2 ^ (h - (L + 1)) := by
      rw [show h - L = (h - (L + 1)) + 1 by omega, Nat.pow_succ, Nat.mul_div_cancel _ (by omega)]
    rw [hw, show 1 + L = L + 1 by omega]
    have hpow : 2 ^ (h - L) = 2 * 2 ^ (h - (L + 1)) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hb : ∀ j (hj : j < 2 ^ (h - (L + 1))),
        Ref.hash16 (node (L + 1) j
          ((List.ofFn fun j : Fin (2 ^ (h - L)) => dv (T L j)).getD (2 * j) [])
          ((List.ofFn fun j : Fin (2 ^ (h - L)) => dv (T L j)).getD (2 * j + 1) [])) =
        dv <$> relabel padQ (hashNode (L + 1) j (T L (2 * j)) (T L (2 * j + 1))) := by
      intro j hj
      rw [getD_ofFn, getD_ofFn, dif_pos (by omega), dif_pos (by omega)]
      exact hnode _ _ _ _
    rw [foldlM_range_seq (fun j : Fin (2 ^ (h - (L + 1))) =>
        relabel padQ (hashNode (L + 1) j (T L (2 * j)) (T L (2 * j + 1)))) _ dv (fun j hj => hb j hj)]
    simp only [relabel_bind, relabel_pure, relabel_sequenceFin, map_bind, map_pure, Functor.map_map,
      bind_map_left, bind_assoc, pure_bind]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun row => ?_
    congr 1
    rw [foldl_finRange_append, List.nil_append, getD_ofFn]
    have hk : (cap / 2 ^ L) ^^^ 1 < 2 ^ (h - L) := by
      have h1 : cap / 2 ^ L < 2 ^ (h - L) := by
        rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, show h - L + L = h by omega]
        exact hcap
      exact Nat.xor_lt_two_pow h1 (Nat.one_lt_two_pow (by omega))
    rw [dif_pos hk]
    simp only [Prod.mk.injEq]
    constructor
    · congr 1; funext j; simp [j.isLt]
    · rw [List.range_succ, List.map_append]
      simp only [List.map_cons, List.map_nil]
      congr 1
      · apply List.map_congr_left
        intro l hl
        rw [List.mem_range] at hl
        simp [show l ≠ L + 1 by omega]
      · simp

include hnode in
theorem buildLevels_eq (h cap : Nat) (hcap : cap < 2 ^ h) (leaves : Nat → Digest) :
    Ref.buildLevels node cap h (List.ofFn (fun j : Fin (2 ^ h) => dv (leaves j))) =
      (fun T => (dv (T h 0), (List.range h).map (fun l => dv (T l (Nat.xor (cap / 2 ^ l) 1))))) <$>
        relabel padQ (SphincsSecurity.Concrete.buildLevels hashNode h leaves h) := by
  unfold Ref.buildLevels
  rw [buildLevels_steps node hashNode hnode h cap hcap leaves h le_rfl]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  refine bind_congr fun T => ?_
  rw [getD_ofFn, dif_pos (by simp)]
  rfl

end levels

/-! ## Whole trees and keygen -/

theorem hash16_node (lay : Layer) (tree : TreeIndex) (lam j : Nat) (l r : Digest) :
    Ref.hash16 (Ref.nodeInput lay tree lam j (dv l) (dv r)) =
      dv <$> relabel padQ (SphincsSecurity.Concrete.tweakableHash (m := AComp) 0
        (.node lay tree lam j) (SphincsSecurity.Concrete.nodePayload l r)) := by
  apply hash16_tweakable
  rw [toB_tweakableHashInput]
  simp only [SphincsSecurity.tweakBytes, SphincsSecurity.hashDomainFields, toB_tweakFields,
    SphincsSecurity.Concrete.nodePayload, toB_append, toB_dv, Ref.nodeInput, Ref.thInput,
    List.append_assoc]

theorem ofFn_leaves {β : Type} {n : Nat} (f : Fin n → β) (g : β → Digest) :
    (List.ofFn fun j => dv (g (f j))) =
      List.ofFn (fun j : Fin n => dv ((fun k => if h : k < n then g (f ⟨k, h⟩) else 0) j)) := by
  congr 1; funext j; simp [j.isLt]

theorem buildTree_eq (seed : MasterSeed) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (hcap : leaf.val < 2 ^ SphincsSecurity.layerHeight lay)
    (digits : Encoding) (x : List Nat) (hx : ∀ i : ChainIndex, x.getD i 0 = (digits i).val) :
    Ref.buildTree (Ref.toList (n := 32) seed) lay tree (SphincsSecurity.layerHeight lay) leaf x =
      (fun r => (dv r.2.2, List.ofFn (fun i => dv (r.1 i)),
          (List.range (SphincsSecurity.layerHeight lay)).map (fun l => dv (r.2.1 l)))) <$>
        relabel padQ (SphincsSecurity.Concrete.buildLayerTree (m := AComp) 0 lay tree
          (SphincsSecurity.Seeded.otsSecret 0 seed lay tree) leaf digits) := by
  unfold Ref.buildTree SphincsSecurity.Concrete.buildLayerTree
  rw [buildLeaves_eq seed lay tree leaf hcap digits x hx]
  simp only [relabel_bind, relabel_pure, map_bind, bind_map_left, map_pure]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun f => ?_
  rw [ofFn_leaves f Prod.snd]
  rw [buildLevels_eq (Ref.nodeInput lay tree) (fun level nodeIdx left right =>
      SphincsSecurity.Concrete.tweakableHash (m := AComp) 0 (.node lay tree level nodeIdx)
        (SphincsSecurity.Concrete.nodePayload left right)) (hash16_node lay tree) _ _ hcap
      (fun k => if h : k < 2 ^ SphincsSecurity.layerHeight lay then (f ⟨k, h⟩).2 else 0)]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun T => ?_
  simp [hcap]

theorem keygenList_eq (seed : MasterSeed) :
    Ref.keygenList (Ref.toList (n := 32) seed) =
      (fun kp => dv kp.1.root) <$> relabel padQ (SphincsSecurity.Seeded.keygenFromSeed seed) := by
  unfold Ref.keygenList SphincsSecurity.Seeded.keygenFromSeed
  have h := buildTree_eq seed SphincsSecurity.topLayer SphincsSecurity.Concrete.rootTree ⟨0, by decide⟩
    (by decide) SphincsSecurity.Concrete.zeroEncoding [] (fun i => rfl)
  rw [show Ref.height 0 = SphincsSecurity.layerHeight SphincsSecurity.topLayer by decide]
  have e1 : ((SphincsSecurity.topLayer : Layer) : Nat) = 0 := rfl
  have e2 : ((SphincsSecurity.Concrete.rootTree : TreeIndex) : Nat) = 0 := rfl
  rw [e1, e2] at h
  rw [h]
  simp only [relabel_bind, relabel_pure, map_bind, bind_map_left, map_pure,
    map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]

/-- **keygen**: the reference key generation is the relabelled abstract key generation. -/
theorem keygenRef_eq (sk : Bytes 32) :
    Ref.keygenRef sk =
      (fun kp => (kp.1.root : Bytes 16)) <$> relabel padQ (SphincsSecurity.Seeded.keygenFromSeed sk) := by
  unfold Ref.keygenRef
  rw [keygenList_eq sk]
  simp only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun kp => ?_
  exact congrArg pure (Ref.ofList_toList (n := 16) kp.1.root)

end SigGolfCandidate.Equiv
