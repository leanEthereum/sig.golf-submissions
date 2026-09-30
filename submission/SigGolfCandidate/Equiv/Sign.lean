import SigGolfCandidate.Equiv.Keygen
import SigGolfCandidate.Equiv.Sched

/-!
# Signing (PORS+FP)

`signRef_eq`: the reference signer is the relabelled abstract signer on the decoded cache, its
output compressed by `compress`.
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

/-! ## The PORS tree -/

theorem flatten_unpairPorsLeaves {α β : Type} (f : SphincsSecurity.FtsPair → α × α) (G : α → β) :
    (List.ofFn fun j : SphincsSecurity.FtsPair => [G (f j).1, G (f j).2]).flatten =
      List.ofFn fun c : FtsLeaf => G (SphincsSecurity.unpairFtsLeaves f c) := by
  let F : Nat → β := fun i =>
    G (SphincsSecurity.unpairFtsLeaves f ⟨i % 16384, Nat.mod_lt _ (by decide)⟩)
  have e1 : (List.ofFn fun j : SphincsSecurity.FtsPair => [G (f j).1, G (f j).2]) =
      List.ofFn fun j : Fin 8192 => [F (2 * j.val), F (2 * j.val + 1)] := by
    apply List.ofFn_inj.mpr
    funext j
    have hj : j.val < 8192 := j.isLt
    have p1 : SphincsSecurity.ftsPairOf ⟨2 * j.val % 16384, Nat.mod_lt _ (by decide)⟩ = j := by
      apply Fin.ext; simp [SphincsSecurity.ftsPairOf]; omega
    have p2 : SphincsSecurity.ftsPairOf ⟨(2 * j.val + 1) % 16384, Nat.mod_lt _ (by decide)⟩ = j := by
      apply Fin.ext; simp [SphincsSecurity.ftsPairOf]; omega
    simp only [F, SphincsSecurity.unpairFtsLeaves, p1, p2]
    rw [if_pos (by simp), if_neg (by simp)]
  rw [e1, flatten_ofFn_pairs, map_range_eq_ofFn]
  apply List.ofFn_inj.mpr
  funext c
  simp only [F]
  exact congrArg (fun c' => G (SphincsSecurity.unpairFtsLeaves f c'))
    (Fin.ext (Nat.mod_eq_of_lt (show c.val < 16384 from c.isLt)))

/-- The abstract leaf pairs of the PORS tree. -/
abbrev absPorsPairs (seed : MasterSeed) (index : Index) :=
  sequenceFin (m := AComp) fun pair : SphincsSecurity.FtsPair => do
    let secrets ← SphincsSecurity.Seeded.ftsSecret 0 seed index SphincsSecurity.Concrete.porsTree pair
    let first ← SphincsSecurity.Concrete.ftsLeafHash 0 index SphincsSecurity.Concrete.porsTree
      (SphincsSecurity.evenFtsLeaf pair).val secrets.1
    let second ← SphincsSecurity.Concrete.ftsLeafHash 0 index SphincsSecurity.Concrete.porsTree
      (SphincsSecurity.oddFtsLeaf pair).val secrets.2
    return ((secrets.1, first), (secrets.2, second))

theorem buildPorsLeaves_eq (seed : MasterSeed) (index : Index) :
    Ref.buildPorsLeaves (Ref.toList (n := 32) seed) index =
      (fun f => (List.ofFn fun j => dv (SphincsSecurity.unpairFtsLeaves f j).2,
          List.ofFn fun j => dv (SphincsSecurity.unpairFtsLeaves f j).1)) <$>
        relabel fmtQ (absPorsPairs seed index) := by
  unfold Ref.buildPorsLeaves
  have hbody : (fun (st : List Ref.Val × List Ref.Val) (q : Nat) => do
      let (s0, s1) ← Ref.prf2 (Ref.porsPrfInput (Ref.toList (n := 32) seed) index q)
      let l0 ← Ref.hash16 (Ref.porsLeafInput index (2 * q) s0)
      let l1 ← Ref.hash16 (Ref.porsLeafInput index (2 * q + 1) s1)
      pure (st.1 ++ [l0, l1], st.2 ++ [s0, s1])) = fun st q =>
      (Ref.prf2 (Ref.porsPrfInput (Ref.toList (n := 32) seed) index q) >>= fun s =>
        Ref.hash16 (Ref.porsLeafInput index (2 * q) s.1) >>= fun l0 =>
          Ref.hash16 (Ref.porsLeafInput index (2 * q + 1) s.2) >>= fun l1 =>
            pure ((s.1, l0), (s.2, l1))) >>= fun r =>
        pure (st.1 ++ [r.1.2, r.2.2], st.2 ++ [r.1.1, r.2.1]) := by
    funext st q; simp only [bind_assoc, pure_bind]
  rw [hbody, show Ref.porsT / 2 = 2 ^ (SphincsSecurity.ftsTreeHeight - 1) from rfl, absPorsPairs,
    relabel_sequenceFin]
  rw [foldlM_range_seq (fun pair : SphincsSecurity.FtsPair => relabel fmtQ (do
      let secrets ← SphincsSecurity.Seeded.ftsSecret (m := AComp) 0 seed index
        SphincsSecurity.Concrete.porsTree pair
      let first ← SphincsSecurity.Concrete.ftsLeafHash (m := AComp) 0 index
        SphincsSecurity.Concrete.porsTree (SphincsSecurity.evenFtsLeaf pair).val secrets.1
      let second ← SphincsSecurity.Concrete.ftsLeafHash (m := AComp) 0 index
        SphincsSecurity.Concrete.porsTree (SphincsSecurity.oddFtsLeaf pair).val secrets.2
      return ((secrets.1, first), (secrets.2, second)))) _
      (fun r : (Digest × Digest) × (Digest × Digest) =>
        ((dv r.1.1, dv r.1.2), (dv r.2.1, dv r.2.2))) (fun j hj => by
    rw [prf2_pors seed index ⟨j, hj⟩, bind_map_left]
    simp only [relabel_bind, relabel_pure, map_bind]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun sec => ?_
    rw [show 2 * j = (SphincsSecurity.evenFtsLeaf ⟨j, hj⟩).val from rfl,
      hash16_porsLeaf index _ sec.1, bind_map_left]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun l0 => ?_
    rw [show (SphincsSecurity.evenFtsLeaf ⟨j, hj⟩).val + 1 = (SphincsSecurity.oddFtsLeaf ⟨j, hj⟩).val
      from rfl, hash16_porsLeaf index _ sec.2, bind_map_left]
    rfl)]
  refine congrArg (· <$> _) ?_
  funext f
  rw [foldl_prod _ (fun acc j => acc ++ [dv (f j).1.2, dv (f j).2.2])
      (fun acc j => acc ++ [dv (f j).1.1, dv (f j).2.1]),
    foldl_finRange_appendList, foldl_finRange_appendList, List.nil_append, List.nil_append,
    flatten_unpairPorsLeaves f (fun r => dv r.2), flatten_unpairPorsLeaves f (fun r => dv r.1)]

theorem hash16_porsNodeFmt (index : Index) (lam j : Nat) (l r : Digest) :
    Ref.hash16 (Ref.porsNodeFmt index lam j (dv l) (dv r)) =
      dv <$> relabel fmtQ (SphincsSecurity.Concrete.tweakableHash (m := AComp) 0
        (.ftsNode index SphincsSecurity.Concrete.porsTree
          (SphincsSecurity.Concrete.ftsHeapIndex lam j)) (SphincsSecurity.Concrete.nodePayload l r)) :=
  hash16_porsNode index _ l r

/-- **The PORS tree**: levels `0 .. 14` (as `levelList`) and the secrets, leaf by leaf. -/
theorem buildPorsTree_eq (seed : MasterSeed) (index : Index) :
    Ref.buildPorsTree (Ref.toList (n := 32) seed) index =
      (fun r : (FtsLeaf → Digest) × (Nat → Nat → Digest) =>
        ((List.range (SphincsSecurity.ftsTreeHeight + 1)).map (levelList r.2 SphincsSecurity.ftsTreeHeight),
          List.ofFn fun j => dv (r.1 j))) <$>
        relabel fmtQ (SphincsSecurity.Concrete.buildFtsTreePaired (m := AComp) 0 index
          (SphincsSecurity.Seeded.ftsSecret 0 seed index SphincsSecurity.Concrete.porsTree)) := by
  unfold Ref.buildPorsTree SphincsSecurity.Concrete.buildFtsTreePaired
  rw [buildPorsLeaves_eq seed index]
  simp only [relabel_bind, relabel_pure, map_bind, bind_map_left, map_pure, bind_assoc, pure_bind]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun f => ?_
  rw [ofFn_leaves (SphincsSecurity.unpairFtsLeaves f) Prod.snd]
  unfold Ref.buildAllLevels
  rw [show Ref.porsH = SphincsSecurity.ftsTreeHeight from rfl]
  rw [buildAllLevels_steps (Ref.porsNodeFmt index) (fun level nodeIdx left right =>
      SphincsSecurity.Concrete.tweakableHash (m := AComp) 0
        (.ftsNode index SphincsSecurity.Concrete.porsTree (SphincsSecurity.Concrete.ftsHeapIndex level nodeIdx))
        (SphincsSecurity.Concrete.nodePayload left right)) (hash16_porsNodeFmt index) _
      (fun k => if h : k < 2 ^ SphincsSecurity.ftsTreeHeight then
        (SphincsSecurity.unpairFtsLeaves f ⟨k, h⟩).2 else 0) _ le_rfl]
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp]

/-! ## The opening and the signature bytes -/

theorem length_sortedSlots (leaves : IndexGroup → FtsLeaf) :
    (SphincsSecurity.Concrete.sortedSlots leaves).length = 15 := by
  unfold SphincsSecurity.Concrete.sortedSlots
  rw [List.length_insertionSort, List.length_finRange]; rfl

theorem sortedLeaves_lt (leaves : IndexGroup → FtsLeaf) :
    ∀ v ∈ SphincsSecurity.Concrete.sortedLeaves leaves, v < 2 ^ 14 := by
  intro v hv
  simp only [SphincsSecurity.Concrete.sortedLeaves, List.mem_map] at hv
  obtain ⟨r, _, rfl⟩ := hv
  exact (leaves r).isLt

/-- The secrets of the opening. -/
theorem opening_secrets (leaves : IndexGroup → FtsLeaf) (sec : FtsLeaf → Digest)
    (T : Nat → Nat → Digest) :
    (SphincsSecurity.Concrete.sortedLeaves leaves).map
        (fun x => (List.ofFn fun j : FtsLeaf => dv (sec j)).getD x []) =
      List.ofFn fun s => dv ((SphincsSecurity.Concrete.honestFts leaves sec T).secrets s) := by
  have hl := length_sortedSlots leaves
  apply List.ext_getElem (by simp [SphincsSecurity.Concrete.sortedLeaves, hl, SphincsSecurity.ftsOpenings])
  intro i h1 h2
  simp only [SphincsSecurity.Concrete.sortedLeaves, List.map_map, List.getElem_map, List.getElem_ofFn,
    SphincsSecurity.Concrete.honestFts, Function.comp]
  have hi : i < (SphincsSecurity.Concrete.sortedSlots leaves).length := by
    simp [SphincsSecurity.Concrete.sortedLeaves] at h1; exact h1
  rw [getD_ofFn, dif_pos ((SphincsSecurity.Concrete.sortedSlots leaves)[i]'hi |> leaves).isLt]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- A tree node read from the reference's level lists. -/
theorem levels_node (T : Nat → Nat → Digest) (p : Nat × Nat) (h1 : p.1 < 14)
    (h2 : p.2 < 2 ^ (14 - p.1)) :
    (((List.range (SphincsSecurity.ftsTreeHeight + 1)).map
        (levelList T SphincsSecurity.ftsTreeHeight)).getD p.1 []).getD p.2 [] = dv (T p.1 p.2) := by
  rw [getD_map_range_list _ _ _ (by simp [SphincsSecurity.ftsTreeHeight]; omega)]
  unfold levelList
  rw [getD_ofFn, dif_pos (by simpa [SphincsSecurity.ftsTreeHeight] using h2)]

/-- The nodes of an honest segment are the table's nodes at its reads. -/
theorem ofFn_toSegment_nodes (seg : SphincsSecurity.Concrete.ScheduleSegment) (hs : seg.reads.length ≤ 14)
    (T : Nat → Nat → Digest) :
    List.ofFn (seg.toSegment fun i =>
        let position := seg.reads.getD i.val (0, 0)
        T position.1 position.2).nodes = seg.reads.map fun p => T p.1 p.2 := by
  have hf : seg.folds.val = seg.reads.length := by
    simp only [SphincsSecurity.Concrete.ScheduleSegment.folds]; omega
  apply List.ext_getElem (by simp only [List.length_ofFn, List.length_map]; exact hf)
  intro i h1 h2
  simp only [List.getElem_ofFn, List.getElem_map, SphincsSecurity.Concrete.ScheduleSegment.toSegment,
    SphincsSecurity.Segment.normalized]
  have hi : i < seg.reads.length := by simpa using h2
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- The authentication nodes of the honest opening: the table's nodes at the schedule's reads. -/
theorem authNodes_honest (rho : Digest) (leaves : IndexGroup → FtsLeaf)
    (hadm : SphincsSecurity.Concrete.AdmissibleLeaves leaves) (sec : FtsLeaf → Digest)
    (T : Nat → Nat → Digest) (layers : (lay : Layer) → LayerSignature lay) :
    authNodes ⟨rho, SphincsSecurity.Concrete.honestFts leaves sec T, layers⟩ =
      (((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map
        (·.reads)).flatten).map fun p => T p.1 p.2 := by
  obtain ⟨hlen, hseg, -⟩ := schedule_admissible leaves hadm
  set segs := SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)
  unfold authNodes
  simp only [SphincsSecurity.Concrete.honestFts]
  rw [List.map_flatten, List.map_map]
  have e : (List.ofFn fun j : Fin SphincsSecurity.ftsSegments =>
      List.ofFn ((segs.getD j.val default).toSegment fun i =>
        let position := (segs.getD j.val default).reads.getD i.val (0, 0)
        T position.1 position.2).nodes) = segs.map ((List.map fun p => T p.1 p.2) ∘ (·.reads)) := by
    apply List.ext_getElem (by simp [hlen, SphincsSecurity.ftsSegments, SphincsSecurity.ftsOpenings])
    intro j h1 h2
    have hj : j < segs.length := by simpa using h2
    simp only [List.getElem_ofFn, List.getElem_map, Function.comp]
    have hg : segs.getD j default = segs[j] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl
    rw [hg]
    exact ofFn_toSegment_nodes _ (hseg _ (List.getElem_mem hj)).1 T
  exact congrArg List.flatten e

theorem length_flatten_map_dv (l : List Digest) : (l.map dv).flatten.length = 16 * l.length := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.map_cons, List.flatten_cons, List.length_append, length_dv, ih,
      List.length_cons]; ring

/-- The layer bytes of the reference serialization. -/
theorem serialize_layers (parts : Layer → SphincsSecurity.Concrete.LayerOutput) (σ : Signature)
    (hσ : σ.layers = fun lay => SphincsSecurity.Concrete.LayerOutput.toSignature lay (parts lay)) :
    ((List.ofFn fun l : Fin (4 + 1) =>
        layerRef (Fin.castLE (le_refl 5) l) (parts (Fin.castLE (le_refl 5) l))).map
      fun l => Ref.le32 l.1 ++ l.2.1.flatten ++ l.2.2.flatten).flatten =
      (List.ofFn (layerBytes σ)).flatten := by
  simp only [List.map_ofFn]
  congr 2
  funext l
  simp only [Function.comp, layerBytes, layerRef, map_range_eq_ofFn, hσ,
    SphincsSecurity.Concrete.LayerOutput.toSignature]
  rw [Ref.le32, leBytes_eq_toList]
  have e : ∀ c : SphincsSecurity.Counter,
      Ref.toList (n := 4) (BitVec.ofNat (8 * 4) c.toNat) = Ref.toList (n := 4) c := fun c => by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [e]
  rfl

/-- **The signature bytes**: the reference serialization of the PORS opening and the layers is the
compressed abstract signature. -/
theorem serialize_eq (rho : Digest) (leaves : IndexGroup → FtsLeaf)
    (hadm : SphincsSecurity.Concrete.AdmissibleLeaves leaves) (sec : FtsLeaf → Digest)
    (T : Nat → Nat → Digest) (parts : Layer → SphincsSecurity.Concrete.LayerOutput) :
    Ref.serialize (dv rho)
      (Ref.porsOpening (Ref.sortLeaves (List.ofFn fun r => (leaves r).val))
        ((List.range (SphincsSecurity.ftsTreeHeight + 1)).map (levelList T SphincsSecurity.ftsTreeHeight))
        (List.ofFn fun j => dv (sec j)))
      (List.ofFn fun l : Fin (4 + 1) =>
        layerRef (Fin.castLE (le_refl 5) l) (parts (Fin.castLE (le_refl 5) l))) =
    compressList ⟨rho, SphincsSecurity.Concrete.honestFts leaves sec T,
      fun lay => SphincsSecurity.Concrete.LayerOutput.toSignature lay (parts lay)⟩ := by
  obtain ⟨hlen, hseg, hoct⟩ := schedule_admissible leaves hadm
  have hoct' := hadm.2
  set σ : Signature := ⟨rho, SphincsSecurity.Concrete.honestFts leaves sec T,
      fun lay => SphincsSecurity.Concrete.LayerOutput.toSignature lay (parts lay)⟩ with hσ
  unfold Ref.serialize compressList
  rw [serialize_layers parts σ rfl, sortLeaves_eq]
  unfold Ref.porsOpening
  rw [schedule_ref _ (sortedLeaves_lt leaves)]
  simp only
  set segs := SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)
  set R := (segs.map (·.reads)).flatten with hR
  have hY : R.map (fun hj => (((List.range (SphincsSecurity.ftsTreeHeight + 1)).map
        (levelList T SphincsSecurity.ftsTreeHeight)).getD hj.1 []).getD hj.2 []) =
      (authNodes σ).map dv := by
    rw [hσ, authNodes_honest rho leaves hadm sec T, List.map_map]
    apply List.map_congr_left
    intro p hp
    rw [hR, List.mem_flatten] at hp
    obtain ⟨l, hl, hpl⟩ := hp
    rw [List.mem_map] at hl
    obtain ⟨sg, hsg, rfl⟩ := hl
    obtain ⟨h1, h2⟩ := (hseg sg hsg).2 p hpl
    exact levels_node T p h1 h2
  rw [opening_secrets leaves sec T, hY]
  have hn : (authNodes σ).length ≤ 120 := by
    rw [hσ, authNodes_honest rho leaves hadm sec T, List.length_map, hoct]
    exact hoct'
  have hA := length_flatten_map_dv (authNodes σ)
  simp only [List.flatten_append, List.flatten_replicate_replicate, List.length_append,
    List.length_ofFn, List.length_map, Ref.zeros, Ref.porsK, Ref.porsM, List.append_assoc]
  rw [List.take_append, List.take_of_length_le (by rw [hA]; omega), hA,
    List.take_replicate]
  have hk : (15 + 120 - (SphincsSecurity.ftsOpenings + (authNodes σ).length)) * 16 =
      min (16 * 120 - 16 * (authNodes σ).length) (16 * 120) := by
    simp only [SphincsSecurity.ftsOpenings]; omega
  rw [hk]
  simp only [List.append_assoc]
  rfl

/-! ## The digest search -/

/-- Project a reference digest-search result to what the rest of the signer reads. -/
def projN (r : Ref.Val × Nat) : Ref.Val × Nat × List Nat := (r.1, Ref.idxOf r.2, Ref.leavesOf r.2)

/-- The same projection of an abstract digest-search result. -/
def projA (r : Digest × Index × (IndexGroup → FtsLeaf)) : Ref.Val × Nat × List Nat :=
  (dv r.1, r.2.1.val, List.ofFn fun i => (r.2.2 i).val)

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
      simp only [projN, projA, idxOf_eq, leavesOf_eq]
    · simp only [hd, decide_false, if_false, pure_bind, Bool.false_eq_true]
      exact ih (a + 1)

theorem mem_support_relabel {ι ι' R α : Type} (f : ι → ι') (oa : OracleComp (ι →ₒ R) α) (x : α)
    (hx : x ∈ support (relabel f oa)) : x ∈ support oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => simpa using hx
  | query_bind t k ih =>
    rw [SigGolfCandidate.Bridge.relabel_query_bind] at hx
    rw [mem_support_bind_iff] at hx ⊢
    obtain ⟨u, -, hu⟩ := hx
    exact ⟨u, by simp, ih u hu⟩

/-- The digest loop only returns admissible leaves. -/
theorem signDigestLoop_admissible (sk : SphincsSecurity.Seeded.SecretKey) (m : Message) :
    ∀ (fuel a : Nat) (randomness : Digest) (index : Index) (leaves : IndexGroup → FtsLeaf),
      some (randomness, index, leaves) ∈
        support (SphincsSecurity.Seeded.signDigestLoop (m := AComp) sk m fuel a) →
      SphincsSecurity.Concrete.AdmissibleLeaves leaves := by
  intro fuel
  induction fuel with
  | zero => intro a randomness index leaves h; simp [SphincsSecurity.Seeded.signDigestLoop] at h
  | succ fuel ih =>
    intro a randomness index leaves h
    unfold SphincsSecurity.Seeded.signDigestLoop SphincsSecurity.Seeded.signAttempt at h
    simp only [bind_assoc, mem_support_bind_iff] at h
    obtain ⟨rho, -, d, -, h⟩ := h
    by_cases hd : SphincsSecurity.Concrete.Admissible d
    · simp only [hd, if_true, support_pure, Set.mem_singleton_iff, exists_eq_left] at h
      simp only [support_pure, Set.mem_singleton_iff, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, -, rfl⟩ := h
      exact hd
    · simp only [hd, if_false, support_pure, Set.mem_singleton_iff, exists_eq_left] at h
      exact ih (a + 1) randomness index leaves h

/-! ## The whole signer -/

/-- What the reference signer does after the MAC check and the digest search. -/
def signCont (S cache : List Byte) (rho : Ref.Val) (idx : Nat) (lv : List Nat) :
    OracleComp SigGolf.HashSpec (Option (List Byte)) := do
  let (levels, secrets) ← Ref.buildPorsTree S idx
  let M := (levels.getD Ref.porsH []).getD 0 []
  let fts := Ref.porsOpening (Ref.sortLeaves lv) levels secrets
  match ← Ref.signLayers S cache idx (Ref.nLayers - 1) M with
  | none => pure none
  | some lays => pure (some (Ref.serialize rho fts lays))

theorem signList_eq_cont (S cache m : List Byte) :
    Ref.signList S cache m = Ref.H (Ref.macInput S (Ref.cacheRegion cache)) >>= fun tag =>
      if Ref.toList (n := 32) tag = Ref.cacheTag cache then
        (Option.map projN <$> Ref.searchDigest S m 0 Ref.aMax) >>= fun r =>
          match r with
          | none => pure none
          | some (rho, idx, lv) => signCont S cache rho idx lv
      else pure none := by
  unfold Ref.signList
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun tag => ?_
  split_ifs
  · rw [bind_map_left]
    refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
    rcases r with _ | ⟨rho, N⟩ <;> rfl
  · rfl

theorem signCont_eq (seed : MasterSeed) (b : SigGolfCandidate.Cache) (randomness : Digest)
    (index : Index) (leaves : IndexGroup → FtsLeaf)
    (hadm : SphincsSecurity.Concrete.AdmissibleLeaves leaves) :
    signCont (Ref.toList (n := 32) seed) (Ref.toList b) (dv randomness) index
        (List.ofFn fun r => (leaves r).val) =
      Option.map compressList <$> relabel fmtQ
        (SphincsSecurity.Concrete.signFromPaired (m := AComp) 0 index
          (SphincsSecurity.Seeded.ftsSecret 0 seed index) (SphincsSecurity.Seeded.otsSecret 0 seed)
          (absTopNode seed b) randomness leaves) := by
  unfold signCont SphincsSecurity.Concrete.signFromPaired
  rw [buildPorsTree_eq]
  simp only [relabel_bind, relabel_pure, bind_map_left, map_bind, bind_assoc, pure_bind]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun tree => ?_
  rcases tree with ⟨sec, T⟩
  have hM : (((List.range (SphincsSecurity.ftsTreeHeight + 1)).map
      (levelList T SphincsSecurity.ftsTreeHeight)).getD Ref.porsH []).getD 0 [] =
      dv (T SphincsSecurity.ftsTreeHeight 0) := by
    rw [show Ref.porsH = SphincsSecurity.ftsTreeHeight from rfl,
      getD_map_range_list _ _ _ (by omega)]
    unfold levelList
    rw [getD_ofFn, dif_pos (by simp)]
  simp only
  rw [hM, show Ref.nLayers - 1 = 4 from rfl]
  rw [signLayers_eq seed b index 4 (le_refl 5) (T SphincsSecurity.ftsTreeHeight 0), bind_map_left]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
  rcases r with _ | parts
  · simp
  · simp only [Option.map_some, relabel_pure, map_pure]
    exact congrArg (fun x => pure (some x)) (serialize_eq randomness leaves hadm sec T parts)

theorem toB_macHashInput (seed : MasterSeed) (b : SigGolfCandidate.Cache) :
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
    (b : SigGolfCandidate.Cache) (m : Message) :
    Ref.signList (Ref.toList (n := 32) sk.seed) (Ref.toList b) (Ref.toList (n := 32) m) =
      Option.map compressList <$> relabel fmtQ
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
    refine OracleComp.bind_congr_of_forall_mem_support _ fun r hr => ?_
    rcases r with _ | ⟨randomness, index, leaves⟩
    · simp
    · simp only [Option.map_some, projA]
      have hadm := signDigestLoop_admissible sk m _ _ randomness index leaves
        (mem_support_relabel fmtQ _ _ hr)
      rw [signCont_eq _ _ _ _ _ hadm, hP]
  · rw [if_neg (fun h => ht ((cacheTag_iff b tag).mp h)), if_neg ht]
    simp

/-- **sign**: `signRef` is the relabelled abstract signer on the decoded cache, compressed. -/
theorem signRef_eq (sk : SphincsSecurity.Seeded.SecretKey) (hP : sk.parameter = 0)
    (b : SigGolfCandidate.Cache) (m : Bytes 32) :
    Ref.signRef sk.seed b m =
      Option.map compress <$> relabel fmtQ
        (SphincsSecurity.Seeded.sign (m := AComp) sk (cacheDec b) m) := by
  unfold Ref.signRef
  rw [signList_eq sk hP b m]
  simp only [Functor.map_map, map_eq_bind_pure_comp, bind_assoc, pure_bind]
  refine bind_congr (m := OracleComp SigGolf.HashSpec) fun r => ?_
  rcases r with _ | σ <;> rfl

end SigGolfCandidate.Equiv
