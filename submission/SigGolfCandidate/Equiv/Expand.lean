import SigGolfCandidate.Equiv.Layers
import SigGolfCandidate.Equiv.Sched

/-!
# Expansion (PORS+FP)

* `expandRef_eq`: the reference expansion is the relabelled abstract expansion `aExpand`.
* `expandOf_compress` / `aExpand_compress` (relation R2): every successful expansion decodes
  (`witSig`/`witDec`) to a signature that compresses back to the input.
* `expandOf_honest` (relation R4): an honest-shaped signature (the honest opening of admissible leaves)
  expands to a witness that decodes to the signature itself.
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

/-- **expand**: the reference expansion is the relabelled abstract expansion (any abstract key). -/
theorem expandRef_eq (m : Bytes 32) (pk : Bytes 16) (pk' : SphincsSecurity.PublicKey)
    (σ : Bytes 6100) :
    Ref.expandRef m pk σ = relabel fmtQ (aExpand m pk' σ) := by
  have hr : dv (Ref.ofList 16 (Ref.sigRho (Ref.toList σ))) = Ref.sigRho (Ref.toList σ) :=
    Ref.toList_ofList 16 _ (by simp [Ref.sigRho, Ref.slice, Ref.length_toList])
  unfold Ref.expandRef Ref.expandList aExpand
  rw [← hr, digest_eq pk'.root _ m]
  simp only [relabel_bind, relabel_pure, map_bind, bind_map_left, bind_assoc, pure_bind]
  rw [show Ref.ofList 16 (dv (Ref.ofList 16 (Ref.sigRho (Ref.toList σ)))) =
    Ref.ofList 16 (Ref.sigRho (Ref.toList σ)) from Ref.ofList_toList _]

/-! ## Generic list facts -/

theorem getD_append_right'' {β : Type} (l₁ l₂ : List β) (i : Nat) (d : β) (h : l₁.length ≤ i) :
    (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem getD_append_left'' {β : Type} (l₁ l₂ : List β) (i : Nat) (d : β) (h : i < l₁.length) :
    (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem wbytes_eq_slice (w : List Byte) (q n : Nat) (h : q + n ≤ w.length) :
    Ref.wbytes w q n = Ref.slice w q n := by
  apply List.ext_getElem
  · simp [Ref.wbytes, Ref.slice]; omega
  · intro i h1 h2
    simp only [Ref.wbytes, Ref.slice, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop, List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_getElem (by simp [Ref.wbytes] at h1; omega)]
    rfl

theorem slice_slice (l : List Byte) (a n b m : Nat) (h : b + m ≤ n) :
    Ref.slice (Ref.slice l a n) b m = Ref.slice l (a + b) m := by
  simp only [Ref.slice, List.drop_take, List.drop_drop, List.take_take]
  congr 1
  omega

/-- The auth-count prefix sums of segment bytes: `sum_{i < j} (bs_i mod 16)`. -/
def asum (bs : List Nat) (j : Nat) : Nat := ((bs.take j).map (· % 16)).sum

theorem asum_succ (bs : List Nat) (j : Nat) (hj : j < bs.length) :
    asum bs (j + 1) = asum bs j + bs.getD j 0 % 16 := by
  simp only [asum, List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some,
    List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons, List.sum_nil,
    List.getD_eq_getElem?_getD, Option.getD_some, Nat.add_zero]

theorem asum_mono (bs : List Nat) {j k : Nat} (h : j ≤ k) : asum bs j ≤ asum bs k := by
  unfold asum
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [List.take_add, List.map_append, List.sum_append]
  omega

theorem asum_length (bs : List Nat) : asum bs bs.length = (bs.map (· % 16)).sum := by
  simp [asum]

/-! ## The segment stream -/

/-- The stream of `Ref.segStream` from auth item `r` on. -/
def streamAux (sig : List Byte) : Nat → List Nat → List Byte
  | _, [] => []
  | r, b :: bs => [Ref.byte b] ++ Ref.zeros 7 ++
      ((List.range (b % 16)).map fun i => Ref.sigAuth sig (r + i)).flatten ++ streamAux sig (r + b % 16) bs

theorem foldl_streamStep (sig : List Byte) : ∀ (bs : List Nat) (acc : List Byte) (r : Nat),
    bs.foldl (Ref.streamStep sig) (acc, r) = (acc ++ streamAux sig r bs, r + (bs.map (· % 16)).sum)
  | [], acc, r => by simp [streamAux]
  | b :: bs, acc, r => by
    rw [List.foldl_cons]
    have e : Ref.streamStep sig (acc, r) b = (acc ++ [Ref.byte b] ++ Ref.zeros 7 ++
        ((List.range (b % 16)).map fun i => Ref.sigAuth sig (r + i)).flatten, r + b % 16) := rfl
    rw [e, foldl_streamStep sig bs]
    simp [streamAux, List.append_assoc, Nat.add_assoc]

theorem segStream_eq (sig : List Byte) (segs : List Nat) :
    Ref.segStream sig segs = streamAux sig 0 segs := by
  unfold Ref.segStream
  rw [foldl_streamStep]
  simp

section stream
variable (sig : List Byte) (hsig : sig.length = 6100)
include hsig

theorem length_sigAuth (k : Nat) (hk : k < 120) : (Ref.sigAuth sig k).length = 16 := by
  unfold Ref.sigAuth Ref.sigItem
  exact length_slice _ _ _ (by rw [hsig]; unfold Ref.porsK; omega)

theorem length_chunk (r a : Nat) (h : r + a ≤ 120) :
    ((List.range a).map fun i => Ref.sigAuth sig (r + i)).flatten.length = 16 * a := by
  rw [map_range_eq_ofFn, length_flatten_ofFn _ 16 (fun j => length_sigAuth sig hsig _ (by omega))]

theorem length_streamAux : ∀ (bs : List Nat) (r : Nat), r + (bs.map (· % 16)).sum ≤ 120 →
    (streamAux sig r bs).length = 8 * bs.length + 16 * (bs.map (· % 16)).sum
  | [], r, _ => by simp [streamAux]
  | b :: bs, r, h => by
    simp only [List.map_cons, List.sum_cons] at h
    simp only [streamAux, List.length_append, List.length_singleton, Ref.length_zeros,
      length_chunk sig hsig r (b % 16) (by omega),
      length_streamAux bs (r + b % 16) (by omega), List.length_cons, List.map_cons, List.sum_cons,
      List.length_nil]
    ring

theorem getD_streamAux : ∀ (bs : List Nat) (r j : Nat), r + (bs.map (· % 16)).sum ≤ 120 →
    j < bs.length →
    (streamAux sig r bs).getD (8 * j + 16 * asum bs j) 0 = Ref.byte (bs.getD j 0)
  | [], r, j, _, hj => by simp at hj
  | b :: bs, r, j, h, hj => by
    simp only [List.map_cons, List.sum_cons] at h
    cases j with
    | zero => simp [streamAux, asum]
    | succ j =>
      have ha : asum (b :: bs) (j + 1) = b % 16 + asum bs j := by simp [asum]
      rw [ha]
      unfold streamAux
      rw [getD_append_right'' _ _ _ _ (by
        simp only [List.length_append, List.length_singleton, Ref.length_zeros,
          length_chunk sig hsig r (b % 16) (by omega)]; omega)]
      simp only [List.length_append, List.length_singleton, Ref.length_zeros,
        length_chunk sig hsig r (b % 16) (by omega)]
      rw [show 8 * (j + 1) + 16 * (b % 16 + asum bs j) - (1 + 7 + 16 * (b % 16)) =
        8 * j + 16 * asum bs j by omega]
      rw [getD_streamAux bs (r + b % 16) j (by omega) (by simpa using hj)]
      rfl

theorem slice_streamAux : ∀ (bs : List Nat) (r j i : Nat), r + (bs.map (· % 16)).sum ≤ 120 →
    j < bs.length → i < bs.getD j 0 % 16 →
    Ref.slice (streamAux sig r bs) (8 * j + 16 * asum bs j + 8 + 16 * i) 16 =
      Ref.sigAuth sig (r + asum bs j + i)
  | [], r, j, i, _, hj, _ => by simp at hj
  | b :: bs, r, j, i, h, hj, hi => by
    simp only [List.map_cons, List.sum_cons] at h
    cases j with
    | zero =>
      simp only [List.getD_cons_zero] at hi
      simp only [asum, List.take_zero, List.map_nil, List.sum_nil, Nat.mul_zero, Nat.zero_add,
        Nat.add_zero]
      unfold streamAux
      rw [List.append_assoc, slice_append_right _ _ _ (16 * i) _ (by simp),
        slice_append_left _ _ _ _ (by rw [length_chunk sig hsig r (b % 16) (by omega)]; omega),
        map_range_eq_ofFn,
        slice_flatten_ofFn _ 16 ⟨i, hi⟩ 0 16 _ (fun k _ => length_sigAuth sig hsig _ (by omega))
          (by simp [length_sigAuth sig hsig _ (show r + i < 120 by omega)]) (by ring),
        slice_full _ _ (length_sigAuth sig hsig _ (by omega))]
    | succ j =>
      simp only [List.getD_cons_succ] at hi
      have ha : asum (b :: bs) (j + 1) = b % 16 + asum bs j := by simp [asum]
      rw [ha]
      unfold streamAux
      rw [slice_append_right _ _ _ (8 * j + 16 * asum bs j + 8 + 16 * i) _ (by
        simp only [List.length_append, List.length_singleton, Ref.length_zeros,
          length_chunk sig hsig r (b % 16) (by omega)]; omega)]
      rw [slice_streamAux bs (r + b % 16) j i (by omega) (by simpa using hj) hi]
      congr 1; omega

end stream

/-- Consecutive chunks of auth items, read back in order. -/
theorem chunks_eq (bs : List Nat) (f : Nat → List Byte) :
    ∀ k, k ≤ bs.length →
      ((List.range k).map fun j =>
          ((List.range (bs.getD j 0 % 16)).map fun i => f (asum bs j + i)).flatten).flatten =
        ((List.range (asum bs k)).map f).flatten := by
  intro k
  induction k with
  | zero => intro _; simp [asum]
  | succ k ih =>
    intro hk
    rw [List.range_succ, List.map_append, List.flatten_append, ih (by omega),
      asum_succ bs k (by omega), List.range_add, List.map_append, List.flatten_append]
    simp [List.map_map, Function.comp_def]

/-! ## The witness layout -/

section layout
variable (sig : List Byte) (hsig : sig.length = 6100) (v vs segs : List Nat) (hvs : vs.length = 15)

/-- The witness: `head (272 bytes) ++ stream region ++ tail`. -/
theorem witnessList_split : Ref.witnessList sig v vs segs =
    (Ref.sigRho sig ++ vs.map (fun x => Ref.byte (8 * v.idxOf x)) ++ Ref.zeros 1 ++
      ((List.range Ref.porsK).map (Ref.sigItem sig)).flatten) ++
    (Ref.segStream sig segs ++ Ref.zeros Ref.streamBytes).take Ref.streamBytes ++
    (((List.range Ref.nLayers).map (Ref.sigLayerBody sig)).flatten ++
      ((List.range Ref.nLayers).map (Ref.sigCounterBytes sig)).flatten) := by
  simp only [Ref.witnessList, List.append_assoc]
  rfl

include hsig in
theorem length_sigItem (i : Nat) (hi : i < 135) : (Ref.sigItem sig i).length = 16 :=
  length_slice _ _ _ (by rw [hsig]; omega)

include hsig hvs in
theorem length_head :
    (Ref.sigRho sig ++ vs.map (fun x => Ref.byte (8 * v.idxOf x)) ++ Ref.zeros 1 ++
      ((List.range Ref.porsK).map (Ref.sigItem sig)).flatten).length = 272 := by
  simp only [List.length_append, List.length_map, hvs, Ref.length_zeros]
  rw [show (Ref.sigRho sig).length = 16 from length_slice _ _ _ (by rw [hsig]; omega),
    map_range_eq_ofFn, length_flatten_ofFn _ 16 (fun j => length_sigItem sig hsig _ (by
      have := j.isLt; unfold Ref.porsK at this; omega))]
  rfl


theorem length_E : ((Ref.segStream sig segs ++ Ref.zeros Ref.streamBytes).take Ref.streamBytes).length =
    2152 := by
  simp [Ref.streamBytes, Ref.porsSegs, Ref.porsK, Ref.porsM]

theorem layer_bound : ∀ l, l < 5 → Ref.sigLayerOff l + Ref.sigLayerBytes l ≤ 6100 := by decide

include hsig in
theorem length_sigLayerBody (l : Nat) (hl : l < 5) :
    (Ref.sigLayerBody sig l).length = Ref.sigLayerBytes l - 4 :=
  length_slice _ _ _ (by have := layer_bound l hl; rw [hsig]; unfold Ref.sigLayerBytes at *; omega)

include hsig in
theorem length_sigCounterBytes (l : Nat) (hl : l < 5) : (Ref.sigCounterBytes sig l).length = 4 :=
  length_slice _ _ _ (by have := layer_bound l hl; rw [hsig]; unfold Ref.sigLayerBytes at *; omega)

include hsig in
theorem length_bodies (k : Nat) (hk : k ≤ 5) :
    ((List.range k).map (Ref.sigLayerBody sig)).flatten.length =
      ((List.range k).map fun l => Ref.sigLayerBytes l - 4).sum := by
  rw [List.length_flatten, List.map_map]
  congr 1
  apply List.map_congr_left
  intro l hl
  exact length_sigLayerBody sig hsig l (by rw [List.mem_range] at hl; omega)

include hsig in
theorem length_T :
    (((List.range Ref.nLayers).map (Ref.sigLayerBody sig)).flatten ++
      ((List.range Ref.nLayers).map (Ref.sigCounterBytes sig)).flatten).length = 3924 := by
  rw [List.length_append, length_bodies sig hsig Ref.nLayers (by decide), map_range_eq_ofFn (f := Ref.sigCounterBytes sig),
    length_flatten_ofFn (fun j : Fin Ref.nLayers => Ref.sigCounterBytes sig j.val) 4
      (fun j => length_sigCounterBytes sig hsig _ j.isLt)]
  decide

include hsig hvs in
theorem slice_W_head (x len : Nat) (h : x + len ≤ 272) :
    Ref.slice (Ref.witnessList sig v vs segs) x len =
      Ref.slice (Ref.sigRho sig ++ vs.map (fun x => Ref.byte (8 * v.idxOf x)) ++ Ref.zeros 1 ++
        ((List.range Ref.porsK).map (Ref.sigItem sig)).flatten) x len := by
  rw [witnessList_split, slice_append_left _ _ _ _ (by rw [List.length_append, length_head sig hsig v vs hvs]; omega),
    slice_append_left _ _ _ _ (by rw [length_head sig hsig v vs hvs]; omega)]

include hsig hvs in
theorem getD_W_head (x : Nat) (h : x < 272) :
    (Ref.witnessList sig v vs segs).getD x 0 =
      (Ref.sigRho sig ++ vs.map (fun x => Ref.byte (8 * v.idxOf x)) ++ Ref.zeros 1 ++
        ((List.range Ref.porsK).map (Ref.sigItem sig)).flatten).getD x 0 := by
  rw [witnessList_split, getD_append_left'' _ _ _ _ (by rw [List.length_append, length_head sig hsig v vs hvs]; omega),
    getD_append_left'' _ _ _ _ (by rw [length_head sig hsig v vs hvs]; omega)]

include hsig hvs in
theorem slice_W_E (x len : Nat) (h : x + len ≤ 2152) :
    Ref.slice (Ref.witnessList sig v vs segs) (272 + x) len =
      Ref.slice ((Ref.segStream sig segs ++ Ref.zeros Ref.streamBytes).take Ref.streamBytes) x len := by
  rw [witnessList_split, slice_append_left _ _ _ _ (by rw [List.length_append, length_head sig hsig v vs hvs, length_E]; omega),
    slice_append_right _ _ _ x _ (by rw [length_head sig hsig v vs hvs])]

include hsig hvs in
theorem getD_W_E (x : Nat) (h : x < 2152) :
    (Ref.witnessList sig v vs segs).getD (272 + x) 0 =
      ((Ref.segStream sig segs ++ Ref.zeros Ref.streamBytes).take Ref.streamBytes).getD x 0 := by
  rw [witnessList_split, getD_append_left'' _ _ _ _ (by rw [List.length_append, length_head sig hsig v vs hvs, length_E]; omega),
    getD_append_right'' _ _ _ _ (by rw [length_head sig hsig v vs hvs]; omega),
    length_head sig hsig v vs hvs, Nat.add_sub_cancel_left]

include hsig hvs in
theorem slice_W_T (x len : Nat) (h : x + len ≤ 3924) :
    Ref.slice (Ref.witnessList sig v vs segs) (2424 + x) len =
      Ref.slice (((List.range Ref.nLayers).map (Ref.sigLayerBody sig)).flatten ++
        ((List.range Ref.nLayers).map (Ref.sigCounterBytes sig)).flatten) x len := by
  rw [witnessList_split, slice_append_right _ _ _ x _ (by rw [List.length_append, length_head sig hsig v vs hvs, length_E])]

include hsig hvs in
theorem witRho_W : Ref.witRho (Ref.witnessList sig v vs segs) = Ref.sigRho sig := by
  unfold Ref.witRho
  rw [slice_W_head sig hsig v vs segs hvs 0 16 (by omega), List.append_assoc, List.append_assoc,
    slice_append_left _ _ _ _ (by rw [show (Ref.sigRho sig).length = 16 from
      length_slice _ _ _ (by rw [hsig]; omega)]),
    slice_full _ _ (show (Ref.sigRho sig).length = 16 from length_slice _ _ _ (by rw [hsig]; omega))]

include hsig hvs in
theorem witSecret_W (s : Nat) (hs : s < 15) :
    Ref.witSecret (Ref.witnessList sig v vs segs) s = Ref.sigItem sig s := by
  unfold Ref.witSecret
  rw [slice_W_head sig hsig v vs segs hvs _ 16 (by unfold Ref.wSec; omega)]
  rw [slice_append_right _ _ _ (16 * s) _ (by
    simp only [List.length_append, List.length_map, hvs, Ref.length_zeros]
    rw [show (Ref.sigRho sig).length = 16 from length_slice _ _ _ (by rw [hsig]; omega)]
    unfold Ref.wSec; omega)]
  rw [map_range_eq_ofFn, slice_flatten_ofFn (fun j : Fin Ref.porsK => Ref.sigItem sig j.val) 16 ⟨s, hs⟩
    0 16 (16 * s)
    (fun j _ => length_sigItem sig hsig _ (by have := j.isLt; unfold Ref.porsK at this; omega))
    (by rw [length_sigItem sig hsig _ (by simp; omega)]) (by ring),
    slice_full _ _ (length_sigItem sig hsig _ (by simp; omega))]

include hsig hvs in
theorem witPi_W (s : Nat) (hs : s < 15) :
    Ref.witPi (Ref.witnessList sig v vs segs) s = (Ref.byte (8 * v.idxOf (vs.getD s 0))).toNat := by
  unfold Ref.witPi
  rw [getD_W_head sig hsig v vs segs hvs _ (by unfold Ref.wPi; omega), List.append_assoc,
    List.append_assoc,
    getD_append_right'' _ _ _ _ (by rw [show (Ref.sigRho sig).length = 16 from
      length_slice _ _ _ (by rw [hsig]; omega)]; unfold Ref.wPi; omega),
    show (Ref.sigRho sig).length = 16 from length_slice _ _ _ (by rw [hsig]; omega),
    getD_append_left'' _ _ _ _ (by simp [hvs]; unfold Ref.wPi; omega)]
  simp only [Ref.wPi, show 16 + s - 16 = s by omega, List.getD_eq_getElem?_getD, List.getElem?_map]
  rw [List.getElem?_eq_getElem (by omega)]
  rfl


/-! ### Layers -/

theorem layer_table : ∀ l, l < 5 →
    Ref.witLayerOff l = 2424 + ((List.range l).map fun l => Ref.sigLayerBytes l - 4).sum ∧
    ((List.range l).map fun l => Ref.sigLayerBytes l - 4).sum + (Ref.sigLayerBytes l - 4) ≤ 3904 ∧
    Ref.sigLayerBytes l = 676 + 16 * Ref.height l ∧ 2176 ≤ Ref.sigLayerOff l := by decide

include hsig in
theorem slice_bodies (lay : Nat) (hlay : lay < 5) (y len : Nat)
    (hy : y + len ≤ Ref.sigLayerBytes lay - 4) :
    Ref.slice ((List.range Ref.nLayers).map (Ref.sigLayerBody sig)).flatten
        (((List.range lay).map fun l => Ref.sigLayerBytes l - 4).sum + y) len =
      Ref.slice sig (Ref.sigLayerOff lay + 4 + y) len := by
  have hL : ((List.range Ref.nLayers).map (Ref.sigLayerBody sig)).take lay =
      (List.range lay).map (Ref.sigLayerBody sig) := by
    rw [← List.map_take, List.take_range, Nat.min_eq_left (by unfold Ref.nLayers; omega)]
  have e := slice_flatten_take ((List.range Ref.nLayers).map (Ref.sigLayerBody sig)) lay y len
    (by simp [Ref.nLayers]; omega) (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by unfold Ref.nLayers; omega)]
      simp only [Option.map_some, Option.getD_some]
      rw [length_sigLayerBody sig hsig lay hlay]; exact hy)
  rw [hL, length_bodies sig hsig lay (by omega)] at e
  rw [e, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (by unfold Ref.nLayers; omega)]
  simp only [Option.map_some, Option.getD_some]
  unfold Ref.sigLayerBody
  rw [slice_slice _ _ _ _ _ hy]

/-- A layer read at the signature offsets. -/
def sigLayerOf (sig : List Byte) (lay : Layer) : LayerSignature lay :=
  ⟨Ref.ofList 4 (Ref.sigCounterBytes sig lay.val),
    fun i => Ref.ofList 16 (Ref.slice sig (Ref.sigLayerOff lay.val + 4 + 16 * i.val) 16),
    fun l => Ref.ofList 16 (Ref.slice sig (Ref.sigLayerOff lay.val + 4 + (672 + 16 * l.val)) 16)⟩

include hsig hvs in
theorem witLayer_W (lay : Layer) :
    witLayer (Ref.witnessList sig v vs segs) lay = sigLayerOf sig lay := by
  have hl := lay.isLt
  simp only [SphincsSecurity.numLayers] at hl
  obtain ⟨t1, t2, t3, t4⟩ := layer_table lay.val hl
  have hh := height_eq lay
  have hB : ((List.range Ref.nLayers).map fun l => Ref.sigLayerBytes l - 4).sum = 3904 := by decide
  unfold witLayer sigLayerOf
  congr 1
  · -- the counter
    congr 1
    rw [show Ref.witCounters + 4 * lay.val = 2424 + (3904 + 4 * lay.val) by
      rw [Ref.witCounters_eq]; omega,
      slice_W_T sig hsig v vs segs hvs _ _ (by omega),
      slice_append_right _ _ _ (4 * lay.val) _ (by
        rw [length_bodies sig hsig _ (by decide), hB]),
      map_range_eq_ofFn (f := Ref.sigCounterBytes sig),
      slice_flatten_ofFn (fun j : Fin Ref.nLayers => Ref.sigCounterBytes sig j.val) 4
        ⟨lay.val, by unfold Ref.nLayers; omega⟩ 0 4 (4 * lay.val)
        (fun j _ => length_sigCounterBytes sig hsig _ j.isLt)
        (by rw [length_sigCounterBytes sig hsig _ hl]) (by ring),
      slice_full _ _ (length_sigCounterBytes sig hsig _ hl)]
  · funext i
    congr 1
    have hi := i.isLt
    simp only [SphincsSecurity.numChains] at hi
    unfold Ref.witChain
    rw [t1, show 2424 + ((List.range lay.val).map fun l => Ref.sigLayerBytes l - 4).sum + 16 * i.val =
      2424 + (((List.range lay.val).map fun l => Ref.sigLayerBytes l - 4).sum + 16 * i.val) by ring,
      slice_W_T sig hsig v vs segs hvs _ _ (by omega),
      slice_append_left _ _ _ _ (by rw [length_bodies sig hsig _ (by decide), hB]; omega),
      slice_bodies sig hsig lay.val hl _ _ (by omega)]
  · funext l
    congr 1
    have hlt : l.val < Ref.height lay.val := by rw [hh]; exact l.isLt
    unfold Ref.witSib
    rw [t1, show 2424 + ((List.range lay.val).map fun l => Ref.sigLayerBytes l - 4).sum + 672 +
        16 * l.val =
      2424 + (((List.range lay.val).map fun l => Ref.sigLayerBytes l - 4).sum + (672 + 16 * l.val)) by
        ring,
      slice_W_T sig hsig v vs segs hvs _ _ (by omega),
      slice_append_left _ _ _ _ (by rw [length_bodies sig hsig _ (by decide), hB]; omega),
      slice_bodies sig hsig lay.val hl _ _ (by omega)]


/-! ### The stream region -/

theorem slice_take (l : List Byte) (k x len : Nat) (h : x + len ≤ k) :
    Ref.slice (l.take k) x len = Ref.slice l x len := by
  unfold Ref.slice
  rw [List.drop_take, List.take_take, Nat.min_eq_left (by omega)]

theorem ofFn_segAt_nodes (w : List Byte) (p : Nat) :
    List.ofFn (segAt w p).nodes = (List.range (Ref.wbyte w p % 16)).map fun i => wdig w (p + 8 + 16 * i) :=
  (map_range_eq_ofFn (Ref.wbyte w p % 16) (fun i => wdig w (p + 8 + 16 * i))).symm

section streamFacts
variable (hsegs : segs.length = 29) (hb : ∀ b ∈ segs, b < 256)
  (hn : (segs.map (· % 16)).sum ≤ 120)

include hsig hn in
theorem length_segStream :
    (Ref.segStream sig segs).length = 8 * segs.length + 16 * (segs.map (· % 16)).sum := by
  rw [segStream_eq, length_streamAux sig hsig segs 0 (by omega)]

include hsig hvs hsegs hn in
theorem getD_W_seg (j : Nat) (hj : j < 29) :
    (Ref.witnessList sig v vs segs).getD (272 + (8 * j + 16 * asum segs j)) 0 =
      Ref.byte (segs.getD j 0) := by
  have ha : asum segs j ≤ (segs.map (· % 16)).sum := by
    rw [← asum_length]; exact asum_mono segs (by omega)
  have hL := length_segStream sig hsig segs hn
  rw [getD_W_E sig hsig v vs segs hvs _ (by omega)]
  rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt (by rw [Ref.streamBytes_eq]; omega),
    ← List.getD_eq_getElem?_getD, getD_append_left'' _ _ _ _ (by rw [hL]; omega), segStream_eq,
    getD_streamAux sig hsig segs 0 j (by omega) (by omega)]

include hsig hvs hsegs hn in
theorem slice_W_node (j i : Nat) (hj : j < 29) (hi : i < segs.getD j 0 % 16) :
    Ref.slice (Ref.witnessList sig v vs segs) (272 + (8 * j + 16 * asum segs j + 8 + 16 * i)) 16 =
      Ref.sigAuth sig (asum segs j + i) := by
  have ha : asum segs (j + 1) ≤ (segs.map (· % 16)).sum := by
    rw [← asum_length]; exact asum_mono segs (by omega)
  rw [asum_succ segs j (by omega)] at ha
  have hL := length_segStream sig hsig segs hn
  rw [slice_W_E sig hsig v vs segs hvs _ _ (by omega)]
  rw [slice_take _ _ _ _ (by rw [Ref.streamBytes_eq]; omega),
    slice_append_left _ _ _ _ (by rw [hL]; omega), segStream_eq,
    slice_streamAux sig hsig segs 0 j i (by omega) (by omega) hi, Nat.zero_add]

include hsig hvs hsegs hb hn in
theorem segPtr_W (j : Nat) (hj : j ≤ 29) :
    segPtr (Ref.witnessList sig v vs segs) j = 272 + (8 * j + 16 * asum segs j) := by
  induction j with
  | zero => simp [segPtr, asum, Ref.wStream, Ref.wSec, Ref.porsK]
  | succ j ih =>
    rw [segPtr, ih (by omega)]
    unfold Ref.wbyte
    rw [getD_W_seg sig hsig v vs segs hvs hsegs hn j (by omega), Ref.byte_toNat,
      asum_succ segs j (by omega)]
    have : segs.getD j 0 < 256 := hb _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _)
    rw [Nat.mod_eq_of_lt this]
    ring

include hsig hvs hsegs hb hn in
theorem wbyte_segPtr_W (j : Nat) (hj : j < 29) :
    Ref.wbyte (Ref.witnessList sig v vs segs) (segPtr (Ref.witnessList sig v vs segs) j) =
      segs.getD j 0 := by
  rw [segPtr_W sig hsig v vs segs hvs hsegs hb hn j (by omega)]
  unfold Ref.wbyte
  rw [getD_W_seg sig hsig v vs segs hvs hsegs hn j hj, Ref.byte_toNat]
  exact Nat.mod_eq_of_lt (hb _ (by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _))

include hsig hvs hsegs hb hn in
theorem dv_node_W (j i : Nat) (hj : j < 29) (hi : i < segs.getD j 0 % 16) :
    dv (wdig (Ref.witnessList sig v vs segs) (segPtr (Ref.witnessList sig v vs segs) j + 8 + 16 * i)) =
      Ref.sigAuth sig (asum segs j + i) := by
  have hW := Ref.length_witnessList sig hsig v vs segs hvs
  have ha : asum segs (j + 1) ≤ (segs.map (· % 16)).sum := by
    rw [← asum_length]; exact asum_mono segs (by omega)
  rw [asum_succ segs j (by omega)] at ha
  rw [dv_wdig, segPtr_W sig hsig v vs segs hvs hsegs hb hn j (by omega),
    wbytes_eq_slice _ _ _ (by rw [hW]; unfold Ref.witBytes; omega),
    show 272 + (8 * j + 16 * asum segs j) + 8 + 16 * i = 272 + (8 * j + 16 * asum segs j + 8 + 16 * i)
      by ring,
    slice_W_node sig hsig v vs segs hvs hsegs hn j i hj hi]

include hsig hvs hsegs hb hn in
/-- The authentication nodes the decoder reads are the signature's first `n` auth items. -/
theorem authNodes_W :
    ((authNodes (witSig (Ref.witnessList sig v vs segs))).map dv).flatten =
      ((List.range (segs.map (· % 16)).sum).map (Ref.sigAuth sig)).flatten := by
  unfold authNodes
  rw [List.map_flatten, List.map_ofFn, List.flatten_flatten]
  have e : ∀ j : Fin SphincsSecurity.ftsSegments,
      ((List.map dv ∘ fun j => List.ofFn ((witSig (Ref.witnessList sig v vs segs)).fts.segments j).nodes) j)
        = (List.range (segs.getD j.val 0 % 16)).map fun i => Ref.sigAuth sig (asum segs j.val + i) := by
    intro j
    have hj : j.val < 29 := j.isLt
    simp only [Function.comp_apply, witSig, witFts]
    rw [ofFn_segAt_nodes, List.map_map, wbyte_segPtr_W sig hsig v vs segs hvs hsegs hb hn j.val hj]
    apply List.map_congr_left
    intro i hi
    rw [List.mem_range] at hi
    exact dv_node_W sig hsig v vs segs hvs hsegs hb hn j.val i hj hi
  rw [List.ofFn_inj.mpr (funext e)]
  have e3 : ∀ (F : Nat → List Byte) (G : Fin SphincsSecurity.ftsSegments → List Byte),
      (∀ j, G j = F j.val) → List.ofFn G = (List.range SphincsSecurity.ftsSegments).map F :=
    fun F G h => by rw [map_range_eq_ofFn]; exact List.ofFn_inj.mpr (funext h)
  rw [List.map_ofFn, e3 (fun j => ((List.range (segs.getD j 0 % 16)).map
    fun i => Ref.sigAuth sig (asum segs j + i)).flatten)
    (List.flatten ∘ fun x : Fin SphincsSecurity.ftsSegments =>
      (List.range (segs.getD x.val 0 % 16)).map fun i => Ref.sigAuth sig (asum segs x.val + i))
    (fun j => rfl)]
  rw [show SphincsSecurity.ftsSegments = segs.length by rw [hsegs]; rfl, chunks_eq segs _ _ (le_refl _),
    asum_length]

end streamFacts


include hsig in
theorem layerBytes_of (S : Signature) (lay : Layer) (h : S.layers lay = sigLayerOf sig lay) :
    layerBytes S lay = Ref.slice sig (Ref.sigLayerOff lay.val) (Ref.sigLayerBytes lay.val) := by
  have hl := lay.isLt
  simp only [SphincsSecurity.numLayers] at hl
  obtain ⟨-, -, t3, -⟩ := layer_table lay.val hl
  have hb := layer_bound lay.val hl
  have hh := height_eq lay
  unfold layerBytes
  rw [h]
  simp only [sigLayerOf]
  rw [Ref.toList_ofList 4 _ (length_sigCounterBytes sig hsig _ hl)]
  have ec : (List.ofFn fun i : Fin SphincsSecurity.numChains =>
      dv (Ref.ofList 16 (Ref.slice sig (Ref.sigLayerOff lay.val + 4 + 16 * i.val) 16))).flatten =
      Ref.slice sig (Ref.sigLayerOff lay.val + 4) (16 * 42) := by
    rw [← flatten_ofFn_slices]
    congr 1
    exact List.ofFn_inj.mpr (funext fun i => dv_ofList_slice _ _ (by
      have := i.isLt; simp only [SphincsSecurity.numChains] at this; rw [hsig]; omega))
  have ep : (List.ofFn fun l : Fin (SphincsSecurity.layerHeight lay) =>
      dv (Ref.ofList 16 (Ref.slice sig (Ref.sigLayerOff lay.val + 4 + (672 + 16 * l.val)) 16))).flatten =
      Ref.slice sig (Ref.sigLayerOff lay.val + 4 + 672) (16 * SphincsSecurity.layerHeight lay) := by
    rw [← flatten_ofFn_slices]
    congr 1
    refine List.ofFn_inj.mpr (funext fun l => ?_)
    have := l.isLt
    rw [dv_ofList_slice _ _ (by rw [hsig]; omega)]
    congr 1; ring
  rw [ec, ep, Ref.sigCounterBytes, List.append_assoc, ← slice_split, ← slice_split]
  congr 1
  rw [t3, hh]; ring

end layout

/-! ## R2 -/

theorem segByte_raw : ∀ a, a < 16 → ∀ m p : Bool,
    (a ||| (if m then 16 else 0) ||| 32 * (if p then 1 else 0)) =
      a + (if m then 16 else 0) + 32 * (if p then 1 else 0) := by decide

theorem segByte_val (sg : SphincsSecurity.Concrete.ScheduleSegment) (h : sg.reads.length < 16) :
    segByte sg = sg.reads.length + (if sg.merge then 16 else 0) + 32 * (if sg.parity then 1 else 0) :=
  segByte_raw _ h _ _

/-- The digest leaves of `N` as a slot map. -/
def leavesN (N : Nat) : IndexGroup → FtsLeaf := fun r => ⟨Ref.leafOf N r.val, Nat.mod_lt _ (by decide)⟩

theorem leavesOf_leavesN (N : Nat) : Ref.leavesOf N = List.ofFn fun r => (leavesN N r).val := by
  unfold Ref.leavesOf
  rw [map_range_eq_ofFn]
  rfl

/-- What a successful `expandOf` knows: the admissible leaves, the schedule, the zero slots. -/
theorem expandOf_some (sig : List Byte) (N : Nat) (wl : List Byte)
    (h : Ref.expandOf sig N = some wl) :
    let vs := Ref.sortLeaves (Ref.leavesOf N)
    (Ref.leavesOf N).Nodup ∧ Ref.octopusSize vs ≤ 120 ∧
      (∀ i, (Ref.schedule vs).2.length ≤ i → i < 120 → Ref.sigAuth sig i = Ref.zeros 16) ∧
      wl = Ref.witnessList sig (Ref.leavesOf N) vs (Ref.schedule vs).1 := by
  unfold Ref.expandOf at h
  dsimp only at h
  split at h
  · cases h
  next hnd =>
  split at h
  · cases h
  next hoct =>
  split at h
  · cases h
  next hz =>
  cases h
  refine ⟨by simpa using hnd, by unfold Ref.porsM at hoct; omega, ?_, rfl⟩
  intro i hi1 hi2
  have hz' : (List.range' (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).2.length
      (Ref.porsM - (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).2.length)).all
      (fun i => Ref.sigAuth sig i == Ref.zeros 16) = true := by simpa using hz
  have := List.all_eq_true.mp hz' i (List.mem_range'_1.mpr ⟨hi1, by unfold Ref.porsM; omega⟩)
  simpa using this

/-- The schedule facts for the leaves of any `N` passing `expandOf`'s checks. -/
theorem sched_facts (N : Nat) (hnd : (Ref.leavesOf N).Nodup)
    (hoct : Ref.octopusSize (Ref.sortLeaves (Ref.leavesOf N)) ≤ 120) :
    let sched := SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves (leavesN N))
    SphincsSecurity.Concrete.AdmissibleLeaves (leavesN N) ∧
    Ref.sortLeaves (Ref.leavesOf N) = SphincsSecurity.Concrete.sortedLeaves (leavesN N) ∧
    Ref.schedule (Ref.sortLeaves (Ref.leavesOf N)) =
      (sched.map segByte, (sched.map (·.reads)).flatten) ∧
    sched.length = 29 ∧ (∀ s ∈ sched, s.reads.length ≤ 14 ∧ ∀ p ∈ s.reads, p.1 < 14 ∧ p.2 < 2 ^ (14 - p.1)) ∧
    ((sched.map (·.reads)).flatten).length ≤ 120 ∧
    ((sched.map segByte).map (· % 16)).sum = ((sched.map (·.reads)).flatten).length ∧
    (∀ b ∈ sched.map segByte, b < 256) := by
  intro sched
  have hsort : Ref.sortLeaves (Ref.leavesOf N) = SphincsSecurity.Concrete.sortedLeaves (leavesN N) := by
    rw [leavesOf_leavesN, sortLeaves_eq]
  have hadm : SphincsSecurity.Concrete.AdmissibleLeaves (leavesN N) := by
    refine ⟨?_, ?_⟩
    · rw [leavesOf_leavesN, List.nodup_ofFn] at hnd
      exact fun a b e => hnd (congrArg Fin.val e)
    · rw [← hsort]; exact hoct
  obtain ⟨hl, hr, ht⟩ := schedule_admissible (leavesN N) hadm
  refine ⟨hadm, hsort, ?_, hl, hr, ?_, ?_, ?_⟩
  · rw [hsort]
    exact schedule_ref _ (fun v hv => by
      simp only [SphincsSecurity.Concrete.sortedLeaves, List.mem_map] at hv
      obtain ⟨r, _, rfl⟩ := hv
      exact (leavesN N r).isLt)
  · rw [ht, ← octopusSize_eq, ← hsort]; exact hoct
  · rw [List.map_map, List.length_flatten, List.map_map]
    refine congrArg List.sum ?_
    apply List.map_congr_left
    intro sg hsg
    simp only [Function.comp_apply]
    rw [segByte_val sg (by have := (hr sg hsg).1; omega)]
    have := (hr sg hsg).1
    split <;> split <;> omega
  · intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨sg, hsg, rfl⟩ := hb
    rw [segByte_val sg (by have := (hr sg hsg).1; omega)]
    have := (hr sg hsg).1
    split <;> split <;> omega

theorem sigAuth_eq (sig : List Byte) (i : Nat) : Ref.sigAuth sig i = Ref.slice sig (256 + 16 * i) 16 := by
  unfold Ref.sigAuth Ref.sigItem Ref.porsK
  congr 1; ring

/-- **R2 on byte lists**: a successful expansion decodes to a signature whose compact form is the
input. -/
theorem compressList_expandOf (sig : List Byte) (hsig : sig.length = 6100) (N : Nat) (wl : List Byte)
    (h : Ref.expandOf sig N = some wl) : compressList (witSig wl) = sig := by
  obtain ⟨hnd, hoct, hz, hwl⟩ := expandOf_some sig N wl h
  obtain ⟨-, -, hsch, hl29, -, hn120, hsum, hb⟩ := sched_facts N hnd hoct
  set sched := SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves (leavesN N))
  set v := Ref.leavesOf N
  set vs := Ref.sortLeaves v
  set segs := sched.map segByte with hsegs_def
  have hvs : vs.length = 15 := by simp [vs, v, Ref.sortLeaves, Ref.leavesOf, Ref.porsK]
  have hsegs : segs.length = 29 := by simp [segs, hl29]
  rw [hsch] at hwl hz
  simp only at hwl hz
  set n := ((sched.map (·.reads)).flatten).length
  have hn : (segs.map (· % 16)).sum ≤ 120 := by rw [hsum]; exact hn120
  subst hwl
  unfold compressList
  -- the four parts
  have p1 : dv (witSig (Ref.witnessList sig v vs segs)).randomness = Ref.slice sig 0 16 := by
    simp only [witSig]
    rw [witRho_W sig hsig v vs segs hvs]
    exact dv_ofList_slice _ _ (by omega)
  have p2 : (List.ofFn fun s => dv ((witSig (Ref.witnessList sig v vs segs)).fts.secrets s)).flatten =
      Ref.slice sig 16 (16 * 15) := by
    rw [← flatten_ofFn_slices]
    refine congrArg List.flatten ?_
    refine List.ofFn_inj.mpr (funext fun s => ?_)
    have := s.isLt
    simp only [SphincsSecurity.ftsOpenings] at this
    simp only [witSig, witFts]
    rw [witSecret_W sig hsig v vs segs hvs _ this]
    exact dv_ofList_slice _ _ (by omega)
  have p3 : (((authNodes (witSig (Ref.witnessList sig v vs segs))).map dv).flatten ++
      Ref.zeros (16 * Ref.porsM)).take (16 * Ref.porsM) = Ref.slice sig 256 (16 * 120) := by
    rw [authNodes_W sig hsig v vs segs hvs hsegs hb hn, hsum]
    have hA : ((List.range n).map (Ref.sigAuth sig)).flatten.length = 16 * n := by
      rw [map_range_eq_ofFn, length_flatten_ofFn _ 16 (fun j => length_sigAuth sig hsig _ (by
        have := j.isLt; omega))]
    rw [← flatten_ofFn_slices, show (List.ofFn fun i : Fin 120 => Ref.slice sig (256 + 16 * i.val) 16) =
      (List.range 120).map (Ref.sigAuth sig) by
        rw [map_range_eq_ofFn]; exact List.ofFn_inj.mpr (funext fun i => (sigAuth_eq sig i).symm)]
    have hB : ∀ k, n + k ≤ 120 →
        ((List.range k).map fun j => Ref.sigAuth sig (n + j)).flatten = Ref.zeros (16 * k) := by
      intro k
      induction k with
      | zero => intro _; rfl
      | succ k ih =>
        intro hk
        rw [List.range_succ, List.map_append, List.flatten_append, ih (by omega)]
        simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
        rw [hz (n + k) (by omega) (by omega)]
        simp only [Ref.zeros, ← List.replicate_add]
        congr 1
    rw [show (120 : Nat) = n + (120 - n) by omega, List.range_add, List.map_append,
      List.flatten_append, List.map_map, List.take_append, List.take_of_length_le (by rw [hA]; unfold Ref.porsM; omega)]
    refine congrArg₂ (· ++ ·) rfl ?_
    rw [hA]
    have e : (fun j => Ref.sigAuth sig (n + j)) = (Ref.sigAuth sig ∘ fun x => n + x) := rfl
    rw [← e, hB _ (by omega)]
    simp only [Ref.zeros, List.take_replicate, Ref.porsM]
    exact congrArg (List.replicate · 0) (by omega)
  have p4 : (List.ofFn (layerBytes (witSig (Ref.witnessList sig v vs segs)))).flatten =
      Ref.slice sig 2176 3924 := by
    rw [show (3924 : Nat) = ((List.range SphincsSecurity.numLayers).map Ref.sigLayerBytes).sum by decide,
      ← flatten_ofFn_slices_var]
    refine congrArg List.flatten (List.ofFn_inj.mpr (funext fun lay => ?_))
    rw [layerBytes_of sig hsig (witSig (Ref.witnessList sig v vs segs)) lay
      (witLayer_W sig hsig v vs segs hvs lay)]
    rfl
  rw [p1, p2, p3, p4]
  conv_rhs => rw [← slice_full sig 6100 hsig]
  rw [show (6100 : Nat) = 16 + (16 * 15 + (16 * 120 + 3924)) from rfl, slice_split, slice_split,
    slice_split]
  simp only [List.append_assoc]

/-- **R2 (bytes)**: a successful reference expansion decodes to a signature compressing to `σ`. -/
theorem expandOf_compress (σ : Bytes 6100) (N : Nat) (wl : List Byte)
    (h : Ref.expandOf (Ref.toList σ) N = some wl) : compress (witSig wl) = σ := by
  unfold compress
  rw [compressList_expandOf (Ref.toList σ) (Ref.length_toList σ) N wl h, Ref.ofList_toList]

/-- **R2**: every successful run of the abstract expansion decodes to a signature compressing to
`σ`. -/
theorem aExpand_compress (m : Message) (pk : SphincsSecurity.PublicKey) (σ : Bytes 6100)
    (w : Bytes 6348) (h : some w ∈ support (aExpand m pk σ)) : compress (witDec w) = σ := by
  unfold aExpand at h
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
  obtain ⟨d, _, hd⟩ := h
  cases he : Ref.expandOf (Ref.toList σ) d.toNat with
  | none => rw [he] at hd; simp at hd
  | some wl =>
    rw [he] at hd
    simp only [Option.map_some, Option.some.injEq] at hd
    subst hd
    have hl := Ref.length_of_expandOf (Ref.toList σ) (Ref.length_toList σ) _ wl he
    unfold witDec
    rw [Ref.toList_ofList 6348 wl hl]
    exact expandOf_compress σ d.toNat wl he

/-! ## R4: honest signatures round-trip -/

theorem ofList_dv (d : Digest) : Ref.ofList 16 (dv d) = d := by
  unfold dv; exact Ref.ofList_toList (n := 16) d

theorem map_range_getD {α β : Type} (l : List α) (f : α → β) (d : α) :
    (List.range l.length).map (fun i => f (l.getD i d)) = l.map f := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  rw [List.getElem?_eq_getElem (by simpa using h2)]
  rfl

theorem slice_flatten_dv (L : List Digest) (k : Nat) (hk : k < L.length) :
    Ref.slice (L.map dv).flatten (16 * k) 16 = dv (L.getD k 0) := by
  induction L generalizing k with
  | nil => simp at hk
  | cons x L ih =>
    cases k with
    | zero =>
      simp only [List.map_cons, List.flatten_cons, Nat.mul_zero, List.getD_cons_zero]
      rw [slice_append_left _ _ _ _ (by simp), slice_full _ _ (length_dv x)]
    | succ k =>
      simp only [List.map_cons, List.flatten_cons, List.getD_cons_succ]
      rw [slice_append_right _ _ _ (16 * k) _ (by simp; ring)]
      exact ih k (by simpa using hk)

theorem length_flatten_dv (L : List Digest) : (L.map dv).flatten.length = 16 * L.length := by
  induction L with
  | nil => simp
  | cons x L ih => simp [ih]; ring

theorem flatten_getD {α : Type} (L : List (List α)) (d : α) :
    ∀ j i, j < L.length → i < (L.getD j []).length →
      L.flatten.getD (((L.take j).map List.length).sum + i) d = (L.getD j []).getD i d := by
  induction L with
  | nil => intro j i hj; simp at hj
  | cons x L ih =>
    intro j i hj hi
    cases j with
    | zero =>
      simp only [List.getD_cons_zero] at hi ⊢
      simp only [List.take_zero, List.map_nil, List.sum_nil, Nat.zero_add, List.flatten_cons]
      exact getD_append_left'' _ _ _ _ hi
    | succ j =>
      simp only [List.getD_cons_succ] at hi ⊢
      simp only [List.take_succ_cons, List.map_cons, List.sum_cons, List.flatten_cons]
      rw [getD_append_right'' _ _ _ _ (by omega), show x.length + ((L.take j).map List.length).sum + i -
        x.length = ((L.take j).map List.length).sum + i by omega]
      exact ih j i (by simpa using hj) hi

/-! ### Slices of the compact signature -/

theorem length_secretsPart (S : Signature) :
    (List.ofFn fun s => dv (S.fts.secrets s)).flatten.length = 240 := by
  rw [length_flatten_ofFn _ 16 (fun _ => length_dv _)]; rfl

theorem length_authPart (S : Signature) :
    ((((authNodes S).map dv).flatten ++ Ref.zeros (16 * Ref.porsM)).take (16 * Ref.porsM)).length =
      1920 := by
  simp [Ref.porsM]

theorem slice_compress_rho (S : Signature) : Ref.slice (compressList S) 0 16 = dv S.randomness := by
  unfold compressList
  rw [List.append_assoc, List.append_assoc, slice_append_left _ _ _ _ (by simp),
    slice_full _ _ (length_dv _)]

theorem slice_compress_secret (S : Signature) (s : Nat) (hs : s < 15) :
    Ref.slice (compressList S) (16 + 16 * s) 16 = dv (S.fts.secrets ⟨s, hs⟩) := by
  unfold compressList
  rw [slice_append_left _ _ _ _ (by
      simp only [List.length_append, length_dv, length_secretsPart, length_authPart]; omega),
    slice_append_left _ _ _ _ (by
      simp only [List.length_append, length_dv, length_secretsPart]; omega),
    slice_append_right _ _ _ (16 * s) _ (by simp),
    slice_flatten_ofFn (fun s => dv (S.fts.secrets s)) 16 ⟨s, hs⟩ 0 16 (16 * s)
      (fun _ _ => length_dv _) (by simp) (by ring),
    slice_full _ _ (length_dv _)]

theorem sigAuth_compress (S : Signature) (hS : (authNodes S).length ≤ 120) (k : Nat) (hk : k < 120) :
    Ref.sigAuth (compressList S) k =
      if k < (authNodes S).length then dv ((authNodes S).getD k 0) else Ref.zeros 16 := by
  rw [sigAuth_eq]
  unfold compressList
  rw [slice_append_left _ _ _ _ (by
      simp only [List.length_append, length_dv, length_secretsPart, length_authPart]; omega),
    slice_append_right _ _ _ (16 * k) _ (by
      simp only [List.length_append, length_dv, length_secretsPart]),
    slice_take _ _ _ _ (by unfold Ref.porsM; omega)]
  have hl := length_flatten_dv (authNodes S)
  split
  · next h =>
    rw [slice_append_left _ _ _ _ (by rw [hl]; omega), slice_flatten_dv _ _ h]
  · next h =>
    rw [slice_append_right _ _ _ (16 * (k - (authNodes S).length)) _ (by rw [hl]; omega)]
    unfold Ref.slice Ref.zeros
    rw [List.drop_replicate, List.take_replicate]
    congr 1
    unfold Ref.porsM; omega

theorem length_layersPart_take (S : Signature) (lay : Nat) (hlay : lay ≤ 5) :
    ((List.ofFn (layerBytes S)).take lay).flatten.length =
      ((List.range lay).map Ref.sigLayerBytes).sum := by
  rw [List.length_flatten, List.map_take, List.map_ofFn]
  have e : (List.length ∘ layerBytes S) = fun l : Layer => Ref.sigLayerBytes l.val :=
    funext fun l => length_layerBytes S l
  rw [e, ← map_range_eq_ofFn (n := SphincsSecurity.numLayers) Ref.sigLayerBytes, ← List.map_take,
    List.take_range, Nat.min_eq_left (by simp [SphincsSecurity.numLayers]; omega)]

theorem slice_compress_layer (S : Signature) (lay : Layer) (y len : Nat)
    (h : y + len ≤ Ref.sigLayerBytes lay.val) :
    Ref.slice (compressList S) (Ref.sigLayerOff lay.val + y) len = Ref.slice (layerBytes S lay) y len := by
  have hl := lay.isLt
  simp only [SphincsSecurity.numLayers] at hl
  unfold compressList
  rw [slice_append_right _ _ _ (((List.ofFn (layerBytes S)).take lay.val).flatten.length + y) _ (by
      simp only [List.length_append, length_dv, length_secretsPart, length_authPart]
      rw [length_layersPart_take S lay.val (by omega)]
      unfold Ref.sigLayerOff Ref.headBytes Ref.porsK Ref.porsM; omega),
    slice_flatten_take _ _ _ _ (by rw [List.length_ofFn]; exact lay.isLt) (by
      rw [getD_ofFn, dif_pos lay.isLt, length_layerBytes]; exact h)]
  rw [getD_ofFn, dif_pos lay.isLt]

theorem sigLayerOf_compress (S : Signature) (lay : Layer) :
    sigLayerOf (compressList S) lay = S.layers lay := by
  have hl := lay.isLt
  simp only [SphincsSecurity.numLayers] at hl
  obtain ⟨-, -, t3, -⟩ := layer_table lay.val hl
  have hh := height_eq lay
  show LayerSignature.mk _ _ _ = LayerSignature.mk (S.layers lay).counter (S.layers lay).chainValues
    (S.layers lay).path
  rw [LayerSignature.mk.injEq]
  refine ⟨?_, funext fun i => ?_, funext fun l => ?_⟩
  · unfold Ref.sigCounterBytes
    rw [show Ref.sigLayerOff lay.val = Ref.sigLayerOff lay.val + 0 from rfl,
      slice_compress_layer S lay 0 4 (by omega)]
    unfold layerBytes
    rw [List.append_assoc, slice_append_left _ _ _ _ (by simp [Ref.length_toList]),
      slice_full _ _ (Ref.length_toList _), Ref.ofList_toList]
  · have hi := i.isLt
    simp only [SphincsSecurity.numChains] at hi
    rw [show Ref.sigLayerOff lay.val + 4 + 16 * i.val = Ref.sigLayerOff lay.val + (4 + 16 * i.val) by ring,
      slice_compress_layer S lay _ 16 (by omega)]
    unfold layerBytes
    rw [slice_append_left _ _ _ _ (by
        simp only [List.length_append, Ref.length_toList]
        rw [length_flatten_ofFn _ 16 (fun _ => length_dv _)]; simp [SphincsSecurity.numChains]; omega),
      slice_append_right _ _ _ (16 * i.val) _ (by simp [Ref.length_toList]),
      slice_flatten_ofFn (fun i => dv ((S.layers lay).chainValues i)) 16 i 0 16 (16 * i.val)
        (fun _ _ => length_dv _) (by simp) (by ring),
      slice_full _ _ (length_dv _)]
    exact Ref.ofList_toList _
  · have hlt : l.val < Ref.height lay.val := by rw [hh]; exact l.isLt
    rw [show Ref.sigLayerOff lay.val + 4 + (672 + 16 * l.val) =
        Ref.sigLayerOff lay.val + (676 + 16 * l.val) by ring,
      slice_compress_layer S lay _ 16 (by omega)]
    unfold layerBytes
    have hc : (Ref.toList (n := 4) (S.layers lay).counter ++
        (List.ofFn fun i => dv ((S.layers lay).chainValues i)).flatten).length = 676 := by
      simp only [List.length_append, Ref.length_toList]
      rw [length_flatten_ofFn _ 16 (fun _ => length_dv _)]; rfl
    rw [slice_append_right _ _ _ (16 * l.val) _ (by rw [hc]),
      slice_flatten_ofFn (fun j => dv ((S.layers lay).path j)) 16 l 0 16 (16 * l.val)
        (fun _ _ => length_dv _) (by simp) (by ring),
      slice_full _ _ (length_dv _)]
    exact Ref.ofList_toList _

theorem expandOf_eq_some (sig : List Byte) (N : Nat) (hnd : (Ref.leavesOf N).Nodup)
    (hoct : Ref.octopusSize (Ref.sortLeaves (Ref.leavesOf N)) ≤ 120)
    (hz : ∀ i, (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).2.length ≤ i → i < 120 →
      Ref.sigAuth sig i = Ref.zeros 16) :
    Ref.expandOf sig N = some (Ref.witnessList sig (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N))
      (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).1) := by
  unfold Ref.expandOf
  dsimp only
  split
  · next h => simp [hnd] at h
  split
  · next h => unfold Ref.porsM at h; omega
  split
  · next h =>
    exfalso
    simp only [Bool.not_eq_true', List.all_eq_false, beq_eq_false_iff_ne, ne_eq] at h
    obtain ⟨i, hi, hne⟩ := h
    have hi' := List.mem_range'_1.mp hi
    exact hne (beq_iff_eq.mpr (hz i hi'.1 (by unfold Ref.porsM at hi'; omega)))
  rfl

theorem idxOf_ofFn {n : Nat} (f : Fin n → Nat) (hf : Function.Injective f) (r : Fin n) :
    (List.ofFn f).idxOf (f r) = r.val := by
  have hmem : f r ∈ List.ofFn f := List.mem_ofFn.mpr ⟨r, rfl⟩
  have hlt : (List.ofFn f).idxOf (f r) < (List.ofFn f).length := List.idxOf_lt_length_iff.mpr hmem
  have hget := List.getElem_idxOf hlt
  rw [List.getElem_ofFn] at hget
  have := hf hget
  exact congrArg Fin.val this

theorem normalized_congr {a a' : Fin 16} (h : a = a') {m m' p p' : Bool} (hm : m = m') (hp : p = p')
    (f : Fin a.val → Digest) (g : Fin a'.val → Digest)
    (hfg : ∀ i (hi : i < a.val), f ⟨i, hi⟩ = g ⟨i, h ▸ hi⟩) :
    SphincsSecurity.Segment.normalized a m p f = SphincsSecurity.Segment.normalized a' m' p' g := by
  subst h hm hp
  congr 1
  funext i
  exact hfg i.val i.isLt

theorem getD_map_lt {α β : Type} (l : List α) (f : α → β) (j : Nat) (d : α) (d' : β) (hj : j < l.length) :
    (l.map f).getD j d' = f (l.getD j d) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hj,
    Option.map_some, Option.getD_some]

section honest
variable (leaves : IndexGroup → FtsLeaf) (hadm : SphincsSecurity.Concrete.AdmissibleLeaves leaves)
  (rho : Digest) (secret : FtsLeaf → Digest) (node : Nat → Nat → Digest)
  (layers : (lay : Layer) → LayerSignature lay)

/-- The honest signature. -/
abbrev honestSig : Signature := ⟨rho, SphincsSecurity.Concrete.honestFts leaves secret node, layers⟩

/-- The honest schedule. -/
abbrev hsched : List SphincsSecurity.Concrete.ScheduleSegment :=
  SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)

include hadm in
theorem authNodes_honestE :
    authNodes (honestSig leaves rho secret node layers) =
      ((hsched leaves).map (·.reads)).flatten.map fun p => node p.1 p.2 := by
  obtain ⟨hl, hr, -⟩ := schedule_admissible leaves hadm
  unfold authNodes
  have e : ∀ j : Fin SphincsSecurity.ftsSegments,
      List.ofFn ((honestSig leaves rho secret node layers).fts.segments j).nodes =
        ((hsched leaves).getD j.val default).reads.map fun p => node p.1 p.2 := by
    intro j
    have hj : j.val < (hsched leaves).length := by rw [hl]; exact j.isLt
    have hlen : ((hsched leaves).getD j.val default).reads.length ≤ 14 := by
      apply (hr _ _).1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; exact List.getElem_mem _
    show List.ofFn (fun i : Fin (((hsched leaves).getD j.val default).reads.length % 16) =>
      node (((hsched leaves).getD j.val default).reads.getD i.val (0, 0)).1
        (((hsched leaves).getD j.val default).reads.getD i.val (0, 0)).2) = _
    rw [← map_range_eq_ofFn (((hsched leaves).getD j.val default).reads.length % 16)
      (fun i => node (((hsched leaves).getD j.val default).reads.getD i (0, 0)).1
        (((hsched leaves).getD j.val default).reads.getD i (0, 0)).2),
      Nat.mod_eq_of_lt (by omega)]
    exact map_range_getD _ (fun p : Nat × Nat => node p.1 p.2) (0, 0)
  rw [List.ofFn_inj.mpr (funext e), List.map_flatten, List.map_map]
  have e3 : (List.ofFn fun j : Fin SphincsSecurity.ftsSegments =>
      ((hsched leaves).getD j.val default).reads.map fun p => node p.1 p.2) =
      (List.range (hsched leaves).length).map fun j =>
        ((hsched leaves).getD j default).reads.map fun p => node p.1 p.2 := by
    rw [hl, map_range_eq_ofFn]; rfl
  rw [e3, map_range_getD (hsched leaves) (fun s => s.reads.map fun p => node p.1 p.2)]
  rfl

include hadm in
theorem length_authNodes_honest :
    (authNodes (honestSig leaves rho secret node layers)).length =
      SphincsSecurity.Concrete.octopusSize (SphincsSecurity.Concrete.sortedLeaves leaves) := by
  rw [authNodes_honestE leaves hadm, List.length_map, (schedule_admissible leaves hadm).2.2]

end honest

/-- **R4**: the honest opening of admissible leaves (any randomness, secrets, node table and layers),
compressed and expanded with a digest whose leaf indices are `leaves`, decodes to itself. -/
theorem expandOf_honest (leaves : IndexGroup → FtsLeaf)
    (hadm : SphincsSecurity.Concrete.AdmissibleLeaves leaves) (N : Nat)
    (hN : ∀ r : IndexGroup, Ref.leafOf N r.val = (leaves r).val) (rho : Digest)
    (secret : FtsLeaf → Digest) (node : Nat → Nat → Digest)
    (layers : (lay : Layer) → LayerSignature lay) :
    ∃ wl, wl.length = 6348 ∧
      Ref.expandOf (compressList ⟨rho, SphincsSecurity.Concrete.honestFts leaves secret node, layers⟩) N
        = some wl ∧
      witSig wl = ⟨rho, SphincsSecurity.Concrete.honestFts leaves secret node, layers⟩ := by
  have hleaves : leavesN N = leaves := funext fun r => Fin.ext (hN r)
  have hv : Ref.leavesOf N = List.ofFn fun r => (leaves r).val := by rw [leavesOf_leavesN, hleaves]
  have hvs : Ref.sortLeaves (Ref.leavesOf N) = SphincsSecurity.Concrete.sortedLeaves leaves := by
    rw [hv, sortLeaves_eq]
  have hnd : (Ref.leavesOf N).Nodup := by
    rw [hv, List.nodup_ofFn]; exact fun a b e => hadm.1 (Fin.ext e)
  have hoct : Ref.octopusSize (Ref.sortLeaves (Ref.leavesOf N)) ≤ 120 := by rw [hvs]; exact hadm.2
  obtain ⟨-, -, hsch, hl29, hr, hn120, hsum, hb⟩ := sched_facts N hnd hoct
  rw [hleaves] at hsch hl29 hr hn120 hsum hb
  have hAN := authNodes_honestE leaves hadm rho secret node layers
  simp only [hsched] at hAN
  have hANl : (authNodes (honestSig leaves rho secret node layers)).length =
      ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).flatten.length := by rw [hAN, List.length_map]
  have hcl := length_compressList (honestSig leaves rho secret node layers)
  have hauth := sigAuth_compress (honestSig leaves rho secret node layers) (by rw [hANl]; exact hn120)
  have hn2 : (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).2.length =
      ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).flatten.length := by rw [hsch]
  have hexp := expandOf_eq_some (compressList (honestSig leaves rho secret node layers)) N hnd hoct
    (fun i hi1 hi2 => by
      rw [hauth i hi2, if_neg (by rw [hANl]; omega)])
  have hvsl : (Ref.sortLeaves (Ref.leavesOf N)).length = 15 := by
    rw [hvs]; exact (SphincsSecurity.Completeness.sortedLeaves_facts leaves hadm.1).1
  have hs1 : (Ref.schedule (Ref.sortLeaves (Ref.leavesOf N))).1 = (SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte := by
    rw [hsch]
  refine ⟨Ref.witnessList (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N)
    (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte),
    Ref.length_witnessList _ hcl _ _ _ hvsl, by rw [hexp, hs1], ?_⟩
  have hsegs : ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte).length = 29 := by rw [List.length_map]; exact hl29
  have hn : (((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte).map (· % 16)).sum ≤ 120 := by rw [hsum]; exact hn120
  have hinj : Function.Injective fun r => (leaves r).val := fun a b e => hadm.1 (Fin.ext e)
  have hmod : ∀ sg ∈ hsched leaves, segByte sg % 16 = sg.reads.length := by
    intro sg hsg
    have := (hr sg hsg).1
    rw [segByte_val sg (by omega)]
    split <;> split <;> omega
  have hasum : ∀ j, asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j =
      ((((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).take j).map List.length).sum := by
    intro j
    unfold asum
    rw [← List.map_take, List.map_map, ← List.map_take, List.map_map]
    refine congrArg List.sum (List.map_congr_left fun sg hsg => ?_)
    exact hmod sg (List.mem_of_mem_take hsg)
  unfold witSig
  rw [SphincsSecurity.Signature.mk.injEq]
  refine ⟨?_, ?_, funext fun lay => ?_⟩
  · rw [witRho_W _ hcl _ _ _ hvsl]
    unfold Ref.sigRho
    rw [slice_compress_rho]
    exact Ref.ofList_toList _
  · unfold witFts
    rw [SphincsSecurity.FtsSignature.mk.injEq]
    refine ⟨funext fun s => ?_, funext fun s => ?_, funext fun j => ?_⟩
    · -- slot codes
      rw [SphincsSecurity.Completeness.honestFts_perm]
      apply Fin.ext
      rw [Fin.val_castSucc, Fin.val_mk]
      have hs : s.val < 15 := s.isLt
      rw [witPi_W _ hcl _ _ _ hvsl s.val hs, hvs,
        SphincsSecurity.Completeness.sortedLeaves_getD leaves s.isLt, hv,
        idxOf_ofFn (fun r => (leaves r).val) hinj, Ref.byte_toNat]
      generalize ((SphincsSecurity.Concrete.sortedSlots leaves).getD s.val ⟨0, by decide⟩) = r
      have := r.isLt
      simp only [SphincsSecurity.ftsOpenings] at this
      omega
    · -- secrets
      rw [witSecret_W _ hcl _ _ _ hvsl s.val s.isLt, Ref.sigItem, slice_compress_secret _ s.val s.isLt,
        ofList_dv]
    · -- segments
      rw [SphincsSecurity.Completeness.honestFts_segments]
      unfold SphincsSecurity.Completeness.honestSegments SphincsSecurity.Concrete.ScheduleSegment.toSegment
      unfold segAt
      have hj : j.val < 29 := j.isLt
      have hjl : j.val < (SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).length := by rw [hl29]; exact hj
      have hmem : (SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default ∈ hsched leaves := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl]; exact List.getElem_mem _
      have hlen := (hr _ hmem).1
      have hw0 := wbyte_segPtr_W _ hcl (Ref.leavesOf N) _ _ hvsl hsegs hb hn j.val hj
      have hw : Ref.wbyte (Ref.witnessList (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte)) (segPtr (Ref.witnessList (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte)) j.val) =
          ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).reads.length +
            (if ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).merge then 16 else 0) +
            32 * (if ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).parity then 1 else 0) := by
        rw [hw0, getD_map_lt _ segByte _ default 0 hjl, segByte_val _ (by omega)]
      refine normalized_congr (Fin.ext ?_) ?_ ?_ _ _ ?_
      · simp only [SphincsSecurity.Concrete.ScheduleSegment.folds, Fin.val_mk]
        rw [hw]
        generalize ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD
          j.val default) = sg at hlen ⊢
        rcases sg with ⟨mg, pr, rd⟩
        simp only at hlen ⊢
        cases mg <;> cases pr <;> simp <;> omega
      · rw [hw]
        generalize ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD
          j.val default) = sg at hlen ⊢
        rcases sg with ⟨mg, pr, rd⟩
        simp only at hlen ⊢
        cases mg <;> cases pr <;> simp <;> omega
      · rw [hw]
        generalize ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD
          j.val default) = sg at hlen ⊢
        rcases sg with ⟨mg, pr, rd⟩
        simp only at hlen ⊢
        cases mg <;> cases pr <;> simp <;> omega
      · intro i hi
        have hi' : i < ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte).getD j.val 0 % 16 := by
          have h0 : i < Ref.wbyte (Ref.witnessList (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte)) (segPtr (Ref.witnessList (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte)) j.val) % 16 := hi
          rw [hw0] at h0; exact h0
        have hi2 : i < ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).reads.length := by
          have h3 := hi'
          rw [getD_map_lt _ segByte _ default 0 hjl, segByte_val _ (by omega)] at h3
          generalize ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default) = sg at h3 hlen ⊢
          rcases sg with ⟨mg, pr, rd⟩
          simp only at h3 hlen ⊢
          cases mg <;> cases pr <;> simp at h3 <;> omega
        have e1 := dv_node_W _ hcl (Ref.leavesOf N) _ _ hvsl hsegs hb hn j.val i hj hi'
        have ha1 := asum_succ ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val (by rw [hsegs]; exact hj)
        have ha2 : asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) (j.val + 1) ≤
            asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte).length :=
          asum_mono _ (by rw [hsegs]; omega)
        rw [asum_length, hsum] at ha2
        have hk : asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i <
            (authNodes (honestSig leaves rho secret node layers)).length := by
          rw [hANl]; omega
        have e2 := hauth (asum ((SphincsSecurity.Concrete.schedule
          (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i) (by
            have := hk; rw [hANl] at this; omega)
        rw [if_pos hk] at e2
        have e3 : (authNodes (honestSig leaves rho secret node layers)).getD
            (asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i) 0 =
            node ((((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).flatten).getD
              (asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i) (0, 0)).1
              ((((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).flatten).getD
              (asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i) (0, 0)).2 := by
          rw [hAN]
          exact getD_map_lt _ (fun p : Nat × Nat => node p.1 p.2) _ (0, 0) 0 (by
            rw [hANl] at hk; exact hk)
        have hLj : ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).getD j.val [] =
            ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).reads :=
          by simp only [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hjl,
            Option.map_some, Option.getD_some]
        have e4 : (((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map (·.reads)).flatten).getD
            (asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i) (0, 0) =
            ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).getD j.val default).reads.getD i (0, 0) := by
          rw [hasum, flatten_getD _ (0, 0) j.val i (by rw [List.length_map]; exact hjl) (by
            rw [hLj]; exact hi2), hLj]
        calc wdig (Ref.witnessList (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte)) (segPtr (Ref.witnessList (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte)) j.val + 8 + 16 * i)
            = Ref.ofList 16 (dv (wdig (Ref.witnessList (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte)) (segPtr (Ref.witnessList (compressList (honestSig leaves rho secret node layers)) (Ref.leavesOf N) (Ref.sortLeaves (Ref.leavesOf N)) ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte)) j.val + 8 + 16 * i))) := (ofList_dv _).symm
          _ = Ref.ofList 16 (Ref.sigAuth (compressList (honestSig leaves rho secret node layers))
              (asum ((SphincsSecurity.Concrete.schedule (SphincsSecurity.Concrete.sortedLeaves leaves)).map segByte) j.val + i)) := by rw [e1]
          _ = _ := by rw [e2, ofList_dv, e3, e4]
  · rw [witLayer_W _ hcl _ _ _ hvsl, sigLayerOf_compress]

end SigGolfCandidate.Equiv
