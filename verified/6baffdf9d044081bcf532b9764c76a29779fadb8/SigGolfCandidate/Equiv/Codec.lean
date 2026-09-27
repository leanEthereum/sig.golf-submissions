import SigGolfCandidate.Equiv.Basic

/-!
# The signature codec

`sigCodec : Bytes 7080 ≃ Signature`: the signature layout of `ref.py`
(`rho | (s_k, path_k)_{k<14} | (LE32 c, 42 chain values, path)_{lay<6}`), and the witness decoder
`witDec` (the same fields read at the witness offsets), with `witDec (expandRef b) = sigCodec b`.
-/

namespace SigGolfCandidate.Equiv

open SigGolf (Byte Bytes)
open SphincsSecurity (Digest Signature Layer FtsTree ChainIndex)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-! ## Slices -/

section slices


theorem slice_append_left (A B : List Byte) (off len : Nat) (h : off + len ≤ A.length) :
    Ref.slice (A ++ B) off len = Ref.slice A off len := by
  unfold Ref.slice
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem slice_append_right (A B : List Byte) (off off' len : Nat) (h : off = A.length + off') :
    Ref.slice (A ++ B) off len = Ref.slice B off' len := by
  unfold Ref.slice
  subst h
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]
  simp

theorem slice_full (A : List Byte) (len : Nat) (h : A.length = len) : Ref.slice A 0 len = A := by
  unfold Ref.slice; subst h; simp

theorem slice_split (l : List Byte) (a b c : Nat) :
    Ref.slice l a (b + c) = Ref.slice l a b ++ Ref.slice l (a + b) c := by
  simp [Ref.slice, List.take_add, List.drop_drop, Nat.add_comm]

theorem slice_flatten_ofFn {n : Nat} (f : Fin n → List Byte) (k : Nat) (i : Fin n) (r len off : Nat)
    (hf : ∀ j : Fin n, j.val < i.val → (f j).length = k) (hr : r + len ≤ (f i).length)
    (hoff : off = k * i.val + r) :
    Ref.slice (List.ofFn f).flatten off len = Ref.slice (f i) r len := by
  induction n generalizing off with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add] at hoff
      subst hoff
      exact slice_append_left _ _ _ _ hr
    | succ i =>
      have h0 := hf 0 (by simp)
      rw [slice_append_right _ _ _ (k * i.val + r) _ (by simp [Fin.val_succ] at hoff; rw [h0, hoff]; ring)]
      exact ih (f := fun j => f j.succ) (i := i) (off := k * i.val + r)
        (hf := fun j hj => hf j.succ (by simp; omega)) (hr := hr) (hoff := rfl)

theorem flatten_ofFn_slices (l : List Byte) (a k n : Nat) :
    (List.ofFn fun i : Fin n => Ref.slice l (a + k * i.val) k).flatten = Ref.slice l a (k * n) := by
  induction n with
  | zero => simp [Ref.slice]
  | succ n ih =>
    rw [List.ofFn_succ_last, List.flatten_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih, ← slice_split, Nat.mul_succ]

theorem length_slice (l : List Byte) (a len : Nat) (h : a + len ≤ l.length) :
    (Ref.slice l a len).length = len := by
  simp [Ref.slice]; omega

end slices

/-! ## Encoding and decoding -/

theorem sig_ext (a b : Signature) (h1 : a.randomness = b.randomness)
    (h2 : ∀ k, a.ftsSecret k = b.ftsSecret k) (h3 : ∀ k j, a.ftsPath k j = b.ftsPath k j)
    (h4 : ∀ lay, (a.layers lay).counter = (b.layers lay).counter)
    (h5 : ∀ lay i, (a.layers lay).chainValues i = (b.layers lay).chainValues i)
    (h6 : ∀ lay j, (a.layers lay).path j = (b.layers lay).path j) : a = b := by
  cases a with | mk ra sa pa la =>
  cases b with | mk rb sb pb lb =>
  simp only at h1 h2 h3 h4 h5 h6
  subst h1
  have e2 : sa = sb := funext h2
  have e3 : pa = pb := funext fun k => funext (h3 k)
  have e4 : la = lb := by
    funext lay
    have e1 := h4 lay; have e2 := h5 lay; have e3 := h6 lay
    revert e1 e2 e3
    cases la lay
    cases lb lay
    intro e1 e2 e3
    simp only at e1 e2 e3
    subst e1
    rw [funext e2, funext e3]
  subst e2 e3 e4
  rfl

/-- One few-time opening: the secret and its ten siblings. -/
def ftsPart (σ : Signature) (k : FtsTree) : List Byte :=
  dv (σ.ftsSecret k) ++ (List.ofFn fun j => dv (σ.ftsPath k j)).flatten

/-- One layer: `LE32 c`, the 42 chain values and the path. -/
def layerPart (σ : Signature) (lay : Layer) : List Byte :=
  Ref.toList (n := 4) (σ.layers lay).counter ++
    (List.ofFn fun i => dv ((σ.layers lay).chainValues i)).flatten ++
    (List.ofFn fun j => dv ((σ.layers lay).path j)).flatten

/-- The signature bytes (`ref.py` layout). -/
def sigToList (σ : Signature) : List Byte :=
  dv σ.randomness ++ (List.ofFn (ftsPart σ)).flatten ++ (List.ofFn (layerPart σ)).flatten

/-! ## Layer offsets (from `Ref.sigLayerOff`) -/

/-- The bytes before layer `lay`'s signature part, after the head. -/
def pre (lay : Nat) : Nat := ((List.range lay).map Ref.sigLayerBytes).sum

theorem sigLayerOff_eq (lay : Nat) : Ref.sigLayerOff lay = 2480 + pre lay := rfl

theorem layerBytes_eq (lay : Layer) :
    Ref.sigLayerBytes lay = 676 + 16 * SphincsSecurity.layerHeight lay := by
  fin_cases lay <;> decide

theorem pre_succ (lay : Nat) : pre (lay + 1) = pre lay + Ref.sigLayerBytes lay := by
  simp [pre, List.range_succ]

theorem layer_bound (lay : Layer) : Ref.sigLayerOff lay + Ref.sigLayerBytes lay ≤ 7080 := by
  fin_cases lay <;> decide

theorem pre_all : pre SphincsSecurity.numLayers = 4600 := by decide

theorem wit_bound (lay : Layer) :
    Ref.witLayerOff lay + 672 + 16 * SphincsSecurity.layerHeight lay ≤ Ref.witCounters := by
  fin_cases lay <;> decide

theorem witCounters_eq : Ref.witCounters = 7056 := by decide

/-- The witness permutation on each layer (kernel evaluation over the six layers). -/
theorem sig_layer_check : (List.range 6).all (fun lay => (List.range (Ref.sigLayerBytes lay)).all
    fun r => Ref.signatureSrc (Ref.sigLayerOff lay + r) ==
      if r < 4 then Ref.witCounters + 4 * lay + r else Ref.witLayerOff lay + (r - 4)) = true := by
  decide +kernel

theorem signatureSrc_layer (lay : Layer) (r : Nat) (hr : r < Ref.sigLayerBytes lay) :
    Ref.signatureSrc (Ref.sigLayerOff lay + r) =
      if r < 4 then Ref.witCounters + 4 * lay.val + r else Ref.witLayerOff lay + (r - 4) := by
  have h := List.all_eq_true.mp sig_layer_check lay.val (List.mem_range.mpr lay.isLt)
  have h2 := List.all_eq_true.mp h r (List.mem_range.mpr hr)
  exact beq_iff_eq.mp h2

theorem signatureSrc_head (i : Nat) (hi : i < 2480) : Ref.signatureSrc i = i := by
  unfold Ref.signatureSrc; rw [if_pos (by exact hi)]

/-- Decode the signature bytes. -/
def sigOfList (l : List Byte) : Signature where
  randomness := Ref.ofList 16 (Ref.slice l 0 16)
  ftsSecret k := Ref.ofList 16 (Ref.slice l (16 + 176 * k.val) 16)
  ftsPath k j := Ref.ofList 16 (Ref.slice l (16 + 176 * k.val + 16 + 16 * j.val) 16)
  layers lay := ⟨Ref.ofList 4 (Ref.slice l (Ref.sigLayerOff lay) 4),
    fun i => Ref.ofList 16 (Ref.slice l (Ref.sigLayerOff lay + 4 + 16 * i.val) 16),
    fun j => Ref.ofList 16 (Ref.slice l (Ref.sigLayerOff lay + 676 + 16 * j.val) 16)⟩

theorem length_flatten_ofFn {n : Nat} (f : Fin n → List Byte) (k : Nat) (hf : ∀ j, (f j).length = k) :
    (List.ofFn f).flatten.length = k * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hf 0,
      ih (fun j => f j.succ) (fun j => hf j.succ), Nat.mul_succ]; ring

theorem length_ftsPart (σ : Signature) (k : FtsTree) : (ftsPart σ k).length = 176 := by
  simp only [ftsPart, List.length_append, length_dv]
  rw [length_flatten_ofFn _ 16 (fun j => length_dv _)]; rfl

theorem length_layerPart (σ : Signature) (lay : Layer) :
    (layerPart σ lay).length = Ref.sigLayerBytes lay := by
  simp only [layerPart, List.length_append, Ref.length_toList]
  rw [length_flatten_ofFn _ 16 (fun j => length_dv _), length_flatten_ofFn _ 16 (fun j => length_dv _),
    layerBytes_eq]
  simp [SphincsSecurity.numChains]

theorem fts_lt (k : FtsTree) : k.val < 14 := k.isLt
theorem ftsH_lt (j : Fin SphincsSecurity.ftsTreeHeight) : j.val < 10 := j.isLt
theorem lay_lt (lay : Layer) : lay.val < 6 := lay.isLt
theorem chain_lt (i : ChainIndex) : i.val < 42 := i.isLt

theorem length_fts_block (σ : Signature) : (List.ofFn (ftsPart σ)).flatten.length = 2464 := by
  rw [length_flatten_ofFn _ 176 (length_ftsPart σ)]; rfl

/-- A slice inside the `i`-th list of a concatenation. -/
theorem slice_flatten_take (L : List (List Byte)) (i r len : Nat) (hi : i < L.length)
    (h : r + len ≤ (L.getD i []).length) :
    Ref.slice L.flatten ((L.take i).flatten.length + r) len = Ref.slice (L.getD i []) r len := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    cases i with
    | zero =>
      simp only [List.take_zero, List.flatten_nil, List.length_nil, Nat.zero_add, List.flatten_cons,
        List.getD_cons_zero] at h ⊢
      exact slice_append_left _ _ _ _ h
    | succ i =>
      simp only [List.take_succ_cons, List.flatten_cons, List.length_append, List.getD_cons_succ] at h ⊢
      rw [slice_append_right _ _ _ ((L.take i).flatten.length + r) _ (by omega)]
      exact ih i (by simp at hi; omega) h

theorem take_layer_length (σ : Signature) (i : Nat) (hi : i ≤ SphincsSecurity.numLayers) :
    ((List.ofFn (layerPart σ)).take i).flatten.length = pre i := by
  induction i with
  | zero => simp [pre]
  | succ i ih =>
    rw [List.take_succ, List.flatten_append, List.length_append, ih (by omega), pre_succ]
    have hl : i < SphincsSecurity.numLayers := by omega
    rw [List.getElem?_ofFn, dif_pos hl]
    simp only [Option.toList_some, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [length_layerPart]

theorem sigOfList_sigToList (σ : Signature) : sigOfList (sigToList σ) = σ := by
  have hA : (dv σ.randomness ++ (List.ofFn (ftsPart σ)).flatten).length = 2480 := by
    rw [List.length_append, length_dv, length_fts_block]
  have hc : ∀ lay, (Ref.toList (n := 4) (σ.layers lay).counter).length = 4 :=
    fun _ => Ref.length_toList _
  have hv : ∀ lay, (List.ofFn fun i => dv ((σ.layers lay).chainValues i)).flatten.length = 672 :=
    fun _ => by rw [length_flatten_ofFn _ 16 (fun j => length_dv _)]; rfl
  -- a slice of the layer block
  have hL : ∀ (lay : Layer) (r len : Nat), r + len ≤ Ref.sigLayerBytes lay →
      Ref.slice (sigToList σ) (Ref.sigLayerOff lay + r) len = Ref.slice (layerPart σ lay) r len := by
    intro lay r len h
    rw [sigToList, sigLayerOff_eq, slice_append_right _ _ _ (pre lay + r) _ (by rw [hA]; ring),
      ← take_layer_length σ lay (by have := lay.isLt; omega),
      slice_flatten_take _ _ _ _ (by simp) (by rw [getD_ofFn, dif_pos lay.isLt, length_layerPart]; exact h),
      getD_ofFn, dif_pos lay.isLt]
  apply sig_ext
  · show Ref.ofList 16 (Ref.slice (sigToList σ) 0 16) = σ.randomness
    rw [sigToList, slice_append_left _ _ _ _ (by simp), slice_append_left _ _ _ _ (by simp),
      slice_full _ _ (length_dv _)]
    exact Ref.ofList_toList (n := 16) _
  · intro k
    show Ref.ofList 16 (Ref.slice (sigToList σ) (16 + 176 * k.val) 16) = σ.ftsSecret k
    have hk := fts_lt k
    rw [sigToList, List.append_assoc, slice_append_right _ _ _ (176 * k.val) _ (by simp),
      slice_append_left _ _ _ _ (by rw [length_fts_block]; omega),
      slice_flatten_ofFn _ 176 k 0 16 _ (fun j _ => length_ftsPart σ j)
        (by rw [length_ftsPart]; omega) (by ring),
      ftsPart, slice_append_left _ _ _ _ (by simp), slice_full _ _ (length_dv _)]
    exact Ref.ofList_toList (n := 16) _
  · intro k j
    show Ref.ofList 16 (Ref.slice (sigToList σ) (16 + 176 * k.val + 16 + 16 * j.val) 16) = σ.ftsPath k j
    have hk := fts_lt k
    have hj := ftsH_lt j
    rw [sigToList, List.append_assoc, slice_append_right _ _ _ (176 * k.val + (16 + 16 * j.val)) _
        (by simp; ring),
      slice_append_left _ _ _ _ (by rw [length_fts_block]; omega),
      slice_flatten_ofFn _ 176 k (16 + 16 * j.val) 16 _ (fun j _ => length_ftsPart σ j)
        (by rw [length_ftsPart]; omega) (by ring),
      ftsPart, slice_append_right _ _ _ (16 * j.val) _ (by simp),
      slice_flatten_ofFn _ 16 j 0 16 _ (fun _ _ => length_dv _) (by simp) (by ring),
      slice_full _ _ (length_dv _)]
    exact Ref.ofList_toList (n := 16) _
  · intro lay
    show Ref.ofList 4 (Ref.slice (sigToList σ) (Ref.sigLayerOff lay) 4) = (σ.layers lay).counter
    rw [← Nat.add_zero (Ref.sigLayerOff lay), hL lay 0 4 (by rw [layerBytes_eq]; omega),
      layerPart, slice_append_left _ _ _ _ (by simp only [List.length_append, hc]; omega),
      slice_append_left _ _ _ _ (by rw [hc]), slice_full _ _ (hc _)]
    exact Ref.ofList_toList (n := 4) _
  · intro lay i
    have hi := chain_lt i
    show Ref.ofList 16 (Ref.slice (sigToList σ) (Ref.sigLayerOff lay + 4 + 16 * i.val) 16) =
      (σ.layers lay).chainValues i
    rw [Nat.add_assoc, hL lay _ 16 (by rw [layerBytes_eq]; omega),
      layerPart, slice_append_left _ _ _ _ (by simp only [List.length_append, hc, hv]; omega),
      slice_append_right _ _ _ (16 * i.val) _ (by rw [hc]),
      slice_flatten_ofFn _ 16 i 0 16 _ (fun _ _ => length_dv _) (by simp) (by ring),
      slice_full _ _ (length_dv _)]
    exact Ref.ofList_toList (n := 16) _
  · intro lay j
    have hj := j.isLt
    show Ref.ofList 16 (Ref.slice (sigToList σ) (Ref.sigLayerOff lay + 676 + 16 * j.val) 16) =
      (σ.layers lay).path j
    rw [Nat.add_assoc, hL lay _ 16 (by rw [layerBytes_eq]; omega),
      layerPart, slice_append_right _ _ _ (16 * j.val) _ (by
        simp only [List.length_append, hc, hv]),
      slice_flatten_ofFn _ 16 j 0 16 _ (fun _ _ => length_dv _) (by simp) (by ring),
      slice_full _ _ (length_dv _)]
    exact Ref.ofList_toList (n := 16) _

theorem dv_ofList_slice (l : List Byte) (a : Nat) (h : a + 16 ≤ l.length) :
    dv (Ref.ofList 16 (Ref.slice l a 16)) = Ref.slice l a 16 :=
  Ref.toList_ofList 16 _ (length_slice l a 16 h)

theorem ftsPart_sigOfList (l : List Byte) (hl : l.length = 7080) (k : FtsTree) :
    ftsPart (sigOfList l) k = Ref.slice l (16 + 176 * k.val) 176 := by
  have hk := fts_lt k
  unfold ftsPart
  simp only [sigOfList]
  rw [dv_ofList_slice _ _ (by omega)]
  have e : (List.ofFn fun j : Fin SphincsSecurity.ftsTreeHeight =>
      dv (Ref.ofList 16 (Ref.slice l (16 + 176 * k.val + 16 + 16 * j.val) 16))) =
      List.ofFn fun j : Fin 10 => Ref.slice l ((16 + 176 * k.val + 16) + 16 * j.val) 16 := by
    apply List.ofFn_inj.mpr
    funext j
    have := ftsH_lt j
    exact dv_ofList_slice _ _ (by omega)
  rw [e, flatten_ofFn_slices, ← slice_split]

theorem layerPart_sigOfList (l : List Byte) (hl : l.length = 7080) (lay : Layer) :
    layerPart (sigOfList l) lay = Ref.slice l (Ref.sigLayerOff lay) (Ref.sigLayerBytes lay) := by
  have hb := layer_bound lay
  have hB := layerBytes_eq lay
  unfold layerPart
  simp only [sigOfList]
  rw [Ref.toList_ofList 4 _ (length_slice _ _ _ (by omega))]
  have e1 : (List.ofFn fun i : ChainIndex =>
      dv (Ref.ofList 16 (Ref.slice l (Ref.sigLayerOff lay + 4 + 16 * i.val) 16))) =
      List.ofFn fun i : Fin 42 => Ref.slice l ((Ref.sigLayerOff lay + 4) + 16 * i.val) 16 := by
    apply List.ofFn_inj.mpr
    funext i
    have := chain_lt i
    exact dv_ofList_slice _ _ (by omega)
  have e2 : (List.ofFn fun j : Fin (SphincsSecurity.layerHeight lay) =>
      dv (Ref.ofList 16 (Ref.slice l (Ref.sigLayerOff lay + 676 + 16 * j.val) 16))) =
      List.ofFn fun j : Fin (SphincsSecurity.layerHeight lay) =>
        Ref.slice l ((Ref.sigLayerOff lay + 676) + 16 * j.val) 16 := by
    apply List.ofFn_inj.mpr
    funext j
    have := j.isLt
    exact dv_ofList_slice _ _ (by omega)
  rw [e1, e2, flatten_ofFn_slices, flatten_ofFn_slices, ← slice_split,
    show Ref.sigLayerOff lay + 4 + 16 * 42 = Ref.sigLayerOff lay + (4 + 16 * 42) by ring,
    show Ref.sigLayerOff lay + 676 = Ref.sigLayerOff lay + (4 + 16 * 42) by ring, ← slice_split, hB]

/-- Consecutive slices of variable widths. -/
theorem flatten_ofFn_slices_var (l : List Byte) (a : Nat) {n : Nat} (w : Nat → Nat) :
    (List.ofFn fun j : Fin n => Ref.slice l (a + ((List.range j).map w).sum) (w j)).flatten =
      Ref.slice l a ((List.range n).map w).sum := by
  induction n with
  | zero => simp [Ref.slice]
  | succ n ih =>
    rw [List.ofFn_succ_last, List.flatten_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih, ← slice_split, List.range_succ, List.map_append, List.sum_append]
    simp

theorem sigToList_sigOfList (l : List Byte) (hl : l.length = 7080) : sigToList (sigOfList l) = l := by
  unfold sigToList
  have e1 : (List.ofFn (ftsPart (sigOfList l))).flatten = Ref.slice l 16 (176 * 14) := by
    rw [← flatten_ofFn_slices]
    congr 1
    exact List.ofFn_inj.mpr (funext fun k => ftsPart_sigOfList l hl k)
  have e2 : (List.ofFn (layerPart (sigOfList l))).flatten = Ref.slice l 2480 4600 := by
    have e3 : List.ofFn (layerPart (sigOfList l)) =
        List.ofFn fun lay : Fin SphincsSecurity.numLayers =>
          Ref.slice l (2480 + ((List.range lay).map Ref.sigLayerBytes).sum) (Ref.sigLayerBytes lay) :=
      List.ofFn_inj.mpr (funext fun lay => layerPart_sigOfList l hl lay)
    rw [e3, flatten_ofFn_slices_var]
    rfl
  rw [e1, e2]
  rw [show dv (sigOfList l).randomness = Ref.slice l 0 16 from dv_ofList_slice _ _ (by omega)]
  rw [show (16 : Nat) = 0 + 16 from rfl, ← slice_split, show 0 + (16 + 176 * 14) = 2480 from rfl,
    ← slice_split]
  exact slice_full _ _ hl

theorem length_sigToList (σ : Signature) : (sigToList σ).length = 7080 := by
  unfold sigToList
  rw [List.length_append, List.length_append, length_dv, length_fts_block, List.length_flatten,
    List.map_ofFn, List.sum_ofFn]
  have : ∀ lay, (List.length ∘ layerPart σ) lay = 676 + 16 * SphincsSecurity.layerHeight lay :=
    fun lay => (length_layerPart σ lay).trans (layerBytes_eq lay)
  simp only [this]
  decide

/-- **The signature codec** (the `ref.py` signature layout). -/
def sigCodec : Bytes 7080 ≃ Signature where
  toFun b := sigOfList (Ref.toList b)
  invFun σ := Ref.ofList 7080 (sigToList σ)
  left_inv b := by
    simp only
    rw [sigToList_sigOfList _ (Ref.length_toList b), Ref.ofList_toList]
  right_inv σ := by
    simp only
    rw [Ref.toList_ofList _ _ (length_sigToList σ), sigOfList_sigToList]

theorem sigCodec_symm_apply (σ : Signature) : sigCodec.symm σ = Ref.ofList 7080 (sigToList σ) := rfl

theorem sigCodec_apply (b : Bytes 7080) : sigCodec b = sigOfList (Ref.toList b) := rfl

/-! ## The witness decoder -/

/-- Decode the witness bytes (the fields at the witness offsets of `PROGRAMS.md`). -/
def sigOfWit (w : List Byte) : Signature where
  randomness := Ref.ofList 16 (Ref.witRho w)
  ftsSecret k := Ref.ofList 16 (Ref.witFtsSecret w k)
  ftsPath k j := Ref.ofList 16 (Ref.witFtsSib w k j)
  layers lay := ⟨Ref.ofList 4 (Ref.slice w (Ref.witCounters + 4 * lay.val) 4),
    fun i => Ref.ofList 16 (Ref.witChain w lay i), fun j => Ref.ofList 16 (Ref.witSib w lay j)⟩

/-- The witness decoder. -/
def witDec (w : Bytes 7080) : Signature := sigOfWit (Ref.toList w)

theorem slice_fromWitness (wl : List Byte) (hl : wl.length = 7080) (a b len : Nat)
    (ha : a + len ≤ 7080) (hb : b + len ≤ 7080)
    (hsrc : ∀ t < len, Ref.signatureSrc (a + t) = b + t) :
    Ref.slice (Ref.fromWitness wl) a len = Ref.slice wl b len := by
  apply List.ext_getElem
  · rw [length_slice _ _ _ (by rw [Ref.length_fromWitness]; exact ha), length_slice _ _ _ (by omega)]
  · intro t h1 h2
    have ht : t < len := by rw [length_slice _ _ _ (by omega)] at h2; exact h2
    simp only [Ref.slice, List.getElem_take, List.getElem_drop, Ref.fromWitness, List.getElem_map,
      List.getElem_range]
    rw [hsrc t ht, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl

theorem sigOfWit_eq (wl : List Byte) (hl : wl.length = 7080) :
    sigOfWit wl = sigOfList (Ref.fromWitness wl) := by
  have hwc := witCounters_eq
  apply sig_ext
  · show Ref.ofList 16 (Ref.slice wl 0 16) = Ref.ofList 16 (Ref.slice (Ref.fromWitness wl) 0 16)
    rw [slice_fromWitness wl hl 0 0 16 (by omega) (by omega) (fun t ht => by
      rw [signatureSrc_head _ (by omega)])]
  · intro k
    have hk := fts_lt k
    show Ref.ofList 16 (Ref.slice wl (16 + 176 * k.val) 16) = Ref.ofList 16
      (Ref.slice (Ref.fromWitness wl) (16 + 176 * k.val) 16)
    rw [slice_fromWitness wl hl _ (16 + 176 * k.val) 16 (by omega) (by omega) (fun t ht => by
      rw [signatureSrc_head _ (by omega)])]
  · intro k j
    have hk := fts_lt k
    have hj := ftsH_lt j
    show Ref.ofList 16 (Ref.slice wl (32 + 176 * k.val + 16 * j.val) 16) = Ref.ofList 16
      (Ref.slice (Ref.fromWitness wl) (16 + 176 * k.val + 16 + 16 * j.val) 16)
    rw [slice_fromWitness wl hl _ (32 + 176 * k.val + 16 * j.val) 16 (by omega) (by omega)
      (fun t ht => by rw [signatureSrc_head _ (by omega)]; omega)]
  · intro lay
    have hlay := lay_lt lay
    have hb := layer_bound lay
    have hB := layerBytes_eq lay
    show Ref.ofList 4 (Ref.slice wl (Ref.witCounters + 4 * lay.val) 4) = Ref.ofList 4
      (Ref.slice (Ref.fromWitness wl) (Ref.sigLayerOff lay) 4)
    rw [slice_fromWitness wl hl _ (Ref.witCounters + 4 * lay.val) 4 (by omega) (by omega)
      (fun t ht => by rw [signatureSrc_layer lay t (by omega), if_pos ht])]
  · intro lay i
    have hi := chain_lt i
    have hb := layer_bound lay
    have hB := layerBytes_eq lay
    have hw := wit_bound lay
    show Ref.ofList 16 (Ref.slice wl (Ref.witLayerOff lay + 16 * i.val) 16) = Ref.ofList 16
      (Ref.slice (Ref.fromWitness wl) (Ref.sigLayerOff lay + 4 + 16 * i.val) 16)
    rw [slice_fromWitness wl hl _ (Ref.witLayerOff lay + 16 * i.val) 16 (by omega) (by omega)
      (fun t ht => by
        rw [show Ref.sigLayerOff lay + 4 + 16 * i.val + t = Ref.sigLayerOff lay + (4 + 16 * i.val + t)
          by ring, signatureSrc_layer lay _ (by omega), if_neg (by omega)]
        omega)]
  · intro lay j
    have hj := j.isLt
    have hb := layer_bound lay
    have hB := layerBytes_eq lay
    have hw := wit_bound lay
    show Ref.ofList 16 (Ref.slice wl (Ref.witLayerOff lay + 672 + 16 * j.val) 16) = Ref.ofList 16
      (Ref.slice (Ref.fromWitness wl) (Ref.sigLayerOff lay + 676 + 16 * j.val) 16)
    rw [slice_fromWitness wl hl _ (Ref.witLayerOff lay + 672 + 16 * j.val) 16 (by omega) (by omega)
      (fun t ht => by
        rw [show Ref.sigLayerOff lay + 676 + 16 * j.val + t =
          Ref.sigLayerOff lay + (676 + 16 * j.val + t) by ring,
          signatureSrc_layer lay _ (by omega), if_neg (by omega)]
        omega)]

/-- The witness decoder reads the signature that expands to the witness. -/
theorem witDec_eq (w : Bytes 7080) : witDec w = sigCodec (Ref.unexpandRef w) := by
  rw [witDec, sigOfWit_eq _ (Ref.length_toList w), sigCodec_apply, Ref.unexpandRef,
    Ref.toList_ofList 7080 _ (Ref.length_fromWitness _)]

theorem witDec_expandRef (b : Bytes 7080) : witDec (Ref.expandRef b) = sigCodec b := by
  rw [witDec_eq, Ref.unexpandRef_expandRef]

end SigGolfCandidate.Equiv
