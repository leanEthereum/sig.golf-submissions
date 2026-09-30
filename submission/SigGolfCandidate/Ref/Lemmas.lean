import SigGolfCandidate.Ref.Scheme

/-!
# Basic facts about the reference specification

* byte conversions: `toList_ofList`, `ofList_toList`, `leNat_toList`, `length_toList`,
  `leNat_div_mod`, `leNat_lt`;
* lengths of the encodings (`length_tweak`, `length_le32`, ...), `pad64_eq` (padding of an input
  of known length);
* parameter tables (`height_values`, `shiftBelow_values`);
* expand is a bijection: `unexpandRef_expandRef`, `expandRef_unexpandRef` (and the list and
  index-map versions).
-/

namespace SigGolfCandidate.Ref
open SigGolf

theorem byte_toNat (v : Nat) : (byte v).toNat = v % 256 := by simp [byte]

theorem leNat_lt (l : List Byte) : leNat l < 256 ^ l.length := by
  induction l with
  | nil => simp [leNat]
  | cons b bs ih =>
    simp only [leNat, List.length_cons, Nat.pow_succ]
    have := b.isLt
    simp only [Nat.reducePow] at this
    nlinarith

theorem leNat_map_range (n v : Nat) :
    leNat ((List.range n).map fun i => byte (v / 256 ^ i)) = v % 256 ^ n := by
  induction n generalizing v with
  | zero => simp [leNat, Nat.mod_one]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    simp only [leNat, Nat.pow_zero, Nat.div_one, byte_toNat]
    have h : (fun i => byte (v / 256 ^ i)) ∘ Nat.succ = fun i => byte (v / 256 / 256 ^ i) := by
      funext i; simp [Nat.pow_succ, Nat.div_div_eq_div_mul, Nat.mul_comm]
    rw [h, ih, Nat.pow_succ, Nat.mul_comm (256 ^ n) 256, Nat.mod_mul]

theorem leNat_div_mod (l : List Byte) (i : Nat) :
    leNat l / 256 ^ i % 256 = (l.getD i 0).toNat := by
  induction l generalizing i with
  | nil => simp [leNat]
  | cons b bs ih =>
    have hb := b.isLt
    cases i with
    | zero => simp only [leNat, Nat.pow_zero, Nat.div_one, List.getD_cons_zero]; simp at hb ⊢; omega
    | succ i =>
      simp only [leNat, List.getD_cons_succ, Nat.pow_succ]
      rw [Nat.mul_comm (256 ^ i) 256, ← Nat.div_div_eq_div_mul]
      rw [show (b.toNat + 256 * leNat bs) / 256 = leNat bs by simp at hb; omega]
      exact ih i

theorem extractByte_ofNat (w v i : Nat) (h : 8 * i + 8 ≤ w) :
    (BitVec.ofNat w v).extractLsb' (8 * i) 8 = byte (v / 256 ^ i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, byte_toNat, Nat.shiftRight_eq_div_pow]
  rw [show (256 : Nat) ^ i = 2 ^ (8 * i) by rw [Nat.pow_mul]]
  rw [show w = 8 * i + (w - 8 * i) by omega, Nat.pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem toList_ofList (n : Nat) (l : List Byte) (h : l.length = n) : toList (ofList n l) = l := by
  subst h
  apply List.ext_getElem (by simp [toList, SigGolf.bytes])
  intro i h1 h2
  simp only [toList, SigGolf.bytes, ofList, List.getElem_map, List.getElem_range]
  rw [extractByte_ofNat _ _ _ (by simp [toList, SigGolf.bytes] at h1; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [byte_toNat, leNat_div_mod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl

theorem toList_eq_map {n : Nat} (x : Bytes n) :
    toList x = (List.range n).map fun i => byte (x.toNat / 256 ^ i) := by
  simp only [toList, SigGolf.bytes]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  have := extractByte_ofNat (8 * n) x.toNat i (by omega)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem leNat_toList {n : Nat} (x : Bytes n) : leNat (toList x) = x.toNat := by
  rw [toList_eq_map, leNat_map_range, Nat.mod_eq_of_lt]
  have := x.isLt
  rwa [Nat.pow_mul] at this

theorem ofList_toList {n : Nat} (x : Bytes n) : ofList n (toList x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp [ofList, leNat_toList]

theorem length_toList {n : Nat} (x : Bytes n) : (toList x).length = n := by
  simp [toList, SigGolf.bytes]

/-- The witness permutation checked on all `6404` positions (kernel evaluation). -/
theorem witness_check : (List.range sigBytes).all (fun i =>
    witnessSrc (signatureSrc i) == i && decide (signatureSrc i < sigBytes) &&
      signatureSrc (witnessSrc i) == i && decide (witnessSrc i < sigBytes)) = true := by
  decide +kernel

private theorem witness_check_at (i : Nat) (hi : i < sigBytes) :
    witnessSrc (signatureSrc i) = i ∧ signatureSrc i < sigBytes ∧
      signatureSrc (witnessSrc i) = i ∧ witnessSrc i < sigBytes := by
  have h := List.all_eq_true.mp witness_check i (List.mem_range.mpr hi)
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem witnessSrc_signatureSrc : ∀ i, i < sigBytes → witnessSrc (signatureSrc i) = i :=
  fun i hi => (witness_check_at i hi).1

theorem signatureSrc_witnessSrc : ∀ i, i < sigBytes → signatureSrc (witnessSrc i) = i :=
  fun i hi => (witness_check_at i hi).2.2.1

theorem signatureSrc_lt : ∀ i, i < sigBytes → signatureSrc i < sigBytes :=
  fun i hi => (witness_check_at i hi).2.1

theorem witnessSrc_lt : ∀ i, i < sigBytes → witnessSrc i < sigBytes :=
  fun i hi => (witness_check_at i hi).2.2.2

/-- Layer offsets. -/
theorem sigLayerOff_values :
    (List.range (nLayers + 1)).map sigLayerOff = [2480, 3332, 4104, 4876, 5648, 6404] := by
  decide
theorem witLayerOff_values :
    (List.range (nLayers + 1)).map witLayerOff = [2480, 3328, 4096, 4864, 5632, 6384] := by
  decide
theorem witCounters_eq : witCounters = 6384 := by decide

private theorem getD_map_range (n : Nat) (f : Nat → Byte) (i : Nat) (h : i < n) :
    ((List.range n).map f).getD i 0 = f i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range h]; rfl

theorem length_toWitness (l : List Byte) : (toWitness l).length = sigBytes := by simp [toWitness]
theorem length_fromWitness (l : List Byte) : (fromWitness l).length = sigBytes := by simp [fromWitness]

theorem fromWitness_toWitness (l : List Byte) (h : l.length = sigBytes) :
    fromWitness (toWitness l) = l := by
  apply List.ext_getElem (by rw [length_fromWitness, h])
  intro i h1 h2
  rw [length_fromWitness] at h1
  simp only [fromWitness, List.getElem_map, List.getElem_range, toWitness]
  rw [getD_map_range _ _ _ (signatureSrc_lt i h1), witnessSrc_signatureSrc i h1,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl

theorem toWitness_fromWitness (l : List Byte) (h : l.length = sigBytes) :
    toWitness (fromWitness l) = l := by
  apply List.ext_getElem (by rw [length_toWitness, h])
  intro i h1 h2
  rw [length_toWitness] at h1
  simp only [fromWitness, List.getElem_map, List.getElem_range, toWitness]
  rw [getD_map_range _ _ _ (witnessSrc_lt i h1), signatureSrc_witnessSrc i h1,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]; rfl

theorem unexpandRef_expandRef (sig : Bytes 6404) : unexpandRef (expandRef sig) = sig := by
  unfold unexpandRef expandRef
  rw [toList_ofList _ _ (by rw [length_toWitness]; rfl), fromWitness_toWitness _ (length_toList sig),
    ofList_toList]

theorem expandRef_unexpandRef (w : Bytes 6404) : expandRef (unexpandRef w) = w := by
  unfold unexpandRef expandRef
  rw [toList_ofList _ _ (by rw [length_fromWitness]; rfl), toWitness_fromWitness _ (length_toList w),
    ofList_toList]

/-! ## Lengths and padding -/

@[simp] theorem length_leBytes (k v : Nat) : (leBytes k v).length = k := by simp [leBytes]
@[simp] theorem length_le32 (v : Nat) : (le32 v).length = 4 := by simp [le32]
@[simp] theorem length_zeros (k : Nat) : (zeros k).length = k := by simp [zeros]
@[simp] theorem length_P : P.length = 16 := rfl
@[simp] theorem length_tweak (t lay tau p j : Nat) : (tweak t lay tau p j).length = 16 := by
  simp [tweak]
@[simp] theorem length_answerBytes (k : Nat) (a : BitVec 256) : (answerBytes k a).length = k := by
  simp [answerBytes]
@[simp] theorem length_thInput (tw payload : List Byte) :
    (thInput tw payload).length = tw.length + 16 + payload.length := by
  simp [thInput]; omega

theorem padBlocks_eq (len n : Nat) (h1 : len ≤ 64 * (n + 1)) (h2 : 64 * n < len) :
    padBlocks len = n := by
  unfold padBlocks; omega

/-- The query of an input of length in `(64 n, 64 (n+1)]`. -/
theorem pad64_eq (x : List Byte) (n : Nat) (h1 : x.length ≤ 64 * (n + 1)) (h2 : 64 * n < x.length) :
    pad64 x = ⟨n, ofList _ (x ++ zeros (64 * (n + 1) - x.length))⟩ := by
  unfold pad64 padTo64
  rw [padBlocks_eq _ _ h1 h2]

/-! ## The oracle input format -/

theorem fmt_of_not_chain (x : List Byte) (h : ¬ IsChainFmt x) : fmt x = pad64 x := by
  unfold fmt; rw [if_neg h]

theorem fmt_of_length_ne (x : List Byte) (h : x.length ≠ 48) : fmt x = pad64 x :=
  fmt_of_not_chain x (fun hc => h hc.1)

theorem fmt_of_chain (x : List Byte) (h : IsChainFmt x) : fmt x = ⟨0, ofList _ (chainBlock x)⟩ := by
  unfold fmt; rw [if_pos h]

theorem getD_one_thInput (t lay tau p j : Nat) (payload : List Byte) :
    (thInput (tweak t lay tau p j) payload).getD 1 0 = byte t := by
  simp [thInput, tweak]

/-- `thInput` with a tag other than 1 is zero padded. -/
theorem fmt_thInput (t lay tau p j : Nat) (payload : List Byte) (ht : byte t ≠ byte 1) :
    fmt (thInput (tweak t lay tau p j) payload) = pad64 (thInput (tweak t lay tau p j) payload) :=
  fmt_of_not_chain _ fun hc => ht ((getD_one_thInput t lay tau p j payload).symm.trans hc.2)

/-- The block of a chain step: `tw || 0^32 || v`. -/
theorem fmt_chainInput (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16) :
    fmt (chainInput lay tau e i mu v) =
      ⟨0, ofList _ (tweak 1 lay tau (8 * i + mu - 1) e ++ zeros 32 ++ v)⟩ := by
  have hc : IsChainFmt (chainInput lay tau e i mu v) :=
    ⟨by simp [chainInput, hv], getD_one_thInput _ _ _ _ _ _⟩
  rw [fmt_of_chain _ hc]
  have h1 := length_tweak 1 lay tau (8 * i + mu - 1) e
  have e : chainBlock (chainInput lay tau e i mu v) = tweak 1 lay tau (8 * i + mu - 1) e ++ zeros 32 ++ v := by
    unfold chainBlock chainInput thInput
    simp only [List.append_assoc]
    rw [List.take_left' h1, List.drop_append, h1, List.drop_eq_nil_of_le (by omega), List.nil_append,
      List.drop_append, length_P, List.drop_eq_nil_of_le (by simp), List.nil_append]
    simp [zeros]
  rw [e]

/-- The chain block has as many blocks as its zero padding (one). -/
theorem blocks_fmt (x : List Byte) : (fmt x).blocks = (pad64 x).blocks := by
  unfold fmt
  split
  · rename_i h
    simp [pad64, Query.blocks, padBlocks, h.1]
  · rfl

/-! ## Parameter tables -/

theorem height_values : (List.range nLayers).map height = [11, 6, 6, 6, 5] := by decide
theorem shiftBelow_values :
    (List.range nLayers).map shiftBelow = [23, 17, 11, 5, 0] := by decide
theorem topH_eq : topH = 11 := rfl
theorem topN_values : (List.range (topH + 1)).map topN =
    [0, 2048, 3072, 3584, 3840, 3968, 4032, 4064, 4080, 4088, 4092, 4094] := by decide
theorem regionBytes_eq : regionBytes = 65504 := by decide

end SigGolfCandidate.Ref
