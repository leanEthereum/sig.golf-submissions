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

theorem leNat_le32 (v : Nat) : leNat (le32 v) = v % 2 ^ 32 := by
  unfold le32 leBytes; rw [leNat_map_range]; norm_num

theorem fmt_of_chain (x : List Byte) (h : IsChainFmt x) : fmt x = ⟨0, ofList _ (chainBlock x)⟩ := by
  unfold fmt; rw [if_pos h]

theorem fmt_of_node (x : List Byte) (h : IsNodeFmt x) : fmt x = ⟨0, ofList _ (nodeBlock x)⟩ := by
  unfold fmt; rw [if_neg (fun hc => by have := hc.1.symm.trans h.1; omega), if_pos h]

theorem fmt_of_digest (x : List Byte) (h : IsDigestFmt x) : fmt x = ⟨0, ofList _ (digestBlock x)⟩ := by
  unfold fmt
  rw [if_neg (fun hc => by have := hc.1.symm.trans h.1; omega),
    if_neg (fun hc => by have := hc.1.symm.trans h.1; omega), if_pos h]

theorem fmt_of_plain (x : List Byte) (h1 : ¬ IsChainFmt x) (h2 : ¬ IsNodeFmt x)
    (h3 : ¬ IsDigestFmt x) : fmt x = pad64 x := by
  unfold fmt; rw [if_neg h1, if_neg h2, if_neg h3]

/-- An input whose tag byte (byte 1) is none of `1, 3, 10, 12` is zero padded. -/
theorem fmt_of_tag (x : List Byte) (h : x.getD 1 0 ∉ [byte 1, byte 3, byte 10, byte 12]) :
    fmt x = pad64 x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  exact fmt_of_plain x (fun hc => h.1 hc.2) (fun hc => hc.2.elim h.2.1 h.2.2.1)
    (fun hc => h.2.2.2 hc.2)

/-- An input of length other than `48, 64, 96` is zero padded. -/
theorem fmt_of_length (x : List Byte) (h : x.length ≠ 48 ∧ x.length ≠ 64 ∧ x.length ≠ 96) :
    fmt x = pad64 x :=
  fmt_of_plain x (fun hc => h.1 hc.1) (fun hc => h.2.1 hc.1) (fun hc => h.2.2 hc.1)

theorem getD_one_thInput (t lay tau p j : Nat) (payload : List Byte) :
    (thInput (tweak t lay tau p j) payload).getD 1 0 = byte t := by
  simp [thInput, tweak]

/-- `thInput` with a tag other than `1, 3, 10, 12` is zero padded. -/
theorem fmt_thInput (t lay tau p j : Nat) (payload : List Byte)
    (ht : byte t ∉ [byte 1, byte 3, byte 10, byte 12]) :
    fmt (thInput (tweak t lay tau p j) payload) = pad64 (thInput (tweak t lay tau p j) payload) :=
  fmt_of_tag _ (by rw [getD_one_thInput]; exact ht)

/-- The pieces of a `thInput` (byte positions `0..4`, `4..8`, `8..12`, `12..16`, `16..`). -/
private theorem thInput_split (t lay tau p j : Nat) (pl : List Byte) :
    thInput (tweak t lay tau p j) pl =
      [byte 1, byte t, byte lay, byte (tau / 2 ^ 32)] ++ (le32 p ++ (le32 (tau % 2 ^ 32) ++
        (le32 j ++ (P ++ pl)))) := by
  simp [thInput, tweak]

private theorem take_app {l₁ : List Byte} (l₂ : List Byte) {n : Nat} (h : l₁.length = n) :
    (l₁ ++ l₂).take n = l₁ := by subst h; simp

private theorem drop_app {l₁ : List Byte} (l₂ : List Byte) {n : Nat} (h : l₁.length = n) :
    (l₁ ++ l₂).drop n = l₂ := by subst h; simp

/-- **Chain block** of `tw(1, lay, tau, p, j) || P || v`: `tw(1, lay, tau, splitP p, j) || 0^32 || v`. -/
theorem fmt_thInput_chain (lay tau p j : Nat) (v : Val) (hv : v.length = 16) (hp : p < 2 ^ 32) :
    fmt (thInput (tweak 1 lay tau p j) v) =
      ⟨0, ofList _ (tweak 1 lay tau (splitP p) j ++ zeros 32 ++ v)⟩ := by
  have hc : IsChainFmt (thInput (tweak 1 lay tau p j) v) :=
    ⟨by simp [hv], getD_one_thInput _ _ _ _ _ _⟩
  rw [fmt_of_chain _ hc]
  congr 2
  unfold chainBlock slice
  rw [thInput_split]
  have e4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).take 4 = [a, b, c, d] :=
    fun l a b c d => rfl
  have d4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).drop 4 = l :=
    fun l a b c d => rfl
  rw [e4, d4, take_app _ (length_le32 p), leNat_le32, Nat.mod_eq_of_lt hp]
  rw [show (8 : Nat) = 4 + 4 from rfl, ← List.drop_drop, d4, drop_app _ (length_le32 p),
    show 32 = 4 + 28 from rfl, ← List.drop_drop, d4, show 28 = 4 + 24 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 p), show 24 = 4 + 20 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 _), show 20 = 4 + 16 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 _), drop_app _ length_P]
  have : (le32 (tau % 2 ^ 32) ++ (le32 j ++ (P ++ v))).take (4 + 4) = le32 (tau % 2 ^ 32) ++ le32 j := by
    rw [List.take_add, take_app _ (length_le32 _), drop_app _ (length_le32 _), take_app _ (length_le32 _)]
  rw [this]
  simp [tweak, zeros]

/-- The chain step `mu ∈ 1..8` of chain `i < 2^24`: the tweak carries `mu - 1` (byte 4) and `i`
(bytes 5..8). -/
theorem fmt_chainInput (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16) (hmu : 1 ≤ mu)
    (hmu' : mu ≤ 8) (hi : i < 2 ^ 24) :
    fmt (chainInput lay tau e i mu v) =
      ⟨0, ofList _ (tweak 1 lay tau (mu - 1 + 256 * i) e ++ zeros 32 ++ v)⟩ := by
  unfold chainInput
  rw [fmt_thInput_chain _ _ _ _ _ hv (by omega)]
  have : splitP (8 * i + mu - 1) = mu - 1 + 256 * i := by unfold splitP; omega
  rw [this]

/-- **Node block** of `tw(t, lay, tau, lam, j) || P || pl` (`t = 3` or `10`, 32-byte payload):
`tw(t, lay, tau, 0, heapIndex h lam j) || P || pl`, `h = height (lay mod 256)` (tag 3) or `ftsA`
(tag 10). -/
theorem fmt_thInput_node (t lay tau lam j : Nat) (pl : List Byte) (ht : t = 3 ∨ t = 10)
    (hpl : pl.length = 32) (hlam : lam < 2 ^ 32) (hj : j < 2 ^ 32) :
    fmt (thInput (tweak t lay tau lam j) pl) =
      ⟨0, ofList _ (thInput (tweak t lay tau 0
        (heapIndex (if t = 3 then height (lay % 256) else ftsA) lam j)) pl)⟩ := by
  have hn : IsNodeFmt (thInput (tweak t lay tau lam j) pl) := by
    refine ⟨by simp [hpl], ?_⟩
    rw [getD_one_thInput]; rcases ht with rfl | rfl <;> simp
  rw [fmt_of_node _ hn]
  congr 2
  have hh : nodeHeight (thInput (tweak t lay tau lam j) pl) =
      if t = 3 then height (lay % 256) else ftsA := by
    unfold nodeHeight
    rw [getD_one_thInput]
    rcases ht with rfl | rfl
    · simp [thInput, tweak, byte_toNat]
    · simp only [show (10 : Nat) ≠ 3 by decide, if_false]
      rw [if_neg (by decide)]
  unfold nodeBlock slice
  rw [hh, thInput_split]
  have e4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).take 4 = [a, b, c, d] :=
    fun l a b c d => rfl
  have d4 : ∀ (l : List Byte) (a b c d : Byte), ([a, b, c, d] ++ l).drop 4 = l :=
    fun l a b c d => rfl
  rw [e4, d4, take_app _ (length_le32 lam), leNat_le32, Nat.mod_eq_of_lt hlam]
  rw [show (8 : Nat) = 4 + 4 from rfl, ← List.drop_drop, d4, drop_app _ (length_le32 lam),
    take_app _ (length_le32 _), show 12 = 4 + 8 from rfl, ← List.drop_drop, d4,
    show 8 = 4 + 4 from rfl, ← List.drop_drop, drop_app _ (length_le32 lam),
    drop_app _ (length_le32 _), take_app _ (length_le32 j), leNat_le32, Nat.mod_eq_of_lt hj,
    show 16 = 4 + 12 from rfl, ← List.drop_drop, d4, show 12 = 4 + 8 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 lam), show 8 = 4 + 4 from rfl, ← List.drop_drop,
    drop_app _ (length_le32 _), drop_app _ (length_le32 j)]
  simp [thInput, tweak]

/-- The block of a hypertree node (`lay < 256`). -/
theorem fmt_nodeInput (lay tau lam j : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16)
    (hlay : lay < 256) (hlam : lam < 2 ^ 32) (hj : j < 2 ^ 32) :
    fmt (nodeInput lay tau lam j l r) =
      ⟨0, ofList _ (thInput (tweak 3 lay tau 0 (heapIndex (height lay) lam j)) (l ++ r))⟩ := by
  unfold nodeInput
  rw [fmt_thInput_node _ _ _ _ _ _ (Or.inl rfl) (by simp [hl, hr]) hlam hj, if_pos rfl,
    Nat.mod_eq_of_lt hlay]

/-- The block of a FORS node. -/
theorem fmt_ftsNodeInput (k idx lam j : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16)
    (hlam : lam < 2 ^ 32) (hj : j < 2 ^ 32) :
    fmt (ftsNodeInput k idx lam j l r) =
      ⟨0, ofList _ (thInput (tweak 10 k idx 0 (heapIndex ftsA lam j)) (l ++ r))⟩ := by
  unfold ftsNodeInput
  rw [fmt_thInput_node _ _ _ _ _ _ (Or.inr rfl) (by simp [hl, hr]) hlam hj, if_neg (by decide)]

/-- **Digest block**: `tw(12, 0, 0, 0, 0) || rho || m` (one block). -/
theorem fmt_digestInput (rho m : List Byte) (hr : rho.length = 16) (hm : m.length = 32) :
    fmt (digestInput rho m) = ⟨0, ofList _ (tweak 12 0 0 0 0 ++ rho ++ m)⟩ := by
  have hd : IsDigestFmt (digestInput rho m) :=
    ⟨by simp [digestInput, hr, hm], getD_one_thInput _ _ _ _ _ _⟩
  rw [fmt_of_digest _ hd]
  congr 2
  unfold digestBlock slice digestInput thInput
  have h16 := length_tweak 12 0 0 0 0
  simp only [List.append_assoc]
  rw [take_app _ h16, show 32 = 16 + 16 from rfl, ← List.drop_drop, drop_app _ h16,
    drop_app _ length_P, take_app _ hr, show 64 = 16 + 48 from rfl, ← List.drop_drop, drop_app _ h16,
    show 48 = 16 + 32 from rfl, ← List.drop_drop, drop_app _ length_P,
    show 32 = 16 + 16 from rfl, ← List.drop_drop, drop_app _ hr, drop_app _ (length_zeros 16)]

/-! ### Lengths, bytes and blocks of `fmt` -/

theorem length_chainBlock (x : List Byte) (h : x.length = 48) : (chainBlock x).length = 64 := by
  simp [chainBlock, slice, h]

theorem length_nodeBlock (x : List Byte) (h : x.length = 64) : (nodeBlock x).length = 64 := by
  simp [nodeBlock, slice, h]

theorem length_digestBlock (x : List Byte) (h : x.length = 96) : (digestBlock x).length = 64 := by
  simp [digestBlock, slice, h]

theorem length_padTo64 (x : List Byte) : (padTo64 x).length = 64 * (padBlocks x.length + 1) := by
  simp only [padTo64, List.length_append, length_zeros, padBlocks]; omega

set_option exponentiation.threshold 600 in
/-- The bytes of the query `fmt x` are `fmtList x`. -/
theorem toList_fmt (x : List Byte) : toList (fmt x).2 = fmtList x := by
  have key : ∀ (l : List Byte) (hl : l.length = 64), toList (⟨0, ofList _ l⟩ : Query).2 = l :=
    fun l hl => toList_ofList _ _ hl
  by_cases h1 : IsChainFmt x
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_chain x h1)
    refine e.trans ((key _ (length_chainBlock x h1.1)).trans ?_)
    unfold fmtList; rw [if_pos h1]
  by_cases h2 : IsNodeFmt x
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_node x h2)
    refine e.trans ((key _ (length_nodeBlock x h2.1)).trans ?_)
    unfold fmtList; rw [if_neg h1, if_pos h2]
  by_cases h3 : IsDigestFmt x
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_digest x h3)
    refine e.trans ((key _ (length_digestBlock x h3.1)).trans ?_)
    unfold fmtList; rw [if_neg h1, if_neg h2, if_pos h3]
  · have e := congrArg (fun q : Query => toList q.2) (fmt_of_plain x h1 h2 h3)
    refine e.trans ((toList_ofList _ _ (length_padTo64 x)).trans ?_)
    unfold fmtList; rw [if_neg h1, if_neg h2, if_neg h3]

/-- Bytes `0..4` and `8..12` (tag, layer, ... and `tau mod 2^32`) are copied by every case of `fmt`. -/
theorem getD_fmtList (x : List Byte) (i : Nat) (hi : i < 4 ∨ (8 ≤ i ∧ i < 12)) :
    (fmtList x).getD i 0 = x.getD i 0 := by
  unfold fmtList
  split_ifs with h1 h2 h3
  · unfold chainBlock slice
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rcases hi with hi | hi
    · rw [List.getElem?_append_left (by simp [h1.1]; omega), List.getElem?_take_of_lt hi]
    · rw [List.getElem?_append_right (by simp [h1.1]; omega),
        List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp [h1.1]; omega),
        List.getElem?_take_of_lt (by simp [h1.1]; omega), List.getElem?_drop]
      simp only [List.length_take, length_le32, h1.1]
      congr 2; omega
  · unfold nodeBlock slice
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rcases hi with hi | hi
    · rw [List.getElem?_append_left (by simp [h2.1]; omega), List.getElem?_take_of_lt hi]
    · rw [List.getElem?_append_right (by simp [h2.1]; omega),
        List.getElem?_append_right (by simp; omega), List.getElem?_append_left (by simp [h2.1]; omega),
        List.getElem?_take_of_lt (by simp [h2.1]; omega), List.getElem?_drop]
      simp only [List.length_take, length_le32, h2.1]
      congr 2; omega
  · unfold digestBlock
    simp only [List.getD_eq_getElem?_getD, List.append_assoc]
    rw [List.getElem?_append_left (by simp [h3.1]; omega), List.getElem?_take_of_lt (by omega)]
  · unfold padTo64
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append, zeros]
    split
    · rfl
    · rename_i h
      simp
      rw [List.getElem?_eq_none (l := x) (by omega), List.getElem?_replicate]
      split <;> rfl

/-- Byte `i < 4` or `8 ≤ i < 12` of the query `fmt x` is byte `i` of `x`. -/
theorem getD_toList_fmt (x : List Byte) (i : Nat) (hi : i < 4 ∨ (8 ≤ i ∧ i < 12)) :
    (toList (fmt x).2).getD i 0 = x.getD i 0 := by
  rw [toList_fmt, getD_fmtList x i hi]

/-- Every case other than the digest has as many blocks as the zero padding. -/
theorem blocks_fmt (x : List Byte) (h : ¬ IsDigestFmt x) : (fmt x).blocks = (pad64 x).blocks := by
  by_cases h1 : IsChainFmt x
  · rw [fmt_of_chain x h1]; show 0 + 1 = padBlocks x.length + 1; rw [h1.1]; rfl
  by_cases h2 : IsNodeFmt x
  · rw [fmt_of_node x h2]; show 0 + 1 = padBlocks x.length + 1; rw [h2.1]; rfl
  rw [fmt_of_plain x h1 h2 h]

/-- The digest block is one block (its zero padding would be two). -/
theorem blocks_fmt_digest (x : List Byte) (h : IsDigestFmt x) : (fmt x).blocks = 1 := by
  rw [fmt_of_digest x h]; rfl

theorem blocks_fmt_le (x : List Byte) : (fmt x).blocks ≤ (pad64 x).blocks := by
  by_cases h : IsDigestFmt x
  · rw [blocks_fmt_digest x h]; show 1 ≤ padBlocks x.length + 1; omega
  · rw [blocks_fmt x h]

/-! ## Parameter tables -/

theorem height_values : (List.range nLayers).map height = [11, 6, 6, 6, 5] := by decide
theorem shiftBelow_values :
    (List.range nLayers).map shiftBelow = [23, 17, 11, 5, 0] := by decide
theorem topH_eq : topH = 11 := rfl
theorem topN_values : (List.range (topH + 1)).map topN =
    [0, 2048, 3072, 3584, 3840, 3968, 4032, 4064, 4080, 4088, 4092, 4094] := by decide
theorem regionBytes_eq : regionBytes = 65504 := by decide

end SigGolfCandidate.Ref
