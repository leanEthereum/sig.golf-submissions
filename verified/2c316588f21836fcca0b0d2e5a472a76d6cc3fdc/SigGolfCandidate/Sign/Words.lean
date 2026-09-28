import SigGolfCandidate.Sign.Sim

/-!
# Byte lists as doublewords; HASH inputs of the reference formats

* `wordsOf l` : the little-endian doublewords of a byte list (last chunk zero-padded);
  `wordsToNat (wordsOf l) = leNat l`, `wordsOf_append` (first part 8-divisible).
* `bytesOfWord`, `valOfWords` (16-byte values from two dwords), `answerBytes_16`.
* `pad64_eq_query` : `pad64 x = queryOfWords (padBlocks |x|) (wordsOf (padTo64 x))`, and
  `hashInput_eq_pad64` : the HASH input of a machine state is `pad64 x` once its buffer
  `readWords` equals `wordsOf (padTo64 x)`.
* `twWords` : the two dwords of a tweak (`wordsOf_tweak`), and the dword lists of every input
  format (`words_prfInput`, `words_chainInput`, …).
* `readWords` helpers on `BitVec.ofNat` addresses, `writeHash` memory.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## `leNat` -/

theorem leNat_append (a b : List Byte) : leNat (a ++ b) = leNat a + 256 ^ a.length * leNat b := by
  induction a with
  | nil => simp [leNat]
  | cons x xs ih => simp only [List.cons_append, leNat, ih, List.length_cons, Nat.pow_succ]; ring

theorem leNat_leBytes (k v : Nat) : leNat (leBytes k v) = v % 256 ^ k := leNat_map_range k v

theorem leNat_le32 (v : Nat) : leNat (le32 v) = v % 2 ^ 32 := by
  rw [le32, leNat_leBytes]; norm_num

theorem leNat_zeros (k : Nat) : leNat (zeros k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [zeros, List.replicate_succ, leNat] at ih ⊢; exact ih

/-! ## `wordsOf` -/

/-- Little-endian doublewords of a byte list (the last chunk zero-padded). -/
def wordsOf : List Byte → List Word
  | [] => []
  | b :: l => BitVec.ofNat 64 (leNat ((b :: l).take 8)) :: wordsOf ((b :: l).drop 8)
termination_by l => l.length
decreasing_by all_goals (simp; try omega)

theorem wordsOf_nil : wordsOf [] = [] := wordsOf.eq_1

theorem wordsOf_cons (b : Byte) (l : List Byte) :
    wordsOf (b :: l) = BitVec.ofNat 64 (leNat ((b :: l).take 8)) :: wordsOf ((b :: l).drop 8) :=
  wordsOf.eq_2 b l

theorem wordsOf_eq (l : List Byte) (h : l ≠ []) :
    wordsOf l = BitVec.ofNat 64 (leNat (l.take 8)) :: wordsOf (l.drop 8) := by
  cases l with
  | nil => exact absurd rfl h
  | cons b l => exact wordsOf_cons b l

theorem wordsToNat_wordsOf (l : List Byte) : wordsToNat (wordsOf l) = leNat l := by
  induction h : l.length using Nat.strong_induction_on generalizing l with
  | _ n ih =>
    cases l with
    | nil => rw [wordsOf_nil]; rfl
    | cons b l' =>
      rw [wordsOf_cons, wordsToNat, ih _ (by simp at h ⊢; omega) _ rfl]
      have hlt := leNat_lt ((b :: l').take 8)
      have hl8 : ((b :: l').take 8).length ≤ 8 := by simp
      have : (256 : Nat) ^ ((b :: l').take 8).length ≤ 2 ^ 64 := by
        calc (256 : Nat) ^ ((b :: l').take 8).length ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) hl8
          _ = 2 ^ 64 := by norm_num
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      conv_rhs => rw [← List.take_append_drop 8 (b :: l'), leNat_append]
      by_cases h8 : 8 ≤ (b :: l').length
      · rw [List.length_take, Nat.min_eq_left h8]; norm_num
      · have : (b :: l').drop 8 = [] := List.drop_eq_nil_of_le (by omega)
        rw [this]; simp [leNat]

theorem wordsOf_append (a b : List Byte) (h : a.length % 8 = 0) :
    wordsOf (a ++ b) = wordsOf a ++ wordsOf b := by
  induction hn : a.length using Nat.strong_induction_on generalizing a with
  | _ n ih =>
    cases a with
    | nil => simp [wordsOf_nil]
    | cons x xs =>
      have h8 : 8 ≤ (x :: xs).length := by simp at h ⊢; omega
      rw [List.cons_append, wordsOf_cons, wordsOf_cons, ← List.cons_append,
        List.take_append_of_le_length h8, List.drop_append_of_le_length h8,
        ih _ (by simp at hn ⊢; omega) _ (by simp at h ⊢; omega) rfl]
      rfl

theorem wordsOf_eight (l : List Byte) (h : l.length = 8) : wordsOf l = [BitVec.ofNat 64 (leNat l)] := by
  have hne : l ≠ [] := by rintro rfl; simp at h
  rw [wordsOf_eq l hne, List.take_of_length_le (by omega),
    List.drop_eq_nil_of_le (by omega), wordsOf_nil]

theorem wordsOf_zeros (k : Nat) : wordsOf (zeros (8 * k)) = List.replicate k 0 := by
  induction k with
  | zero => simp [zeros, wordsOf_nil]
  | succ k ih =>
    rw [show 8 * (k + 1) = 8 + 8 * k by ring,
      show zeros (8 + 8 * k) = zeros 8 ++ zeros (8 * k) from List.replicate_add _ _ _,
      wordsOf_append _ _ (by simp), wordsOf_eight _ (by simp), ih, leNat_zeros, List.replicate_succ]
    rfl

@[simp] theorem length_wordsOf_16 (l : List Byte) (h : l.length = 16) : (wordsOf l).length = 2 := by
  rw [← List.take_append_drop 8 l, wordsOf_append _ _ (by simp; omega),
    wordsOf_eight _ (by simp; omega), wordsOf_eight _ (by simp; omega)]
  rfl

/-! ## Words and values -/

/-- The 8 little-endian bytes of a dword. -/
def bytesOfWord (w : Word) : List Byte := (List.range 8).map fun i => w.extractLsb' (8 * i) 8

@[simp] theorem length_bytesOfWord (w : Word) : (bytesOfWord w).length = 8 := by simp [bytesOfWord]

theorem leNat_bytesOfWord (w : Word) : leNat (bytesOfWord w) = w.toNat := by
  have h := leNat_map_range 8 w.toNat
  have he : bytesOfWord w = (List.range 8).map fun i => byte (w.toNat / 256 ^ i) := by
    unfold bytesOfWord
    apply List.map_congr_left
    intro i hi
    have hi' : i < 8 := List.mem_range.mp hi
    have := extractByte_ofNat 64 w.toNat i (by omega)
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
    exact this
  rw [he, h]
  exact Nat.mod_eq_of_lt (by have := w.isLt; norm_num at this ⊢; omega)

@[simp] theorem wordsOf_bytesOfWord (w : Word) : wordsOf (bytesOfWord w) = [w] := by
  rw [wordsOf_eight _ (by simp), leNat_bytesOfWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- The 16-byte value of two dwords. -/
def valOfWords (w0 w1 : Word) : Val := bytesOfWord w0 ++ bytesOfWord w1

@[simp] theorem length_valOfWords (w0 w1 : Word) : (valOfWords w0 w1).length = 16 := by
  simp [valOfWords]

@[simp] theorem wordsOf_valOfWords (w0 w1 : Word) : wordsOf (valOfWords w0 w1) = [w0, w1] := by
  rw [valOfWords, wordsOf_append _ _ (by simp)]; simp

theorem extractLsb'_extractLsb' (a : BitVec 256) (o i : Nat) (hi : i < 8) :
    (a.extractLsb' o 64).extractLsb' (8 * i) 8 = a.extractLsb' (o + 8 * i) 8 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.pow_add, ← Nat.div_div_eq_div_mul]
  rw [show (64 : Nat) = 8 * i + (64 - 8 * i) by omega, Nat.pow_add, Nat.mod_mul_right_div_self,
    Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

/-- A 16-byte hash answer as two dwords. -/
theorem answerBytes_16 (a : BitVec 256) :
    answerBytes 16 a = valOfWords (a.extractLsb' 0 64) (a.extractLsb' 64 64) := by
  unfold answerBytes valOfWords bytesOfWord
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append]
  simp only [extractLsb'_extractLsb' _ _ _ (by norm_num : (0 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (1 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (2 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (3 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (4 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (5 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (6 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (7 : Nat) < 8)]

theorem wordsOf_answerBytes_16 (a : BitVec 256) :
    wordsOf (answerBytes 16 a) = [a.extractLsb' 0 64, a.extractLsb' 64 64] := by
  rw [answerBytes_16, wordsOf_valOfWords]

/-- A 16-byte value is determined by its dwords. -/
theorem val_eq_valOfWords (v : Val) (h : v.length = 16) (w0 w1 : Word) (hw : wordsOf v = [w0, w1]) :
    v = valOfWords w0 w1 := by
  have h1 : v = v.take 8 ++ v.drop 8 := (List.take_append_drop 8 v).symm
  rw [h1, wordsOf_append _ _ (by simp; omega), wordsOf_eight _ (by simp; omega),
    wordsOf_eight _ (by simp; omega)] at hw
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at hw
  have key : ∀ (l : List Byte), l.length = 8 → l = bytesOfWord (BitVec.ofNat 64 (leNat l)) := by
    intro l hl
    apply List.ext_getElem (by simp [hl])
    intro i h1 h2
    simp only [bytesOfWord, List.getElem_map, List.getElem_range]
    rw [extractByte_ofNat _ _ _ (by simp at h2; omega)]
    apply BitVec.eq_of_toNat_eq
    rw [byte_toNat, leNat_div_mod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]; rfl
  rw [h1, valOfWords, key (v.take 8) (by simp; omega), key (v.drop 8) (by simp; omega), hw.1, hw.2]

/-! ## Queries -/

theorem pad64_eq_query (x : List Byte) :
    pad64 x = queryOfWords (padBlocks x.length) (wordsOf (padTo64 x)) := by
  unfold pad64 queryOfWords ofList
  rw [wordsToNat_wordsOf]

/-- The HASH input of a state whose buffer holds the padded words of `x`. -/
theorem hashInput_eq_pad64 (t : MachineState) (x : List Byte) (n : Nat) (hn : padBlocks x.length = n)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1))) (hn' : 64 * (n + 1) < 2 ^ 64)
    (h10 : (t.getReg .x10).toNat % 8 = 0)
    (hw : t.readWords (t.getReg .x10) (8 * (n + 1)) = wordsOf (padTo64 x)) :
    hashInput t = pad64 x := by
  rw [hashInput_eq_words t n h11 hn' h10, hw, pad64_eq_query, hn]

/-- HASH argument validity for numeric registers. -/
theorem hashArgs_of {t : MachineState} {a n d : Nat} (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha : a % 8 = 0) (hn : 0 < n ∧ n % 64 = 0) (han : a + n ≤ 2 ^ 24) (hd : d % 8 = 0)
    (hd' : d + 32 ≤ 2 ^ 24) (hn' : n < 2 ^ 64) : hashArgumentsValid t = true := by
  have ha' : a < 2 ^ 64 := by omega
  have hd'' : d < 2 ^ 64 := by omega
  simp only [hashArgumentsValid, h10, h11, h12, accessValid, rangeValid, MEMORY_BYTES,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hd'', Nat.mod_eq_of_lt hn',
    Bool.and_eq_true, decide_eq_true_eq]
  omega

/-! ## Tweaks -/

/-- The two dwords of `tweak t lay tau p j` (fields reduced mod their widths). -/
def twWords (t lay tau p j : Nat) : List Word :=
  [BitVec.ofNat 64 (1 + 256 * (t % 256) + 65536 * (lay % 256) + 2 ^ 24 * (tau / 2 ^ 32 % 256) +
      2 ^ 32 * (p % 2 ^ 32)),
   BitVec.ofNat 64 (tau % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32))]

theorem wordsOf_tweak (t lay tau p j : Nat) : wordsOf (tweak t lay tau p j) = twWords t lay tau p j := by
  unfold tweak
  rw [List.append_assoc, wordsOf_append _ _ (by simp), wordsOf_eight _ (by simp),
    wordsOf_eight _ (by simp)]
  simp only [twWords, leNat_append, leNat, leNat_le32, byte_toNat, List.length_cons,
    List.length_nil, length_le32]
  simp only [List.cons_append, List.nil_append, Nat.mod_mod, List.cons.injEq, and_true]
  constructor <;> congr 1 <;> ring

/-- `thInput tw payload` followed by zero padding, as dwords. -/
theorem wordsOf_thInput_pad (t lay tau p j : Nat) (payload : List Byte) (z : Nat) :
    wordsOf (thInput (tweak t lay tau p j) payload ++ zeros z) =
      twWords t lay tau p j ++ [0, 0] ++ wordsOf (payload ++ zeros z) := by
  unfold thInput P
  rw [List.append_assoc, List.append_assoc, wordsOf_append _ _ (by simp), wordsOf_tweak,
    wordsOf_append _ _ (by simp), show (16 : Nat) = 8 * 2 from rfl, wordsOf_zeros]
  simp

theorem padTo64_eq (x : List Byte) (n : Nat) (h1 : x.length ≤ 64 * (n + 1)) (h2 : 64 * n < x.length) :
    padBlocks x.length = n ∧ padTo64 x = x ++ zeros (64 * (n + 1) - x.length) := by
  have := padBlocks_eq _ _ h1 h2
  exact ⟨this, by unfold padTo64; rw [this]⟩

/-- A 16-byte value followed by zero padding. -/
theorem wordsOf_val_append (v : Val) (hv : v.length = 16) (rest : List Byte) :
    wordsOf (v ++ rest) = wordsOf v ++ wordsOf rest := wordsOf_append _ _ (by omega)

/-- A list of 16-byte values. -/
theorem wordsOf_flatten (vs : List Val) (hv : ∀ v ∈ vs, v.length = 16) :
    wordsOf vs.flatten = (vs.map wordsOf).flatten := by
  induction vs with
  | nil => simp [wordsOf_nil]
  | cons v vs ih =>
    rw [List.flatten_cons, wordsOf_append _ _ (by rw [hv v (by simp)]),
      ih (fun w hw => hv w (by simp [hw]))]
    simp

theorem length_flatten_vals (vs : List Val) (hv : ∀ v ∈ vs, v.length = 16) :
    vs.flatten.length = 16 * vs.length := by
  induction vs with
  | nil => simp
  | cons v vs ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      hv v (by simp), ih (fun w hw => hv w (by simp [hw]))]
    ring

/-! ## Input formats as dwords (`wordsOf (padTo64 x)` and `padBlocks`) -/

theorem words_prfInput (S : List Byte) (hS : S.length = 32) (lay tau e i : Nat) :
    padBlocks (prfInput S lay tau e i).length = 0 ∧
    wordsOf (padTo64 (prfInput S lay tau e i)) = twWords 0 lay tau i e ++ [0, 0] ++ wordsOf S := by
  obtain ⟨h1, h2⟩ := padTo64_eq (prfInput S lay tau e i) 0 (by simp [prfInput, hS])
    (by simp [prfInput, hS])
  refine ⟨h1, ?_⟩
  rw [h2, prfInput, wordsOf_thInput_pad]
  simp [hS, zeros]

theorem words_porsPrfInput (S : List Byte) (hS : S.length = 32) (idx q : Nat) :
    padBlocks (porsPrfInput S idx q).length = 0 ∧
    wordsOf (padTo64 (porsPrfInput S idx q)) = twWords 8 0 idx 0 q ++ [0, 0] ++ wordsOf S := by
  obtain ⟨h1, h2⟩ := padTo64_eq (porsPrfInput S idx q) 0 (by simp [porsPrfInput, hS])
    (by simp [porsPrfInput, hS])
  refine ⟨h1, ?_⟩
  rw [h2, porsPrfInput, wordsOf_thInput_pad]
  simp [hS, zeros]

/-- A 48-byte input `tw | P | v` (chain step, FORS leaf). -/
theorem words_th16 (t lay tau p j : Nat) (v : Val) (hv : v.length = 16) :
    padBlocks (thInput (tweak t lay tau p j) v).length = 0 ∧
    wordsOf (padTo64 (thInput (tweak t lay tau p j) v)) =
      twWords t lay tau p j ++ [0, 0] ++ wordsOf v ++ [0, 0] := by
  obtain ⟨h1, h2⟩ := padTo64_eq (thInput (tweak t lay tau p j) v) 0 (by simp [hv]) (by simp [hv])
  refine ⟨h1, ?_⟩
  rw [h2, wordsOf_thInput_pad, wordsOf_val_append _ hv]
  simp only [length_thInput, length_tweak, hv]
  rw [show 64 * (0 + 1) - (16 + 16 + 16) = 8 * 2 from rfl, wordsOf_zeros]
  simp

/-- The HASH input of a chain step (value-last format `tw || 0^32 || v`, `fmt_chainInput`). -/
theorem hashInput_eq_chain (t : MachineState) (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16)
    (hmu : 1 ≤ mu) (hmu' : mu ≤ 8) (hi : i < 2 ^ 24)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (h10 : (t.getReg .x10).toNat % 8 = 0)
    (hw : t.readWords (t.getReg .x10) 8 =
      twWords 1 lay tau (mu - 1 + 256 * i) e ++ [0, 0, 0, 0] ++ wordsOf v) :
    hashInput t = fmt (chainInput lay tau e i mu v) := by
  rw [hashInput_eq_words t 0 h11 (by norm_num) h10, hw, fmt_chainInput _ _ _ _ _ _ hv hmu hmu' hi]
  unfold queryOfWords ofList
  rw [← wordsToNat_wordsOf (tweak 1 lay tau (mu - 1 + 256 * i) e ++ zeros 32 ++ v),
    wordsOf_append _ _ (by simp [zeros]), wordsOf_append _ _ (by simp), wordsOf_tweak,
    show (32 : Nat) = 8 * 4 from rfl, wordsOf_zeros]
  rfl

/-- The HASH input of the one-block digest (`tw | rho | m`, `fmt_digestInput`). -/
theorem hashInput_eq_digest (t : MachineState) (rho m : List Byte) (hr : rho.length = 16)
    (hm : m.length = 32)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64) (h10 : (t.getReg .x10).toNat % 8 = 0)
    (hw : t.readWords (t.getReg .x10) 8 = twWords 12 0 0 0 0 ++ wordsOf rho ++ wordsOf m) :
    hashInput t = fmt (digestInput rho m) := by
  rw [hashInput_eq_words t 0 h11 (by norm_num) h10, hw, fmt_digestInput _ _ hr hm]
  unfold queryOfWords ofList
  rw [← wordsToNat_wordsOf (tweak 12 0 0 0 0 ++ rho ++ m),
    wordsOf_append _ _ (by simp [hr]), wordsOf_append _ _ (by simp), wordsOf_tweak]

theorem blocks_fmt_th (t lay tau p j : Nat) (payload : List Byte)
    (ht : byte t ∉ [byte 1, byte 3, byte 12]) :
    (fmt (thInput (tweak t lay tau p j) payload)).blocks = (pad64 (thInput (tweak t lay tau p j) payload)).blocks := by
  rw [fmt_thInput _ _ _ _ _ _ ht]

/-- A 64-byte input `tw | P | l | r` (tree node, FORS node). -/
theorem words_th32 (t lay tau p j : Nat) (l r : Val) (hl : l.length = 16) (hr : r.length = 16) :
    padBlocks (thInput (tweak t lay tau p j) (l ++ r)).length = 0 ∧
    wordsOf (padTo64 (thInput (tweak t lay tau p j) (l ++ r))) =
      twWords t lay tau p j ++ [0, 0] ++ wordsOf l ++ wordsOf r := by
  obtain ⟨h1, h2⟩ := padTo64_eq (thInput (tweak t lay tau p j) (l ++ r)) 0 (by simp [hl, hr])
    (by simp [hl, hr])
  refine ⟨h1, ?_⟩
  rw [h2, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, List.length_append, hl, hr]
  rw [show 64 * (0 + 1) - (16 + 16 + (16 + 16)) = 0 from rfl, show zeros 0 = [] from rfl,
    List.append_nil, wordsOf_val_append _ hl]
  simp

/-- Inputs `tw | P | v_0 .. v_{m-1}` with `m` 16-byte values filling whole blocks
(`32 + 16 m = 64 (n+1)`): OTS leaf (`m = 42`), FORS roots (`m = 14`). -/
theorem words_thVals (t lay tau p j : Nat) (vs : List Val) (hv : ∀ v ∈ vs, v.length = 16) (n : Nat)
    (hn : 32 + 16 * vs.length = 64 * (n + 1)) :
    padBlocks (thInput (tweak t lay tau p j) vs.flatten).length = n ∧
    wordsOf (padTo64 (thInput (tweak t lay tau p j) vs.flatten)) =
      twWords t lay tau p j ++ [0, 0] ++ (vs.map wordsOf).flatten := by
  have hl := length_flatten_vals vs hv
  obtain ⟨h1, h2⟩ := padTo64_eq (thInput (tweak t lay tau p j) vs.flatten) n
    (by simp [hl]; omega) (by simp [hl]; omega)
  refine ⟨h1, ?_⟩
  rw [h2, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, hl]
  rw [show 64 * (n + 1) - (16 + 16 + 16 * vs.length) = 0 by omega, show zeros 0 = [] from rfl,
    List.append_nil, wordsOf_flatten _ hv]

theorem wordsOf_le32_pad (c : Nat) : wordsOf (le32 c ++ zeros 12) = [BitVec.ofNat 64 (c % 2 ^ 32), 0] := by
  rw [show zeros 12 = zeros 4 ++ zeros (8 * 1) from List.replicate_add 4 8 (0 : Byte), ← List.append_assoc,
    wordsOf_append _ _ (by simp), wordsOf_eight _ (by simp), wordsOf_zeros]
  simp [leNat_append, leNat_le32, leNat_zeros]

theorem words_encInput (lay tau e : Nat) (M : Val) (hM : M.length = 16) (c : Nat) :
    padBlocks (encInput lay tau e M c).length = 0 ∧
    wordsOf (padTo64 (encInput lay tau e M c)) =
      twWords 4 lay tau 0 e ++ [0, 0] ++ wordsOf M ++ [BitVec.ofNat 64 (c % 2 ^ 32), 0] := by
  obtain ⟨h1, h2⟩ := padTo64_eq (encInput lay tau e M c) 0 (by simp [encInput, hM])
    (by simp [encInput, hM])
  refine ⟨h1, ?_⟩
  rw [h2, encInput, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, List.length_append, hM, length_le32]
  rw [show 64 * (0 + 1) - (16 + 16 + (16 + 4)) = 12 from rfl, List.append_assoc M,
    wordsOf_val_append _ hM, wordsOf_le32_pad]
  simp

theorem words_rndInput (S m : List Byte) (hS : S.length = 32) (hm : m.length = 32) (a : Nat) :
    padBlocks (rndInput S m a).length = 1 ∧
    wordsOf (padTo64 (rndInput S m a)) =
      twWords 7 0 0 a 0 ++ [0, 0] ++ wordsOf S ++ wordsOf m ++ [0, 0, 0, 0] := by
  obtain ⟨h1, h2⟩ := padTo64_eq (rndInput S m a) 1 (by simp [rndInput, hS, hm])
    (by simp [rndInput, hS, hm])
  refine ⟨h1, ?_⟩
  rw [h2, rndInput, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, List.length_append, hS, hm]
  rw [show 64 * (1 + 1) - (16 + 16 + (32 + 32)) = 8 * 4 from rfl,
    wordsOf_append _ _ (by simp [hS, hm]), wordsOf_append _ _ (by omega), wordsOf_zeros]
  simp

theorem words_digestInput (rho m : List Byte) (hr : rho.length = 16) (hm : m.length = 32) :
    padBlocks (digestInput rho m).length = 1 ∧
    wordsOf (padTo64 (digestInput rho m)) =
      twWords 12 0 0 0 0 ++ [0, 0] ++ wordsOf rho ++ [0, 0] ++ wordsOf m ++ [0, 0, 0, 0] := by
  obtain ⟨h1, h2⟩ := padTo64_eq (digestInput rho m) 1 (by simp [digestInput, hr, hm])
    (by simp [digestInput, hr, hm])
  refine ⟨h1, ?_⟩
  rw [h2, digestInput, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, List.length_append, hr, hm, length_zeros]
  rw [show 64 * (1 + 1) - (16 + 16 + (16 + 16 + 32)) = 8 * 4 from rfl,
    wordsOf_append _ _ (by simp [hr, hm]), wordsOf_append _ _ (by simp [hr]),
    wordsOf_append _ _ (by omega), wordsOf_zeros, show (16 : Nat) = 8 * 2 from rfl, wordsOf_zeros]
  simp

/-! ## `readWords` on numeric addresses -/

theorem readWords_add (t : MachineState) (a : Word) (m n : Nat) :
    t.readWords a (m + n) = t.readWords a m ++ t.readWords (a + BitVec.ofNat 64 (8 * m)) n := by
  induction m generalizing a with
  | zero => simp [MachineState.readWords]
  | succ m ih =>
    rw [Nat.add_right_comm, MachineState.readWords_succ, ih, MachineState.readWords_succ]
    simp only [List.cons_append, BitVec.add_assoc]
    congr 3
    apply BitVec.eq_of_toNat_eq; simp <;> omega

theorem readWords_ofNat_add (t : MachineState) (a m n : Nat) :
    t.readWords (BitVec.ofNat 64 a) (m + n) =
      t.readWords (BitVec.ofNat 64 a) m ++ t.readWords (BitVec.ofNat 64 (a + 8 * m)) n := by
  rw [readWords_add, BitVec.ofNat_add]

theorem readWords_ofNat_succ (t : MachineState) (a n : Nat) :
    t.readWords (BitVec.ofNat 64 a) (n + 1) =
      t.getMem (BitVec.ofNat 64 a) :: t.readWords (BitVec.ofNat 64 (a + 8)) n := by
  rw [MachineState.readWords_succ]
  congr 2
  apply BitVec.eq_of_toNat_eq; simp <;> omega

theorem readWords_ofNat_one (t : MachineState) (a : Nat) :
    t.readWords (BitVec.ofNat 64 a) 1 = [t.getMem (BitVec.ofNat 64 a)] := rfl

theorem readWords_ofNat_two (t : MachineState) (a : Nat) :
    t.readWords (BitVec.ofNat 64 a) 2 = [t.getMem (BitVec.ofNat 64 a), t.getMem (BitVec.ofNat 64 (a + 8))] := by
  rw [readWords_ofNat_succ, readWords_ofNat_succ]; rfl

/-- `readWords` depends only on the memory at the read addresses. -/
theorem readWords_congr (t t' : MachineState) (a : Nat) (n : Nat)
    (h : ∀ i < n, t'.getMem (BitVec.ofNat 64 (a + 8 * i)) = t.getMem (BitVec.ofNat 64 (a + 8 * i))) :
    t'.readWords (BitVec.ofNat 64 a) n = t.readWords (BitVec.ofNat 64 a) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [readWords_ofNat_succ, readWords_ofNat_succ, ih (a + 8)]
    · congr 1; simpa using h 0 (by omega)
    · intro i hi; have := h (i + 1) (by omega); rw [show a + 8 + 8 * i = a + 8 * (i + 1) by ring]; exact this

/-- An element of a `readWords` list. -/
theorem getMem_of_readWords (t : MachineState) : ∀ (n a i : Nat) (L : List Word),
    t.readWords (BitVec.ofNat 64 a) n = L → i < n → t.getMem (BitVec.ofNat 64 (a + 8 * i)) = L.getD i 0 := by
  intro n
  induction n with
  | zero => intro a i L _ hi; omega
  | succ n ih =>
    intro a i L h hi
    rw [readWords_ofNat_succ] at h
    subst h
    cases i with
    | zero => simp
    | succ i =>
      rw [show a + 8 * (i + 1) = a + 8 + 8 * i by ring, ih (a + 8) i _ rfl (by omega)]
      simp

/-- `readWords` of 16-byte slots `base + 16 i`, `i < m`. -/
theorem readWords_slots (t : MachineState) (base : Nat) (vs : List Val)
    (h : ∀ i (hi : i < vs.length), t.readWords (BitVec.ofNat 64 (base + 16 * i)) 2 = wordsOf vs[i]) :
    t.readWords (BitVec.ofNat 64 base) (2 * vs.length) = (vs.map wordsOf).flatten := by
  induction vs generalizing base with
  | nil => rfl
  | cons v vs ih =>
    rw [List.length_cons, show 2 * (vs.length + 1) = 2 + 2 * vs.length by ring,
      readWords_ofNat_add, ih (base + 16)]
    · have := h 0 (by simp); simp at this; simp [this]
    · intro i hi; have := h (i + 1) (by simp; omega)
      rw [show base + 16 + 16 * i = base + 16 * (i + 1) by ring]; simpa using this

/-! ## `writeHash` -/

theorem writeHash_getMem (s : MachineState) (a : BitVec 256) (x : Word) :
    (writeHash s a).getMem x =
      if x = s.getReg .x12 + 8 + 8 + 8 then a.extractLsb' 192 64
      else if x = s.getReg .x12 + 8 + 8 then a.extractLsb' 128 64
      else if x = s.getReg .x12 + 8 then a.extractLsb' 64 64
      else if x = s.getReg .x12 then a.extractLsb' 0 64
      else s.getMem x := by
  simp only [writeHash, MachineState.writeWords, MachineState.getMem, MachineState.setMem,
    MachineState.setPC, beq_iff_eq]

@[simp] theorem writeHash_getReg (s : MachineState) (a : BitVec 256) (r : Reg) :
    (writeHash s a).getReg r = s.getReg r := by
  cases r <;> simp [writeHash, MachineState.writeWords, MachineState.getReg, MachineState.setMem,
    MachineState.setPC]

@[simp] theorem writeHash_pc (s : MachineState) (a : BitVec 256) : (writeHash s a).pc = s.pc + 4 := by
  simp [writeHash, MachineState.writeWords, MachineState.setMem, MachineState.setPC]

/-- Memory after `writeHash` at `x12 = ofNat d` for a numeric address `x`. -/
theorem writeHash_getMem_ofNat (s : MachineState) (a : BitVec 256) (d x : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) (hx : x < 2 ^ 64) :
    (writeHash s a).getMem (BitVec.ofNat 64 x) =
      if x = d + 24 then a.extractLsb' 192 64
      else if x = d + 16 then a.extractLsb' 128 64
      else if x = d + 8 then a.extractLsb' 64 64
      else if x = d then a.extractLsb' 0 64
      else s.getMem (BitVec.ofNat 64 x) := by
  rw [writeHash_getMem, hd]
  have e : ∀ k, k < 2 ^ 64 → (BitVec.ofNat 64 x = BitVec.ofNat 64 k ↔ x = k) := by
    intro k hk
    constructor
    · intro h; have := congrArg BitVec.toNat h; simp at this; omega
    · rintro rfl; rfl
  have h3 : BitVec.ofNat 64 d + 8 + 8 + 8 = BitVec.ofNat 64 (d + 24) := by
    apply BitVec.eq_of_toNat_eq; simp <;> omega
  have h2 : BitVec.ofNat 64 d + 8 + 8 = BitVec.ofNat 64 (d + 16) := by
    apply BitVec.eq_of_toNat_eq; simp <;> omega
  have h1 : BitVec.ofNat 64 d + 8 = BitVec.ofNat 64 (d + 8) := by
    apply BitVec.eq_of_toNat_eq; simp <;> omega
  rw [h3, h2, h1]
  simp only [e _ (by omega : d + 24 < 2 ^ 64), e _ (by omega : d + 16 < 2 ^ 64),
    e _ (by omega : d + 8 < 2 ^ 64), e _ (by omega : d < 2 ^ 64)]

/-- The value written by `writeHash` at `x12 = ofNat d` (a 16-byte slot). -/
theorem writeHash_readWords_val (s : MachineState) (a : BitVec 256) (d : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    (writeHash s a).readWords (BitVec.ofNat 64 d) 2 = wordsOf (answerBytes 16 a) := by
  rw [readWords_ofNat_two, writeHash_getMem_ofNat _ _ _ _ hd hd' (by omega),
    writeHash_getMem_ofNat _ _ _ _ hd hd' (by omega), wordsOf_answerBytes_16]
  simp

/-- `writeHash` does not touch dwords outside `[d, d + 32)` (numeric addresses). -/
theorem writeHash_getMem_frame (s : MachineState) (a : BitVec 256) (d x : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) (hx : x < 2 ^ 64)
    (hout : x < d ∨ d + 32 ≤ x ∨ x % 8 ≠ d % 8) :
    (writeHash s a).getMem (BitVec.ofNat 64 x) = s.getMem (BitVec.ofNat 64 x) := by
  rw [writeHash_getMem_ofNat _ _ _ _ hd hd' hx]
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

end SigGolfCandidate.Sign
