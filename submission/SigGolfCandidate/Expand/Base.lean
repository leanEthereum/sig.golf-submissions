import SigGolfCandidate.Ref
import SigGolfCandidate.Rv

/-!
# Generic helpers for the expand proof (local copies of `Sign/Base`, `Sign/Inv`, `Sign/Words`)

Duplicated from the sign proof (namespace `Expand`, tactic names `ex_*`) so that this directory
depends only on `Rv` and `Ref`: `kernel_theorem`-style relocatable blocks, `pcOf`, `BitVec.ofNat`
arithmetic, `Frame` / `RegsEq`, `wordsOf`, `readWords` and `writeHash` lemmas, and the HASH input
of the one-block digest.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Expand
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

open Lean Elab Command Meta in
/-- `kernel_theorem name : ∀ xs, lhs = rhs` — proof `fun xs => Eq.refl lhs`, checked by the
kernel only. -/
elab "ex_kernel_theorem " id:ident " : " t:term : command => do
  liftTermElabM do
    let ty ← Term.elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    if ty.hasMVar then throwError "kernel_theorem: statement has metavariables"
    let pf ← forallTelescope ty fun xs body => do
      let some (_, lhs, _) := body.eq? | throwError "kernel_theorem: not an equation"
      mkLambdaFVars xs (← mkEqRefl lhs)
    let base := (← getCurrNamespace) ++ id.getId
    addDecl <| Declaration.thmDecl { name := base, levelParams := [], type := ty, value := pf }

/-- The executor's pc after `n` instructions from `pc`. -/
def addN (pc : Word) : Nat → Word
  | 0 => pc
  | n + 1 => addN (pc + 4) n

/-- `pc` of instruction index `i` (image code starts at `0x1000`). -/
abbrev pcOf (i : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * i)

theorem addN_ofNat (a n : Nat) : addN (BitVec.ofNat 64 a) n = BitVec.ofNat 64 (a + 4 * n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [addN, show BitVec.ofNat 64 a + 4 = BitVec.ofNat 64 (a + 4) from by
      apply BitVec.eq_of_toNat_eq; simp <;> omega, ih]
    congr 1; ring

theorem addN_pcOf (i n : Nat) : addN (pcOf i) n = pcOf (i + n) := by
  rw [addN_ofNat]; congr 1; ring

/-- Replace the two constant targets of a branch pc. -/
def retarget : E → Word → Word → E
  | .ite op x y _ _, a, b => .ite op x y (.c a) (.c b)
  | e, _, _ => e

/-! ## `BitVec.ofNat 64` arithmetic as `Nat` arithmetic -/

theorem ofNat_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_sub_ofNat (a b : Nat) (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

theorem ofNat_shiftLeft (a k : Nat) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]

theorem ofNat_ushiftRight (a k : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt ha]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem ofNat_and_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 b = BitVec.ofNat 64 (a &&& b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left ha)]

theorem ofNat_or_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (a ||| b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)]

theorem ofNat_xor_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = BitVec.ofNat 64 (a ^^^ b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)]

theorem ofNat_eq_iff (a b : Nat) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a % 2 ^ 64 = b % 2 ^ 64 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa using this
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

theorem accessValid_ofNat (a w : Nat) :
    accessValid (BitVec.ofNat 64 a) w = true ↔ a % 2 ^ 64 + w ≤ 2 ^ 24 ∧ a % 2 ^ 64 % w = 0 := by
  simp [accessValid, rangeValid, MEMORY_BYTES]

theorem toNat_ofNat_64 (a : Nat) : (BitVec.ofNat 64 a).toNat = a % 2 ^ 64 := by simp

theorem ofNat_beq_ofNat (a b : Nat) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a % 2 ^ 64 = b % 2 ^ 64) :=
  Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, ofNat_eq_iff, decide_eq_true_eq])

theorem ofNat_bne_ofNat (a b : Nat) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = !decide (a % 2 ^ 64 = b % 2 ^ 64) := by
  rw [bne, ofNat_beq_ofNat]

/-- Signed comparison of small numbers. -/
theorem ofNat_slt_ofNat (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.slt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [BitVec.slt_eq_ult_of_msb_eq]
  · simp [BitVec.ult]; omega
  · simp [BitVec.msb_eq_decide, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]; omega

/-- First tweak dword (independent of `j`). -/
def twWord0 (t lay tau p : Nat) : Word :=
  BitVec.ofNat 64 (1 + 256 * (t % 256) + 65536 * (lay % 256) + 2 ^ 24 * (tau / 2 ^ 32 % 256) +
    2 ^ 32 * (p % 2 ^ 32))

theorem twWords_eq (t lay tau p j : Nat) :
    twWords t lay tau p j = [twWord0 t lay tau p, BitVec.ofNat 64 (tau % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32))] :=
  rfl

/-! ## 32-bit halves of dwords (`SW` merges) -/

/-- Low / high 32-bit half of a dword. -/
abbrev lo32 (w : Word) : BitVec 32 := w.extractLsb' 0 32
abbrev hi32 (w : Word) : BitVec 32 := w.extractLsb' 32 32

@[simp] theorem lo32_replace0 (w : Word) (v : BitVec 32) : lo32 (replaceWord32 w 0 v) = v := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp
@[simp] theorem hi32_replace0 (w : Word) (v : BitVec 32) : hi32 (replaceWord32 w 0 v) = hi32 w := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp
@[simp] theorem lo32_replace1 (w : Word) (v : BitVec 32) : lo32 (replaceWord32 w 1 v) = lo32 w := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp
@[simp] theorem hi32_replace1 (w : Word) (v : BitVec 32) : hi32 (replaceWord32 w 1 v) = v := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp

/-- A dword from its halves. -/
theorem word_of_halves (w : Word) (a b : Nat) (hlo : lo32 w = BitVec.ofNat 32 a)
    (hhi : hi32 w = BitVec.ofNat 32 b) : w = BitVec.ofNat 64 (a % 2 ^ 32 + 2 ^ 32 * (b % 2 ^ 32)) := by
  have h1 := congrArg BitVec.toNat hlo
  have h2 := congrArg BitVec.toNat hhi
  simp only [lo32, hi32, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at h1 h2
  apply BitVec.eq_of_toNat_eq
  have := w.isLt
  simp only [BitVec.toNat_ofNat]
  omega

@[simp] theorem lo32_ofNat (n : Nat) : lo32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo32, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

@[simp] theorem hi32_ofNat (n : Nat) : hi32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 (n / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [hi32, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

@[simp] theorem truncate32_ofNat (n : Nat) : (BitVec.ofNat 64 n).truncate 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp <;> omega

end SigGolfCandidate.Expand

namespace SigGolfCandidate.Expand
/-- `rvs [hs]` : `rv_simp` plus constant folding, `ite` on `True/False`, and the `ofNat`
normalizations. -/
macro "ex_rvs" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp only [rv_simp, ite_true, ite_false, if_true, if_false, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, truncate32_ofNat, BitVec.toNat_ofNat,
      ofNat_add_ofNat, ofNat_shiftLeft, $ts',*])
end SigGolfCandidate.Expand

namespace SigGolfCandidate.Expand
/-- `omega` after removing `% 2^64` of in-range terms (omega is incomplete with the huge
coefficients those produce). -/
macro "ex_bvomega" : tactic =>
  `(tactic| ((try simp (disch := omega) only [Nat.reducePow, Nat.mod_eq_of_lt]); omega))
end SigGolfCandidate.Expand

namespace SigGolfCandidate.Expand
open RiscvZkvm.Rv64

/-- OR of values with disjoint bit ranges is addition. -/
theorem ofNat_or_disjoint (x b i : Nat) (hx : x % 2 ^ i = 0) (hb : b < 2 ^ i) (h : x + b < 2 ^ 64) :
    BitVec.ofNat 64 x ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (x + b) := by
  rw [ofNat_or_ofNat _ _ (by omega) (by omega)]
  congr 1
  obtain ⟨q, rfl⟩ : ∃ q, x = 2 ^ i * q := ⟨x / 2 ^ i, by rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hx)]⟩
  rw [Nat.two_pow_add_eq_or_of_lt hb]

theorem ofNat_or_disjoint' (x b i : Nat) (hx : x % 2 ^ i = 0) (hb : b < 2 ^ i) (h : x + b < 2 ^ 64) :
    BitVec.ofNat 64 b ||| BitVec.ofNat 64 x = BitVec.ofNat 64 (x + b) := by
  rw [BitVec.or_comm, ofNat_or_disjoint x b i hx hb h]
end SigGolfCandidate.Expand

namespace SigGolfCandidate.Expand
/-- `BitVec.ofNat 64` arithmetic → `Nat` arithmetic, side conditions by `omega`. Run after
`simp only [blk.res, rv_simp]` (whose `addNegLit` turns `x + (-c)` into `x - c`). -/
macro "ex_bvsimp" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp (disch := omega) only [ofNat_add_ofNat, ofNat_sub_ofNat, ofNat_shiftLeft,
      ofNat_ushiftRight, ofNat_and_ofNat, ofNat_xor_ofNat, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, truncate32_ofNat,
      ite_true, ite_false, if_true, if_false, BitVec.ofNat_eq_ofNat, Nat.add_sub_cancel,
      Nat.mod_eq_of_lt, Nat.reduceEqDiff, reduceIte, and_true, true_and, or_false, false_or, not_false_eq_true, $ts',*])
end SigGolfCandidate.Expand

namespace SigGolfCandidate.Expand
theorem bne_cond (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((!decide (a % 2 ^ 64 = b % 2 ^ 64)) = true) ↔ a ≠ b := by
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; simp
end SigGolfCandidate.Expand

namespace SigGolfCandidate.Expand
theorem ofNat_congr {a b : Nat} (h : a = b) : BitVec.ofNat 64 a = BitVec.ofNat 64 b := h ▸ rfl

open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def Frame (s t : MachineState) (W : Nat → Prop) : Prop :=
  ∀ a, a < 2 ^ 64 → ¬ W a → t.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)

theorem Frame.refl (s : MachineState) (W : Nat → Prop) : Frame s s W := fun _ _ _ => rfl

theorem Frame.trans {s t u : MachineState} {W₁ W₂ : Nat → Prop} (h₁ : Frame s t W₁)
    (h₂ : Frame t u W₂) : Frame s u (fun a => W₁ a ∨ W₂ a) := by
  intro a ha hW
  rw [h₂ a ha (fun h => hW (Or.inr h)), h₁ a ha (fun h => hW (Or.inl h))]

theorem Frame.mono {s t : MachineState} {W W' : Nat → Prop} (h : Frame s t W)
    (hW : ∀ a, W a → W' a) : Frame s t W' :=
  fun a ha hna => h a ha (fun h' => hna (hW a h'))

theorem Frame.trans' {s t u : MachineState} {W₁ W₂ W : Nat → Prop} (h₁ : Frame s t W₁)
    (h₂ : Frame t u W₂) (hW : ∀ a, W₁ a ∨ W₂ a → W a) : Frame s u W :=
  (h₁.trans h₂).mono hW

theorem Frame.getMem {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) {a : Nat}
    (ha : a < 2 ^ 64) (hW : ¬ W a) : t.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a) :=
  h a ha hW

theorem Frame.readWords {s t : MachineState} {W : Nat → Prop} (h : Frame s t W) (a n : Nat)
    (ha : a + 8 * n < 2 ^ 64) (hW : ∀ i < n, ¬ W (a + 8 * i)) :
    t.readWords (BitVec.ofNat 64 a) n = s.readWords (BitVec.ofNat 64 a) n :=
  readWords_congr s t a n (fun i hi => h _ (by omega) (hW i hi))

theorem frame_writeHash (s : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 32 < 2 ^ 64) :
    Frame s (writeHash s ans) (fun a => d ≤ a ∧ a < d + 32) := by
  intro a ha hW
  exact writeHash_getMem_frame s ans d a hd hd' ha (by omega)

/-- Frame of a block result from a proof that no written key equals an address outside `W`. -/
theorem frame_toState (r : Result) (s : MachineState) (W : Nat → Prop)
    (h : ∀ a, a < 2 ^ 64 → ¬ W a → ∀ p ∈ r.st.mem, BitVec.ofNat 64 a ≠ p.1.eval s) :
    Frame s (r.toState s) W := by
  intro a ha hW
  rw [Result.toState_getMem]
  exact memEval_frame s r.st.mem _ (h a ha hW)

def RegsEq (s t : MachineState) (l : List Reg) : Prop := ∀ r, r ∉ l → t.getReg r = s.getReg r

theorem RegsEq.refl (s : MachineState) (l : List Reg) : RegsEq s s l := fun _ _ => rfl

theorem RegsEq.trans {s t u : MachineState} {l₁ l₂ : List Reg} (h₁ : RegsEq s t l₁)
    (h₂ : RegsEq t u l₂) : RegsEq s u (l₁ ++ l₂) := by
  intro r hr
  rw [h₂ r (fun h => hr (List.mem_append_right _ h)), h₁ r (fun h => hr (List.mem_append_left _ h))]

theorem RegsEq.mono {s t : MachineState} {l l' : List Reg} (h : RegsEq s t l) (hl : ∀ r ∈ l, r ∈ l') :
    RegsEq s t l' := fun r hr => h r (fun h' => hr (hl r h'))

theorem RegsEq.trans' {s t u : MachineState} {l₁ l₂ l : List Reg} (h₁ : RegsEq s t l₁)
    (h₂ : RegsEq t u l₂) (hl : ∀ r, r ∈ l₁ ∨ r ∈ l₂ → r ∈ l) : RegsEq s u l :=
  (h₁.trans h₂).mono (fun r hr => hl r (List.mem_append.mp hr))

theorem RegsEq.get {s t : MachineState} {l : List Reg} (h : RegsEq s t l) (r : Reg)
    (hr : r ∉ l := by decide) : t.getReg r = s.getReg r := h r hr

theorem regsEq_writeHash (s : MachineState) (ans : BitVec 256) (l : List Reg) :
    RegsEq s (writeHash s ans) l := fun r _ => writeHash_getReg s ans r

/-- Registers of a block result: all registers whose symbolic value is `.reg r` are unchanged. -/
theorem regsEq_toState (r : Result) (s : MachineState) (l : List Reg)
    (h : ∀ x : Reg, x ∉ l → (r.st.regs.get x).eval s = s.getReg x) : RegsEq s (r.toState s) l := by
  intro x hx
  rw [Result.toState_getReg]
  exact h x hx

theorem getReg_x0 (s : MachineState) : s.getReg .x0 = 0 := rfl

/-! ## Arrays of 16-byte values -/

/-- `vs[i]` is stored at `B + 16 i`. -/
def Slots (t : MachineState) (B : Nat) (vs : List Val) : Prop :=
  ∀ i (hi : i < vs.length), t.readWords (BitVec.ofNat 64 (B + 16 * i)) 2 = wordsOf vs[i]

theorem Slots.nil (t : MachineState) (B : Nat) : Slots t B [] := fun i hi => by simp at hi

theorem Slots.snoc {t : MachineState} {B : Nat} {vs : List Val} {v : Val} (h : Slots t B vs)
    (hv : t.readWords (BitVec.ofNat 64 (B + 16 * vs.length)) 2 = wordsOf v) : Slots t B (vs ++ [v]) := by
  intro i hi
  simp only [List.length_append, List.length_singleton] at hi
  by_cases h' : i < vs.length
  · rw [List.getElem_append_left h']; exact h i h'
  · have : i = vs.length := by omega
    subst this
    rw [List.getElem_append_right (le_refl _)]; simpa using hv

theorem Slots.frame {s t : MachineState} {W : Nat → Prop} {B : Nat} {vs : List Val}
    (h : Slots s B vs) (hf : Frame s t W) (hB : B + 16 * vs.length + 16 < 2 ^ 64)
    (hW : ∀ i < vs.length, ¬ W (B + 16 * i) ∧ ¬ W (B + 16 * i + 8)) : Slots t B vs := by
  intro i hi
  rw [hf.readWords _ _ (by omega) (by
    intro j hj
    have := hW i hi
    interval_cases j
    · simpa using this.1
    · simpa using this.2)]
  exact h i hi

theorem Slots.getD {t : MachineState} {B : Nat} {vs : List Val} (h : Slots t B vs) (i : Nat)
    (hi : i < vs.length) :
    t.readWords (BitVec.ofNat 64 (B + 16 * i)) 2 = wordsOf (vs.getD i []) := by
  rw [h i hi]; simp [List.getD, List.getElem?_eq_getElem hi]

theorem Slots.append {t : MachineState} {B : Nat} {l1 l2 : List Val} (h1 : Slots t B l1)
    (h2 : Slots t (B + 16 * l1.length) l2) : Slots t B (l1 ++ l2) := by
  intro i hi
  by_cases h : i < l1.length
  · rw [List.getElem_append_left h]; exact h1 i h
  · rw [List.getElem_append_right (by omega)]
    have := h2 (i - l1.length) (by simp at hi; omega)
    rw [show B + 16 * l1.length + 16 * (i - l1.length) = B + 16 * i by omega] at this
    exact this

theorem Slots.cons {t : MachineState} {B : Nat} {v : Val} {vs : List Val}
    (h1 : t.readWords (BitVec.ofNat 64 B) 2 = wordsOf v) (h2 : Slots t (B + 16) vs) :
    Slots t B (v :: vs) := by
  intro i hi
  cases i with
  | zero => simpa using h1
  | succ i =>
    have := h2 i (by simpa using hi)
    rw [show B + 16 * (i + 1) = B + 16 + 16 * i by ring]; simpa using this

end SigGolfCandidate.Expand
