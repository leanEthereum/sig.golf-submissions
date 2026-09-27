import SigGolfCandidate.Verify.Judg

/-!
# Bytes and doublewords

`w64 l` is the little-endian doubleword of (at most 8) bytes, `wordsOfN n l` the first `n`
doublewords of a byte list. The HASH query of a padded input is `queryOfWords` of its words
(`pad64_eq_words`); the word lists of all input formats are computed below.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def w64 (l : List Byte) : Word := BitVec.ofNat 64 (leNat l)

def wordsOfN : Nat → List Byte → List Word
  | 0, _ => []
  | n + 1, l => w64 (l.take 8) :: wordsOfN n (l.drop 8)

theorem leNat_append (a b : List Byte) : leNat (a ++ b) = leNat a + 256 ^ a.length * leNat b := by
  induction a with
  | nil => simp [leNat]
  | cons x xs ih => simp only [List.cons_append, leNat, ih, List.length_cons, Nat.pow_succ]; ring

theorem leNat_zeros (k : Nat) : leNat (zeros k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [zeros, List.replicate_succ, leNat] at ih ⊢; rw [ih]; rfl

theorem w64_toNat (l : List Byte) (h : l.length ≤ 8) : (w64 l).toNat = leNat l := by
  unfold w64
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  have := leNat_lt l
  calc leNat l < 256 ^ l.length := this
    _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by decide) h
    _ = 2 ^ 64 := by norm_num

theorem wordsToNat_wordsOfN : ∀ (n : Nat) (l : List Byte), l.length ≤ 8 * n →
    wordsToNat (wordsOfN n l) = leNat l := by
  intro n
  induction n with
  | zero => intro l h; have : l = [] := List.eq_nil_of_length_eq_zero (by omega); subst this; rfl
  | succ n ih =>
    intro l h
    simp only [wordsOfN, wordsToNat]
    rw [ih _ (by simp; omega), w64_toNat _ (by simp)]
    conv_rhs => rw [← List.take_append_drop 8 l, leNat_append]
    by_cases hl : 8 ≤ l.length
    · rw [List.length_take_of_le hl]; norm_num
    · have : l.drop 8 = [] := List.drop_eq_nil_of_le (by omega)
      rw [this]; simp [leNat]

theorem length_padTo64 (x : List Byte) : (padTo64 x).length = 64 * (padBlocks x.length + 1) := by
  unfold padTo64 padBlocks
  simp only [List.length_append, length_zeros]
  omega

theorem pad64_eq_words (x : List Byte) :
    pad64 x = queryOfWords (padBlocks x.length)
      (wordsOfN (8 * (padBlocks x.length + 1)) (padTo64 x)) := by
  unfold pad64 queryOfWords ofList
  rw [wordsToNat_wordsOfN _ _ (by rw [length_padTo64]; omega)]

theorem wordsOfN_append : ∀ (a b : Nat) (l1 l2 : List Byte), l1.length = 8 * a →
    wordsOfN (a + b) (l1 ++ l2) = wordsOfN a l1 ++ wordsOfN b l2 := by
  intro a
  induction a with
  | zero => intro b l1 l2 h; have : l1 = [] := List.eq_nil_of_length_eq_zero (by omega); subst this; simp [wordsOfN]
  | succ a ih =>
    intro b l1 l2 h
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [wordsOfN, List.cons_append]
    rw [List.take_append_of_le_length (by omega), List.drop_append_of_le_length (by omega),
      ih _ _ _ (by simp; omega)]

theorem wordsOfN_zeros : ∀ (n : Nat), wordsOfN n (zeros (8 * n)) = List.replicate n 0 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [wordsOfN, List.replicate_succ]
    rw [show 8 * (n + 1) = 8 + 8 * n by omega]
    have h1 : (zeros (8 + 8 * n)).take 8 = zeros 8 := by simp [zeros, List.take_replicate]
    have h2 : (zeros (8 + 8 * n)).drop 8 = zeros (8 * n) := by simp [zeros, List.drop_replicate]
    rw [h1, h2, ih]
    rfl

/-! ## Tweak words -/

def twLo (t lay tau p : Nat) : Nat :=
  1 + 256 * (t % 256) + 65536 * (lay % 256) + 2 ^ 24 * (tau / 2 ^ 32 % 256) + 2 ^ 32 * (p % 2 ^ 32)

def twHi (tau j : Nat) : Nat := tau % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32)

theorem leNat_le32 (v : Nat) : leNat (le32 v) = v % 2 ^ 32 := by
  have := leNat_map_range 4 v
  simpa [le32, leBytes] using this

theorem wordsOfN_tweak (t lay tau p j : Nat) :
    wordsOfN 2 (tweak t lay tau p j) =
      [BitVec.ofNat 64 (twLo t lay tau p), BitVec.ofNat 64 (twHi tau j)] := by
  unfold tweak
  have e1 : [byte 1, byte t, byte lay, byte (tau / 2 ^ 32)] ++ le32 p ++ le32 (tau % 2 ^ 32) ++
      le32 j = ([byte 1, byte t, byte lay, byte (tau / 2 ^ 32)] ++ le32 p) ++
        (le32 (tau % 2 ^ 32) ++ le32 j) := by simp
  rw [e1, show (2 : Nat) = 1 + 1 from rfl, wordsOfN_append 1 1 _ _ (by simp)]
  simp only [wordsOfN, List.cons_append, List.nil_append]
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)]
  simp only [w64, leNat_append, leNat, leNat_le32, byte_toNat, length_le32, twLo, twHi,
    List.length_cons, List.length_nil]
  refine congrArg₂ _ (congrArg _ ?_) (congrArg₂ _ (congrArg _ ?_) rfl) <;> omega

/-! ## Values -/

def vw0 (v : Val) : Word := w64 (v.take 8)
def vw1 (v : Val) : Word := w64 (v.drop 8)

theorem wordsOfN_val_append (v : Val) (hv : v.length = 16) (k : Nat) (l : List Byte) :
    wordsOfN (2 + k) (v ++ l) = [vw0 v, vw1 v] ++ wordsOfN k l := by
  rw [wordsOfN_append 2 k v l (by omega)]
  simp only [wordsOfN, vw0, vw1, List.drop_drop]
  rw [List.take_of_length_le (l := v.drop 8) (by simp; omega)]

theorem wordsOfN_flatten_append : ∀ (vs : List Val), (∀ v ∈ vs, v.length = 16) →
    ∀ (k : Nat) (l : List Byte),
    wordsOfN (2 * vs.length + k) (vs.flatten ++ l) =
      (vs.map fun v => [vw0 v, vw1 v]).flatten ++ wordsOfN k l := by
  intro vs
  induction vs with
  | nil => intro _ k l; simp
  | cons v vs ih =>
    intro h k l
    simp only [List.length_cons, List.flatten_cons, List.map_cons, List.append_assoc]
    rw [show 2 * (vs.length + 1) + k = 2 + (2 * vs.length + k) by omega,
      wordsOfN_val_append v (h v (List.mem_cons_self ..)),
      ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]

theorem padBlocks_val (len n : Nat) (h1 : len ≤ 64 * (n + 1)) (h2 : 64 * n < len) :
    padBlocks len = n := by unfold padBlocks; omega

/-- The query of `thInput tw payload` (a 16-byte tweak) of `n + 1` blocks. -/
theorem pad64_thInput (tw payload : List Byte) (htw : tw.length = 16) (n : Nat)
    (h1 : 32 + payload.length ≤ 64 * (n + 1)) (h2 : 64 * n < 32 + payload.length) :
    pad64 (thInput tw payload) = queryOfWords n (wordsOfN 2 tw ++ [0, 0] ++
      wordsOfN (8 * n + 4) (payload ++ zeros (64 * (n + 1) - (32 + payload.length)))) := by
  have hl : (thInput tw payload).length = 32 + payload.length := by
    simp [thInput, htw]; omega
  rw [pad64_eq_words, hl, padBlocks_val _ _ h1 h2]
  unfold padTo64
  rw [hl, padBlocks_val _ _ h1 h2]
  unfold thInput
  rw [show 8 * (n + 1) = 2 + (2 + (8 * n + 4)) by omega, List.append_assoc, List.append_assoc,
    wordsOfN_append 2 _ tw _ (by omega), wordsOfN_append 2 _ P _ (by rfl)]
  rfl

theorem w64_zeros8 : w64 (zeros 8) = 0 := rfl

theorem wordsOfN_zeros' (n : Nat) : wordsOfN n (zeros (8 * n)) = List.replicate n 0 :=
  wordsOfN_zeros n

/-! ## Input formats -/

theorem pad64_chainInput (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16) :
    pad64 (chainInput lay tau e i mu v) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 1 lay tau (8 * i + mu - 1)), BitVec.ofNat 64 (twHi tau e), 0, 0,
        vw0 v, vw1 v, 0, 0] := by
  unfold chainInput
  rw [pad64_thInput _ _ (by simp) 0 (by omega) (by omega), wordsOfN_tweak, hv,
    show 8 * 0 + 4 = 2 + 2 by rfl, wordsOfN_val_append v hv]
  rfl

theorem pad64_ftsLeafInput (k idx j : Nat) (v : Val) (hv : v.length = 16) :
    pad64 (ftsLeafInput k idx j v) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 9 k idx 0), BitVec.ofNat 64 (twHi idx j), 0, 0,
        vw0 v, vw1 v, 0, 0] := by
  unfold ftsLeafInput
  rw [pad64_thInput _ _ (by simp) 0 (by omega) (by omega), wordsOfN_tweak, hv,
    show 8 * 0 + 4 = 2 + 2 by rfl, wordsOfN_val_append v hv]
  rfl

theorem pad64_nodeInput (lay tau lam j : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) :
    pad64 (nodeInput lay tau lam j l r) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 3 lay tau lam), BitVec.ofNat 64 (twHi tau j), 0, 0,
        vw0 l, vw1 l, vw0 r, vw1 r] := by
  unfold nodeInput
  rw [pad64_thInput _ _ (by simp) 0 (by simp [hl, hr]) (by simp [hl, hr]), wordsOfN_tweak]
  simp only [List.length_append, hl, hr]
  rw [show 8 * 0 + 4 = 2 + (2 + 0) by rfl, List.append_assoc l r, wordsOfN_val_append l hl,
    wordsOfN_val_append r hr]
  rfl

theorem pad64_ftsNodeInput (k idx lam j : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) :
    pad64 (ftsNodeInput k idx lam j l r) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 10 k idx lam), BitVec.ofNat 64 (twHi idx j), 0, 0,
        vw0 l, vw1 l, vw0 r, vw1 r] := by
  unfold ftsNodeInput
  rw [pad64_thInput _ _ (by simp) 0 (by simp [hl, hr]) (by simp [hl, hr]), wordsOfN_tweak]
  simp only [List.length_append, hl, hr]
  rw [show 8 * 0 + 4 = 2 + (2 + 0) by rfl, List.append_assoc l r, wordsOfN_val_append l hl,
    wordsOfN_val_append r hr]
  rfl

theorem pad64_encInput (lay tau e : Nat) (M : Val) (hM : M.length = 16) (c : Nat) :
    pad64 (encInput lay tau e M c) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 4 lay tau 0), BitVec.ofNat 64 (twHi tau e), 0, 0,
        vw0 M, vw1 M, BitVec.ofNat 64 (c % 2 ^ 32), 0] := by
  unfold encInput
  rw [pad64_thInput _ _ (by simp) 0 (by simp [hM]) (by simp [hM]), wordsOfN_tweak]
  simp only [List.length_append, hM, length_le32]
  rw [show 8 * 0 + 4 = 2 + 2 by rfl, List.append_assoc M, wordsOfN_val_append M hM]
  simp only [wordsOfN]
  have h1 : (le32 c ++ zeros (64 * (0 + 1) - (32 + (16 + 4)))).take 8 = le32 c ++ zeros 4 := by
    simp [zeros, List.take_append]
  have h2 : ((le32 c ++ zeros (64 * (0 + 1) - (32 + (16 + 4)))).drop 8).take 8 = zeros 8 := by
    rw [List.drop_append, List.drop_eq_nil_of_le (by simp : (le32 c).length ≤ 8)]
    simp [zeros, List.take_replicate]
  rw [h1, h2]
  simp only [w64, leNat_append, leNat_le32, leNat_zeros, Nat.mul_zero, Nat.add_zero]
  rfl

theorem pad64_leafInput (lay tau e : Nat) (ends : List Val) (hl : ends.length = 42)
    (hv : ∀ v ∈ ends, v.length = 16) :
    pad64 (leafInput lay tau e ends) = queryOfWords 10
      ([BitVec.ofNat 64 (twLo 2 lay tau 0), BitVec.ofNat 64 (twHi tau e), 0, 0] ++
        (ends.map fun v => [vw0 v, vw1 v]).flatten) := by
  have hflat : ends.flatten.length = 672 := by
    rw [List.length_flatten]
    have : ends.map List.length = List.replicate 42 16 := by
      apply List.ext_getElem (by simp [hl])
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_replicate]
      exact hv _ (List.getElem_mem _)
    rw [this]; decide
  unfold leafInput
  rw [pad64_thInput _ _ (by simp) 10 (by omega) (by omega), wordsOfN_tweak, hflat,
    show 8 * 10 + 4 = 2 * ends.length + 0 by omega, wordsOfN_flatten_append ends hv]
  simp [wordsOfN]

theorem pad64_rootsInput (idx : Nat) (roots : List Val) (hl : roots.length = 14)
    (hv : ∀ v ∈ roots, v.length = 16) :
    pad64 (rootsInput idx roots) = queryOfWords 3
      ([BitVec.ofNat 64 (twLo 11 0 idx 0), BitVec.ofNat 64 (twHi idx 0), 0, 0] ++
        (roots.map fun v => [vw0 v, vw1 v]).flatten) := by
  have hflat : roots.flatten.length = 224 := by
    rw [List.length_flatten]
    have : roots.map List.length = List.replicate 14 16 := by
      apply List.ext_getElem (by simp [hl])
      intro i h1 h2
      simp only [List.getElem_map, List.getElem_replicate]
      exact hv _ (List.getElem_mem _)
    rw [this]; decide
  unfold rootsInput
  rw [pad64_thInput _ _ (by simp) 3 (by omega) (by omega), wordsOfN_tweak, hflat,
    show 8 * 3 + 4 = 2 * roots.length + 0 by omega, wordsOfN_flatten_append roots hv]
  simp [wordsOfN]

theorem pad64_digestInput (rho m : List Byte) (hr : rho.length = 16) (hm : m.length = 32) :
    pad64 (digestInput rho m) = queryOfWords 1
      ([BitVec.ofNat 64 (twLo 12 0 0 0), BitVec.ofNat 64 (twHi 0 0), 0, 0, vw0 rho, vw1 rho, 0, 0] ++
        wordsOfN 4 m ++ [0, 0, 0, 0]) := by
  unfold digestInput
  rw [pad64_thInput _ _ (by simp) 1 (by simp [hr, hm]) (by simp [hr, hm]), wordsOfN_tweak]
  simp only [List.length_append, hr, hm, length_zeros]
  simp only [List.append_assoc]
  rw [show 8 * 1 + 4 = 2 + (2 + (4 + 4)) by rfl, wordsOfN_val_append rho hr,
    wordsOfN_append 2 _ (zeros 16) _ (by rfl),
    wordsOfN_append 4 4 m _ (by omega), show 64 * (1 + 1) - (32 + (16 + 16 + 32)) = 8 * 4 by rfl,
    wordsOfN_zeros, wordsOfN_zeros 4]
  simp

/-! ## Answers -/

theorem extractLsb'_byte (a : BitVec 256) (i : Nat) (hi : i < 32) :
    a.extractLsb' (8 * i) 8 = byte (a.toNat / 256 ^ i) := by
  have := extractByte_ofNat 256 a.toNat i (by omega)
  rwa [BitVec.ofNat_toNat, BitVec.setWidth_eq] at this

theorem answerBytes_eq (a : BitVec 256) :
    answerBytes 16 a = (List.range 16).map fun i => byte (a.toNat / 256 ^ i) :=
  List.map_congr_left (fun i hi => extractLsb'_byte a i (by simp at hi; omega))

theorem vw0_answer (a : BitVec 256) : vw0 (answerBytes 16 a) = a.extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  unfold vw0
  rw [w64_toNat _ (by simp), BitVec.extractLsb'_toNat, Nat.shiftRight_zero, answerBytes_eq,
    ← List.map_take, List.take_range, show min 8 16 = 8 by rfl, leNat_map_range]
  rfl

theorem vw1_answer (a : BitVec 256) : vw1 (answerBytes 16 a) = a.extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  unfold vw1
  rw [w64_toNat _ (by simp), BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, answerBytes_eq,
    ← List.map_drop, List.range_eq_range', List.drop_range', List.range'_eq_map_range, List.map_map]
  have : ((fun i => byte (a.toNat / 256 ^ i)) ∘ fun i => 0 + 8 + i) =
      fun i => byte (a.toNat / 2 ^ 64 / 256 ^ i) := by
    funext i; simp only [Function.comp, Nat.zero_add, Nat.pow_add, Nat.div_div_eq_div_mul]
    norm_num
  rw [show 16 - 8 = 8 by rfl, this, leNat_map_range]
  norm_num

theorem length_answerBytes16 (a : BitVec 256) : (answerBytes 16 a).length = 16 := by simp

end SigGolfCandidate.Verify
