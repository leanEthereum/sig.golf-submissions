import SigGolfCandidate.Expand.Mem

/-!
# Doubleword-level lemmas for `keygen`

* `rw32_one_toNat`, `rw32_zero_low` : the `SW` merges.
* `leNat_append`, `leNat_zeros`, `leNat_tweak0`, `leNat_val` : the input formats as numbers.
* `readWords_add`, `wordsToNat_append`, `wordsToNat_vals` : buffers of 16-byte values.
* `hashInput_eq_pad64` : a HASH input is `pad64 x` when the buffer's words encode `x`.
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## Sub-doubleword merges -/

theorem rw32_one_toNat (x : Word) (v : BitVec 32) :
    (replaceWord32 x 1 v).toNat = x.toNat % 2 ^ 32 + 2 ^ 32 * v.toNat := by
  have hmask : (~~~(0xFFFFFFFF#64 <<< (1 * 32))) = 0xFFFFFFFF#64 := by decide
  simp only [replaceWord32, hmask, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_shiftLeft]
  have hv := v.isLt
  have h1 : x.toNat &&& (0xFFFFFFFF#64).toNat = x.toNat % 2 ^ 32 := by
    rw [show (0xFFFFFFFF#64).toNat = 2 ^ 32 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  have h2 : (v.setWidth 64).toNat <<< (1 * 32) % 2 ^ 64 = v.toNat <<< 32 := by
    rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (by omega : v.toNat < 2 ^ 64), Nat.mod_eq_of_lt]
    rw [Nat.shiftLeft_eq]; omega
  rw [h1, h2, Nat.or_comm, ← Nat.shiftLeft_add_eq_or_of_lt (Nat.mod_lt _ (by decide)),
    Nat.shiftLeft_eq]
  ring

theorem rw32_zero_low (x : Word) (v : BitVec 32) :
    (replaceWord32 x 0 v).toNat % 2 ^ 32 = v.toNat := by
  have : (replaceWord32 x 0 v).truncate 32 = v := by
    ext i hi; simp only [replaceWord32]; interval_cases i <;> simp
  have h2 := congrArg BitVec.toNat this
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth] at h2
  exact h2

theorem rw32_zero_low' (x : Word) (v : BitVec 32) :
    (replaceWord32 x 0 v).toNat % 4294967296 = v.toNat := rw32_zero_low x v

theorem rw32_one_toNat' (x : Word) (v : BitVec 32) :
    (replaceWord32 x 1 v).toNat = x.toNat % 4294967296 + 4294967296 * v.toNat := rw32_one_toNat x v

theorem truncate32_toNat (x : Word) : (x.truncate 32).toNat = x.toNat % 2 ^ 32 := by
  rw [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]

/-! ## Byte lists as numbers -/

theorem leNat_append (l₁ l₂ : List Byte) :
    leNat (l₁ ++ l₂) = leNat l₁ + 2 ^ (8 * l₁.length) * leNat l₂ := by
  induction l₁ with
  | nil => simp [leNat]
  | cons b bs ih =>
    simp only [List.cons_append, leNat, ih, List.length_cons]
    rw [show 8 * (bs.length + 1) = 8 + 8 * bs.length by ring, Nat.pow_add]
    ring

@[simp] theorem leNat_zeros (k : Nat) : leNat (zeros k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [zeros, List.replicate_succ, leNat] at ih ⊢; exact ih

theorem leNat_le32 (v : Nat) : leNat (le32 v) = v % 2 ^ 32 := by
  rw [le32, leBytes, leNat_map_range]; norm_num

/-- A tweak with `tau = 0`, small `t` and `lay`. -/
theorem leNat_tweak0 (t lay p j : Nat) (ht : t < 256) (hl : lay < 256) :
    leNat (tweak t lay 0 p j) =
      (1 + 256 * t + 2 ^ 16 * lay + 2 ^ 32 * (p % 2 ^ 32)) + 2 ^ 64 * (2 ^ 32 * (j % 2 ^ 32)) := by
  simp only [tweak, leNat_append, leNat_le32, List.length_append, List.length_cons,
    List.length_nil, length_le32]
  simp only [leNat, byte_toNat]
  simp
  omega

/-- The two words of a 16-byte value. -/
def lo (v : Val) : Word := BitVec.ofNat 64 (leNat v)
def hi (v : Val) : Word := BitVec.ofNat 64 (leNat v / 2 ^ 64)

theorem leNat_val (v : Val) (hv : v.length = 16) :
    leNat v = (lo v).toNat + 2 ^ 64 * (hi v).toNat := by
  have := leNat_lt v
  rw [hv] at this
  norm_num at this
  simp only [lo, hi, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := leNat v / 2 ^ 64) (by omega)]
  omega

/-- `v` is stored at `A`, `A + 8`. -/
def ValAt (t : MachineState) (A : Nat) (v : Val) : Prop :=
  t.getMem (BitVec.ofNat 64 A) = lo v ∧ t.getMem (BitVec.ofNat 64 (A + 8)) = hi v

theorem answerBytes_eq (k : Nat) (a : BitVec 256) :
    answerBytes k a = (List.range k).map fun i => byte (a.toNat / 256 ^ i) := by
  unfold answerBytes
  apply List.map_congr_left
  intro i _
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, byte, BitVec.toNat_ofNat]
  rw [Nat.shiftRight_eq_div_pow, show 256 ^ i = 2 ^ (8 * i) by rw [Nat.pow_mul]]

theorem leNat_answer (k : Nat) (a : BitVec 256) : leNat (answerBytes k a) = a.toNat % 256 ^ k := by
  rw [answerBytes_eq, leNat_map_range]

@[simp] theorem length_answer16 (a : BitVec 256) : (answerBytes 16 a).length = 16 := by simp

theorem lo_answer (a : BitVec 256) : lo (answerBytes 16 a) = a.extractLsb' 0 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, leNat_answer]
  norm_num

theorem hi_answer (a : BitVec 256) : hi (answerBytes 16 a) = a.extractLsb' 64 64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [hi, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat, leNat_answer, Nat.shiftRight_eq_div_pow]
  norm_num
  omega

/-! ## Buffers -/

theorem wordsToNat_append (l₁ l₂ : List Word) :
    wordsToNat (l₁ ++ l₂) = wordsToNat l₁ + 2 ^ (64 * l₁.length) * wordsToNat l₂ := by
  induction l₁ with
  | nil => simp [wordsToNat]
  | cons w ws ih =>
    simp only [List.cons_append, wordsToNat, ih, List.length_cons]
    rw [show 64 * (ws.length + 1) = 64 + 64 * ws.length by ring, Nat.pow_add]
    ring

theorem ofNat_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_add8 (a : Nat) : BitVec.ofNat 64 a + (8 : Word) = BitVec.ofNat 64 (a + 8) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_add8' (a : Nat) : BitVec.ofNat 64 a + 8#64 = BitVec.ofNat 64 (a + 8) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem length_flatten16 (vs : List Val) (h : ∀ v ∈ vs, v.length = 16) :
    vs.flatten.length = 16 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    simp only [List.flatten_cons, List.length_append, List.length_cons,
      h v List.mem_cons_self, ih (fun w hw => h w (List.mem_cons_of_mem _ hw))]
    ring

theorem readWords_add (t : MachineState) (A m₁ m₂ : Nat) :
    t.readWords (BitVec.ofNat 64 A) (m₁ + m₂) =
      t.readWords (BitVec.ofNat 64 A) m₁ ++ t.readWords (BitVec.ofNat 64 (A + 8 * m₁)) m₂ := by
  induction m₁ generalizing A with
  | zero => simp
  | succ m ih =>
    rw [show m + 1 + m₂ = (m + m₂) + 1 by omega, MachineState.readWords_succ,
      MachineState.readWords_succ, ofNat_add8, ih]
    simp only [List.cons_append]
    rw [show A + 8 + 8 * m = A + 8 * (m + 1) by ring]

theorem readWords_two (t : MachineState) (A : Nat) :
    t.readWords (BitVec.ofNat 64 A) 2 = [t.getMem (BitVec.ofNat 64 A), t.getMem (BitVec.ofNat 64 (A + 8))] := by
  simp [MachineState.readWords, ofNat_add8, ofNat_add8']

theorem wordsToNat_val (t : MachineState) (A : Nat) (v : Val) (hv : v.length = 16)
    (h : ValAt t A v) : wordsToNat (t.readWords (BitVec.ofNat 64 A) 2) = leNat v := by
  rw [readWords_two, h.1, h.2, leNat_val v hv]
  simp [wordsToNat]

/-- A buffer of 16-byte values `vs[i]` at `A + 16 i`. -/
theorem wordsToNat_vals (t : MachineState) (A : Nat) (vs : List Val)
    (hlen : ∀ v ∈ vs, v.length = 16) (h : ∀ i < vs.length, ValAt t (A + 16 * i) (vs.getD i [])) :
    wordsToNat (t.readWords (BitVec.ofNat 64 A) (2 * vs.length)) = leNat vs.flatten := by
  induction vs using List.reverseRecOn with
  | nil => simp [wordsToNat, leNat]
  | append_singleton vs v ih =>
    have hl : ∀ w ∈ vs, w.length = 16 := fun w hw => hlen w (List.mem_append_left _ hw)
    have hv : v.length = 16 := hlen v (by simp)
    rw [List.length_append, List.length_singleton, show 2 * (vs.length + 1) = 2 * vs.length + 2 by ring,
      readWords_add, wordsToNat_append, readWords_length, List.flatten_append, leNat_append,
      ih hl (fun i hi => by
        have := h i (by simp; omega)
        simpa [List.getD_eq_getElem?_getD, List.getElem?_append_left hi] using this)]
    have hv' := h vs.length (by simp)
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self,
      List.getElem?_cons_zero, Option.getD_some] at hv'
    rw [show A + 8 * (2 * vs.length) = A + 16 * vs.length by ring, wordsToNat_val t _ v hv hv']
    simp only [List.flatten_singleton]
    rw [length_flatten16 vs hl]; ring_nf

/-- The HASH input is `pad64 x` when the `8 (n+1)` words of the buffer encode `x`. -/
theorem hashInput_eq_pad64 (t : MachineState) (n B : Nat) (x : List Byte)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1))) (hn : 64 * (n + 1) < 2 ^ 64)
    (h10 : t.getReg .x10 = BitVec.ofNat 64 B) (hB : B % 8 = 0) (hB' : B < 2 ^ 64)
    (h1 : x.length ≤ 64 * (n + 1)) (h2 : 64 * n < x.length)
    (hw : wordsToNat (t.readWords (BitVec.ofNat 64 B) (8 * (n + 1))) = leNat x) :
    hashInput t = pad64 x := by
  rw [hashInput_eq_words t n h11 hn (by rw [h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hB']; exact hB),
    pad64_eq x n h1 h2, h10, queryOfWords, hw]
  simp [ofList, leNat_append]

end SigGolfCandidate.Keygen
