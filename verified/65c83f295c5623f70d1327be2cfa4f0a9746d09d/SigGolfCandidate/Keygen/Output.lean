import SigGolfCandidate.Keygen.Init
import SigGolfCandidate.Keygen.Inv

/-!
# The outputs of `keygen`: public key buffer and cache buffer
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Mem

theorem getByte_eq_word (t : MachineState) (a : Nat) (ha : a < 2 ^ 64) :
    t.getByte (BitVec.ofNat 64 a) = extractByte (t.getMem (BitVec.ofNat 64 (a - a % 8))) (a % 8) := by
  unfold MachineState.getByte
  rw [byteOffset_ofNat ha]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [alignToDword_toNat, toNat_ofNat_lt ha, toNat_ofNat_lt (by omega)]

theorem extractByte_ofNat_leNat (l : List Byte) (i j : Nat) (hj : j < 8) :
    extractByte (BitVec.ofNat 64 (leNat l / 2 ^ (64 * i))) j = l.getD (8 * i + j) 0 := by
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat', BitVec.toNat_ofNat, ← leNat_div_mod]
  rw [show 256 ^ (8 * i + j) = 2 ^ (64 * i) * 2 ^ (8 * j) by
    rw [show (256 : Nat) = 2 ^ 8 by norm_num, ← Nat.pow_mul, ← Nat.pow_add]; ring_nf]
  rw [← Nat.div_div_eq_div_mul]
  generalize leNat l / 2 ^ (64 * i) = N
  interval_cases j <;> simp only [Nat.reducePow, Nat.reduceMul] <;> omega

theorem hi_def (v : Val) : hi v = BitVec.ofNat 64 (leNat v / 2 ^ 64) := rfl

/-- The public key buffer holds `v` (stored as two doublewords). -/
theorem readBuffer_val (t : MachineState) (A : Nat) (v : Val) (hv : v.length = 16) (hA : A % 8 = 0)
    (hA' : A + 16 < 2 ^ 64) (h : ValAt t A v) : readBuffer t A 16 = ofList 16 v := by
  rw [readBuffer_eq, ofList]
  congr 2
  apply List.ext_getElem (by simp [hv])
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  rw [getByte_eq_word t _ (by simp at h1; omega)]
  simp only [List.length_map, List.length_range] at h1
  by_cases hi : i < 8
  · rw [show A + i - (A + i) % 8 = A by omega, h.1, lo,
      show BitVec.ofNat 64 (leNat v) = BitVec.ofNat 64 (leNat v / 2 ^ (64 * 0)) by simp,
      extractByte_ofNat_leNat _ 0 _ (by omega)]
    rw [show 8 * 0 + (A + i) % 8 = i by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]
  · rw [show A + i - (A + i) % 8 = A + 8 by omega, h.2, hi_def,
      show leNat v / 2 ^ 64 = leNat v / 2 ^ (64 * 1) by simp,
      extractByte_ofNat_leNat _ 1 _ (by omega)]
    rw [show 8 * 1 + (A + i) % 8 = i by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem h2, Option.getD_some]

theorem leNat_map_zero (n : Nat) : leNat ((List.range n).map fun _ => (0 : Byte)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, leNat_append, ih]
    simp [leNat]

/-- The cache buffer is zero. -/
theorem readBuffer_cache (t : MachineState)
    (h : ∀ A, 0x44A0 ≤ A → A < 0x244A0 → t.getMem (BitVec.ofNat 64 A) = 0) :
    readBuffer t 0x44A0 CACHE_BYTES = 0 := by
  rw [readBuffer_eq]
  have : (List.range CACHE_BYTES).map (fun i => t.getByte (BitVec.ofNat 64 (0x44A0 + i))) =
      (List.range CACHE_BYTES).map fun _ => (0 : Byte) := by
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range, CACHE_BYTES] at hi
    rw [getByte_eq_word t _ (by omega), h _ (by omega) (by omega)]
    simp [extractByte]
  rw [this, leNat_map_zero]
  rfl

end SigGolfCandidate.Keygen
