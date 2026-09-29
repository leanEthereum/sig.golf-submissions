import SigGolfCandidate.Keygen.Init
import SigGolfCandidate.Keygen.Inv

/-!
# The outputs of `keygen`: public key buffer and cache buffer
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref
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

/-- Byte `r` of doubleword `q` of a 256-bit answer. -/
theorem extractByte_extractLsb (a : BitVec 256) (q r : Nat) (hr : r < 8) :
    extractByte (a.extractLsb' (64 * q) 64) r = a.extractLsb' (8 * (8 * q + r)) 8 := by
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat', BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow,
    show 8 * (8 * q + r) = 64 * q + 8 * r by ring, Nat.pow_add, ← Nat.div_div_eq_div_mul]
  generalize a.toNat / 2 ^ (64 * q) = x
  interval_cases r <;> simp only [Nat.reducePow, Nat.reduceMul, Nat.mul_zero, Nat.pow_zero] <;> omega

theorem getD_lt' {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem h]

theorem getD_flatten16 : ∀ (vs : List Val), (∀ v ∈ vs, v.length = 16) → ∀ (m r : Nat),
    m < vs.length → r < 16 → vs.flatten.getD (16 * m + r) 0 = (vs.getD m []).getD r 0
  | [], _, m, r, hm, _ => by simp at hm
  | v :: vs, hv, m, r, hm, hr => by
    have hvl : v.length = 16 := hv v (by simp)
    rcases m with _ | m
    · simp only [List.flatten_cons, List.getD_eq_getElem?_getD, List.getElem?_append_left
        (show 16 * 0 + r < v.length by omega), List.getElem?_cons_zero, Option.getD_some]
      simp
    · simp only [List.flatten_cons, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_right (by omega), hvl,
        show 16 * (m + 1) + r - 16 = 16 * m + r by omega, List.getElem?_cons_succ]
      have := getD_flatten16 vs (fun w hw => hv w (by simp [hw])) m r (by simp at hm; omega) hr
      simp only [List.getD_eq_getElem?_getD] at this
      exact this

/-- The cache buffer: the tag (the full answer `a`), the masked region, zeros. -/
theorem readBuffer_cache_eq (t : MachineState) (a : BitVec 256) (masked : List Val)
    (hlen : masked.length = 4094)
    (htag : ∀ k < 4, t.getMem (BitVec.ofNat 64 (0x4B00 + 8 * k)) = a.extractLsb' (64 * k) 64)
    (hreg : Vals t REGION masked)
    (hz : ∀ A, 0x14B00 ≤ A → A < 0x24B00 → A % 8 = 0 → t.getMem (BitVec.ofNat 64 A) = 0) :
    readBuffer t 0x4B00 CACHE_BYTES =
      ofList CACHE_BYTES (toList (n := 32) a ++ masked.flatten ++ zeros (cacheBytes - 32 - regionBytes)) := by
  have hfl : masked.flatten.length = 65504 := by rw [length_flatten16 _ hreg.1, hlen]
  suffices hl : (List.range CACHE_BYTES).map (fun i => t.getByte (BitVec.ofNat 64 (0x4B00 + i))) =
      toList (n := 32) a ++ masked.flatten ++ zeros (cacheBytes - 32 - regionBytes) by
    rw [readBuffer_eq, ofList, hl]
  apply List.ext_getElem (by
    rw [List.length_map, List.length_range, List.length_append, List.length_append, hfl, zeros,
      List.length_replicate, regionBytes_eq, toList, SigGolfCandidate.Legacy.bytes, List.length_map, List.length_range]
    rfl)
  intro i h1 h2
  simp only [List.length_map, List.length_range, CACHE_BYTES] at h1
  simp only [List.getElem_map, List.getElem_range]
  rw [getByte_eq_word t _ (by omega)]
  by_cases hi32 : i < 32
  · rw [List.getElem_append_left (by simp [hfl, toList, SigGolfCandidate.Legacy.bytes]; omega),
      List.getElem_append_left (by simp [toList, SigGolfCandidate.Legacy.bytes]; omega)]
    simp only [toList, SigGolfCandidate.Legacy.bytes, List.getElem_map, List.getElem_range]
    rw [show 0x4B00 + i - (0x4B00 + i) % 8 = 0x4B00 + 8 * (i / 8) by omega,
      htag (i / 8) (by omega), show (0x4B00 + i) % 8 = i % 8 by omega,
      extractByte_extractLsb a (i / 8) (i % 8) (by omega), show 8 * (i / 8) + i % 8 = i by omega]
  · by_cases hir : i < 32 + 65504
    · rw [List.getElem_append_left (by simp [hfl, toList, SigGolfCandidate.Legacy.bytes]; omega),
        List.getElem_append_right (by simp [toList, SigGolfCandidate.Legacy.bytes]; omega)]
      simp only [toList, SigGolfCandidate.Legacy.bytes, List.length_map, List.length_range]
      have hm : (i - 32) / 16 < masked.length := by rw [hlen]; omega
      have hv := hreg.2 ((i - 32) / 16) hm
      rw [getD_lt' masked _ [] hm] at hv
      have hvl : masked[(i - 32) / 16].length = 16 := hreg.1 _ (List.getElem_mem hm)
      have hfg := getD_flatten16 masked hreg.1 ((i - 32) / 16) ((i - 32) % 16) hm (by omega)
      rw [show 16 * ((i - 32) / 16) + (i - 32) % 16 = i - 32 by omega, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hfl]; omega), Option.getD_some, getD_lt' masked _ [] hm] at hfg
      rw [hfg]
      by_cases hlo : (i - 32) % 16 < 8
      · rw [show 0x4B00 + i - (0x4B00 + i) % 8 = REGION + 16 * ((i - 32) / 16) by unfold REGION; omega,
          hv.1, lo, show BitVec.ofNat 64 (leNat masked[(i - 32) / 16]) =
            BitVec.ofNat 64 (leNat masked[(i - 32) / 16] / 2 ^ (64 * 0)) by simp,
          extractByte_ofNat_leNat _ 0 _ (by omega)]
        congr 1; omega
      · rw [show 0x4B00 + i - (0x4B00 + i) % 8 = REGION + 16 * ((i - 32) / 16) + 8 by unfold REGION; omega,
          hv.2, hi_def, show leNat masked[(i - 32) / 16] / 2 ^ 64 =
            leNat masked[(i - 32) / 16] / 2 ^ (64 * 1) by simp,
          extractByte_ofNat_leNat _ 1 _ (by omega)]
        congr 1; omega
    · rw [List.getElem_append_right (by simp [hfl, toList, SigGolfCandidate.Legacy.bytes]; omega)]
      simp only [zeros, List.getElem_replicate]
      rw [hz _ (by omega) (by omega) (by omega)]
      simp [extractByte]

theorem leNat_map_zero (n : Nat) : leNat ((List.range n).map fun _ => (0 : Byte)) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.map_append, leNat_append, ih]
    simp [leNat]

/-- The cache buffer is zero. -/
theorem readBuffer_cache (t : MachineState)
    (h : ∀ A, 0x4B00 ≤ A → A < 0x24B00 → t.getMem (BitVec.ofNat 64 A) = 0) :
    readBuffer t 0x4B00 CACHE_BYTES = 0 := by
  rw [readBuffer_eq]
  have : (List.range CACHE_BYTES).map (fun i => t.getByte (BitVec.ofNat 64 (0x4B00 + i))) =
      (List.range CACHE_BYTES).map fun _ => (0 : Byte) := by
    apply List.map_congr_left
    intro i hi
    simp only [List.mem_range, CACHE_BYTES] at hi
    rw [getByte_eq_word t _ (by omega), h _ (by omega) (by omega)]
    simp [extractByte]
  rw [this, leNat_map_zero]
  rfl

end SigGolfCandidate.Keygen
