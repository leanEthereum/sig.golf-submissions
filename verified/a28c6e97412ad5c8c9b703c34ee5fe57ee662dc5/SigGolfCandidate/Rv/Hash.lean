import SigGolfCandidate.Rv.Sound

/-!
# HASH input as a list of doublewords

`hashInput_eq_words` : when `x10` is 8-aligned and `x11 = 64 * (n + 1)`,

  `hashInput t = ⟨n, BitVec.ofNat _ (wordsToNat (t.readWords (t.getReg .x10) (8 * (n + 1))))⟩`

i.e. the oracle input is the little-endian concatenation of the `8 * (n+1)` doublewords of the
buffer. Together with `Result.readWords_toState` (reflective symbolic `readWords`) this computes
the HASH input of a buffer written by a block.
-/

namespace SigGolfCandidate.Rv
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

/-- Little-endian concatenation of doublewords. -/
def wordsToNat : List Word → Nat
  | [] => 0
  | w :: ws => w.toNat + 2 ^ 64 * wordsToNat ws

/-- The HASH query of `n + 1` blocks given by the doublewords `ws` (`ws.length = 8 * (n + 1)`). -/
def queryOfWords (n : Nat) (ws : List Word) : Query := ⟨n, BitVec.ofNat _ (wordsToNat ws)⟩

theorem wordsToNat_append_single (l : List Word) (w : Word) :
    wordsToNat (l ++ [w]) = wordsToNat l + 2 ^ (64 * l.length) * w.toNat := by
  induction l with
  | nil => simp [wordsToNat]
  | cons x xs ih =>
    simp only [List.cons_append, wordsToNat, ih, List.length_cons]
    rw [show 64 * (xs.length + 1) = 64 + 64 * xs.length by ring, Nat.pow_add]
    ring

theorem readWords_succ_last (t : MachineState) (base : Word) (m : Nat) :
    t.readWords base (m + 1) = t.readWords base m ++ [t.getMem (base + BitVec.ofNat 64 (8 * m))] := by
  induction m generalizing base with
  | zero => simp
  | succ m ih =>
    rw [MachineState.readWords_succ, ih (base + 8), MachineState.readWords_succ]
    simp only [List.cons_append, List.cons.injEq, List.append_cancel_left_eq, List.cons.injEq,
      and_true, true_and]
    congr 1
    rw [BitVec.add_assoc]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, show (8 : Word).toNat = 8 from rfl]
    omega

theorem readWords_length (t : MachineState) (base : Word) (m : Nat) :
    (t.readWords base m).length = m := by
  induction m generalizing base with
  | zero => rfl
  | succ m ih => simp [ih]

private theorem foldl_range_succ (g : Nat → Nat) (N : Nat) :
    (List.range (N + 1)).foldl (fun acc i => acc + g i) 0 =
      (List.range N).foldl (fun acc i => acc + g i) 0 + g N := by
  rw [List.range_succ, List.foldl_append]; rfl

private theorem extractByte_toNat (w : Word) (b : Nat) :
    (extractByte w b).toNat = w.toNat / 2 ^ (8 * b) % 256 := by
  unfold extractByte
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mul_comm b 8]

private theorem word_bytes (x : Nat) (hx : x < 2 ^ 64) :
    x / 2 ^ (8 * 0) % 256 * 2 ^ (8 * 0) + x / 2 ^ (8 * 1) % 256 * 2 ^ (8 * 1) +
      x / 2 ^ (8 * 2) % 256 * 2 ^ (8 * 2) + x / 2 ^ (8 * 3) % 256 * 2 ^ (8 * 3) +
      x / 2 ^ (8 * 4) % 256 * 2 ^ (8 * 4) + x / 2 ^ (8 * 5) % 256 * 2 ^ (8 * 5) +
      x / 2 ^ (8 * 6) % 256 * 2 ^ (8 * 6) + x / 2 ^ (8 * 7) % 256 * 2 ^ (8 * 7) = x := by
  simp only [Nat.reducePow, Nat.reduceMul]
  omega

private theorem getByte_aligned (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b : Nat) (hb : b < 8) (hi : 8 * m + b < 2 ^ 64) :
    t.getByte (src + BitVec.ofNat 64 (8 * m + b)) =
      extractByte (t.getMem (src + BitVec.ofNat 64 (8 * m))) b := by
  unfold MachineState.getByte
  obtain ⟨h1, h2⟩ := aligned_add src (BitVec.ofNat 64 (8 * m + b)) hal
  rw [h1, h2, byteOffset_eq]
  have hlt : (BitVec.ofNat 64 (8 * m + b)).toNat = 8 * m + b := by
    simp only [BitVec.toNat_ofNat]; omega
  congr 2
  · congr 1
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, hlt]
    simp only [BitVec.toNat_ofNat]
    omega
  · rw [hlt]; omega

private theorem byte_term (t : MachineState) (src : Word) (hal : src.toNat % 8 = 0)
    (m b i : Nat) (hb : b < 8) (hi : i = 8 * m + b) (hlt : i < 2 ^ 64) :
    (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i) =
      2 ^ (64 * m) * ((t.getMem (src + BitVec.ofNat 64 (8 * m))).toNat / 2 ^ (8 * b) % 256 *
        2 ^ (8 * b)) := by
  subst hi
  rw [getByte_aligned t src hal m b hb hlt, extractByte_toNat,
    show 8 * (8 * m + b) = 64 * m + 8 * b by ring, Nat.pow_add]
  ring

/-- The HASH oracle input is the little-endian concatenation of the buffer's doublewords. -/
theorem hashInput_eq_words (t : MachineState) (n : Nat)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1))) (hn : 64 * (n + 1) < 2 ^ 64)
    (h10 : (t.getReg .x10).toNat % 8 = 0) :
    hashInput t = queryOfWords n (t.readWords (t.getReg .x10) (8 * (n + 1))) := by
  have hN : (t.getReg .x11).toNat / 64 - 1 = n := by
    rw [h11, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hn]; omega
  generalize hsrc : t.getReg .x10 = src at h10
  have key : ∀ m, 8 * m ≤ 64 * (n + 1) →
      (List.range (8 * m)).foldl (fun acc i =>
        acc + (t.getByte (src + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0 =
        wordsToNat (t.readWords src m) := by
    intro m
    induction m with
    | zero => intro _; rfl
    | succ m ih =>
      intro hm
      rw [show 8 * (m + 1) = 8 * m + 7 + 1 by omega]
      simp only [foldl_range_succ]
      rw [ih (by omega), readWords_succ_last, wordsToNat_append_single, readWords_length,
        byte_term t src h10 m 0 (8 * m) (by omega) (by omega) (by omega),
        byte_term t src h10 m 1 (8 * m + 1) (by omega) (by omega) (by omega),
        byte_term t src h10 m 2 (8 * m + 2) (by omega) (by omega) (by omega),
        byte_term t src h10 m 3 (8 * m + 3) (by omega) (by omega) (by omega),
        byte_term t src h10 m 4 (8 * m + 4) (by omega) (by omega) (by omega),
        byte_term t src h10 m 5 (8 * m + 5) (by omega) (by omega) (by omega),
        byte_term t src h10 m 6 (8 * m + 6) (by omega) (by omega) (by omega),
        byte_term t src h10 m 7 (8 * m + 6 + 1) (by omega) (by omega) (by omega)]
      generalize (t.getMem (src + BitVec.ofNat 64 (8 * m))) = w
      conv_rhs => rw [← word_bytes w.toNat w.isLt]
      ring
  have k := key (8 * (n + 1)) (by omega)
  rw [show 8 * (8 * (n + 1)) = 64 * (n + 1) by ring] at k
  unfold hashInput queryOfWords
  rw [hsrc]
  generalize (t.getReg .x11).toNat / 64 - 1 = N at hN ⊢
  subst hN
  simp only []
  rw [k]

end SigGolfCandidate.Rv
