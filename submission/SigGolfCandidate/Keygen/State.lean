import SigGolfCandidate.Keygen.Words

/-!
# Machine-state lemmas for `keygen`: `writeHash`, `ofNat` arithmetic, output buffers
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## `BitVec.ofNat 64` arithmetic (simp normal forms) -/

theorem ofNat_inj {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x = y := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  · rintro rfl; rfl

theorem ofNat_eq_iff (x y : Nat) :
    BitVec.ofNat 64 x = BitVec.ofNat 64 y ↔ x % 18446744073709551616 = y % 18446744073709551616 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa using this
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

theorem ofNat_shl (a k : Nat) : BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem ofNat_shr (a k : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem ofNat_or_add (a b k : Nat) (ha : a < 2 ^ k) :
    BitVec.ofNat 64 (b * 2 ^ k) ||| BitVec.ofNat 64 a = BitVec.ofNat 64 (b * 2 ^ k + a) := by
  have e1 : BitVec.ofNat 64 (b * 2 ^ k) = BitVec.ofNat 64 b <<< k := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  have hz : (BitVec.ofNat 64 b <<< k) &&& BitVec.ofNat 64 a = 0#64 := by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ofNat]
    by_cases h : i < k
    · simp [h]
    · have : a.testBit i = false :=
        Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [this]
  rw [e1, ← BitVec.add_eq_or_of_and_eq_zero _ _ hz, ← e1]
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_shl' (a k : Nat) :
    BitVec.ofNat 64 a <<< ((BitVec.ofNat 64 k).toNat % 64) = BitVec.ofNat 64 (a * 2 ^ (k % 2 ^ 64 % 64)) := by
  rw [ofNat_shl, BitVec.toNat_ofNat]

theorem ofNat_shr' (a k : Nat) :
    BitVec.ofNat 64 a >>> ((BitVec.ofNat 64 k).toNat % 64) =
      BitVec.ofNat 64 (a % 2 ^ 64 / 2 ^ (k % 2 ^ 64 % 64)) := by
  rw [BitVec.toNat_ofNat, show BitVec.ofNat 64 a = BitVec.ofNat 64 (a % 2 ^ 64) by
    apply BitVec.eq_of_toNat_eq; simp, ofNat_shr _ _ (Nat.mod_lt _ (by decide))]

theorem ofNat_slt (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    (BitVec.ofNat 64 a).slt (BitVec.ofNat 64 b) = decide (a < b) := by
  have h1 : (BitVec.ofNat 64 a).toInt = a := by
    rw [BitVec.toInt_eq_toNat_of_msb]; · simp; omega
    rw [BitVec.msb_eq_decide]; simp; omega
  have h2 : (BitVec.ofNat 64 b).toInt = b := by
    rw [BitVec.toInt_eq_toNat_of_msb]; · simp; omega
    rw [BitVec.msb_eq_decide]; simp; omega
  rw [BitVec.slt, h1, h2]
  simp

theorem toNat_ofNat_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-! ## `writeHash` -/

@[simp] theorem getReg_setMem' (t : MachineState) (a v : Word) (r : Reg) :
    (t.setMem a v).getReg r = t.getReg r := by cases r <;> rfl

@[simp] theorem getReg_writeHash (t : MachineState) (a : BitVec 256) (r : Reg) :
    (writeHash t a).getReg r = t.getReg r := by
  simp [writeHash]

@[simp] theorem pc_writeHash (t : MachineState) (a : BitVec 256) :
    (writeHash t a).pc = t.pc + 4 := by
  simp [writeHash, MachineState.setPC]

theorem getMem_writeHash (t : MachineState) (a : BitVec 256) (B A : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) (hA : A < 2 ^ 64) :
    (writeHash t a).getMem (BitVec.ofNat 64 A) =
      if A = B then a.extractLsb' 0 64 else if A = B + 8 then a.extractLsb' 64 64
      else if A = B + 16 then a.extractLsb' 128 64 else if A = B + 24 then a.extractLsb' 192 64
      else t.getMem (BitVec.ofNat 64 A) := by
  simp only [writeHash, h12, MachineState.writeWords_cons, MachineState.writeWords_nil,
    ofNat_add8, ofNat_add8', MachineState.getMem_setPC]
  simp only [MachineState.getMem, MachineState.setMem, beq_iff_eq,
    ofNat_inj hA (by omega : B + 8 + 8 + 8 < 2 ^ 64), ofNat_inj hA (by omega : B + 8 + 8 < 2 ^ 64),
    ofNat_inj hA (by omega : B + 8 < 2 ^ 64), ofNat_inj hA (by omega : B < 2 ^ 64)]
  split_ifs <;> first | (exfalso; omega) | rfl

/-- The answer's first 16 bytes are stored at `B` by `writeHash`. -/
theorem valAt_writeHash (t : MachineState) (a : BitVec 256) (B : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) :
    ValAt (writeHash t a) B (answerBytes 16 a) := by
  constructor
  · rw [getMem_writeHash t a B B h12 hB (by omega), if_pos rfl, lo_answer]
  · rw [getMem_writeHash t a B (B + 8) h12 hB (by omega), if_neg (by omega), if_pos rfl, hi_answer]

theorem getMem_writeHash_frame (t : MachineState) (a : BitVec 256) (B A : Nat)
    (h12 : t.getReg .x12 = BitVec.ofNat 64 B) (hB : B + 32 < 2 ^ 64) (hA : A < 2 ^ 64)
    (h : A + 8 ≤ B ∨ B + 32 ≤ A) :
    (writeHash t a).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
  rw [getMem_writeHash t a B A h12 hB hA, if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

end SigGolfCandidate.Keygen
