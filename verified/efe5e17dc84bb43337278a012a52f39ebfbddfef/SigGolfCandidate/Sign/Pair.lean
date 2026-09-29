import SigGolfCandidate.Sign.Blocks
import SigGolfCandidate.Sign.Mac

/-!
# Paired PRF secrets (SPEC-v5)

One seed-derivation query `prf2 x` yields two 16-byte secrets: the low and the high half of the
32-byte answer. The programs query on even items into `SEC = EO = 0x140` (32 bytes) and copy the
half `SEC + 16 (i & 1)` for item `i`.

* `prf2_eq` : `prf2 x = H x >>= fun a => pure (answerBytes 16 a, hiVal a)`.
* `sec_lo` / `sec_hi` : the two halves as dwords at `SEC` / `SEC + 16` after the query.
* `and_one_ofNat`, `secAddr` : the address `SEC + 16 (i & 1)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- The high 16 bytes of an answer. -/
def hiVal (a : BitVec 256) : Val := valOfWords (a.extractLsb' 128 64) (a.extractLsb' 192 64)

theorem answerBytes_32_take (a : BitVec 256) : (answerBytes 32 a).take 16 = answerBytes 16 a := by
  unfold answerBytes
  rw [← List.map_take, List.take_range, Nat.min_eq_left (by norm_num)]

theorem answerBytes_32_drop (a : BitVec 256) : (answerBytes 32 a).drop 16 = hiVal a := by
  rw [answerBytes_32, hiVal, valOfWords]
  simp only [List.append_assoc]
  rw [show (16 : Nat) = (bytesOfWord (a.extractLsb' 0 64) ++ bytesOfWord (a.extractLsb' 64 64)).length by simp,
    ← List.append_assoc, List.drop_left]

theorem prf2_eq (x : List Byte) :
    prf2 x = H x >>= fun a => pure (answerBytes 16 a, hiVal a) := by
  unfold prf2
  simp only [answerBytes_32_take, answerBytes_32_drop]

@[simp] theorem length_hiVal (a : BitVec 256) : (hiVal a).length = 16 := by simp [hiVal]

theorem sec_lo (s : MachineState) (a : BitVec 256) (h12 : s.getReg .x12 = BitVec.ofNat 64 0x140) :
    (writeHash s a).readWords (BitVec.ofNat 64 0x140) 2 = wordsOf (answerBytes 16 a) :=
  writeHash_readWords_val s a _ h12 (by norm_num)

theorem sec_hi (s : MachineState) (a : BitVec 256) (h12 : s.getReg .x12 = BitVec.ofNat 64 0x140) :
    (writeHash s a).readWords (BitVec.ofNat 64 0x150) 2 = wordsOf (hiVal a) := by
  rw [readWords_ofNat_two, writeHash_getMem_ofNat _ _ _ _ h12 (by norm_num) (by norm_num),
    writeHash_getMem_ofNat _ _ _ _ h12 (by norm_num) (by norm_num), hiVal, wordsOf_valOfWords]
  simp

theorem and_one_ofNat (j : Nat) (hj : j < 2 ^ 64) :
    BitVec.ofNat 64 j &&& 1#64 = BitVec.ofNat 64 (j % 2) := by
  apply BitVec.eq_of_toNat_eq
  have h1 : (1#64 : Word).toNat = 2 ^ 1 - 1 := rfl
  rw [BitVec.toNat_and, h1, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj,
    Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem secAddr (j : Nat) (hj : j < 2 ^ 64) (o : Nat) (ho : o < 2 ^ 32) :
    (BitVec.ofNat 64 j &&& 1#64) <<< ((4#64).toNat % 64) + BitVec.ofNat 64 o =
      BitVec.ofNat 64 (o + 16 * (j % 2)) := by
  rw [and_one_ofNat j hj]
  apply BitVec.eq_of_toNat_eq
  have h2 : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  rw [show (4#64 : Word).toNat % 64 = 4 from rfl]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt (a := j % 2) (by omega), Nat.mod_eq_of_lt (a := o) (by omega)]
  omega

end SigGolfCandidate.Sign
