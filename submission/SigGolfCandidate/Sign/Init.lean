import SigGolfCandidate.Sign.Code
import SigGolfCandidate.Sign.Inv
import SigGolfCandidate.Expand.Mem

/-!
# The initial state of `sign`

`initialState submission .sign (sk, cache, m) = some (s0 sk cache m)`; its registers are `0`
except `x2`, its memory holds the secret key at `0x80`, the message at `0x40`, the cache at
`0x44A0`, and zeros elsewhere (`s0_readWords_sk`, `s0_readWords_msg`, `s0_zero`).
-/

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

set_option maxRecDepth 100000

/-- The loaded initial state. -/
def s0 (sk : SecretKey) (cache : Cache) (m : Message) : MachineState :=
  let blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  ((((blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase image)) image.data).writeBytesAsWords
      (BitVec.ofNat 64 0x80) (SigGolf.bytes sk)).writeBytesAsWords (BitVec.ofNat 64 0x44A0)
      (SigGolf.bytes cache)).writeBytesAsWords
      (BitVec.ofNat 64 0x40) (SigGolf.bytes m)).setReg .x2 (BitVec.ofNat 64 (dataBase image))

theorem initialState_eq (sk : SecretKey) (cache : Cache) (m : Message) :
    initialState submission .sign (sk, cache, m) = some (s0 sk cache m) := by
  unfold initialState
  rw [if_pos (submission_admissible.2 .sign)]
  -- (`simp only [List.foldl]` or a direct `rfl` here make the elaborator unfold
  -- `writeBytesAsWords` over the 128 KiB cache; rewrite structurally instead)
  simp only [inputBuffers]
  rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    show submission.image .sign = image from rfl,
    show (submission.layout.secretKey, bytes sk).1 = 0x80 from rfl,
    show (submission.layout.cache, bytes cache).1 = 0x44A0 from rfl,
    show (submission.layout.message, bytes m).1 = 0x40 from rfl]
  dsimp only
  rfl

theorem s0_pc (sk : SecretKey) (cache : Cache) (m : Message) : (s0 sk cache m).pc = pcOf 0 := by
  rw [initialState_pc submission .sign (sk, cache, m) _ (initialState_eq sk cache m)]; rfl

theorem regs_writeBytesAsWords (l : List Byte) : ∀ (s : MachineState) (base : Word),
    (s.writeBytesAsWords base l).regs = s.regs := by
  induction l using WellFounded.induction (r := fun x y : List Byte => x.length < y.length) with
  | hwf => exact (measure List.length).wf
  | h l ih =>
    intro s base
    match l with
    | [] => simp [MachineState.writeBytesAsWords]
    | b :: bs =>
      unfold MachineState.writeBytesAsWords
      simp only
      rw [ih _ (by simp only [List.length_drop, List.length_cons]; omega)]
      rfl

theorem s0_getReg (sk : SecretKey) (cache : Cache) (m : Message) (r : Reg) (hr : r ≠ .x2) :
    (s0 sk cache m).getReg r = 0 := by
  unfold s0
  dsimp only
  rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  unfold MachineState.getReg
  rw [regs_writeBytesAsWords, regs_writeBytesAsWords, regs_writeBytesAsWords, regs_writeBytesAsWords]
  cases r <;> rfl

theorem image_data : image.data = [] := by kernel_rfl

theorem length_bytes {n : Nat} (x : Bytes n) : (SigGolf.bytes x).length = n := by
  simp [SigGolf.bytes]

/-- Bytes of the initial memory. -/
theorem s0_getByte (sk : SecretKey) (cache : Cache) (m : Message) (a : Nat) (ha : a < 2 ^ 64) :
    (s0 sk cache m).getByte (BitVec.ofNat 64 a) =
      if 0x40 ≤ a ∧ a < 0x60 then (SigGolf.bytes m).getD (a - 0x40) 0
      else if 0x44A0 ≤ a ∧ a < 0x44A0 + 131072 then (SigGolf.bytes cache).getD (a - 0x44A0) 0
      else if 0x80 ≤ a ∧ a < 0xA0 then (SigGolf.bytes sk).getD (a - 0x80) 0
      else 0 := by
  unfold s0
  simp only [getByte_setReg, image_data]
  have L1 : (SigGolf.bytes m).length = 32 := length_bytes m
  have L2 : (SigGolf.bytes cache).length = 131072 := length_bytes cache
  have L3 : (SigGolf.bytes sk).length = 32 := length_bytes sk
  rw [getByte_writeBytesAsWords _ _ _ _ (by decide) (by rw [L1]; norm_num) ha, L1]
  by_cases h1 : 0x40 ≤ a ∧ a < 0x60
  · rw [if_pos (by omega), if_pos h1]
  rw [if_neg (by omega), if_neg h1, getByte_writeBytesAsWords _ _ _ _ (by decide)
    (by rw [L2]; norm_num) ha, L2]
  by_cases h2 : 0x44A0 ≤ a ∧ a < 0x44A0 + 131072
  · rw [if_pos (by omega), if_pos h2]
  rw [if_neg (by omega), if_neg h2, getByte_writeBytesAsWords _ _ _ _ (by decide)
    (by rw [L3]; norm_num) ha, L3]
  by_cases h3 : 0x80 ≤ a ∧ a < 0xA0
  · rw [if_pos (by omega), if_pos h3]
  rw [if_neg (by omega), if_neg h3]
  simp [MachineState.writeBytesAsWords, MachineState.getByte, MachineState.getMem, extractByte]

/-- A dword from its bytes. -/
theorem getMem_of_bytes (t : MachineState) (A : Nat) (hA : A % 8 = 0) (hA' : A + 8 < 2 ^ 64) :
    t.getMem (BitVec.ofNat 64 A) =
      BitVec.ofNat 64 (leNat ((List.range 8).map fun j => t.getByte (BitVec.ofNat 64 (A + j)))) := by
  have : (List.range 8).map (fun j => t.getByte (BitVec.ofNat 64 (A + j))) =
      bytesOfWord (t.getMem (BitVec.ofNat 64 A)) := by
    unfold bytesOfWord
    apply List.map_congr_left
    intro j hj
    have hj' : j < 8 := List.mem_range.mp hj
    simp only [MachineState.getByte]
    rw [byteOffset_ofNat (by omega), show BitVec.ofNat 64 (A + j) = BitVec.ofNat 64 (A + j) from rfl]
    have : alignToDword (BitVec.ofNat 64 (A + j)) = BitVec.ofNat 64 A := by
      rw [← alignToDword_ofNat_aligned (by omega) hA, alignToDword_ofNat_eq (by omega) (by omega)]
      omega
    rw [this, show (A + j) % 8 = j by omega]
    apply BitVec.eq_of_toNat_eq
    simp only [extractByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
      BitVec.toNat_ushiftRight, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mul_comm j 8]
  rw [this, leNat_bytesOfWord, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-- `readWords` of a region whose bytes are `l`. -/
theorem readWords_of_bytes (t : MachineState) (A : Nat) (l : List Byte) (n : Nat)
    (hl : l.length = 8 * n) (hA : A % 8 = 0) (hA' : A + 8 * n + 8 < 2 ^ 64)
    (hb : ∀ j < 8 * n, t.getByte (BitVec.ofNat 64 (A + j)) = l.getD j 0) :
    t.readWords (BitVec.ofNat 64 A) n = wordsOf l := by
  induction n generalizing A l with
  | zero => simp at hl; subst hl; rw [wordsOf_nil]; rfl
  | succ n ih =>
    have h8 : 8 ≤ l.length := by omega
    rw [readWords_ofNat_succ, ← List.take_append_drop 8 l, wordsOf_append _ _ (by simp; omega),
      wordsOf_eight _ (by simp; omega), ih (A + 8) (l.drop 8) (by simp; omega) (by omega) (by omega)]
    · rw [getMem_of_bytes t A hA (by omega)]
      congr 3
      apply List.ext_getElem (by simp; omega)
      intro j h1 h2
      simp only [List.getElem_map, List.getElem_range]
      simp at h1
      rw [hb j (by omega), List.getD_eq_getElem?_getD, List.getElem_take,
        List.getElem?_eq_getElem (by omega)]
      rfl
    · intro j hj
      rw [show A + 8 + j = A + (8 + j) by ring, hb (8 + j) (by omega)]
      simp [List.getD_eq_getElem?_getD]

theorem s0_readWords_sk (sk : SecretKey) (cache : Cache) (m : Message) :
    (s0 sk cache m).readWords (BitVec.ofNat 64 0x80) 4 = wordsOf (toList sk) := by
  apply readWords_of_bytes _ _ _ _ (by simp [toList, SigGolf.bytes]) (by norm_num) (by norm_num)
  intro j hj
  rw [s0_getByte _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega),
    if_pos (by omega)]
  simp [toList]

theorem s0_readWords_msg (sk : SecretKey) (cache : Cache) (m : Message) :
    (s0 sk cache m).readWords (BitVec.ofNat 64 0x40) 4 = wordsOf (toList m) := by
  apply readWords_of_bytes _ _ _ _ (by simp [toList, SigGolf.bytes]) (by norm_num) (by norm_num)
  intro j hj
  rw [s0_getByte _ _ _ _ (by omega), if_pos (by omega)]
  simp [toList]

/-- The initial memory is zero outside the message, secret key and cache. -/
theorem s0_zero (sk : SecretKey) (cache : Cache) (m : Message) (A : Nat) (hA : A % 8 = 0)
    (hA' : A + 8 < 2 ^ 64)
    (hout : A + 8 ≤ 0x40 ∨ (0x60 ≤ A ∧ A + 8 ≤ 0x80) ∨ (0xA0 ≤ A ∧ A + 8 ≤ 0x44A0) ∨ 0x244A0 ≤ A) :
    (s0 sk cache m).getMem (BitVec.ofNat 64 A) = 0 := by
  rw [getMem_of_bytes _ A hA hA']
  have : (List.range 8).map (fun j => (s0 sk cache m).getByte (BitVec.ofNat 64 (A + j))) =
      List.replicate 8 0 := by
    apply List.ext_getElem (by simp)
    intro j h1 h2
    simp only [List.getElem_map, List.getElem_range, List.getElem_replicate]
    simp at h1
    rw [s0_getByte _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
  rw [this]; rfl

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem getD_slice (l : List Byte) (off len j : Nat) (hj : j < len) (hl : off + len ≤ l.length) :
    (slice l off len).getD j 0 = l.getD (off + j) 0 := by
  simp only [slice, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hj]

/-- The initial cache words: `8 n` bytes at cache offset `off` (8-aligned). -/
theorem s0_readWords_cache (sk : SecretKey) (cache : Cache) (m : Message) (off n : Nat)
    (h8 : off % 8 = 0) (hn : off + 8 * n ≤ 131072) :
    (s0 sk cache m).readWords (BitVec.ofNat 64 (0x44A0 + off)) n =
      wordsOf (slice (toList cache) off (8 * n)) := by
  have hlen : (toList cache).length = 131072 := by simp [toList, SigGolf.bytes]; rfl
  apply readWords_of_bytes _ _ _ _ (by simp [slice, hlen]; omega) (by omega) (by omega)
  intro j hj
  rw [s0_getByte _ _ _ _ (by omega), if_neg (by omega), if_pos (by omega),
    getD_slice _ _ _ _ hj (by rw [hlen]; omega), show 0x44A0 + off + j - 0x44A0 = off + j by omega]
  rfl

end SigGolfCandidate.Sign
