import SigGolfCandidate.Expand.Witness

/-!
# The initial state of `expand`

`initialState submission .expand (m, pk, σ) = some (sI m pk σ)`: registers `0` except `x2`,
memory = message at `0x40`, public key at `0xA0`, signature at `0x3300`, zeros elsewhere.
(`regs_writeBytesAsWords`, `getMem_of_bytes`, `readWords_of_bytes` are local copies of
`Sign/Init.lean`.)
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Expand
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

set_option maxRecDepth 100000

/-- The loaded initial state. -/
def sI (m : Message) (pk : PublicKey) (σ : Bytes 6100) : MachineState :=
  let blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  ((((blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase image)) image.data).writeBytesAsWords
      (BitVec.ofNat 64 0x40) (SigGolf.bytes m)).writeBytesAsWords (BitVec.ofNat 64 0xA0)
      (SigGolf.bytes pk)).writeBytesAsWords
      (BitVec.ofNat 64 0x3300) (SigGolf.bytes σ)).setReg .x2 (BitVec.ofNat 64 (dataBase image))

theorem initialState_eq (m : Message) (pk : PublicKey) (σ : Bytes 6100) :
    initialState submission .expand (m, pk, σ) = some (sI m pk σ) := by
  unfold initialState
  rw [if_pos (submission_admissible.2 .expand)]
  simp only [inputBuffers]
  rw [List.foldl_cons, List.foldl_cons, List.foldl_cons, List.foldl_nil,
    show submission.image .expand = image from rfl,
    show (submission.layout.message, bytes m).1 = 0x40 from rfl,
    show (submission.layout.publicKey, bytes pk).1 = 0xA0 from rfl,
    show (submission.layout.signature, bytes σ).1 = 0x3300 from rfl]
  dsimp only
  rfl

theorem sI_pc (m : Message) (pk : PublicKey) (σ : Bytes 6100) : (sI m pk σ).pc = pcOf 0 := by
  rw [initialState_pc submission .expand (m, pk, σ) _ (initialState_eq m pk σ)]; rfl

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

theorem sI_getReg (m : Message) (pk : PublicKey) (σ : Bytes 6100) (r : Reg) (hr : r ≠ .x2) :
    (sI m pk σ).getReg r = 0 := by
  unfold sI
  dsimp only
  rw [MachineState.getReg_setReg_ne _ _ _ _ (Ne.symm hr)]
  unfold MachineState.getReg
  rw [regs_writeBytesAsWords, regs_writeBytesAsWords, regs_writeBytesAsWords, regs_writeBytesAsWords]
  cases r <;> rfl

theorem image_data : image.data = [] := by kernel_rfl

theorem length_bytes {n : Nat} (x : Bytes n) : (SigGolf.bytes x).length = n := by
  simp [SigGolf.bytes]

/-- Bytes of the initial memory. -/
theorem sI_getByte (m : Message) (pk : PublicKey) (σ : Bytes 6100) (a : Nat) (ha : a < 2 ^ 64) :
    (sI m pk σ).getByte (BitVec.ofNat 64 a) =
      if 0x3300 ≤ a ∧ a < 0x3300 + 6104 then (SigGolf.bytes σ).getD (a - 0x3300) 0
      else if 0xA0 ≤ a ∧ a < 0xB0 then (SigGolf.bytes pk).getD (a - 0xA0) 0
      else if 0x40 ≤ a ∧ a < 0x60 then (SigGolf.bytes m).getD (a - 0x40) 0
      else 0 := by
  unfold sI
  simp only [getByte_setReg, image_data]
  have L1 : (SigGolf.bytes σ).length = 6100 := length_bytes σ
  have L2 : (SigGolf.bytes pk).length = 16 := length_bytes pk
  have L3 : (SigGolf.bytes m).length = 32 := length_bytes m
  rw [getByte_writeBytesAsWords _ _ _ _ (by decide) (by rw [L1]; norm_num) ha, L1]
  by_cases h1 : 0x3300 ≤ a ∧ a < 0x3300 + 6104
  · rw [if_pos (by omega), if_pos h1]
  rw [if_neg (by omega), if_neg h1, getByte_writeBytesAsWords _ _ _ _ (by decide)
    (by rw [L2]; norm_num) ha, L2]
  by_cases h2 : 0xA0 ≤ a ∧ a < 0xB0
  · rw [if_pos (by omega), if_pos h2]
  rw [if_neg (by omega), if_neg h2, getByte_writeBytesAsWords _ _ _ _ (by decide)
    (by rw [L3]; norm_num) ha, L3]
  by_cases h3 : 0x40 ≤ a ∧ a < 0x60
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


end SigGolfCandidate.Expand
