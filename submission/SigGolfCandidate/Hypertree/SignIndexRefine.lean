import SigGolfCandidate.Hypertree.SignRefine
import SigGolfCandidate.Hypertree.SignIndexPrepare

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def indexPayload (message : Message) (r : Bytes 32) : List Byte :=
  bytes (n := 8) (5 : BitVec 64) ++ bytes (n := 24) (0 : BitVec 192) ++
    (bytes (0 : Bytes 16) ++ bytes message ++ bytes r)

@[simp] theorem indexPayload_length (message : Message) (r : Bytes 32) :
    (indexPayload message r).length = 112 := by simp [indexPayload, bytes]

theorem indexPayload_byte (message : Message) (r : Bytes 32) (i : Fin 112) :
    (indexPayload message r)[i.val]'(by simp) =
      if i.val = 0 then 5 else if i.val < 32 then 0 else
        if i.val < 48 then (0 : Bytes 16).extractLsb' (8 * (i.val - 32)) 8
        else if i.val < 80 then message.extractLsb' (8 * (i.val - 48)) 8
        else r.extractLsb' (8 * (i.val - 80)) 8 := by
  fin_cases i <;> simp [indexPayload, bytes, List.getElem_append]

def indexInputByte (s : MachineState) (i : Fin 112) : Byte :=
  extractByte (indexInputWord s ⟨i.val / 8, by have := i.isLt; omega⟩) (i.val % 8)

theorem indexInputByte_spec (s : MachineState) (i : Fin 112) :
    indexInputByte s i =
      if i.val = 0 then 5 else if i.val < 32 then 0 else
        if i.val < 48 then s.getByte (BitVec.ofNat 64 (0x50 + (i.val - 32)))
        else if i.val < 80 then s.getByte (BitVec.ofNat 64 (i.val - 48))
        else s.getByte (BitVec.ofNat 64 (0x20060 + (i.val - 80))) := by
  fin_cases i <;> first | rfl | simp [indexInputByte, indexInputWord, extractByte]

theorem prepared_index_bytes (original ready : MachineState)
    (words : ∀ i : Fin 14, ready.getMem (wordAddress 0x80000 i.val) = indexInputWord original i)
    (i : Fin 112) :
    ready.getByte (BitVec.ofNat 64 (0x80000 + i.val)) = indexInputByte original i := by
  rw [getByte_word ready 0x80000 i.val (by decide) (by have := i.isLt; omega)]
  exact congrArg (fun word => extractByte word (i.val % 8))
    (words ⟨i.val / 8, by have := i.isLt; omega⟩)

theorem indexHashState_mem (s : MachineState) (a : Word) :
    (indexHashState s).getMem a = s.getMem a := by simp [indexHashState, execInstrBr]

theorem indexHashState_byte (s : MachineState) (a : Word) :
    (indexHashState s).getByte a = s.getByte a := by
  simp only [MachineState.getByte, indexHashState_mem]

/-- The bytecode's index oracle input is exactly the reference tag5 query. -/
theorem index_query (original ready : MachineState) (message : Message) (r : Bytes 32)
    (hzero : ∀ i, i < 16 → original.getByte (BitVec.ofNat 64 (0x50 + i)) = 0)
    (hmessage : ∀ i, i < 32 → original.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8)
    (hr : ∀ i, i < 32 → original.getByte (BitVec.ofNat 64 (0x20060 + i)) = r.extractLsb' (8 * i) 8)
    (words : ∀ i : Fin 14, ready.getMem (wordAddress 0x80000 i.val) = indexInputWord original i) :
    hashInput (indexHashState ready) = Reference.packed (indexPayload message r) := by
  apply Serialization.hashInput_of_list (indexHashState ready) 0x80000 (indexPayload message r)
  · exact (indexHashState_regs ready).2.1
  · rw [(indexHashState_regs ready).2.2.1, indexPayload_length]; rfl
  · intro i hi
    have bound : i < 112 := by simpa using hi
    rw [indexHashState_byte, prepared_index_bytes original ready words ⟨i, bound⟩,
      indexInputByte_spec, indexPayload_byte message r ⟨i, bound⟩]
    dsimp only
    split_ifs with h0 h32 h48 h80
    · rfl
    · rfl
    · rw [hzero (i - 32) (by omega)]; simp
    · exact hmessage (i - 48) (by omega)
    · exact hr (i - 80) (by omega)

theorem extractByte_mask_slice (value : BitVec 256) (i : Fin 4) :
    extractByte ((value.extractLsb' 128 64 <<< 32) >>> 32) i.val =
      value.extractLsb' (128 + 8 * i.val) 8 := by
  ext j hj
  have bound : i.val * 8 + j < 32 := by have := i.isLt; omega
  simp [extractByte, show i.val * 8 + j + 32 < 64 by omega,
    show 32 ≤ i.val * 8 + j + 32 by omega,
    show i.val * 8 + j < 64 by omega, Nat.add_assoc, Nat.mul_comm]
  omega

/-- The three scratch words decode to exactly the low 160 bits of the oracle answer. -/
theorem read_index_words (s : MachineState) (answer : BitVec 256)
    (low : ∀ i : Fin 2, s.getMem (wordAddress 0x80408 i.val) = answer.extractLsb' (64 * i.val) 64)
    (high : s.getMem 0x80418 = (answer.extractLsb' 128 64 <<< 32) >>> 32) :
    readBuffer s 0x80408 20 = answer.extractLsb' 0 160 := by
  apply Memory.readBuffer_of_bytes
  intro i hi
  rw [BitVec.extractLsb'_extractLsb'_of_le (by omega)]
  rw [getByte_word s 0x80408 i (by decide) (by omega)]
  by_cases h : i < 16
  · rw [low ⟨i / 8, by omega⟩]
    exact extractByte_slice answer ⟨i, by omega⟩
  · rw [show i / 8 = 2 by omega]
    change extractByte (s.getMem 0x80418) (i % 8) = _
    rw [high]
    have hb : i - 16 < 4 := by omega
    have eq := extractByte_mask_slice answer ⟨i - 16, hb⟩
    dsimp only at eq
    rw [show i % 8 = i - 16 by omega, show 8 * i = 128 + 8 * (i - 16) by omega]
    exact eq

/-- Exact execution refinement of the whole tag5 preparation, HASH and index
extraction, for arbitrary memory containing the three required input buffers. -/
theorem index_refines (hash : Hash) (s : MachineState) (message : Message) (r : Bytes 32)
    (pc : s.pc = 0x10fc)
    (hzero : ∀ i, i < 16 → s.getByte (BitVec.ofNat 64 (0x50 + i)) = 0)
    (hmessage : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8)
    (hr : ∀ i, i < 32 → s.getByte (BitVec.ofNat 64 (0x20060 + i)) = r.extractLsb' (8 * i) 8) :
    ∃ final, Trace hash sign s 121 136 1 2 final ∧ final.pc = 0x1220 ∧
      readBuffer final 0x80408 20 = Reference.indexOf hash message r := by
  obtain ⟨ready, prepare, readypc, words, _⟩ := index_prepare s pc
  obtain ⟨final, trace, finalpc, low, high⟩ := index_trace hash ready readypc
  have query := index_query s ready message r hzero hmessage hr words
  refine ⟨final, prepare.trace.trans trace, finalpc, ?_⟩
  rw [read_index_words final _ low high, query]
  rfl

/-- info: 'SigGolfCandidate.Hypertree.Signing.index_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms index_refines

/-- The organizer's typed sign input executes both reference oracle computations and
reaches the main hypertree loop with the exact reference 160-bit index. -/
theorem loaded_index_refines (hash : Hash) (secretKey : SecretKey)
    (cache : Cache) (message : Message) :
    ∃ initial final,
      initialState submission .sign (secretKey, cache, message) = some initial ∧
      Trace hash sign initial 238 268 2 4 final ∧ final.pc = 0x1220 ∧
      readBuffer final 0x80408 20 =
        Reference.indexOf hash message (Reference.randomizer hash secretKey message) := by
  obtain ⟨initial, loaded, pc⟩ := initialState_exists submission admitted .sign (secretKey, cache, message)
  obtain ⟨randomized, randomTrace, randomPC, randomWords, frame⟩ := entry_randomizer_refines_frame hash initial secretKey message pc
    (Loader.sign_secretKey submission (admitted.2 .sign) (by rfl) secretKey cache message initial loaded)
    (Loader.sign_message submission (admitted.2 .sign) (by rfl) secretKey cache message initial loaded)
  have zeroBytes : ∀ i, i < 16 → randomized.getByte (BitVec.ofNat 64 (0x50 + i)) = 0 := by
    intro i hi
    rw [low_words_byte initial randomized frame 0x50 i (by decide) (by omega)]
    exact Loader.sign_zeroSlot submission (admitted.2 .sign) (by rfl) (by rfl) secretKey cache message initial loaded i hi
  have msgBytes : ∀ i, i < 32 → randomized.getByte (BitVec.ofNat 64 i) = message.extractLsb' (8 * i) 8 := by
    intro i hi
    have unchanged := low_words_byte initial randomized frame 0 i (by decide) (by omega)
    simp only [Nat.zero_add] at unchanged
    rw [unchanged]
    exact Loader.sign_message submission (admitted.2 .sign) (by rfl) secretKey cache message initial loaded i hi
  have randBytes := bytes_of_answer_words randomized 0x20060 (Reference.randomizer hash secretKey message)
    (by decide) (by decide) randomWords
  obtain ⟨final, indexTrace, finalPC, index⟩ := index_refines hash randomized message
    (Reference.randomizer hash secretKey message) randomPC zeroBytes msgBytes randBytes
  exact ⟨initial, final, loaded, randomTrace.trans indexTrace, finalPC, index⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.loaded_index_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms loaded_index_refines

end SigGolfCandidate.Hypertree.Signing
