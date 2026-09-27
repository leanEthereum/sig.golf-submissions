import SigGolfCandidate.Verify.Words

/-!
# Machine-state facts: address normalization, `writeHash`, global invariant

`Glob wl pk s`: the registers that are constant after the prologue, the witness region, the public
key and the zero `P` slots of all hash buffers. Every block of the verify program preserves it; the
side conditions are Boolean facts about the (concrete) symbolic results (`memOK`, `regsOK`,
`safeDest`) checked by the kernel.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## Addresses -/

theorem ofNat_eq_iff {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    (BitVec.ofNat 64 a = BitVec.ofNat 64 b) ↔ a = b := by
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this
  · intro h; rw [h]

theorem ofNat_ne {a b : Nat} (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) (h : a ≠ b) :
    BitVec.ofNat 64 a ≠ BitVec.ofNat 64 b := fun h' => h ((ofNat_eq_iff ha hb).mp h')

/-! ## `writeHash` -/

theorem getMem_setMem (s : MachineState) (a v A : Word) :
    (s.setMem a v).getMem A = if A = a then v else s.getMem A := by
  simp [MachineState.setMem, MachineState.getMem]

theorem writeHash_getMem (s : MachineState) (ans : BitVec 256) (A : Word) :
    (writeHash s ans).getMem A =
      if A = s.getReg .x12 + 8 + 8 + 8 then ans.extractLsb' 192 64
      else if A = s.getReg .x12 + 8 + 8 then ans.extractLsb' 128 64
      else if A = s.getReg .x12 + 8 then ans.extractLsb' 64 64
      else if A = s.getReg .x12 then ans.extractLsb' 0 64
      else s.getMem A := by
  simp only [writeHash, MachineState.writeWords]
  show ((((s.setMem _ _).setMem _ _).setMem _ _).setMem _ _).getMem A = _
  simp only [getMem_setMem]

/-- `writeHash` at a constant destination `d`. -/
theorem writeHash_getMem_ofNat (s : MachineState) (ans : BitVec 256) (d A : Nat)
    (hd : s.getReg .x12 = BitVec.ofNat 64 d) (hA : A < 2 ^ 64) (hd' : d + 24 < 2 ^ 64) :
    (writeHash s ans).getMem (BitVec.ofNat 64 A) =
      if A = d + 24 then ans.extractLsb' 192 64
      else if A = d + 16 then ans.extractLsb' 128 64
      else if A = d + 8 then ans.extractLsb' 64 64
      else if A = d then ans.extractLsb' 0 64
      else s.getMem (BitVec.ofNat 64 A) := by
  rw [writeHash_getMem, hd]
  simp only [show (8 : Word) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat,
    ofNat_eq_iff hA (by omega : d + 8 + 8 + 8 < 2 ^ 64), ofNat_eq_iff hA (by omega : d + 8 + 8 < 2 ^ 64),
    ofNat_eq_iff hA (by omega : d + 8 < 2 ^ 64), ofNat_eq_iff hA (by omega : d < 2 ^ 64)]

theorem writeWords_regs : ∀ (ws : List Word) (s : MachineState) (base : Word),
    (s.writeWords base ws).regs = s.regs ∧ (s.writeWords base ws).pc = s.pc
  | [], _, _ => ⟨rfl, rfl⟩
  | w :: ws, s, base => by
    simp only [MachineState.writeWords]
    obtain ⟨h1, h2⟩ := writeWords_regs ws (s.setMem base w) (base + 8)
    exact ⟨h1.trans rfl, h2.trans rfl⟩

@[simp] theorem writeHash_getReg (s : MachineState) (ans : BitVec 256) (r : Reg) :
    (writeHash s ans).getReg r = s.getReg r := by
  unfold writeHash
  have := (writeWords_regs [ans.extractLsb' 0 64, ans.extractLsb' 64 64, ans.extractLsb' 128 64,
    ans.extractLsb' 192 64] s (s.getReg .x12)).1
  have h : ((s.writeWords (s.getReg .x12) [ans.extractLsb' 0 64, ans.extractLsb' 64 64,
    ans.extractLsb' 128 64, ans.extractLsb' 192 64]).setPC (s.pc + 4)).regs = s.regs := this
  unfold MachineState.getReg
  split
  · rfl
  · exact congrFun h _

@[simp] theorem writeHash_pc (s : MachineState) (ans : BitVec 256) :
    (writeHash s ans).pc = s.pc + 4 := by
  unfold writeHash; rfl

/-! ## The global invariant -/

def M1w : Word := 0x71c71c71c71c71c7#64
def M2w : Word := 0xf03f03f03f03f03f#64

/-- Registers that are constant after the prologue. -/
def globK : List (Reg × Word) :=
  [(.x5, 0), (.x6, 1 <<< 61), (.x7, 2 <<< 61), (.x8, 3 <<< 61), (.x9, 4 <<< 61),
   (.x13, 5 <<< 61), (.x14, 6 <<< 61), (.x15, 7 <<< 61), (.x18, 0x800), (.x19, 0x1000),
   (.x20, 0x1800), (.x21, 0x2000), (.x26, M1w), (.x27, M2w)]

/-- The `P` slots (`+16 .. +32`) of the hash buffers DB, CB, EB, NB, RB2, LB. -/
def pSlots : List Nat := [0x10, 0x18, 0xD0, 0xD8, 0x110, 0x118, 0x1D0, 0x1D8, 0x230, 0x238,
  0x350, 0x358]

def WitOK (wl : List Byte) (s : MachineState) : Prop :=
  ∀ j, j < 970 → s.getMem (BitVec.ofNat 64 (0x800 + 8 * j)) = w64 (slice wl (8 * j) 8)

def PkOK (pk : List Byte) (s : MachineState) : Prop :=
  s.getMem 0xA0 = w64 (pk.take 8) ∧ s.getMem 0xA8 = w64 (pk.drop 8)

def PZero (s : MachineState) : Prop := ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0

def Glob (wl pk : List Byte) (s : MachineState) : Prop :=
  (∀ p ∈ globK, s.getReg p.1 = p.2) ∧ WitOK wl s ∧ PkOK pk s ∧ PZero s

/-- A doubleword address that no block may write. -/
def safeAddr (n : Nat) : Bool :=
  decide (n + 8 ≤ 0x800) && !(pSlots.contains n) && n != 0xA0 && n != 0xA8

def memOK (ws : SymMem) : Bool :=
  ws.all fun p => p.1.base.isNone && safeAddr p.1.off.toNat

def regsOK (rf : RegFile) : Bool := globK.all fun p => E.beq (rf.get p.1) (.c p.2)

def safeDest (d : Nat) : Bool :=
  decide (d % 8 = 0) && decide (d + 32 ≤ 0x800) && pSlots.all (fun q => decide (q + 8 ≤ d ∨ d + 32 ≤ q)) &&
    decide (0xA8 + 8 ≤ d ∨ d + 32 ≤ 0xA0)

theorem memOK_ne {ws : SymMem} (h : memOK ws = true) (s : MachineState) (A : Nat)
    (hA : A < 2 ^ 64) (hprot : 0x800 ≤ A ∨ A ∈ pSlots ∨ A = 0xA0 ∨ A = 0xA8) :
    ∀ p ∈ ws, BitVec.ofNat 64 A ≠ p.1.eval s := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  obtain ⟨⟨_ | b, off⟩, v⟩ := p
  · simp only [Option.isNone_none, Bool.true_and, safeAddr, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', bne_iff_ne, ne_eq] at this
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := this
    simp only [Addr.eval]
    intro heq
    have hoff : off.toNat = A := by
      rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
    rw [hoff] at h1 h2 h3 h4
    rcases hprot with h | h | h | h
    · omega
    · simp [List.contains_iff_mem, h] at h2
    · exact h3 h
    · exact h4 h
  · simp at this

theorem Glob_toState {wl pk : List Byte} {s : MachineState} (hG : Glob wl pk s) (σ : SymState)
    (pc : Word) (hm : memOK σ.mem = true) (hr : regsOK σ.regs = true) :
    Glob wl pk (σ.toState s pc) := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  have fr : ∀ A, A < 2 ^ 64 → (0x800 ≤ A ∨ A ∈ pSlots ∨ A = 0xA0 ∨ A = 0xA8) →
      (σ.toState s pc).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hp
    rw [SymState.toState_getMem]
    exact memEval_frame s _ _ (memOK_ne hm s A hA hp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    have := List.all_eq_true.mp hr p hp
    rw [SymState.toState_getReg, E.beq_eq this]; rfl
  · intro j hj
    rw [fr _ (by omega) (Or.inl (by omega))]; exact h2 j hj
  · exact ⟨(fr 0xA0 (by omega) (by simp)).trans h3.1, (fr 0xA8 (by omega) (by simp)).trans h3.2⟩
  · intro a ha
    have : a < 2 ^ 64 := by simp [pSlots] at ha; omega
    rw [fr a this (Or.inr (Or.inl ha))]; exact h4 a ha

theorem Glob_writeHash {wl pk : List Byte} {s : MachineState} (hG : Glob wl pk s)
    (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d)
    (hsafe : safeDest d = true) : Glob wl pk (writeHash s ans) := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  simp only [safeDest, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsafe
  obtain ⟨⟨⟨-, hd1⟩, hd2⟩, hd3⟩ := hsafe
  have fr : ∀ A, A < 2 ^ 64 → (A + 8 ≤ d ∨ d + 32 ≤ A) →
      (writeHash s ans).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hp
    rw [writeHash_getMem_ofNat s ans d A hd hA (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp; rw [writeHash_getReg]; exact h1 p hp
  · intro j hj; rw [fr _ (by omega) (Or.inr (by omega))]; exact h2 j hj
  · exact ⟨(fr 0xA0 (by omega) (by omega)).trans h3.1, (fr 0xA8 (by omega) (by omega)).trans h3.2⟩
  · intro a ha
    have := hd2 a ha
    have : a < 2 ^ 64 := by simp [pSlots] at ha; omega
    rw [fr a this (by omega)]; exact h4 a ha

end SigGolfCandidate.Verify
