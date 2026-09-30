import SigGolfCandidate.Verify.FoldRuns

/-! # Chains (JALR dispatch tables): expected symbolic results -/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def tget (tab : List (List Nat)) (lay i : Nat) : Nat := (tab.getD lay []).getD i 0

def s1Pc (lay i : Nat) : Nat := tget s1Tab lay i
def nextPc' (lay i : Nat) : Nat := tget nextTab lay i
def tabAddr (lay i : Nat) : Nat := tget tabTab lay i
def bVal (lay i : Nat) : Nat := tget bTab lay i
def hasLui (lay i : Nat) : Bool := (luiTab.getD lay []).getD i false

/-- B at the checkpoint of chain `i`. -/
def bIn (lay i : Nat) : Nat := if i = 0 then bVal lay 0 else bVal lay (i - 1)

/-- Chain kinds: pair-first chains (with a dispatch prep), pair-second, singles. -/
def isSingle (i : Nat) : Bool := i = 20 || i = 41
def isFirst (i : Nat) : Bool := !isSingle i && (i % 21) % 2 = 0
/-- The chain's segment starts with a dispatch prep (not for chain 0: prep in the layer code). -/
def hasPrep (i : Nat) : Bool := i ≠ 0 && (isFirst i || isSingle i)

def hWord (lay : Nat) : Nat := 0x101 + 65536 * lay
def h3Word (lay : Nat) : Nat := 0x301 + 65536 * lay + 2 ^ 32

def chK (lay a2 : Nat) : List (Reg × Word) :=
  gkL ++ [(.x26, BitVec.ofNat 64 (h3Word lay)), (.x27, BitVec.ofNat 64 (hWord lay)), (.x10, 0xC0),
    (.x11, 64), (.x12, BitVec.ofNat 64 a2)]

def headK (lay i : Nat) : List (Reg × Word) := chK lay 0xE0 ++ [(.x15, BitVec.ofNat 64 (bIn lay i))]

def dReg (i : Nat) : Reg := if i < 21 then .x16 else .x17

/-- The dispatch register value computed by the prep of chain `i` (`r = i mod 21`). -/
def maskE (i : Nat) : E :=
  if isSingle i then mkBin .sll (mkBin .srl (.reg (dReg i)) (cw 60)) (cw 4)
  else if i % 21 = 0 then mkBin .and (mkBin .sll (.reg (dReg i)) (cw 4)) (cw 0x3F0)
  else mkBin .and (mkBin .srl (.reg (dReg i)) (cw (3 * (i % 21) - 4))) (cw 0x3F0)

def rE (lay i : Nat) : E := mkBin .add (maskE i) (cw (bVal lay i))

def chainAddr (lay i : Nat) : Nat := 0x800 + 2480 + 752 * lay + 16 * i

/-- Head of chain `i`: (lui) (prep) `ld; ld; jalr`, stopping at the symbolic target. -/
def headExp (lay i : Nat) : PRes :=
  let wa := chainAddr lay i
  let rf0 := RegFile.withKnown (headK lay i)
  let rf1 := if hasPrep i && hasLui lay i then rf0.set .x15 (cw (bVal lay i)) else rf0
  let rf2 := if hasPrep i then rf1.set .x14 (rE lay i) else rf1
  let rcur : E := if hasPrep i then rE lay i else .reg .x14
  let n := 3 + (if hasPrep i then 3 else 0) + (if hasPrep i && hasLui lay i then 1 else 0)
  ⟨⟨(rf2.set .x1 (ldE wa)).set .x2 (ldE (wa + 8)), [], []⟩, 0, false, n, n, [],
    some (mkBin .and (mkAdd rcur (.c (BitVec.ofNat 64 (tabAddr lay i) - BitVec.ofNat 64 (bVal lay i))))
      (.c (~~~1#64)))⟩

/-- Table entry of chain `i` for its digit `d`. -/
def entryExp (lay i d : Nat) : PRes :=
  let dst := if d < 7 then 0xE0 else 0x360 + 16 * i
  let tgt := if d < 7 then s1Pc lay i + 5 * d else nextPc' lay i
  ⟨⟨RegFile.init,
    [(⟨none, BitVec.ofNat 64 (dst + 8)⟩, .reg .x2), (⟨none, BitVec.ofNat 64 dst⟩, .reg .x1)], []⟩,
    pcOf tgt, false, 3, 3, [], none⟩

def stopsOf (lay i : Nat) : List Nat := (List.range 7).map (fun m => s1Pc lay i + 5 * m) ++ [nextPc' lay i]

/-- Step `mu ∈ 1..7`, from its label to its ecall. -/
def stepExp (lay i mu : Nat) : PRes :=
  let p := 8 * i + mu - 1
  let st := s1Pc lay i + 5 * (mu - 1)
  if mu = 7 then
    ⟨⟨((RegFile.withKnown (chK lay 0xE0)).set .x4 (cw p)).set .x12 (cw (0x360 + 16 * i)),
      [(⟨none, BitVec.ofNat 64 0xC0⟩, stW 0xC0 (cw p))], []⟩, pcOf (st + 3), true, 3, 3, [], none⟩
  else
    ⟨⟨(RegFile.withKnown (chK lay 0xE0)).set .x4 (cw p),
      [(⟨none, BitVec.ofNat 64 0xC0⟩, stW 0xC0 (cw p))], []⟩, pcOf (st + 2), true, 2, 2, [], none⟩

/-- Tail of step `mu ∈ 1..6` (after its ecall): zero the pad. -/
def tailExp (lay i mu : Nat) : PRes :=
  ⟨⟨RegFile.withKnown (chK lay 0xE0),
    [(⟨none, BitVec.ofNat 64 0xF8⟩, .c 0), (⟨none, BitVec.ofNat 64 0xF0⟩, .c 0)], []⟩,
    pcOf (s1Pc lay i + 5 * mu), false, 2, 2, [], none⟩

/-- After the ecall of step 7: `addi a2, a0, 32`. -/
def endExp (lay i : Nat) : PRes :=
  ⟨⟨(RegFile.withKnown (chK lay (0x360 + 16 * i))).set .x12 (cw 0xE0), [], []⟩,
    pcOf (nextPc' lay i), false, 1, 1, [], none⟩

def ckeep : List Reg := [.x14, .x15, .x16, .x17, .x22, .x23, .x30, .x31]

def okC (o : Option PRes) (e : PRes) (post : List (Reg × Word)) (keep : List Reg) : Bool :=
  optBeq o e && resOK gkL e && knownB post e && keepB keep e

def entryIdx (lay i e : Nat) : Nat := (tabAddr lay i - 0x1000) / 4 + 4 * e

def nEnt (i : Nat) : Nat := if isSingle i then 8 else 64

def entDigit (i e : Nat) : Nat := if isSingle i then e else if isFirst i then e % 8 else e / 8

def resBeq (a b : Result) : Bool :=
  SymState.beq a.st b.st && E.beq a.pc b.pc && decide (a.stop = b.stop) && a.steps == b.steps &&
    a.cycles == b.cycles

theorem resBeq_eq {a b : Result} (h : resBeq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := a; obtain ⟨b1, b2, b3, b4, b5⟩ := b
  simp only [resBeq, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  rw [SymState.beq_eq h1, E.beq_eq h2, h3, h4, h5]

/-- Table entry of chain `i` for its digit `d`, as a straight-line run ending at the `jal`. -/
def entryRes (lay i d : Nat) : Result :=
  let dst := if d < 7 then 0xE0 else 0x360 + 16 * i
  let tgt := if d < 7 then s1Pc lay i + 5 * d else nextPc' lay i
  ⟨⟨RegFile.init,
    [(⟨none, BitVec.ofNat 64 (dst + 8)⟩, .reg .x2), (⟨none, BitVec.ofNat 64 dst⟩, .reg .x1)], []⟩,
    .c (pcOf tgt), .jump, 3, 3⟩

/-- Check the entries `e, e+1, ...` of a table whose code (from entry `e`) is `ws`. -/
def entChk (lay i : Nat) : List (BitVec 32) → Nat → Nat → Bool
  | _, _, 0 => true
  | ws, e, n + 1 =>
    (match symRun cfg0 ws (pcOf (entryIdx lay i e)) 3 with
     | some r => resBeq r (entryRes lay i (entDigit i e))
     | none => false) && entChk lay i (ws.drop 4) (e + 1) n

def entriesCheck (lay i : Nat) : Bool := entChk lay i (codeFrom (entryIdx lay i 0)) 0 (nEnt i)

def stepsCheck (lay i : Nat) : Bool :=
  ((List.range 7).all fun m =>
    okC (runAt (chK lay 0xE0) [] (s1Pc lay i + 5 * m) []) (stepExp lay i (m + 1))
      (chK lay (if m = 6 then 0x360 + 16 * i else 0xE0)) ckeep) &&
  ((List.range 6).all fun m =>
    okC (runAt (chK lay 0xE0) [s1Pc lay i + 5 * (m + 1)] (s1Pc lay i + 5 * m + 3) [])
      (tailExp lay i (m + 1)) (chK lay 0xE0) ckeep) &&
  okC (runAt (chK lay (0x360 + 16 * i)) [nextPc' lay i] (s1Pc lay i + 34) []) (endExp lay i)
    (chK lay 0xE0) ckeep

def headKeep (i : Nat) : List Reg :=
  [.x16, .x17, .x22, .x23, .x30, .x31] ++ (if hasPrep i then [] else [.x14])

def headCheck (lay i : Nat) : Bool :=
  (i == 0 || okC (runAt (headK lay i) [] (nextPc' lay (i - 1)) [.jmp]) (headExp lay i)
    (chK lay 0xE0 ++ [(.x15, BitVec.ofNat 64 (bVal lay i))]) (headKeep i))

def chainCheck (lay i : Nat) : Bool := headCheck lay i && stepsCheck lay i && entriesCheck lay i

end SigGolfCandidate.Verify
