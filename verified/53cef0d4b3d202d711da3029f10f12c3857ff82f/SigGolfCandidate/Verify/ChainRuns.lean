import SigGolfCandidate.Verify.Post
import SigGolfCandidate.Verify.Tab

/-! # Chain blocks: expected symbolic results, checked by the kernel for all 294 chains -/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def cw (n : Nat) : E := .c (BitVec.ofNat 64 n)

def head (lay i : Nat) : Nat := (headTab.getD lay []).getD i 0
def nextHead (lay i : Nat) : Nat := if i < 41 then head lay (i + 1) else leafTab.getD lay 0
def grp (i : Nat) : Nat := if i = 13 ∨ i = 27 ∨ i = 41 then 1 else 0

/-- Witness address of chain value `i` of layer `lay`. -/
def chainAddr (lay i : Nat) : Nat := 0x800 + 2480 + 752 * lay + 16 * i

def chainK (a2 : Nat) : List (Reg × Word) :=
  globK ++ [(.x10, 0xC0), (.x11, 64), (.x12, BitVec.ofNat 64 a2)]

def kRegs (a2 : Nat) : RegFile := RegFile.withKnown (chainK a2)

def stMerge (p : Nat) : E := .bin (.st .w 4) (.ld (cw 0xC0)) (cw p)

/-- Step `mu ∈ 2..7` of chain `i` (from the tail of step `mu - 1`). -/
def stepExp (i h mu : Nat) : PRes :=
  if mu = 7 then
    ⟨⟨((kRegs 0xE0).set .x4 (cw (8 * i + 6))).set .x12 (cw (0x360 + 16 * i)),
      [(⟨none, 0xC0⟩, stMerge (8 * i + 6)), (⟨none, 0xF8⟩, .c 0), (⟨none, 0xF0⟩, .c 0)], []⟩,
      pcOf (h + 43), true, 5, 5, []⟩
  else
    ⟨⟨(kRegs 0xE0).set .x4 (cw (8 * i + mu - 1)),
      [(⟨none, 0xC0⟩, stMerge (8 * i + mu - 1)), (⟨none, 0xF8⟩, .c 0), (⟨none, 0xF0⟩, .c 0)], []⟩,
      pcOf (h + 5 * mu + 7), true, 4, 4, []⟩

def stepStart (h mu : Nat) : Nat := h + 5 * mu + 3

/-- The end of a chain (after the ecall of step 7). -/
def endExp (i h nx : Nat) : PRes :=
  ⟨⟨(kRegs (0x360 + 16 * i)).set .x12 (cw 0xE0), [], []⟩, pcOf nx, false, 1 + grp i, 1 + grp i, []⟩

def dirsOf : Nat → List Bool
  | 0 => [false, false, false, false, false]
  | 1 => [false, false, false, false, true]
  | 2 => [false, false, false, true]
  | 3 => [false, false, true]
  | 4 => [false, true, false, false]
  | 5 => [false, true, false, true]
  | 6 => [false, true, true]
  | _ => [true]

def digReg (i : Nat) : Reg := if i < 21 then .x16 else .x17

def tExp (i : Nat) : E := .bin .sll (.reg (digReg i)) (cw (61 - 3 * (i % 21)))

def brK (i k : Nat) (d : Bool) : Br := ⟨.geu, tExp i, .c (BitVec.ofNat 64 k <<< 61), d⟩

def brsOf (i : Nat) : Nat → List Br
  | 0 => [brK i 1 false, brK i 2 false, brK i 3 false, brK i 4 false, brK i 7 false]
  | 1 => [brK i 1 true, brK i 2 false, brK i 3 false, brK i 4 false, brK i 7 false]
  | 2 => [brK i 2 true, brK i 3 false, brK i 4 false, brK i 7 false]
  | 3 => [brK i 3 true, brK i 4 false, brK i 7 false]
  | 4 => [brK i 5 false, brK i 6 false, brK i 4 true, brK i 7 false]
  | 5 => [brK i 5 true, brK i 6 false, brK i 4 true, brK i 7 false]
  | 6 => [brK i 6 true, brK i 4 true, brK i 7 false]
  | _ => [brK i 7 true]

def headRegs (lay i : Nat) : RegFile :=
  (((kRegs 0xE0).set .x1 (.ld (cw (chainAddr lay i)))).set .x2
    (.ld (cw (chainAddr lay i + 8)))).set .x3 (tExp i)

/-- Chain head with digit `x`: to the first step's ecall (`x < 7`) or the next chain (`x = 7`). -/
def dispExp (lay i h nx x : Nat) : PRes :=
  let wa := chainAddr lay i
  if x = 7 then
    ⟨⟨headRegs lay i,
      [(⟨none, BitVec.ofNat 64 (0x368 + 16 * i)⟩, .ld (cw (wa + 8))),
       (⟨none, BitVec.ofNat 64 (0x360 + 16 * i)⟩, .ld (cw wa)),
       (⟨none, 0xE8⟩, .ld (cw (wa + 8))), (⟨none, 0xE0⟩, .ld (cw wa))], []⟩,
      pcOf nx, false, 10 + grp i, 10 + grp i, brsOf i 7⟩
  else if x = 6 then
    ⟨⟨((headRegs lay i).set .x4 (cw (8 * i + 6))).set .x12 (cw (0x360 + 16 * i)),
      [(⟨none, 0xC0⟩, stMerge (8 * i + 6)), (⟨none, 0xE8⟩, .ld (cw (wa + 8))),
       (⟨none, 0xE0⟩, .ld (cw wa))], []⟩,
      pcOf (h + 43), true, 13, 13, brsOf i 6⟩
  else
    ⟨⟨(headRegs lay i).set .x4 (cw (8 * i + x)),
      [(⟨none, 0xC0⟩, stMerge (8 * i + x)), (⟨none, 0xE8⟩, .ld (cw (wa + 8))),
       (⟨none, 0xE0⟩, .ld (cw wa))], []⟩,
      pcOf (h + 12 + 5 * x), true, 12, 12, brsOf i x⟩

def layRegs : List Reg := [.x16, .x17, .x22, .x23, .x30, .x31]

/-- A run is as expected, side-condition free, and ends with the given known registers. -/
def okRun (o : Option PRes) (e : PRes) (post : List (Reg × Word)) : Bool :=
  optBeq o e && resOK e && knownB post e && keepB layRegs e

def chainCheck (lay i : Nat) : Bool :=
  let h := head lay i
  let nx := nextHead lay i
  ((List.range 6).all fun m =>
    let mu := m + 2
    okRun (runAt (chainK 0xE0) [] (stepStart h mu) []) (stepExp i h mu)
      (chainK (if mu = 7 then 0x360 + 16 * i else 0xE0))) &&
  okRun (runAt (chainK (0x360 + 16 * i)) [nx] (h + 44) []) (endExp i h nx) (chainK 0xE0) &&
  ((List.range 8).all fun x => okRun (runAt (chainK 0xE0) [nx] h (dirsOf x)) (dispExp lay i h nx x)
    (chainK (if x = 6 then 0x360 + 16 * i else 0xE0)))


end SigGolfCandidate.Verify
