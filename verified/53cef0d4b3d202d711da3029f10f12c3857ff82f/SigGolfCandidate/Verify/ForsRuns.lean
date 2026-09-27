import SigGolfCandidate.Verify.LayerRuns

/-! # FORS blocks (tree headers, fold setup, roots) and the prologue: expected results -/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def forsPc (k : Nat) : Nat := forsTab.getD k 0
def forsFoldPc (k : Nat) : Nat := forsFoldTab.getD k 0

/-- `u_k` from the digest words `w 0, w 1, w 2` (the generator's `u_extract`). -/
def uExprW (w : Nat → E) (k : Nat) : E :=
  let start := 34 + 10 * k
  let wi := start / 64
  let bit := start % 64
  if bit + 10 ≤ 64 then
    if bit = 0 then .bin .and (w wi) (cw 1023)
    else if bit + 10 = 64 then .bin .srl (w wi) (cw bit)
    else .bin .and (.bin .srl (w wi) (cw bit)) (cw 1023)
  else .bin .or (.bin .sll (.bin .and (w (wi + 1)) (cw (2 ^ (bit - 54) - 1))) (cw (64 - bit)))
    (.bin .srl (w wi) (cw bit))

def uSteps (k : Nat) : Nat :=
  let bit := (34 + 10 * k) % 64
  if bit + 10 ≤ 64 then (if bit = 0 ∨ bit + 10 = 64 then 1 else 2) else 4

def wRegE (i : Nat) : E := .reg (if i = 0 then .x16 else if i = 1 then .x17 else .x25)
def wLdE (i : Nat) : E := ldE (0x160 + 8 * i)

def uE' (k : Nat) : E := uExprW wRegE k
def gpF (u : E) : E := .bin .and (.bin .sll u (cw 4)) (cw 16)

def forsK : List (Reg × Word) := globK ++ [(.x11, 64)]

def headSteps (k : Nat) : Nat := 11 + uSteps k

/-- Tree `k ≥ 1`: from the `add FW` to the leaf hash. -/
def headExp (k : Nat) : PRes :=
  let sa := 0x800 + 16 + 176 * k
  let fw : E := .bin .add (.reg .x29) (.reg .x31)
  ⟨⟨(((((((((RegFile.withKnown forsK).set .x29 fw).set .x23 (uE' k)).set .x1 (ldE sa)).set .x2
      (ldE (sa + 8))).set .x24 (.bin .sll (uE' k) (cw 4))).set .x3 (gpF (uE' k))).set .x12
      (.bin .add (gpF (uE' k)) (cw 480))).set .x10 (cw 0xC0)),
    [(⟨none, BitVec.ofNat 64 0xE8⟩, ldE (sa + 8)), (⟨none, BitVec.ofNat 64 0xE0⟩, ldE sa),
     (⟨none, BitVec.ofNat 64 0xC8⟩, .bin (.st .w 4) (ldE 0xC8) (uE' k)),
     (⟨none, BitVec.ofNat 64 0xC0⟩, stW0 0xC0 fw)], []⟩,
   pcOf (forsPc k - 1 + headSteps k), true, headSteps k, headSteps k, []⟩

def forsLeafK : List (Reg × Word) := globK ++ [(.x10, 0xC0), (.x11, 64)]

def fsetupFExp (k : Nat) : PRes :=
  ⟨⟨((RegFile.withKnown forsLeafK).set .x10 (cw 0x1C0)).set .x3 (.bin .add (.reg .x29) (cw 256)),
    [(⟨none, BitVec.ofNat 64 0x1C0⟩, stW0 0x1C0 (.bin .add (.reg .x29) (cw 256)))], []⟩,
   pcOf (forsFoldPc k), false, 3, 3, []⟩

def forsKeep : List Reg := [.x16, .x17, .x22, .x25, .x31]

def forsCheck (k : Nat) : Bool :=
  (k == 0 || okRunK (runAt forsK [] (forsPc k - 1) []) (headExp k) forsLeafK forsKeep) &&
  okRunK (runAt forsLeafK [forsFoldPc k] (forsPc k - 1 + headSteps k + 1) []) (fsetupFExp k)
    (globK ++ [(.x10, 0x1C0), (.x11, 64)]) (forsKeep ++ [.x23, .x24, .x29])

set_option maxRecDepth 100000 in
theorem forsCheck_all : ((List.range 14).all forsCheck) = true := by decide +kernel

end SigGolfCandidate.Verify

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def rw0E : E := .bin .or (.bin .sll (.bin .srl (.reg .x22) (cw 32)) (cw 24)) (cw 2817)

def rootsExp : PRes :=
  ⟨⟨((((((RegFile.withKnown forsK).set .x29 (.bin .add (.reg .x29) (.reg .x31))).set .x3 rw0E).set
      .x28 (cw 2817)).set .x10 (cw 544)).set .x11 (cw 256)).set .x12 (cw 288),
    [(⟨none, BitVec.ofNat 64 544⟩, stW0 544 rw0E)], []⟩, pcOf 2095, true, 10, 10, []⟩

def dgK : List (Reg × Word) := globK ++ [(.x10, 0), (.x11, 128), (.x12, 0x160)]

def idxE : E := .bin .srl (.bin .sll (wLdE 0) (cw 30)) (cw 30)
def fw0E : E := .bin .or (.bin .sll (.bin .srl idxE (cw 32)) (cw 24)) (cw 2305)
def u0E : E := uExprW wLdE 0
def admE : E := .bin .srl (.bin .sll (wLdE 2) (cw 8)) (cw 54)

def dgOkExp : PRes :=
  ⟨⟨(((((((((((((((RegFile.withKnown dgK).set .x25 (wLdE 2)).set .x3 (gpF u0E)).set .x16 (wLdE 0)).set
      .x17 (wLdE 1)).set .x22 idxE).set .x28 (cw 2305)).set .x29 fw0E).set .x31 (cw 65536)).set .x11
      (cw 64)).set .x23 u0E).set .x1 (ldE 2064)).set .x2 (ldE 2072)).set .x24 (.bin .sll u0E (cw 4))).set
      .x12 (.bin .add (gpF u0E) (cw 480))).set .x10 (cw 192),
    [(⟨none, BitVec.ofNat 64 232⟩, ldE 2072), (⟨none, BitVec.ofNat 64 224⟩, ldE 2064),
     (⟨none, BitVec.ofNat 64 200⟩, .bin (.st .w 4) (stW0 200 idxE) u0E),
     (⟨none, BitVec.ofNat 64 192⟩, stW0 192 fw0E),
     (⟨none, BitVec.ofNat 64 552⟩, stW0 552 idxE), (⟨none, BitVec.ofNat 64 456⟩, stW0 456 idxE)], []⟩,
   pcOf 96, true, 30, 30, [⟨.eq, admE, .c 0, true⟩]⟩

def dgRejExp : PRes :=
  ⟨⟨((((RegFile.withKnown dgK).set .x25 (wLdE 2)).set .x3 admE).set .x5 (cw 1)).set .x10 (cw 1), [], []⟩,
   pcOf 69, true, 6, 6, [⟨.eq, admE, .c 0, false⟩]⟩

def ctrMask : Nat := 0x000FFFFF000FFFFF
def ctrOrE : E :=
  .bin .or (.bin .or (.bin .or (.bin .or (ldE 9776) (ldE 9784)) (ldE 9792)) (.un (.ld .wu 0) (ldE 9800)))
    (cw ctrMask)

/-- All registers except `x2` are zero in the initial state. -/
def k0 : List (Reg × Word) :=
  [(.x1, 0), (.x3, 0), (.x4, 0), (.x5, 0), (.x6, 0), (.x7, 0), (.x8, 0), (.x9, 0), (.x10, 0), (.x11, 0),
   (.x12, 0), (.x13, 0), (.x14, 0), (.x15, 0), (.x16, 0), (.x17, 0), (.x18, 0), (.x19, 0), (.x20, 0),
   (.x21, 0), (.x22, 0), (.x23, 0), (.x24, 0), (.x25, 0), (.x26, 0), (.x27, 0), (.x28, 0), (.x29, 0),
   (.x30, 0), (.x31, 0)]

def constRegs (rf : RegFile) : RegFile :=
  ((((((((((((((rf.set .x18 (cw 0x800)).set .x19 (cw 0x1000)).set .x20 (cw 0x1800)).set .x21 (cw 0x2000)).set
    .x6 (cw (1 * 2 ^ 61))).set .x7 (cw (2 * 2 ^ 61))).set .x8 (cw (3 * 2 ^ 61))).set .x9 (cw (4 * 2 ^ 61))).set
    .x13 (cw (5 * 2 ^ 61))).set .x14 (cw (6 * 2 ^ 61))).set .x15 (cw (7 * 2 ^ 61))).set .x26
    (cw 0x71c71c71c71c71c7)).set .x27 (cw 0xf03f03f03f03f03f)).set .x4 (cw ctrMask))

def startOkExp : PRes :=
  ⟨⟨(((((constRegs (RegFile.withKnown k0)).set .x3 (cw 3073)).set .x1 (ldE 2048)).set .x2 (ldE 2056)).set
      .x11 (cw 128)).set .x12 (cw 352),
    [(⟨none, BitVec.ofNat 64 40⟩, ldE 2056), (⟨none, BitVec.ofNat 64 32⟩, ldE 2048),
     (⟨none, BitVec.ofNat 64 0⟩, cw 3073)], []⟩,
   pcOf 62, true, 62, 62, [⟨.ne, ctrOrE, cw ctrMask, false⟩]⟩

def startRejExp : PRes :=
  ⟨⟨(((constRegs (RegFile.withKnown k0)).set .x3 ctrOrE).set .x5 (cw 1)).set .x10 (cw 1), [], []⟩,
   pcOf 69, true, 54, 54, [⟨.ne, ctrOrE, cw ctrMask, true⟩]⟩

theorem top_runs :
    runAt forsK [] 2085 [] = some rootsExp ∧ runAt dgK [] 63 [true] = some dgOkExp ∧
    runAt dgK [] 63 [false] = some dgRejExp ∧ runAt k0 [] 0 [false] = some startOkExp ∧
    runAt k0 [] 0 [true] = some startRejExp := by
  refine ⟨optBeq_eq ?_, optBeq_eq ?_, optBeq_eq ?_, optBeq_eq ?_, optBeq_eq ?_⟩ <;> decide +kernel

end SigGolfCandidate.Verify
