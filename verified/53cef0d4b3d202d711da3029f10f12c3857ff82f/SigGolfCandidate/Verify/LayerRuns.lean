import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.FoldRuns

/-! # Layer blocks (route + encoding, encoding check, leaf, fold setup): expected results -/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def layS (lay : Nat) : Nat := [29, 24, 19, 14, 9, 4, 0].getD lay 0
def layH (lay : Nat) : Nat := if lay = 6 then 4 else 5

def layerPc (lay : Nat) : Nat := layerTab.getD lay 0
def leafPc (lay : Nat) : Nat := leafTab.getD lay 0
def layFoldPc (lay : Nat) : Nat := layFoldTab.getD lay 0

def ldE (a : Nat) : E := .ld (cw a)

def uE (lay : Nat) : E :=
  if lay = 6 then .bin .and (.reg .x22) (cw 15)
  else .bin .and (.bin .srl (.reg .x22) (cw (layS lay))) (cw (2 ^ layH lay - 1))
def tauE (lay : Nat) : E := .bin .srl (.reg .x22) (cw (layS lay + layH lay))
def x31E (lay : Nat) : E := .bin .or (tauE lay) (.bin .sll (uE lay) (cw 32))
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * (lay % 2))) (ldE (0x2630 + 8 * (lay / 2)))

def encSteps (lay : Nat) : Nat := (if lay = 6 then 4 else 5) + (if lay = 0 then 1 else 2) + 9

def stW0 (a : Nat) (v : E) : E := .bin (.st .w 0) (ldE a) v

def encExp (lay : Nat) : PRes :=
  ⟨⟨(((((((RegFile.withKnown globK).set .x3 (ctrE lay)).set .x10 (cw 0x100)).set .x11 (cw 64)).set
      .x12 (cw 0x140)).set .x23 (uE lay)).set .x30 (tauE lay)).set .x31 (x31E lay),
    [(⟨none, BitVec.ofNat 64 0x138⟩, .c 0),
     (⟨none, BitVec.ofNat 64 0x130⟩, .bin (.st .w 4) (stW0 0x130 (ctrE lay)) (.c 0)),
     (⟨none, BitVec.ofNat 64 0x108⟩, x31E lay),
     (⟨none, BitVec.ofNat 64 0x100⟩, cw (0x401 + 65536 * lay))], []⟩,
   pcOf (layerPc lay + encSteps lay), true, encSteps lay, encSteps lay, []⟩

def encK : List (Reg × Word) := globK ++ [(.x10, 0x100), (.x11, 64), (.x12, 0x140)]

/-! ## The encoding check -/

def d0E : E := ldE 0x140
def d1E : E := ldE 0x148
def m1E : E := cw 0x71c71c71c71c71c7
def m2E : E := cw 0xf03f03f03f03f03f

def swRa4 : E :=
  let ra1 := E.bin .add (.bin .and (.bin .srl d0E (cw 3)) m1E) (.bin .and d0E m1E)
  let ra2 := E.bin .add ra1 (.bin .and (.bin .srl d1E (cw 3)) m1E)
  let ra3 := E.bin .add ra2 (.bin .and d1E m1E)
  E.bin .add ra3 (.bin .srl ra3 (cw 6))
def swRa7 : E :=
  let ra5 := E.bin .and swRa4 m2E
  let ra6 := E.bin .add ra5 (.bin .srl ra5 (cw 12))
  E.bin .add ra6 (.bin .srl ra6 (cw 24))
def swX28 : E := .bin .srl swRa7 (cw 48)
def swX25 : E := .bin .add (.bin .and (.bin .add swRa7 swX28) (cw 2047)) (cw (2 ^ 64 - 170))
def orE : E := .bin .or d0E d1E

def encPostPc (lay : Nat) : Nat := layerPc lay + encSteps lay + 1
def encPostSteps (lay : Nat) : Nat := 25 + (if lay = 0 then 5 else 6)

/-- The valid case: through the check and the chain setup to the first chain. -/
def encOkExp (lay : Nat) : PRes :=
  ⟨⟨(((((((RegFile.withKnown encK).set .x3 (cw (0x101 + 65536 * lay))).set .x10 (cw 0xC0)).set
      .x12 (cw 0xE0)).set .x16 d0E).set .x17 d1E).set .x25 swX25).set .x28 swX28,
    [(⟨none, BitVec.ofNat 64 0xC8⟩, .reg .x31),
     (⟨none, BitVec.ofNat 64 0xC0⟩, stW0 0xC0 (cw (0x101 + 65536 * lay)))], []⟩,
   pcOf (head lay 0), false, encPostSteps lay, encPostSteps lay,
   [⟨.ne, swX25, .c 0, false⟩, ⟨.lt, orE, .c 0, false⟩]⟩

def encRej1Exp : PRes :=
  ⟨⟨(((((RegFile.withKnown encK).set .x3 orE).set .x5 (cw 1)).set .x10 (cw 1)).set .x16 d0E).set
      .x17 d1E, [], []⟩, pcOf 69, true, 7, 7, [⟨.lt, orE, .c 0, true⟩]⟩

def encRej2Exp : PRes :=
  ⟨⟨(((((((RegFile.withKnown encK).set .x3 orE).set .x5 (cw 1)).set .x10 (cw 1)).set .x16 d0E).set
      .x17 d1E).set .x25 swX25).set .x28 swX28, [], []⟩, pcOf 69, true, 28, 28,
   [⟨.ne, swX25, .c 0, true⟩, ⟨.lt, orE, .c 0, false⟩]⟩

/-! ## Leaf and fold setup -/

def leafSteps (lay : Nat) : Nat := if lay = 0 then 8 else 9

def gpLeaf : E := .bin .and (.bin .sll (.reg .x23) (cw 4)) (cw 16)

def leafExp (lay : Nat) : PRes :=
  ⟨⟨(((((kRegs 0xE0).set .x3 gpLeaf).set .x10 (cw 0x340)).set .x11 (cw 704)).set .x12
      (.bin .add gpLeaf (cw 480))).set .x24 (.bin .sll (.reg .x23) (cw 4)),
    [(⟨none, BitVec.ofNat 64 0x348⟩, .reg .x31), (⟨none, BitVec.ofNat 64 0x340⟩, cw (0x201 + 65536 * lay))], []⟩,
   pcOf (leafPc lay + leafSteps lay), true, leafSteps lay, leafSteps lay, []⟩

def leafK : List (Reg × Word) := globK ++ [(.x10, 0x340), (.x11, 704)]

def fsetupExp (lay : Nat) : PRes :=
  ⟨⟨(((RegFile.withKnown leafK).set .x3 (cw (0x301 + 65536 * lay))).set .x10 (cw 0x1C0)).set .x11 (cw 64),
    [(⟨none, BitVec.ofNat 64 0x1C8⟩, stW0 0x1C8 (.reg .x30)),
     (⟨none, BitVec.ofNat 64 0x1C0⟩, stW0 0x1C0 (cw (0x301 + 65536 * lay)))], []⟩,
   pcOf (layFoldPc lay), false, leafSteps lay - 3, leafSteps lay - 3, []⟩

def okRunK (o : Option PRes) (e : PRes) (post : List (Reg × Word)) (keep : List Reg) : Bool :=
  optBeq o e && resOK e && knownB post e && keepB keep e

def layerCheck (lay : Nat) : Bool :=
  okRunK (runAt globK [] (layerPc lay) []) (encExp lay) encK [.x22] &&
  okRunK (runAt encK [head lay 0] (encPostPc lay) [false, false]) (encOkExp lay) (chainK 0xE0)
    [.x22, .x23, .x30, .x31] &&
  optBeq (runAt encK [head lay 0] (encPostPc lay) [true]) encRej1Exp &&
  optBeq (runAt encK [head lay 0] (encPostPc lay) [false, true]) encRej2Exp &&
  okRun (runAt (chainK 0xE0) [] (leafPc lay) []) (leafExp lay) leafK &&
  okFold (runAt leafK [layFoldPc lay] (leafPc lay + leafSteps lay + 1) []) (fsetupExp lay)
    (globK ++ [(.x10, 0x1C0), (.x11, 64)])



set_option maxRecDepth 100000 in
theorem layerCheck_all : ((List.range 7).all layerCheck) = true := by decide +kernel

end SigGolfCandidate.Verify
