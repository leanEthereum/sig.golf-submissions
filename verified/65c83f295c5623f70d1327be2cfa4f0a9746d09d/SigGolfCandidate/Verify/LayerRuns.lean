import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.Spec

/-! # Layer blocks: precode (route, encoding, check, chain-0 dispatch), leaf, compare -/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def heightL (lay : Nat) : Nat := if lay = 6 then 4 else 5

/-- Start of the precode of layer `lay` in stream `t`: after the roots hash (layer 6) or after the
last fold hash of layer `lay + 1`. -/
def rootsStart (t : Nat) : Nat := lvlPc 1 t 60 9 + 8
def preStart (lay t : Nat) : Nat :=
  if lay = 6 then rootsStart t + 6 else lvlPc (7 - lay) t 0 (heightL (lay + 1) - 1) + 8
def stepsA (lay : Nat) : Nat := if lay = 6 then 29 else 14
def encPc (lay t : Nat) : Nat := preStart lay t + stepsA lay

/-- Known registers at the precode start. -/
def a6K : List (Reg × Word) := gkF ++ [(.x10, 544), (.x11, 256), (.x12, 224)]
def aK (lay : Nat) : List (Reg × Word) :=
  gkL ++ [(.x10, 0x1C0), (.x11, 64), (.x12, 0xE0), (.x26, BitVec.ofNat 64 (h3Word (lay + 1))),
    (.x27, BitVec.ofNat 64 (hWord (lay + 1))), (.x15, BitVec.ofNat 64 (bVal (lay + 1) 41))]
def preK (lay : Nat) : List (Reg × Word) := if lay = 6 then a6K else aK lay

/-- Known registers after the encoding hash call. -/
def bK (lay : Nat) : List (Reg × Word) :=
  gkL ++ [(.x26, BitVec.ofNat 64 (h3Word lay)), (.x27, BitVec.ofNat 64 (hWord lay)), (.x10, 0xC0),
    (.x11, 64), (.x12, 0x140)] ++
    (if lay < 6 then [(.x15, BitVec.ofNat 64 (bVal (lay + 1) 41))] else [])

def uEr (lay : Nat) : E := if lay = 6 then .bin .and (.reg .x22) (cw 15) else .bin .and (.reg .x30) (cw 31)
def tauEr (lay : Nat) : E := if lay = 6 then .bin .srl (.reg .x22) (cw 4) else .bin .srl (.reg .x30) (cw 5)
def x31Er (lay : Nat) : E := .bin .add (tauEr lay) (.bin .sll (uEr lay) (cw 32))
def ctrE (lay : Nat) : E := .un (.ld .wu (4 * (lay % 2))) (ldE (0x2630 + 8 * (lay / 2)))

def specA (lay t : Nat) : Spec :=
  ⟨[(.x23, uEr lay), (.x30, tauEr lay), (.x31, x31Er lay)],
   [(⟨none, BitVec.ofNat 64 248⟩, .c 0), (⟨none, BitVec.ofNat 64 240⟩, ctrE lay),
    (⟨none, BitVec.ofNat 64 200⟩, x31Er lay), (⟨none, BitVec.ofNat 64 192⟩, cw (hWord lay + 768))],
   encPc lay t, true, stepsA lay, [], none⟩

/-! ## The encoding check (`slli 52; bne K170`) -/

def d0E : E := ldE 320
def d1E : E := ldE 328
def m1E : E := .c M1w
def m2E : E := .c M2w
def orE : E := .bin .or d0E d1E
def swA3 : E :=
  .bin .add (.bin .add (.bin .add (.bin .and (.bin .srl d0E (cw 3)) m1E) (.bin .and d0E m1E))
    (.bin .and (.bin .srl d1E (cw 3)) m1E)) (.bin .and d1E m1E)
def swA4 : E := .bin .add swA3 (.bin .srl swA3 (cw 6))
def swA5 : E := .bin .and swA4 m2E
def swA6 : E := .bin .add swA5 (.bin .srl swA5 (cw 12))
def swA7 : E := .bin .add swA6 (.bin .srl swA6 (cw 24))
def swS : E := .bin .sll (.bin .add swA7 (.bin .srl swA7 (cw 48))) (cw 52)

/-- The dispatch register of a site computed from the digit word `D`. -/
def maskD (i : Nat) (D : E) : E :=
  if isSingle i then mkBin .sll (mkBin .srl D (cw 60)) (cw 4)
  else if i % 21 = 0 then mkBin .and (mkBin .sll D (cw 4)) (cw 0x3F0)
  else mkBin .and (mkBin .srl D (cw (3 * (i % 21) - 4))) (cw 0x3F0)

def rE0 (lay : Nat) : E := mkBin .add (maskD 0 d0E) (cw (bVal lay 0))

def stepsB (lay : Nat) : Nat := if lay = 6 then 34 else 33

def specBok (lay t : Nat) : Spec :=
  ⟨[(.x1, ldE (chainAddr lay 0)), (.x2, ldE (chainAddr lay 0 + 8)), (.x14, rE0 lay),
    (.x15, cw (bVal lay 0)), (.x16, d0E), (.x17, d1E)],
   [(⟨none, BitVec.ofNat 64 240⟩, .c 0), (⟨none, BitVec.ofNat 64 192⟩, stW0 192 (cw (hWord lay)))],
   0, false, stepsB lay,
   [⟨.ne, swS, .c K170, false⟩, ⟨.lt, orE, .c 0, false⟩],
   some (mkBin .and (mkAdd (rE0 lay) (.c (BitVec.ofNat 64 (tabAddr lay 0) - BitVec.ofNat 64 (bVal lay 0))))
     (.c (~~~1#64)))⟩

def rejK : List (Reg × E) := [(.x5, cw 1), (.x10, cw 1)]

def specRej1 : Spec := ⟨rejK, [], 39, true, 7, [⟨.lt, orE, .c 0, true⟩], none⟩
def specRej2 : Spec := ⟨rejK, [], 39, true, 27, [⟨.ne, swS, .c K170, true⟩, ⟨.lt, orE, .c 0, false⟩], none⟩

/-! ## Leaf -/

def specLeaf (lay : Nat) (d : Bool) : Spec :=
  ⟨[(.x10, cw 832), (.x11, cw 704), (.x12, cw (480 + 16 * (if d then 1 else 0)))],
   [(⟨none, BitVec.ofNat 64 456⟩, stW0 456 (.reg .x30)), (⟨none, BitVec.ofNat 64 448⟩, cw (h3Word lay)),
    (⟨none, BitVec.ofNat 64 840⟩, .reg .x31), (⟨none, BitVec.ofNat 64 832⟩, cw (hWord lay + 256))],
   xPc (8 - lay) (if d then 1 else 0) 0 + 1, true, 10,
   [⟨.lt, .bin .sll (.reg .x23) (cw 63), .c 0, d⟩], none⟩

def leafKeep : List Reg := [.x16, .x17, .x22, .x23, .x30, .x31]
def leafPost (lay : Nat) : List (Reg × Word) :=
  fk false 0x340 704 ++ [(.x26, BitVec.ofNat 64 (h3Word lay)), (.x27, BitVec.ofNat 64 (hWord lay)),
    (.x15, BitVec.ofNat 64 (bVal lay 41))]

/-! ## Compare -/

def cmpPc (t : Nat) : Nat := compareTab.getD t 0
def cmpK : List (Reg × Word) := fk false 0x1C0 64 ++ [(.x12, 0x180)]
def specAcc (t : Nat) : Spec :=
  ⟨[(.x5, cw 1), (.x10, cw 0)], [], cmpPc t + 8, true, 8,
   [⟨.ne, ldE 392, ldE 168, false⟩, ⟨.ne, ldE 384, ldE 160, false⟩], none⟩
def specCR1 (t : Nat) : Spec :=
  ⟨rejK, [], cmpPc t + 11, true, 5, [⟨.ne, ldE 384, ldE 160, true⟩], none⟩
def specCR2 (t : Nat) : Spec :=
  ⟨rejK, [], cmpPc t + 11, true, 8, [⟨.ne, ldE 392, ldE 168, true⟩, ⟨.ne, ldE 384, ldE 160, false⟩], none⟩

/-! ## The per-layer check -/

def layerCheck (lay : Nat) : Bool :=
  ((List.range 2).all fun t =>
    specB gkL (runAt (preK lay) [] (preStart lay t) []) (specA lay t) (bK lay) [] &&
    specB gkL (runAt (bK lay) [] (encPc lay t + 1) [.br false, .br false, .jmp]) (specBok lay t)
      (chK lay 0xE0) [.x22, .x23, .x30, .x31] &&
    specB [] (runAt (bK lay) [] (encPc lay t + 1) [.br true]) specRej1 [] [] &&
    specB [] (runAt (bK lay) [] (encPc lay t + 1) [.br false, .br true]) specRej2 [] [] &&
    (lay != 0 || (specB [] (runAt cmpK [] (cmpPc t) [.br false, .br false]) (specAcc t) [] [] &&
      specB [] (runAt cmpK [] (cmpPc t) [.br true]) (specCR1 t) [] [] &&
      specB [] (runAt cmpK [] (cmpPc t) [.br false, .br true]) (specCR2 t) [] []))) &&
  ((List.range 2).all fun d =>
    specB gkL (runAt (headK lay 42) [] (nextPc' lay 41) [.br (d == 1)]) (specLeaf lay (d == 1))
      (leafPost lay) leafKeep)

end SigGolfCandidate.Verify
