import SigGolfCandidate.Verify.Post
import SigGolfCandidate.Verify.Tab

/-! # Merkle fold levels: expected symbolic results, checked for all 174 levels -/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def cwf (n : Nat) : E := .c (BitVec.ofNat 64 n)

def foldK (a2 : Nat) : List (Reg × Word) :=
  globK ++ [(.x10, 0x1C0), (.x11, 64), (.x12, BitVec.ofNat 64 a2)]

def foldPc (base lam : Nat) : Nat := base + 13 * lam - (if 4 ≤ lam then 1 else 0)

/-- `x3` after a non-final level `lam` (the next slot bit). -/
def gpE (b : Nat) : E :=
  if b = 4 then .bin .and (.reg .x23) (cwf 16) else .bin .and (.bin .srl (.reg .x24) (cwf b)) (cwf 16)

def stW (a : Nat) (v : E) : E := .bin (.st .w 4) (.ld (cwf a)) v

/-- Fold level `lam` of `h`, current node in slot `a2 = 0x1E0 + 16 bit`, sibling at witness
address `wa`, final destination `dst`. -/
def foldExp (base h lam bit wa dst : Nat) : PRes :=
  let a2 := 0x1E0 + 16 * bit
  let sib := 0x1F0 - 16 * bit
  let rf := ((RegFile.withKnown (foldK a2)).set .x1 (.ld (cwf wa))).set .x2 (.ld (cwf (wa + 8)))
  let mb := [(⟨none, BitVec.ofNat 64 (sib + 8)⟩, .ld (cwf (wa + 8))), (⟨none, BitVec.ofNat 64 sib⟩, .ld (cwf wa))]
  if lam + 1 = h then
    ⟨⟨((rf.set .x3 (cwf sib)).set .x4 (cwf (lam + 1))).set .x12 (cwf dst),
      [(⟨none, 0x1C8⟩, stW 0x1C8 (cwf 0)), (⟨none, 0x1C0⟩, stW 0x1C0 (cwf (lam + 1)))] ++ mb, []⟩,
      pcOf (foldPc base lam + 9), true, 9, 9, []⟩
  else
    ⟨⟨((rf.set .x3 (gpE (lam + 1))).set .x4 (.bin .srl (.reg .x23) (cwf (lam + 1)))).set .x12
        (.bin .add (gpE (lam + 1)) (cwf 480)),
      [(⟨none, 0x1C8⟩, stW 0x1C8 (.bin .srl (.reg .x23) (cwf (lam + 1)))),
       (⟨none, 0x1C0⟩, stW 0x1C0 (cwf (lam + 1)))] ++ mb, []⟩,
      pcOf (foldPc base (lam + 1) - 1), true, if lam = 3 then 11 else 12,
      if lam = 3 then 11 else 12, []⟩

def keepRegs : List Reg :=
  [.x16, .x17, .x22, .x23, .x24, .x25, .x28, .x29, .x30, .x31]

def okFold (o : Option PRes) (e : PRes) (post : List (Reg × Word)) : Bool :=
  optBeq o e && resOK e && knownB post e && keepB keepRegs e

def foldPost (h lam : Nat) (dst : Nat) (b : Nat) : List (Reg × Word) :=
  if lam + 1 = h then globK ++ [(.x10, 0x1C0), (.x11, 64), (.x12, BitVec.ofNat 64 dst)]
  else globK ++ [(.x10, 0x1C0), (.x11, 64)]

/-- All levels of one fold (`h` levels starting at `base`, siblings at witness address `wa0`). -/
def foldCheck (base h wa0 dst : Nat) : Bool :=
  (List.range h).all fun lam => (List.range 2).all fun b =>
    okFold (runAt (foldK (0x1E0 + 16 * b)) [] (foldPc base lam) [])
      (foldExp base h lam b (wa0 + 16 * lam) dst) (foldPost h lam dst b)



end SigGolfCandidate.Verify
