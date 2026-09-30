import SigGolfCandidate.Verify.Post
import SigGolfCandidate.Verify.Tab

/-! # Merkle fold levels (two-track regions): expected symbolic results -/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

def cw (n : Nat) : E := .c (BitVec.ofNat 64 n)
def ldE (a : Nat) : E := .ld (cw a)
def stW (a : Nat) (v : E) : E := .bin (.st .w 4) (ldE a) v
def stW0 (a : Nat) (v : E) : E := .bin (.st .w 0) (ldE a) v

/-- Layer heights (layer 0 = top) and witness offsets of the layer bodies (SPEC-v4). -/
def heightL (lay : Nat) : Nat := [11, 5, 5, 5, 4, 4].getD lay 0
def layBody (lay : Nat) : Nat := [2480, 3328, 4080, 4832, 5584, 6320].getD lay 0

/-- X-block pc `j` of stream `t` of region `rg`. -/
def xPc (rg t j : Nat) : Nat := ((xTab.getD rg []).getD t []).getD j 0

/-- Start of fold level `lam` (right after the ecall of X-block `j0 + lam`). -/
def lvlPc (rg t j0 lam : Nat) : Nat := xPc rg t (j0 + lam) + 2

/-- Known registers: FORS (`kind = true`) or layers. -/
def gkOf (kind : Bool) : List (Reg × Word) := if kind then gkF else gkL

def fk (kind : Bool) (a0 a1 : Nat) : List (Reg × Word) :=
  gkOf kind ++ [(.x10, BitVec.ofNat 64 a0), (.x11, BitVec.ofNat 64 a1)]

/-- Extra instruction of a layer-phase fold level `lam ≥ 5`: `addi TP, x0, lam+1` (P6..P10 are
reused in the layer phase), before `sw TP, NB+4`. -/
def xp (kind : Bool) (lam : Nat) : Nat := if kind = false ∧ 5 ≤ lam then 1 else 0

/-- Fold level `lam` of `h`, in stream `t`, sibling at witness address `wa`, next stream `t'`
(unused for the last level), final destination `dst`. -/
def lvlExp (kind : Bool) (a1 : Nat) (rg t j0 h lam wa dst t' : Nat) : PRes :=
  let sib := 0x1F0 - 16 * t
  let base := RegFile.withKnown (fk kind (if lam = 0 then (if kind then 0xC0 else 0x340) else 0x1C0) a1)
  let rf0 := if lam = 0 then
      (if kind then base.set .x10 (cw 0x1C0) else (base.set .x10 (cw 0x1C0)).set .x11 (cw 64))
    else base
  let rf1 := (rf0.set .x1 (ldE wa)).set .x2 (ldE (wa + 8))
  let rf := if xp kind lam = 1 then rf1.set .x4 (cw (lam + 1)) else rf1
  let mb : List (Addr × E) :=
    [(⟨none, BitVec.ofNat 64 (sib + 8)⟩, ldE (wa + 8)), (⟨none, BitVec.ofNat 64 sib⟩, ldE wa)]
  let mh : List (Addr × E) := if lam = 0 ∧ kind then [(⟨none, BitVec.ofNat 64 0x1C0⟩, .reg .x27)] else []
  let mp : List (Addr × E) :=
    if lam = 0 then [] else [(⟨none, BitVec.ofNat 64 0x1C0⟩, stW 0x1C0 (cw (lam + 1)))]
  let hs := (if lam = 0 then 2 else 1) + xp kind lam
  if lam + 1 = h then
    ⟨⟨rf.set .x12 (cw dst), [(⟨none, BitVec.ofNat 64 0x1C8⟩, stW 0x1C8 (cw 0))] ++ mp ++ mb ++ mh, []⟩,
      pcOf (lvlPc rg t j0 lam + hs + 6), true, hs + 6, hs + 6, [], none⟩
  else
    let tE : E := .bin .sll (.reg .x23) (cw (62 - lam))
    let jE : E := .bin .srl (.reg .x23) (cw (lam + 1))
    ⟨⟨(((rf.set .x4 jE).set .x3 tE).set .x12 (cw (0x1E0 + 16 * t'))),
      [(⟨none, BitVec.ofNat 64 0x1C8⟩, stW 0x1C8 jE)] ++ mp ++ mb ++ mh, []⟩,
      pcOf (xPc rg t' (j0 + lam + 1) + 1), true, hs + 9, hs + 9,
      [⟨if t = 0 then .lt else .ge, tE, .c 0, if t = 0 then t' = 1 else t' = 0⟩], none⟩

def lvlDirs (h lam t' : Nat) : List Dir := if lam + 1 = h then [] else [.br (t' = 1)]

def lvlDirs' (t h lam t' : Nat) : List Dir :=
  if lam + 1 = h then [] else [.br (if t = 0 then t' = 1 else t' = 0)]

def fkeep (kind : Bool) : List Reg :=
  if kind then [.x16, .x17, .x22, .x23, .x25, .x27, .x28, .x29, .x30, .x31]
  else [.x14, .x15, .x16, .x17, .x22, .x23, .x25, .x26, .x27, .x28, .x30, .x31]

def okFold (kind : Bool) (o : Option PRes) (e : PRes) (post : List (Reg × Word)) : Bool :=
  optBeq o e && resOK (gkOf kind) e && knownB post e && keepB (fkeep kind) e

def lvlPost (kind : Bool) (h lam dst t' : Nat) : List (Reg × Word) :=
  fk kind 0x1C0 64 ++ [(.x12, BitVec.ofNat 64 (if lam + 1 = h then dst else 0x1E0 + 16 * t'))]

/-- All levels of one fold (both streams, both successor streams). -/
def foldCheck (kind : Bool) (a1 rg j0 h wa0 dst : Nat) : Bool :=
  (List.range h).all fun lam => (List.range 2).all fun t => (List.range 2).all fun t' =>
    (lam + 1 = h ∧ t' = 1) ||
    okFold kind (runAt (fk kind (if lam = 0 then (if kind then 0xC0 else 0x340) else 0x1C0) (if lam = 0 then a1 else 64)) []
        (lvlPc rg t j0 lam) (lvlDirs' t h lam t'))
      (lvlExp kind (if lam = 0 then a1 else 64) rg t j0 h lam (wa0 + 16 * lam) dst t')
      (lvlPost kind h lam dst t')

end SigGolfCandidate.Verify
