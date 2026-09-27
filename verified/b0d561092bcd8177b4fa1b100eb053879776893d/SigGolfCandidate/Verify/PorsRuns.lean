import SigGolfCandidate.Verify.PorsMem
import SigGolfCandidate.Verify.LayerRuns

/-!
# The PORS stack machine: expected symbolic results of its code blocks

Families (each a list of path runs, checked by `pspecB` in the `PorsCheck*` files):

* `setup`: from the digest's `j pors_setup` to `leaf_0` (leaf index table, tweak words, guard);
* `leaf s` (`s < 15`): pi byte, `x = PIND[pi & 0x78 / 8]`, the order checks, leaf tweak, secret,
  `E = x | 2^14`, `a0 = CB`, up to the dispatch (the rejects: HALT(1));
* `disp c` (`c < 18`): the dispatch `lbu T, 224(FR); slli; add TB; jalr` of leaf `c` (link `x24`)
  or of the merge tail copy `c - 15` (no link), stopping at the symbolic table entry;
* `tab tb b` (`tb < 2`, `b < 256`): table entry `b` (`SUM += a; FR += 16 a + 8; j entry`) and the
  entry prefix up to the pending hash (`a > 14`: HALT(1); `a ≥ 1`: the parity test
  `andi T, E, 1; beq/bne T, x0, pors_bad_par`, taken: HALT(1));
* `ent t V k`: after the pending hash, `a0 = NB; j lad_V_t_(14-k)`;
* `pos V t p t'`: ladder position `p` of stream `t` (sibling from `FR + 16 p`, `E >>= 1`, heap
  index, branch to stream `t'`), up to the next hash (`p = 13`: the variant's destination);
* tails `tailM c d`, `tailP c d`, `tailF c` (copy `c`: `0`, `1` = after stream `c`'s ladder, `2` = after
  `entry0_V`), with `STK = EMPTY + 80 d` known where the tail writes through it.

Variants: `V = 0` (M, merge), `1` (P, push), `2` (F, root).
-/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! ## pcs -/

def leafPc (s : Nat) : Nat := leafTab.getD s 0
/-- The dispatch of leaf `s` (after the leaf code). -/
def dispLeafPc (s : Nat) : Nat := leafPc s + (if s = 0 then 10 else if s = 14 then 15 else 11)
def entryPc (t V k : Nat) : Nat := ((entryTab.getD t []).getD V []).getD (k - 1) 0
def entry0Pc (V : Nat) : Nat := entry0Tab.getD V 0
def ladPc (V t p : Nat) : Nat := ((ladTab.getD V []).getD t []).getD p 0
def lbrPc (V t p : Nat) : Nat := ((lbrTab.getD V []).getD t []).getD p 0
/-- Start of the tail of variant `V`, copy `c` (after the destination hash). -/
def tailPc (V c : Nat) : Nat := if c = 2 then entry0Pc V + 2 else ladPc V c 13 + 8
/-- The dispatch of merge-tail copy `c`. -/
def dispTailPc (c : Nat) : Nat := tailPc 0 c + 6
/-- Dispatch copies: leaves `0..14`, merge tails `15..17`. -/
def dispPc (c : Nat) : Nat := if c < 15 then dispLeafPc c else dispTailPc (c - 15)
/-- The start of the layer-4 precode after the root tail copy `c`. -/
def f4Pc (c : Nat) : Nat := if c = 2 then layerPcTab.getD 4 [] |>.getD 0 0
  else if c = 1 then (layerPcTab.getD 4 []).getD 1 0 else (layerPcTab.getD 4 []).getD 2 0

/-! ## Expressions -/

def ldR (r : Reg) (off : Nat) : E := .ld (addC (.reg r) (BitVec.ofNat 64 off))
def eS : E := .bin .srl (.reg .x23) (cw 1)
def notOne : E := .c (~~~1#64)
/-- The table entry address `(lbu (FR + 224) << 4) + TB`. -/
def dispT (tb : Nat) : E :=
  .bin .add (.bin .sll (.un (.ld .bu 0) (.ld (.bin .add (.reg .x14) (cw 224)))) (cw 4)) (cw tb)
def dispObl : List Oblig := [.align8 (.reg .x14), .valid ⟨some (.reg .x14), BitVec.ofNat 64 224⟩ 1]

/-- The table of leaf `s`. -/
def tbOf (s : Nat) : Nat := if s = 14 then tbL else tbN

/-- The destination of the last hash of a segment of variant `V`. -/
def destE (V : Nat) : E :=
  if V = 0 then .bin .add (.reg .x15) (cw 48) else if V = 1 then .bin .add (.reg .x15) (cw 112)
  else cw 0x120

def rejSpec (steps : Nat) (brs : List Br) : Spec :=
  ⟨[(.x5, cw 1), (.x10, cw 1)], [], rejectPc + 2, true, steps, brs, none⟩

/-! ## Dispatch -/

/-- Dispatch copy `c` with table `tb` (the merge-tail copies run with either table). -/
def dispKnown (tb : Nat) : List (Reg × Word) := gkP ++ [(.x20, BitVec.ofNat 64 tb)]
def dispKeep : List Reg := [.x10, .x14, .x15, .x16, .x17, .x22, .x23, .x29]

def dispSpec (c tb : Nat) : Spec :=
  ⟨[(.x3, dispT tb)] ++ (if c < 15 then [(.x24, cw (0x1000 + 4 * (dispPc c + 4)))] else []), [],
    0, false, 4, [], some (.bin .and (dispT tb) notOne)⟩

def dispCheck2 (c tb : Nat) : Bool :=
  pspecB gkP (runAt (dispKnown tb) [] (dispPc c) [.jmp]) (dispSpec c tb) dispObl (dispKnown tb)
    (dispKeep ++ (if c < 15 then [] else [.x24]))

def dispCheck (c : Nat) : Bool :=
  if c < 15 then dispCheck2 c (tbOf c) else dispCheck2 c tbN && dispCheck2 c tbL

/-! ## Table entries -/

def tabBase (tb : Nat) : Nat := if tb = 0 then ptabN else ptabL
def segA (b : Nat) : Nat := b % 16
def segM (b : Nat) : Nat := b / 16 % 2
def segT (b : Nat) : Nat := b / 32 % 2
/-- The variant of byte `b` in table `tb`. -/
def segV (tb b : Nat) : Nat := if segM b = 1 then 0 else if tb = 0 then 1 else 2

/-- The entry code's parity test `andi T, E, 1; beq/bne T, x0, pors_bad_par` (`t = 1` / `t = 0`),
taken (reject) iff bit 0 of `E` differs from `t`. -/
def parE : E := .bin .and (.reg .x23) (cw 1)
def parBr (t : Nat) (d : Bool) : Br := ⟨if t = 1 then .eq else .ne, parE, .c 0, d⟩

/-- Table entry `b` up to the pending hash (`a = 0`: straight from the table; `a ≥ 1`: through the
entry's parity test, not taken). -/
def tabSpec (tb b : Nat) : Spec :=
  let a := segA b
  if a > 14 then rejSpec 4 []
  else
    ⟨[(.x29, addC (.reg .x29) (BitVec.ofNat 64 a)), (.x14, addC (.reg .x14) (BitVec.ofNat 64 (16 * a + 8))),
      (.x12, if a = 0 then destE (segV tb b) else cw (0x1E0 + 16 * segT b))], [],
      if a = 0 then entry0Pc (segV tb b) + 1 else entryPc (segT b) (segV tb b) a + 3, true,
      if a = 0 then 4 else 6, if a = 0 then [] else [parBr (segT b) false], none⟩

/-- Table entry `b` (`1 ≤ a ≤ 14`) with a wrong parity bit: `j pors_bad_par; j reject`, HALT(1). -/
def tabRej (b : Nat) : Spec := rejSpec 8 [parBr (segT b) true]

def tabKeep : List Reg := [.x10, .x15, .x16, .x17, .x20, .x22, .x23, .x24]

def tabCheck1 (tb b : Nat) : Bool :=
  if segA b > 14 then pspecB [] (runAt gkP [] (tabBase tb + 4 * b) []) (tabSpec tb b) [] [] []
  else if segA b = 0 then pspecB gkP (runAt gkP [] (tabBase tb + 4 * b) []) (tabSpec tb b) [] gkP tabKeep
  else
    pspecB gkP (runAt gkP [] (tabBase tb + 4 * b) [.br false]) (tabSpec tb b) [] gkP tabKeep &&
    pspecB [] (runAt gkP [] (tabBase tb + 4 * b) [.br true]) (tabRej b) [] [] []

def tabCheck (tb lo n : Nat) : Bool := (List.range' lo n).all fun b => tabCheck1 tb b

/-! ## Entry tails and ladder positions -/

def entSpec (t V k : Nat) : Spec := ⟨[(.x10, cw 0x1C0)], [], ladPc V t (14 - k), false, 2, [], none⟩

def entCheck : Bool :=
  (List.range 2).all fun t => (List.range 3).all fun V => (List.range' 1 14).all fun k =>
    pspecB gkP (runAt gkP [ladPc V t (14 - k)] (entryPc t V k + 4) []) (entSpec t V k) []
      (gkP ++ [(.x10, 0x1C0)]) [.x14, .x15, .x16, .x17, .x20, .x22, .x23, .x24, .x29]

def posKnown : List (Reg × Word) := gkP ++ [(.x10, 0x1C0)]
def posKeep : List Reg := [.x14, .x15, .x16, .x17, .x20, .x22, .x24, .x29]

def posMem (t p : Nat) : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 0x1C8⟩, stW 0x1C8 eS), (⟨none, BitVec.ofNat 64 (0x1F8 - 16 * t)⟩, ldR .x14 (16 * p + 8)),
    (⟨none, BitVec.ofNat 64 (0x1F0 - 16 * t)⟩, ldR .x14 (16 * p))]

def posObl (p : Nat) : List Oblig :=
  [.valid ⟨some (.reg .x14), BitVec.ofNat 64 (16 * p + 8)⟩ 8, .valid ⟨some (.reg .x14), BitVec.ofNat 64 (16 * p)⟩ 8]

/-- The branch direction from stream `t` to stream `t'`. -/
def crossDir (t t' : Nat) : Bool := if t = 0 then t' = 1 else t' = 0

def posSpec (V t p t' : Nat) : Spec :=
  let regs0 := [(.x1, ldR .x14 (16 * p)), (.x2, ldR .x14 (16 * p + 8)), ((.x23 : Reg), eS)]
  if p = 13 then ⟨regs0 ++ [(.x12, destE V)], posMem t p, ladPc V t p + 7, true, 7, [], none⟩
  else
    ⟨regs0 ++ [(.x3, .bin .sll eS (cw 63)), (.x12, cw (0x1E0 + 16 * t'))], posMem t p,
      lbrPc V t' (p + 1) + 1, true, 9,
      [⟨if t = 0 then .lt else .ge, .bin .sll eS (cw 63), .c 0, crossDir t t'⟩], none⟩

def posDirs (t p t' : Nat) : List Dir := if p = 13 then [] else [.br (crossDir t t')]

def posCheck1 (V t p t' : Nat) : Bool :=
  pspecB gkP (runAt posKnown [] (ladPc V t p) (posDirs t p t')) (posSpec V t p t') (posObl p)
    posKnown posKeep

def posCheck (V : Nat) : Bool :=
  (List.range 2).all fun t => (List.range 14).all fun p => (List.range 2).all fun t' =>
    (p = 13 && t' = 1) || posCheck1 V t p t'

/-! ## Tails -/

def stkOf (d : Nat) : Nat := EMPTY + 80 * d
def tailKnown (d : Nat) : List (Reg × Word) := gkP ++ [(.x15, BitVec.ofNat 64 (stkOf d))]
def tailKeep : List Reg := [.x14, .x16, .x17, .x20, .x22, .x24, .x29]

def tailMSpec (c d : Nat) : Spec :=
  ⟨[(.x3, ldE (stkOf d - 16)), (.x23, eS), (.x10, cw (stkOf d)), (.x15, cw (stkOf d - 80))],
    [(⟨none, BitVec.ofNat 64 (stkOf d + 8)⟩, stW (stkOf d + 8) eS)], dispTailPc c, false, 6,
    [⟨.ne, ldE (stkOf d - 16), .reg .x23, false⟩], none⟩

def tailMRej (d : Nat) : Spec := rejSpec 5 [⟨.ne, ldE (stkOf d - 16), .reg .x23, true⟩]

def tailPSpec (d : Nat) : Spec :=
  ⟨[(.x15, cw (stkOf d + 80)), (.x3, .bin .xor (.reg .x23) (cw 1))],
    [(⟨none, BitVec.ofNat 64 (stkOf d + 64)⟩, .bin .xor (.reg .x23) (cw 1))], 0, false, 4, [],
    some (.bin .and (.reg .x24) notOne)⟩

def tailCheck (c : Nat) : Bool :=
  (List.range 15).all (fun d =>
    pspecB gkP (runAt (tailKnown d) [dispTailPc c] (tailPc 0 c) [.br false]) (tailMSpec c d) []
      (tailKnown d |>.map fun p => if p.1 = .x15 then (.x15, BitVec.ofNat 64 (stkOf d - 80)) else p)
      tailKeep &&
    pspecB [] (runAt (tailKnown d) [] (tailPc 0 c) [.br true]) (tailMRej d) [] [] []) &&
  (List.range 14).all (fun d =>
    pspecB gkP (runAt (tailKnown d) [] (tailPc 1 c) [.jmp]) (tailPSpec d) []
      (tailKnown d |>.map fun p => if p.1 = .x15 then (.x15, BitVec.ofNat 64 (stkOf d + 80)) else p)
      [.x14, .x16, .x17, .x20, .x22, .x23, .x24, .x29])

/-! ### The root tail (checks, layer constants) -/

def fBr1 (d : Bool) : Br := ⟨.ltu, cw 120, .reg .x29, d⟩
def fBr2 (d : Bool) : Br := ⟨.ne, addC (.reg .x23) (-1#64), .c 0, d⟩
def fBr3 (d : Bool) : Br := ⟨.ne, .reg .x15, cw EMPTY, d⟩

def tailFKnown : List (Reg × Word) := gkP ++ [(.x12, 0x120)]

def tailFSpec (c : Nat) : Spec :=
  ⟨[], [], f4Pc c, false, 22, [fBr3 false, fBr2 false, fBr1 false], none⟩

def tailFCheck (c : Nat) : Bool :=
  pspecB gkL (runAt tailFKnown [f4Pc c] (tailPc 2 c) [.br false, .br false, .br false]) (tailFSpec c) []
    l4K [.x22] &&
  pspecB [] (runAt tailFKnown [] (tailPc 2 c) [.br true]) (rejSpec 5 [fBr1 true]) [] [] [] &&
  pspecB [] (runAt tailFKnown [] (tailPc 2 c) [.br false, .br true]) (rejSpec 7 [fBr2 true, fBr1 false]) [] [] [] &&
  pspecB [] (runAt tailFKnown [] (tailPc 2 c) [.br false, .br false, .br true])
    (rejSpec 9 [fBr3 true, fBr2 false, fBr1 false]) [] [] []

/-! ## Leaves -/

/-- The register holding leaf `s`'s index (`XA`, `XB` alternate). -/
def xReg (s : Nat) : Reg := if s % 2 = 0 then .x16 else .x17
/-- `pi_s & 0x78` (the slot's byte offset in `PIND`). -/
def piT (s : Nat) : E :=
  .bin .and (.un (.ld .bu ((16 + s) % 8)) (ldE (0x800 + 16 + (16 + s) / 8 * 8 - 16))) (cw 0x78)
def xE (s : Nat) : E := .ld (.bin .add (piT s) (cw PIND))
def secA (s : Nat) : Nat := 0x800 + 32 + 16 * s

def leafKnown : List (Reg × Word) := gkP ++ [(.x20, BitVec.ofNat 64 tbN)]
def pleafPost (s : Nat) : List (Reg × Word) := gkP ++ [(.x20, BitVec.ofNat 64 (tbOf s)), (.x10, 0xC0)]
def pleafKeep (s : Nat) : List Reg := [xReg (s + 1), .x14, .x15, .x22, .x24, .x29]

def leafBrs (s : Nat) (d1 d2 : Bool) : List Br :=
  (if s = 14 then [⟨.ne, .bin .srl (xE s) (cw 14), .c 0, d2⟩] else []) ++
  (if s = 0 then [] else [⟨.geu, .reg (xReg (s + 1)), xE s, d1⟩])

def leafSpec (s : Nat) : Spec :=
  ⟨[(xReg s, xE s), (.x23, .bin .or (xE s) (cw 0x4000)), (.x1, ldE (secA s)), (.x2, ldE (secA s + 8))],
    [(⟨none, BitVec.ofNat 64 0xE8⟩, ldE (secA s + 8)), (⟨none, BitVec.ofNat 64 0xE0⟩, ldE (secA s)),
      (⟨none, BitVec.ofNat 64 0xC8⟩, stW 0xC8 (xE s))],
    dispLeafPc s, false, if s = 0 then 10 else if s = 14 then 15 else 11, leafBrs s false false, none⟩

def leafObl (s : Nat) : List Oblig := [.valid ⟨some (piT s), BitVec.ofNat 64 PIND⟩ 8]

def leafDirs (s : Nat) : List Dir :=
  if s = 0 then [] else if s = 14 then [.br false, .br false] else [.br false]

def leafCheck (s : Nat) : Bool :=
  pspecB gkP (runAt leafKnown [dispLeafPc s] (leafPc s) (leafDirs s)) (leafSpec s) (leafObl s)
    (pleafPost s) (pleafKeep s) &&
  (s = 0 || pspecB [] (runAt leafKnown [] (leafPc s) [.br true])
    (rejSpec (if s = 14 then 9 else 7) [⟨.geu, .reg (xReg (s + 1)), xE s, true⟩]) (leafObl s) [] []) &&
  (s != 14 || pspecB [] (runAt leafKnown [] (leafPc s) [.br false, .br true])
    (rejSpec 11 (leafBrs s false true)) (leafObl s) [] [])

end SigGolfCandidate.Verify

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! ## Prologue, counter check, digest, PORS setup -/

/-- All registers except `x2` are zero in the initial state. -/
def k0 : List (Reg × Word) :=
  [(.x1, 0), (.x3, 0), (.x4, 0), (.x5, 0), (.x6, 0), (.x7, 0), (.x8, 0), (.x9, 0), (.x10, 0), (.x11, 0),
   (.x12, 0), (.x13, 0), (.x14, 0), (.x15, 0), (.x16, 0), (.x17, 0), (.x18, 0), (.x19, 0), (.x20, 0),
   (.x21, 0), (.x22, 0), (.x23, 0), (.x24, 0), (.x25, 0), (.x26, 0), (.x27, 0), (.x28, 0), (.x29, 0),
   (.x30, 0), (.x31, 0)]

/-- Digest phase: witness bases and `P1 .. P5`. -/
def gkD : List (Reg × Word) := baseK
def dgK : List (Reg × Word) := gkD ++ [(.x10, 0x20), (.x11, 64), (.x12, 0x160)]

/-- The counters: two doublewords and a word at `WIT + 6328`. -/
def ctrX : E := .bin .or (.bin .or (ldE 8376) (ldE 8384)) (.un (.ld .wu 0) (ldE 8392))
def ctrE' : E := .bin .srl (.bin .or ctrX (.bin .sll ctrX (cw 32))) (cw 54)

def specStartOk : Spec :=
  ⟨[], [(⟨none, BitVec.ofNat 64 56⟩, ldE 2056), (⟨none, BitVec.ofNat 64 48⟩, ldE 2048),
    (⟨none, BitVec.ofNat 64 32⟩, cw 3073)], 28, true, 28, [⟨.ne, ctrE', .c 0, false⟩], none⟩
def specStartRej : Spec := ⟨[(.x5, cw 1), (.x10, cw 1)], [], 32, true, 20, [⟨.ne, ctrE', .c 0, true⟩], none⟩

def wLdE (i : Nat) : E := ldE (0x160 + 8 * i)
def idxE : E := .bin .srl (.bin .sll (wLdE 0) (cw 30)) (cw 30)
def hiE : E := .bin .sll (.bin .srl idxE (cw 32)) (cw 24)

/-- Leaf index `v_r` (bits `34 + 14 r ..` of the digest). -/
def pindE (r : Nat) : E :=
  let p := 34 + 14 * r
  let lo : E := .bin .srl (wLdE (p / 64)) (cw (p % 64))
  .bin .and (if p % 64 + 14 ≤ 64 then lo else .bin .or lo (.bin .sll (wLdE (p / 64 + 1)) (cw (64 - p % 64))))
    (cw 0x3FFF)

def nbW0E : E := .bin .add hiE (cw 0xA01)

def psetupMem : List (Addr × E) :=
  [(⟨none, BitVec.ofNat 64 0x240⟩, .c (-1#64)), (⟨none, BitVec.ofNat 64 0xC8⟩, stW0 0xC8 idxE),
    (⟨none, BitVec.ofNat 64 0xC0⟩, .bin .add hiE (cw 0x901))] ++
  ((List.range 14).reverse.flatMap fun i =>
    [(⟨none, BitVec.ofNat 64 (PSB + 80 * i + 8)⟩, stW0 (PSB + 80 * i + 8) idxE),
      (⟨none, BitVec.ofNat 64 (PSB + 80 * i)⟩, nbW0E)]) ++
  [(⟨none, BitVec.ofNat 64 0x1C8⟩, stW0 0x1C8 idxE), (⟨none, BitVec.ofNat 64 0x1C0⟩, nbW0E),
    (⟨none, BitVec.ofNat 64 0x7F8⟩, cw 0x4000)] ++
  ((List.range 15).reverse.map fun r => (⟨none, BitVec.ofNat 64 (PIND + 8 * r)⟩, pindE r))

/-- Known after the setup: the PORS constants, `TB = ptab_n`, `FR` (first header at `FR + 224`),
the empty stack, `SUM = 0`. -/
def setupPost : List (Reg × Word) :=
  gkP ++ [(.x20, BitVec.ofNat 64 tbN), (.x14, 0x830), (.x15, BitVec.ofNat 64 EMPTY), (.x29, 0)]

def setupSpec : Spec := ⟨[(.x22, idxE)], psetupMem, leafPc 0, false, 108, [], none⟩

def startCheck : Bool :=
  specB gkD (runAt k0 [] 0 [.br false]) specStartOk dgK [] &&
  specB [] (runAt k0 [] 0 [.br true]) specStartRej [] [] &&
  specB gkD (runAt dgK [leafPc 0] 29 []) setupSpec setupPost []

end SigGolfCandidate.Verify
