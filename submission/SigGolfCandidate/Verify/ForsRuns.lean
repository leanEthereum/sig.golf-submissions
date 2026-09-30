import SigGolfCandidate.Verify.LayerRuns

/-! # Prologue, digest, FORS tree prefixes and the roots hash: partial specifications -/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

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

/-- After the last fold hash of FORS tree `k` in stream `t`. -/
def tEnd (k t : Nat) : Nat := lvlPc (k / 7) t (10 * (k % 7)) 9 + 8
def fK (k : Nat) : List (Reg × Word) := fk true 0x1C0 64 ++ [(.x12, BitVec.ofNat 64 (0x240 + 16 * k))]

/-- The branch direction into the X-block of stream `b` from stream `t`. -/
def dirOf (t b : Nat) : Bool := if t = 0 then b == 1 else b == 0

/-- The stream whose branch shape the prefix of tree `k` has (tree 7 follows the merge). -/
def tsh (k t : Nat) : Nat := if k = 7 then 0 else t

def secAddr (k : Nat) : Nat := 0x800 + 16 + 176 * k
def fwE' : E := .bin .add (.reg .x29) (.c 65536)

def treeSteps (k : Nat) : Nat := 12 + uSteps k + (if k = 7 then 1 else 0)

/-- Tree `k ≥ 1`, from the end of tree `k - 1` (stream `t`) to the leaf hash in stream `b`. -/
def specTree (k t b : Nat) : Spec :=
  ⟨[(.x1, ldE (secAddr k)), (.x2, ldE (secAddr k + 8)), (.x12, cw (480 + 16 * b)), (.x23, uE' k),
    (.x27, .bin .add (.reg .x27) (.c 65536)), (.x29, fwE')],
   [(⟨none, BitVec.ofNat 64 232⟩, ldE (secAddr k + 8)), (⟨none, BitVec.ofNat 64 224⟩, ldE (secAddr k)),
    (⟨none, BitVec.ofNat 64 200⟩, stW 200 (uE' k)), (⟨none, BitVec.ofNat 64 192⟩, stW0 192 fwE')],
   xPc (k / 7) b (10 * (k % 7)) + 1, true, treeSteps k,
   [⟨if tsh k t = 0 then .lt else .ge, .bin .sll (uE' k) (cw 63), .c 0, dirOf (tsh k t) b⟩], none⟩

def forsKeep : List Reg := [.x16, .x17, .x22, .x25]

def treeCheck (k : Nat) : Bool :=
  (List.range 2).all fun t => (List.range 2).all fun b =>
    specB gkF (runAt (fK (k - 1)) [] (tEnd (k - 1) t) [.br (dirOf (tsh k t) b)]) (specTree k t b)
      (fk true 0xC0 64) forsKeep

def specRoots (t : Nat) : Spec :=
  ⟨[], [], rootsStart t + 5, true, 5, [], none⟩

def rootsCheck : Bool :=
  (List.range 2).all fun t => specB gkF (runAt (fK 13) [] (tEnd 13 t) []) (specRoots t) a6K forsKeep

/-! ## Prologue and digest -/

/-- All registers except `x2` are zero in the initial state. -/
def k0 : List (Reg × Word) :=
  [(.x1, 0), (.x3, 0), (.x4, 0), (.x5, 0), (.x6, 0), (.x7, 0), (.x8, 0), (.x9, 0), (.x10, 0), (.x11, 0),
   (.x12, 0), (.x13, 0), (.x14, 0), (.x15, 0), (.x16, 0), (.x17, 0), (.x18, 0), (.x19, 0), (.x20, 0),
   (.x21, 0), (.x22, 0), (.x23, 0), (.x24, 0), (.x25, 0), (.x26, 0), (.x27, 0), (.x28, 0), (.x29, 0),
   (.x30, 0), (.x31, 0)]

/-- Digest phase: witness bases and the fold constants `P1 .. P10`. -/
def gkD : List (Reg × Word) := baseK ++ [(.x14, 6), (.x15, 7), (.x20, 8), (.x21, 9), (.x26, 10)]
def dgK : List (Reg × Word) := gkD ++ [(.x10, 0), (.x11, 128), (.x12, 0x160)]

def ctrX : E := .bin .or (.bin .or (ldE 8432) (ldE 8440)) (.un (.ld .wu 0) (ldE 8448))
def ctrE' : E := .bin .srl (.bin .or ctrX (.bin .sll ctrX (cw 32))) (cw 54)

def specStartOk : Spec :=
  ⟨[], [(⟨none, BitVec.ofNat 64 40⟩, ldE 2056), (⟨none, BitVec.ofNat 64 32⟩, ldE 2048),
    (⟨none, BitVec.ofNat 64 0⟩, cw 3073)], 30, true, 30, [⟨.ne, ctrE', .c 0, false⟩], none⟩
def specStartRej : Spec := ⟨rejK, [], 37, true, 23, [⟨.ne, ctrE', .c 0, true⟩], none⟩

def idxE : E := .bin .srl (.bin .sll (wLdE 0) (cw 30)) (cw 30)
def hiE : E := .bin .sll (.bin .srl idxE (cw 32)) (cw 24)
def u0E : E := uExprW wLdE 0
def admE : E := .bin .srl (.bin .sll (wLdE 2) (cw 8)) (cw 54)

def specDgOk (b : Nat) : Spec :=
  ⟨[(.x1, ldE 2064), (.x2, ldE 2072), (.x12, cw (480 + 16 * b)), (.x16, wLdE 0), (.x17, wLdE 1),
    (.x22, idxE), (.x23, u0E), (.x25, wLdE 2), (.x27, .bin .add hiE (cw 4294969857)),
    (.x29, .bin .add hiE (cw 2305))],
   [(⟨none, BitVec.ofNat 64 232⟩, ldE 2072), (⟨none, BitVec.ofNat 64 224⟩, ldE 2064),
    (⟨none, BitVec.ofNat 64 200⟩, .bin (.st .w 4) (stW0 200 idxE) u0E),
    (⟨none, BitVec.ofNat 64 192⟩, stW0 192 (.bin .add hiE (cw 2305))),
    (⟨none, BitVec.ofNat 64 544⟩, stW0 544 (.bin .add hiE (cw 2817))),
    (⟨none, BitVec.ofNat 64 552⟩, stW0 552 idxE), (⟨none, BitVec.ofNat 64 456⟩, stW0 456 idxE)],
   xPc 0 b 0 + 1, true, 34,
   [⟨.lt, .bin .sll u0E (cw 63), .c 0, b == 1⟩, ⟨.eq, admE, .c 0, true⟩], none⟩

def specDgRej : Spec := ⟨rejK, [], 37, true, 6, [⟨.eq, admE, .c 0, false⟩], none⟩

def topCheck : Bool :=
  specB gkD (runAt k0 [] 0 [.br false]) specStartOk dgK [] &&
  specB [] (runAt k0 [] 0 [.br true]) specStartRej [] [] &&
  specB gkF (runAt dgK [] 31 [.br true, .br false]) (specDgOk 0) (fk true 0xC0 64) [] &&
  specB gkF (runAt dgK [] 31 [.br true, .br true]) (specDgOk 1) (fk true 0xC0 64) [] &&
  specB [] (runAt dgK [] 31 [.br false]) specDgRej [] []

end SigGolfCandidate.Verify
