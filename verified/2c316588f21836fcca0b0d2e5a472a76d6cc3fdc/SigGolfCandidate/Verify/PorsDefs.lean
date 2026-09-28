import SigGolfCandidate.Verify.PorsArith
import SigGolfCandidate.Verify.PorsCheckB

/-!
# The PORS stack machine: machine invariants at the block boundaries

Ghost context `PCtx` (witness, public key, digest answer). The reference state `s0` is the state
after the setup (at `leaf_0`); `S0 P s0` lists what the setup established there. The boundaries:

* `LeafIn`: at `leaf_s` (the Ref's `PorsState`);
* `DispIn`: at a dispatch (after a leaf code, or in a merge tail), the Ref's `segLoop` arguments;
* `EntIn`: after the pending hash of a segment with `a ≥ 1` folds;
* `PosIn`: at a ladder position (fold `i` of the segment);
* `TailIn`: after the last hash of a segment (the node at the variant's destination).

Stack block `i` (base `PSB + 80 i`): `Q` at `blkQ i = PSB + 80 i - 16`, `L` at `blkL i = PSB + 80 i + 32`.
The Ref's stack (head = top) is `stk`; element `i` from the bottom is `stk.reverse[i]`.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

structure PCtx where
  wl : List Byte
  pk : List Byte
  a : BitVec 256

def PCtx.A (P : PCtx) : Nat := P.a.toNat
def PCtx.idx (P : PCtx) : Nat := idxOf P.A
def PCtx.v (P : PCtx) : List Nat := leavesOf P.A

def PCtx.ok (P : PCtx) : Prop := P.wl.length = 6348 ∧ P.pk.length = 16

theorem PCtx.idx_lt (P : PCtx) : P.idx < 2 ^ 34 := Nat.mod_lt _ (by decide)

/-! ## The reference state -/

/-- Zero words (the `P` slots of all hash buffers and stack blocks, `CB + 48 .. 64`). -/
def zeroP : List Nat :=
  [0x10, 0x18, 0xD0, 0xD8, 0xF0, 0xF8, 0x110, 0x118, 0x1D0, 0x1D8, 0x230, 0x238] ++
    (List.range 14).flatMap fun i => [PSB + 80 * i + 16, PSB + 80 * i + 24]

theorem zeroP_sub : ∀ a ∈ zeroP, a ∈ protP := by decide

theorem pSlots_sub : ∀ a ∈ pSlots, a ∈ zeroP := by decide

structure S0 (P : PCtx) (s0 : MachineState) : Prop where
  wit : WitOK P.wl s0
  pk : PkOK P.pk s0
  zero : ∀ a ∈ zeroP, s0.getMem (BitVec.ofNat 64 a) = 0
  cb0 : s0.getMem (BitVec.ofNat 64 0xC0) = BitVec.ofNat 64 (twLo 9 0 P.idx 0)
  nb0 : s0.getMem (BitVec.ofNat 64 0x1C0) = BitVec.ofNat 64 (twLo 10 0 P.idx 0)
  blk0 : ∀ i, i < 14 → s0.getMem (BitVec.ofNat 64 (PSB + 80 * i)) = BitVec.ofNat 64 (twLo 10 0 P.idx 0)
  half : ∀ a ∈ halfP, (s0.getMem (BitVec.ofNat 64 a)).toNat % 2 ^ 32 = P.idx % 2 ^ 32
  guard : s0.getMem (BitVec.ofNat 64 0x240) = -1#64
  pind : ∀ r, r < 16 → s0.getMem (BitVec.ofNat 64 (PIND + 8 * r)) =
    BitVec.ofNat 64 ((P.v ++ [porsT]).getD r 0)

/-- Common part of the PORS boundaries: constant registers (`x20` = the leaf's table), the frame
relative to `s0`, the facts at `s0`, `x22 = idx`. -/
structure PB (P : PCtx) (s0 m : MachineState) (tb : Nat) : Prop where
  glob : GlobP (gkP ++ [(.x20, BitVec.ofNat 64 tb)]) s0 m
  s0ok : S0 P s0
  idx : m.getReg .x22 = BitVec.ofNat 64 P.idx

/-! ## The stack -/

def blkQ (i : Nat) : Nat := PSB + 80 * i - 16
def blkL (i : Nat) : Nat := PSB + 80 * i + 32

def stkE (stk : List (Val × Nat)) (i : Nat) : Val × Nat := stk.reverse.getD i ([], 0)

def StackOK (stk : List (Val × Nat)) (m : MachineState) : Prop :=
  ∀ i, i < stk.length →
    m.getMem (BitVec.ofNat 64 (blkQ i)) = BitVec.ofNat 64 (stkE stk i).2 ∧
    m.getMem (BitVec.ofNat 64 (blkL i)) = vw0 (stkE stk i).1 ∧
    m.getMem (BitVec.ofNat 64 (blkL i + 8)) = vw1 (stkE stk i).1 ∧
    (stkE stk i).1.length = 16 ∧ (stkE stk i).2 < 2 ^ 15

/-- `STK` at depth `d`. -/
def stkOf' (d : Nat) : Nat := EMPTY + 80 * d

/-! ## Pending hash inputs -/

def pendAddr : Pending → Nat → Nat
  | .leaf _ _, _ => 0xC0
  | .merge _ _, d => PSB + 80 * d

def pendInput (P : PCtx) (node : Val) : Pending → List Byte
  | .leaf x s => porsLeafInput P.idx x s
  | .merge H l => porsNodeInput P.idx H l node

def isLeafP : Pending → Bool
  | .leaf _ _ => true
  | .merge _ _ => false

/-- The pending input in memory (tweak word `+8`, payload); the rest of the block is constant. -/
def PendMem (P : PCtx) (node : Val) (d : Nat) (m : MachineState) : Pending → Prop
  | .leaf x sec =>
    m.getMem (BitVec.ofNat 64 0xC8) = BitVec.ofNat 64 (twHi P.idx x) ∧
    m.getMem (BitVec.ofNat 64 0xE0) = vw0 sec ∧ m.getMem (BitVec.ofNat 64 0xE8) = vw1 sec ∧
    sec.length = 16 ∧ x ≤ 2 ^ 14
  | .merge H l =>
    m.getMem (BitVec.ofNat 64 (PSB + 80 * d + 8)) = BitVec.ofNat 64 (twHi P.idx H) ∧
    m.getMem (BitVec.ofNat 64 (PSB + 80 * d + 32)) = vw0 l ∧
    m.getMem (BitVec.ofNat 64 (PSB + 80 * d + 40)) = vw1 l ∧
    m.getMem (BitVec.ofNat 64 (PSB + 80 * d + 48)) = vw0 node ∧
    m.getMem (BitVec.ofNat 64 (PSB + 80 * d + 56)) = vw1 node ∧
    l.length = 16 ∧ node.length = 16 ∧ H < 2 ^ 15 ∧ d < 14

/-! ## Boundaries -/

/-- The link register value set by leaf `s`'s dispatch (the next leaf's start for `s < 14`). -/
def lnkOf (s : Nat) : Nat := 0x1000 + 4 * (dispLeafPc s + 4)

/-- Bounds at a segment start of leaf `s` with depth `d`: `2 s - d` segments are done. -/
def SegBnd (s d ptr folds : Nat) : Prop :=
  s < 15 ∧ d ≤ s ∧ 272 ≤ ptr ∧ ptr % 8 = 0 ∧ ptr + 232 * d ≤ 272 + 464 * s ∧ folds + 14 * d ≤ 28 * s

/-- Bounds after a segment (`2 s - d + 1` segments done). -/
def TailBnd (s d ptr folds : Nat) : Prop :=
  s < 15 ∧ d ≤ s ∧ 272 ≤ ptr ∧ ptr % 8 = 0 ∧ ptr + 232 * d ≤ 504 + 464 * s ∧ folds + 14 * d ≤ 28 * s + 14

structure LeafIn (P : PCtx) (s0 : MachineState) (s : Nat) (st : PorsState) (m : MachineState) : Prop where
  pb : PB P s0 m tbN
  pc : m.pc = pcOf (leafPc s)
  fr : m.getReg .x14 = BitVec.ofNat 64 (0x800 + st.ptr - 224)
  sum : m.getReg .x29 = BitVec.ofNat 64 st.folds
  rS : m.getReg .x15 = BitVec.ofNat 64 (stkOf' st.stack.length)
  stack : StackOK st.stack m
  prev : 0 < s → m.getReg (xReg (s + 1)) = BitVec.ofNat 64 st.prev ∧ st.prev ≤ 2 ^ 14
  bnd : SegBnd s st.stack.length st.ptr st.folds

structure DispIn (P : PCtx) (s0 : MachineState) (s x c ptr E folds : Nat) (pend : Pending)
    (node : Val) (stk : List (Val × Nat)) (m : MachineState) : Prop where
  pb : PB P s0 m (tbOf s)
  pc : m.pc = pcOf (dispPc c)
  copy : (c = s ∧ isLeafP pend = true) ∨ (15 ≤ c ∧ c < 18 ∧ isLeafP pend = false)
  fr : m.getReg .x14 = BitVec.ofNat 64 (0x800 + ptr - 224)
  rE : m.getReg .x23 = BitVec.ofNat 64 E
  sum : m.getReg .x29 = BitVec.ofNat 64 folds
  rS : m.getReg .x15 = BitVec.ofNat 64 (stkOf' stk.length)
  stack : StackOK stk m
  a0 : m.getReg .x10 = BitVec.ofNat 64 (pendAddr pend stk.length)
  pmem : PendMem P node stk.length m pend
  cur : m.getReg (xReg s) = BitVec.ofNat 64 x
  lnk : 15 ≤ c → m.getReg .x24 = BitVec.ofNat 64 (lnkOf s)
  bnd : SegBnd s stk.length ptr folds
  hE : E < 2 ^ 15
  hx : x ≤ 2 ^ 14

/-- After the pending hash of a segment (header at `ptr`, `a ≥ 1` folds, slot bit `t`, variant `V`):
the node in NB slot `t`, `FR` and `SUM` advanced. -/
structure EntIn (P : PCtx) (s0 : MachineState) (s x V t a ptr E folds : Nat) (node : Val)
    (stk : List (Val × Nat)) (m : MachineState) : Prop where
  pb : PB P s0 m (tbOf s)
  pc : m.pc = pcOf (entryPc t V a + 4)
  fr : m.getReg .x14 = BitVec.ofNat 64 (0x800 + ptr - 224 + 16 * a + 8)
  rE : m.getReg .x23 = BitVec.ofNat 64 E
  sum : m.getReg .x29 = BitVec.ofNat 64 (folds + a)
  rS : m.getReg .x15 = BitVec.ofNat 64 (stkOf' stk.length)
  stack : StackOK stk m
  cur : m.getReg (xReg s) = BitVec.ofNat 64 x
  lnk : m.getReg .x24 = BitVec.ofNat 64 (lnkOf s)
  node0 : m.getMem (BitVec.ofNat 64 (0x1E0 + 16 * t)) = vw0 node
  node1 : m.getMem (BitVec.ofNat 64 (0x1E8 + 16 * t)) = vw1 node
  nodeLen : node.length = 16
  bnd : SegBnd s stk.length ptr folds
  hE : E < 2 ^ 15
  hx : x ≤ 2 ^ 14
  ha : 1 ≤ a ∧ a ≤ 14
  ht : t < 2
  hV : V < 3
  hd : V = 1 → stk.length < 14

/-- At ladder position `p = 14 - a + i` of variant `V` in stream `t` (fold `i` of the segment whose
header is at `ptr`): the current node in NB slot `t`, `E` its heap index. -/
structure PosIn (P : PCtx) (s0 : MachineState) (s x V t a i ptr E folds : Nat) (node : Val)
    (stk : List (Val × Nat)) (m : MachineState) : Prop where
  pb : PB P s0 m (tbOf s)
  pc : m.pc = pcOf (ladPc V t (14 - a + i))
  a0 : m.getReg .x10 = BitVec.ofNat 64 0x1C0
  fr : m.getReg .x14 = BitVec.ofNat 64 (0x800 + ptr - 224 + 16 * a + 8)
  rE : m.getReg .x23 = BitVec.ofNat 64 E
  sum : m.getReg .x29 = BitVec.ofNat 64 (folds + a)
  rS : m.getReg .x15 = BitVec.ofNat 64 (stkOf' stk.length)
  stack : StackOK stk m
  cur : m.getReg (xReg s) = BitVec.ofNat 64 x
  lnk : m.getReg .x24 = BitVec.ofNat 64 (lnkOf s)
  node0 : m.getMem (BitVec.ofNat 64 (0x1E0 + 16 * t)) = vw0 node
  node1 : m.getMem (BitVec.ofNat 64 (0x1E8 + 16 * t)) = vw1 node
  nodeLen : node.length = 16
  bnd : SegBnd s stk.length ptr folds
  hE : E < 2 ^ 15
  hx : x ≤ 2 ^ 14
  ha : i < a ∧ a ≤ 14
  ht : t < 2
  hV : V < 3
  hd : V = 1 → stk.length < 14

/-- The destination of the last hash of a segment of variant `V` at depth `d`. -/
def destOf (V d : Nat) : Nat :=
  if V = 0 then stkOf' d + 48 else if V = 1 then stkOf' d + 112 else 0x120

/-- After the last hash of a segment of variant `V` (tail copy `c`): the new node at `destOf V d`;
`ptr` is the next header. -/
structure TailIn (P : PCtx) (s0 : MachineState) (s x V c ptr E folds : Nat) (node : Val)
    (stk : List (Val × Nat)) (m : MachineState) : Prop where
  pb : PB P s0 m (tbOf s)
  pc : m.pc = pcOf (tailPc V c)
  fr : m.getReg .x14 = BitVec.ofNat 64 (0x800 + ptr - 224)
  rE : m.getReg .x23 = BitVec.ofNat 64 E
  sum : m.getReg .x29 = BitVec.ofNat 64 folds
  rS : m.getReg .x15 = BitVec.ofNat 64 (stkOf' stk.length)
  stack : StackOK stk m
  cur : m.getReg (xReg s) = BitVec.ofNat 64 x
  lnk : m.getReg .x24 = BitVec.ofNat 64 (lnkOf s)
  node0 : m.getMem (BitVec.ofNat 64 (destOf V stk.length)) = vw0 node
  node1 : m.getMem (BitVec.ofNat 64 (destOf V stk.length + 8)) = vw1 node
  nodeLen : node.length = 16
  a2 : m.getReg .x12 = BitVec.ofNat 64 (destOf V stk.length)
  bnd : TailBnd s stk.length ptr folds
  hE : E < 2 ^ 15
  hx : x ≤ 2 ^ 14
  hc : c < 3
  hV : V < 3
  hd : V = 1 → stk.length < 14

end SigGolfCandidate.Verify
