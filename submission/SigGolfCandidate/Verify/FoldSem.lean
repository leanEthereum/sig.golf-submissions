import SigGolfCandidate.Verify.FoldRuns
import SigGolfCandidate.Verify.Common
import Mathlib.Data.Nat.Bitwise

/-! # Merkle fold levels: semantics -/

set_option linter.unusedSimpArgs false


namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Node format `tw(t, f2, tau, lam, j) | P | l | r` (`nodeInput`, `ftsNodeInput`). -/
def nodeF (t f2 tau : Nat) : NodeFmt := fun lam j l r => thInput (tweak t f2 tau lam j) (l ++ r)

theorem nodeInput_eq (lay tau : Nat) : nodeInput lay tau = nodeF 3 lay tau := rfl
theorem ftsNodeInput_eq (k idx : Nat) : ftsNodeInput k idx = nodeF 10 k idx := rfl

theorem pad64_nodeF (t f2 tau lam j : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) :
    pad64 (nodeF t f2 tau lam j l r) = queryOfWords 0
      [BitVec.ofNat 64 (twLo t f2 tau lam), BitVec.ofNat 64 (twHi tau j), 0, 0,
        vw0 l, vw1 l, vw0 r, vw1 r] := by
  unfold nodeF
  rw [pad64_thInput _ _ (by simp) 0 (by simp [hl, hr]) (by simp [hl, hr]), wordsOfN_tweak]
  simp only [List.length_append, hl, hr]
  rw [show 8 * 0 + 4 = 2 + (2 + 0) by rfl, List.append_assoc l r, wordsOfN_val_append l hl,
    wordsOfN_val_append r hr]
  rfl

structure FCtx where
  wl : List Byte
  pk : List Byte
  E : Nat
  h : Nat
  kind : Bool
  rg : Nat
  j0 : Nat
  a1 : Nat
  t : Nat
  f2 : Nat
  tau : Nat
  sibOff : Nat
  dst : Nat

def FCtx.ok (fc : FCtx) : Prop :=
  2 ≤ fc.h ∧ fc.h ≤ 11 ∧ fc.E < 2 ^ fc.h ∧ fc.t < 256 ∧ fc.f2 < 256 ∧ fc.wl.length = 6404 ∧
  fc.sibOff % 8 = 0 ∧ fc.sibOff + 16 * fc.h ≤ 6404 ∧ safeDest fc.dst = true ∧
  (fc.dst + 32 ≤ 0x1C0 ∨ 0x210 ≤ fc.dst) ∧ fc.a1 < 2 ^ 20

def FCtx.lo0 (fc : FCtx) : Nat := 1 + 256 * fc.t + 65536 * fc.f2 + 2 ^ 24 * (fc.tau / 2 ^ 32 % 256)

def FCtx.path (fc : FCtx) : List Val := (List.range fc.h).map fun l => slice fc.wl (fc.sibOff + 16 * l) 16

def FCtx.node (fc : FCtx) : NodeFmt := nodeF fc.t fc.f2 fc.tau

def FCtx.gk (fc : FCtx) : List (Reg × Word) := gkOf fc.kind

def bitOf (E lam : Nat) : Nat := E / 2 ^ lam % 2

def FrameOK (kind : Bool) (s0 s : MachineState) : Prop :=
  (∀ r ∈ fkeep kind, s.getReg r = s0.getReg r) ∧
  (∀ A, A < 2 ^ 64 → (A < 0x1C0 ∨ 0x210 ≤ A) → s.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A))

/-- Tweak word 0 of the node input at level 1 (before level 0) / its low half (later). -/
def NBhdr (fc : FCtx) (lam : Nat) (s : MachineState) : Prop :=
  if lam = 0 then
    (if fc.kind then s.getReg .x27 = BitVec.ofNat 64 (fc.lo0 + 2 ^ 32)
     else s.getMem (BitVec.ofNat 64 0x1C0) = BitVec.ofNat 64 (fc.lo0 + 2 ^ 32))
  else (s.getMem (BitVec.ofNat 64 0x1C0)).toNat % 2 ^ 32 = fc.lo0

def FoldInv (fc : FCtx) (s0 : MachineState) (lam : Nat) (v : Val) (s : MachineState) : Prop :=
  Glob fc.gk fc.wl fc.pk s ∧
  KnownOK (fk fc.kind (if lam = 0 then (if fc.kind then 0xC0 else 0x340) else 0x1C0) (if lam = 0 then fc.a1 else 64)) s ∧
  s.getReg .x23 = BitVec.ofNat 64 fc.E ∧ NBhdr fc lam s ∧
  (s.getMem (BitVec.ofNat 64 0x1C8)).toNat % 2 ^ 32 = fc.tau % 2 ^ 32 ∧
  s.getMem (BitVec.ofNat 64 (0x1E0 + 16 * bitOf fc.E lam)) = vw0 v ∧
  s.getMem (BitVec.ofNat 64 (0x1E8 + 16 * bitOf fc.E lam)) = vw1 v ∧ v.length = 16 ∧
  FrameOK fc.kind s0 s ∧ s.pc = pcOf (lvlPc fc.rg (bitOf fc.E lam) fc.j0 lam)

def FoldEnd (fc : FCtx) (s0 : MachineState) (u : MachineState) : Prop :=
  Glob fc.gk fc.wl fc.pk u ∧ KnownOK (fk fc.kind 0x1C0 64 ++ [(.x12, BitVec.ofNat 64 fc.dst)]) u ∧
  FrameOK fc.kind s0 u ∧
  u.pc = pcOf (lvlPc fc.rg (bitOf fc.E (fc.h - 1)) fc.j0 (fc.h - 1) + 7 + xp fc.kind (fc.h - 1)) ∧
  fetch image u = some (.base .ECALL) ∧
  (u.getMem (BitVec.ofNat 64 0x1C8)).toNat % 2 ^ 32 = fc.tau % 2 ^ 32

/-! ## Bits -/

theorem land16 (n : Nat) : n &&& 16 = 16 * (n / 16 % 2) := by
  rw [show (16 : Nat) = 2 ^ 4 from rfl, Nat.and_two_pow, Nat.toNat_testBit, Nat.mul_comm]

theorem srl_eval (u b : Nat) (hE : u < 2 ^ 11) (hb : b ≤ 11) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 u) :
    (Rv.E.bin .srl (.reg .x23) (cw b)).eval s = BitVec.ofNat 64 (u / 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Rv.E.eval, BinOp.eval, cw, h23, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have : u / 2 ^ b ≤ u := Nat.div_le_self _ _
  rw [Nat.mod_eq_of_lt (show u < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b < 64 by omega), Nat.mod_eq_of_lt (show u / 2 ^ b < 2 ^ 64 by omega)]

/-- The branch point: `slli T, E, 62 - lam; blt/bge T, x0` tests bit `lam + 1` of `E`. -/
theorem sll_lt (u lam : Nat) (hu : u < 2 ^ 11) (hl : lam ≤ 9) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 u) :
    CmpOp.lt.eval ((Rv.E.bin .sll (.reg .x23) (cw (62 - lam))).eval s) ((Rv.E.c 0).eval s) =
      decide (bitOf u (lam + 1) = 1) := by
  simp only [CmpOp.eval, Rv.E.eval, BinOp.eval, cw, h23]
  rw [show (0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, bitOf]
  rw [Nat.mod_eq_of_lt (show u < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show 62 - lam < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show 62 - lam < 64 by omega)]
  apply decide_eq_decide.mpr
  interval_cases lam <;> simp only [Nat.reduceSub, Nat.reduceAdd, Nat.reducePow] <;> omega

theorem sll_ge (u lam : Nat) (hu : u < 2 ^ 11) (hl : lam ≤ 9) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 u) :
    CmpOp.ge.eval ((Rv.E.bin .sll (.reg .x23) (cw (62 - lam))).eval s) ((Rv.E.c 0).eval s) =
      decide (bitOf u (lam + 1) = 0) := by
  have h := sll_lt u lam hu hl s h23
  simp only [CmpOp.eval] at h ⊢
  rw [h]
  have := Nat.mod_lt (u / 2 ^ (lam + 1)) (show 2 > 0 by decide)
  unfold bitOf
  rcases (show u / 2 ^ (lam + 1) % 2 = 0 ∨ u / 2 ^ (lam + 1) % 2 = 1 by omega) with e | e <;> simp [e]

theorem stW_eval (a : Nat) (v : Rv.E) (s : MachineState) :
    (stW a v).eval s = StoreKind.merge .w (s.getMem (BitVec.ofNat 64 a)) 4 (v.eval s) := rfl

theorem bitOf_lt (u lam : Nat) : bitOf u lam < 2 := Nat.mod_lt _ (by decide)

/-! ## Family facts -/

theorem okFold_spec {kind : Bool} {o : Option PRes} {e : PRes} {post : List (Reg × Word)}
    (h : okFold kind o e post = true) :
    o = some e ∧ resOK (gkOf kind) e = true ∧ knownB post e = true ∧ keepB (fkeep kind) e = true := by
  simp only [okFold, Bool.and_eq_true] at h
  exact ⟨optBeq_eq h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem foldCheck_at {kind : Bool} {a1 rg j0 h wa0 dst : Nat}
    (hc : foldCheck kind a1 rg j0 h wa0 dst = true) (lam t t' : Nat)
    (hlam : lam < h) (ht : t < 2) (ht' : t' < 2) (hn : ¬ (lam + 1 = h ∧ t' = 1)) :
    okFold kind (runAt (fk kind (if lam = 0 then (if kind then 0xC0 else 0x340) else 0x1C0) (if lam = 0 then a1 else 64)) []
        (lvlPc rg t j0 lam) (lvlDirs' t h lam t'))
      (lvlExp kind (if lam = 0 then a1 else 64) rg t j0 h lam (wa0 + 16 * lam) dst t')
      (lvlPost kind h lam dst t') = true := by
  simp only [foldCheck, List.all_eq_true, List.mem_range] at hc
  have := hc lam hlam t ht t' ht'
  simpa [hn] using this

theorem FrameOK.trans {kind : Bool} {s0 s t : MachineState} (h1 : FrameOK kind s0 s)
    (hr : ∀ r ∈ fkeep kind, t.getReg r = s.getReg r)
    (hm : ∀ A, A < 2 ^ 64 → (A < 0x1C0 ∨ 0x210 ≤ A) →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : FrameOK kind s0 t :=
  ⟨fun r hr' => (hr r hr').trans (h1.1 r hr'), fun A hA hA' => (hm A hA hA').trans (h1.2 A hA hA')⟩

theorem sib_words (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam < fc.h) (s : MachineState)
    (hG : Glob fc.gk fc.wl fc.pk s) :
    s.getMem (BitVec.ofNat 64 (0x800 + fc.sibOff + 16 * lam)) =
      vw0 (slice fc.wl (fc.sibOff + 16 * lam) 16) ∧
    s.getMem (BitVec.ofNat 64 (0x800 + fc.sibOff + 16 * lam + 8)) =
      vw1 (slice fc.wl (fc.sibOff + 16 * lam) 16) := by
  obtain ⟨-, h10, -, -, -, hwl, h8, hsz, -⟩ := hfc
  rw [vw0_slice, vw1_slice, show 0x800 + fc.sibOff + 16 * lam = 0x800 + (fc.sibOff + 16 * lam) by omega,
    show 0x800 + (fc.sibOff + 16 * lam) + 8 = 0x800 + (fc.sibOff + 16 * lam + 8) by omega]
  exact ⟨wit_word hG.2.1 _ (by omega) (by omega), wit_word hG.2.1 _ (by omega) (by omega)⟩

def FCtx.sib (fc : FCtx) (lam : Nat) : Val := slice fc.wl (fc.sibOff + 16 * lam) 16

/-- The spec's input of fold level `lam` with current value `v`. -/
def FCtx.input (fc : FCtx) (lam : Nat) (v : Val) : List Byte :=
  if fc.E / 2 ^ lam % 2 = 1 then fc.node (lam + 1) (fc.E / 2 ^ (lam + 1)) (fc.sib lam) v
  else fc.node (lam + 1) (fc.E / 2 ^ (lam + 1)) v (fc.sib lam)

theorem length_sib (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam < fc.h) :
    (fc.sib lam).length = 16 := by
  obtain ⟨-, h10, -, -, -, hwl, h8, hsz, -⟩ := hfc
  unfold FCtx.sib; apply length_slice16; omega

theorem pad64_input (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam < fc.h) (v : Val)
    (hv : v.length = 16) :
    pad64 (fc.input lam v) = queryOfWords 0
      [BitVec.ofNat 64 (twLo fc.t fc.f2 fc.tau (lam + 1)),
        BitVec.ofNat 64 (twHi fc.tau (fc.E / 2 ^ (lam + 1))), 0, 0,
        if bitOf fc.E lam = 1 then vw0 (fc.sib lam) else vw0 v,
        if bitOf fc.E lam = 1 then vw1 (fc.sib lam) else vw1 v,
        if bitOf fc.E lam = 1 then vw0 v else vw0 (fc.sib lam),
        if bitOf fc.E lam = 1 then vw1 v else vw1 (fc.sib lam)] := by
  unfold FCtx.input bitOf
  split
  · rw [FCtx.node, pad64_nodeF _ _ _ _ _ _ _ (length_sib fc hfc lam hlam) hv]; try simp_all
  · rw [FCtx.node, pad64_nodeF _ _ _ _ _ _ _ hv (length_sib fc hfc lam hlam)]; try simp_all


/-- The word-0 header after level `lam`'s block. -/
theorem lvl_hdr (fc : FCtx) (lam : Nat) (hlam : lam + 1 ≤ fc.h) (t t' : Nat) (ht : t < 2)
    (s : MachineState) (hN0 : NBhdr fc lam s) (hlo : fc.lo0 < 2 ^ 32) (hl : lam < 2 ^ 20) :
    memEval s (lvlExp fc.kind (if lam = 0 then fc.a1 else 64) fc.rg t fc.j0 fc.h lam
      (0x800 + fc.sibOff + 16 * lam) fc.dst t').st.mem (BitVec.ofNat 64 0x1C0) =
      BitVec.ofNat 64 (fc.lo0 + 2 ^ 32 * (lam + 1)) := by
  unfold NBhdr at hN0
  by_cases h0 : lam = 0
  · subst h0
    rw [if_pos rfl] at hN0
    cases hk : fc.kind
    · rw [hk] at hN0; simp only [if_false, Bool.false_eq_true] at hN0
      rw [memEval_frame_ofNat _ _ _ (by omega) (by
        simp only [lvlExp, hk]
        split <;> simp <;> omega), hN0]
      simp
    · rw [hk] at hN0; simp only [if_true] at hN0
      simp only [lvlExp, hk]
      split
      · simp only [List.cons_append, List.nil_append, if_true, and_self]
        rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
          memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
        simp only [Rv.E.eval]; rw [hN0]; simp
      · simp only [List.cons_append, List.nil_append, if_true, and_self]
        rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
          memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
        simp only [Rv.E.eval]; rw [hN0]; simp
  · rw [if_neg h0] at hN0
    simp only [lvlExp, h0, false_and, if_false]
    split
    · simp only [List.cons_append, List.nil_append, List.append_nil]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl, stW_eval]
      simp only [Rv.E.eval, cw]
      rw [stMerge_eval _ _ _ (by omega) hN0]
    · simp only [List.cons_append, List.nil_append, List.append_nil]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl, stW_eval]
      simp only [Rv.E.eval, cw]
      rw [stMerge_eval _ _ _ (by omega) hN0]

/-- Addresses not written by level `lam`'s block. -/
theorem lvl_frame (fc : FCtx) (lam : Nat) (t t' : Nat) (ht : t < 2) (s : MachineState) (A : Nat)
    (hA : A < 2 ^ 64) (h1 : A ≠ 0x1C8) (h2 : A ≠ 0x1C0) (h3 : A ≠ 0x1F0 - 16 * t + 8)
    (h4 : A ≠ 0x1F0 - 16 * t) :
    memEval s (lvlExp fc.kind (if lam = 0 then fc.a1 else 64) fc.rg t fc.j0 fc.h lam
      (0x800 + fc.sibOff + 16 * lam) fc.dst t').st.mem (BitVec.ofNat 64 A) =
      s.getMem (BitVec.ofNat 64 A) := by
  apply memEval_frame_ofNat _ _ _ hA
  simp only [lvlExp]
  split_ifs <;> simp_all <;> omega

theorem lvl_sib (fc : FCtx) (lam : Nat) (t t' : Nat) (ht : t < 2) (s : MachineState) :
    memEval s (lvlExp fc.kind (if lam = 0 then fc.a1 else 64) fc.rg t fc.j0 fc.h lam
      (0x800 + fc.sibOff + 16 * lam) fc.dst t').st.mem (BitVec.ofNat 64 (0x1F0 - 16 * t)) =
      s.getMem (BitVec.ofNat 64 (0x800 + fc.sibOff + 16 * lam)) ∧
    memEval s (lvlExp fc.kind (if lam = 0 then fc.a1 else 64) fc.rg t fc.j0 fc.h lam
      (0x800 + fc.sibOff + 16 * lam) fc.dst t').st.mem (BitVec.ofNat 64 (0x1F0 - 16 * t + 8)) =
      s.getMem (BitVec.ofNat 64 (0x800 + fc.sibOff + 16 * lam + 8)) := by
  have key : ∀ (l1 l2 : List (Addr × Rv.E)), (∀ p ∈ l1, p.1.base = none ∧ p.1.off.toNat ≠ 0x1F0 - 16 * t ∧
      p.1.off.toNat ≠ 0x1F0 - 16 * t + 8) →
      memEval s (l1 ++ ([(⟨none, BitVec.ofNat 64 (0x1F0 - 16 * t + 8)⟩, ldE (0x800 + fc.sibOff + 16 * lam + 8)),
        (⟨none, BitVec.ofNat 64 (0x1F0 - 16 * t)⟩, ldE (0x800 + fc.sibOff + 16 * lam))] ++ l2))
        (BitVec.ofNat 64 (0x1F0 - 16 * t)) = s.getMem (BitVec.ofNat 64 (0x800 + fc.sibOff + 16 * lam)) ∧
      memEval s (l1 ++ ([(⟨none, BitVec.ofNat 64 (0x1F0 - 16 * t + 8)⟩, ldE (0x800 + fc.sibOff + 16 * lam + 8)),
        (⟨none, BitVec.ofNat 64 (0x1F0 - 16 * t)⟩, ldE (0x800 + fc.sibOff + 16 * lam))] ++ l2))
        (BitVec.ofNat 64 (0x1F0 - 16 * t + 8)) = s.getMem (BitVec.ofNat 64 (0x800 + fc.sibOff + 16 * lam + 8)) := by
    intro l1 l2 hl1
    induction l1 with
    | nil =>
      simp only [List.nil_append, List.cons_append]
      constructor
      · rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]; rfl
      · rw [memEval_cons_eq _ _ _ _ _ rfl]; rfl
    | cons p l1 ih =>
      obtain ⟨⟨b, off⟩, v⟩ := p
      obtain ⟨hb, hn1, hn2⟩ := hl1 _ (List.mem_cons_self ..)
      simp only at hb; subst hb
      have ih' := ih (fun q hq => hl1 q (List.mem_cons_of_mem _ hq))
      simp only [List.cons_append] at ih' ⊢
      rw [memEval_cons_ne _ _ _ _ _ (by intro h; apply hn1; rw [← h, BitVec.toNat_ofNat]; omega),
        memEval_cons_ne _ _ _ _ _ (by intro h; apply hn2; rw [← h, BitVec.toNat_ofNat]; omega)]
      exact ih'
  simp only [lvlExp]
  split
  · rw [List.append_assoc]; apply key; simp; (repeat' (first | apply And.intro | intro)) <;> omega
  · rw [List.append_assoc]; apply key; simp; (repeat' (first | apply And.intro | intro)) <;> omega


theorem hdr_low (fc : FCtx) (s : MachineState) (lam : Nat) (hlo : fc.lo0 < 2 ^ 32)
    (h : s.getMem (BitVec.ofNat 64 0x1C0) = BitVec.ofNat 64 (fc.lo0 + 2 ^ 32 * (lam + 1))) :
    (s.getMem (BitVec.ofNat 64 0x1C0)).toNat % 2 ^ 32 = fc.lo0 := by
  rw [h, BitVec.toNat_ofNat]; omega

theorem lo0_lt (fc : FCtx) (hfc : fc.ok) : fc.lo0 < 2 ^ 32 := by
  obtain ⟨-, -, -, ht, hf2, -⟩ := hfc
  unfold FCtx.lo0; omega

theorem level_step (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam + 1 ≤ fc.h)
    (hchk : foldCheck fc.kind fc.a1 fc.rg fc.j0 fc.h (0x800 + fc.sibOff) fc.dst = true)
    (s0 : MachineState) (v : Val) (s : MachineState) (hs : FoldInv fc s0 lam v s) :
    let t' := if lam + 1 = fc.h then 0 else bitOf fc.E (lam + 1)
    let r := lvlExp fc.kind (if lam = 0 then fc.a1 else 64) fc.rg (bitOf fc.E lam) fc.j0 fc.h lam
      (0x800 + fc.sibOff + 16 * lam) fc.dst t'
    Steps image s r.steps r.cycles (r.toState s) ∧ fetch image (r.toState s) = some (.base .ECALL) ∧
      (r.toState s).getReg .x5 = 0 ∧
      KnownOK (lvlPost fc.kind fc.h lam fc.dst t') (r.toState s) ∧
      (∀ x ∈ fkeep fc.kind, (r.toState s).getReg x = s.getReg x) ∧
      Glob fc.gk fc.wl fc.pk (r.toState s) ∧
      (r.toState s).getMem (BitVec.ofNat 64 0x1C0) = BitVec.ofNat 64 (fc.lo0 + 2 ^ 32 * (lam + 1)) ∧
      (r.toState s).getMem (BitVec.ofNat 64 (0x1F0 - 16 * bitOf fc.E lam)) = vw0 (fc.sib lam) ∧
      (r.toState s).getMem (BitVec.ofNat 64 (0x1F0 - 16 * bitOf fc.E lam + 8)) = vw1 (fc.sib lam) ∧
      (∀ A, A < 2 ^ 64 → A ≠ 0x1C8 → A ≠ 0x1C0 → A ≠ 0x1F0 - 16 * bitOf fc.E lam + 8 →
        A ≠ 0x1F0 - 16 * bitOf fc.E lam →
        (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) ∧
      r.spc = none := by
  intro t' r
  have hb2 := bitOf_lt fc.E lam
  have hlo := lo0_lt fc hfc
  have hE : fc.E < 2 ^ 11 := lt_of_lt_of_le hfc.2.2.1 (Nat.pow_le_pow_right (by decide) hfc.2.1)
  have ht' : t' < 2 := by simp only [t']; split; omega; exact bitOf_lt _ _
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okFold_spec (foldCheck_at hchk lam (bitOf fc.E lam) t' (by omega) hb2 ht'
    (by simp only [t']; split <;> simp_all))
  obtain ⟨hG, hK, h23, hN0, hN8, hv0, hv1, hvl, hF, hpc⟩ := hs
  have hbr : ∀ b ∈ r.brs, b.holds s := by
    intro b hb
    simp only [r, lvlExp] at hb
    split at hb
    · simp at hb
    · rename_i hne
      simp only [List.mem_singleton] at hb
      subst hb
      simp only [Br.holds]
      have hl8 : lam ≤ 9 := by have := hfc.2.1; omega
      have ht'v : t' = bitOf fc.E (lam + 1) := by simp only [t', if_neg hne]
      rcases (show bitOf fc.E lam = 0 ∨ bitOf fc.E lam = 1 by omega) with h0 | h1
      · rw [h0]; simp only [if_true]
        rw [sll_lt fc.E lam hE hl8 s h23, ht'v]
      · rw [h1]; simp only [one_ne_zero, if_false]
        rw [sll_ge fc.E lam hE hl8 s h23, ht'v]
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK hbr
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have hsib := sib_words fc hfc lam (by omega) s hG
  refine ⟨hst, hec (by simp only [r, lvlExp]; split <;> rfl), ?_, hK', hkeep', hglob _ _ hG, ?_, ?_, ?_, ?_,
    by simp only [r, lvlExp]; split <;> rfl⟩
  · exact hK' (.x5, 0) (by simp [lvlPost, fk, gkOf, gkF, gkL, baseK]; split <;> simp)
  · rw [PRes.toState_getMem _ _]
    exact lvl_hdr fc lam hlam _ t' hb2 s hN0 hlo (by have := hfc.2.1; omega)
  · rw [PRes.toState_getMem, (lvl_sib fc lam _ t' hb2 s).1]; exact hsib.1
  · rw [PRes.toState_getMem, (lvl_sib fc lam _ t' hb2 s).2]; exact hsib.2
  · intro A hA h1 h2 h3 h4
    rw [PRes.toState_getMem]; exact lvl_frame fc lam _ t' hb2 s A hA h1 h2 h3 h4

theorem lvl_nb8 (fc : FCtx) (lam t t' : Nat) (s : MachineState) :
    memEval s (lvlExp fc.kind (if lam = 0 then fc.a1 else 64) fc.rg t fc.j0 fc.h lam
      (0x800 + fc.sibOff + 16 * lam) fc.dst t').st.mem (BitVec.ofNat 64 0x1C8) =
      StoreKind.merge .w (s.getMem (BitVec.ofNat 64 0x1C8)) 4
        ((if lam + 1 = fc.h then cw 0 else Rv.E.bin .srl (.reg .x23) (cw (lam + 1))).eval s) := by
  simp only [lvlExp]
  split <;> (simp only [List.cons_append]; rw [memEval_cons_eq _ _ _ _ _ rfl, stW_eval])

theorem level_lt (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam + 1 < fc.h)
    (hchk : foldCheck fc.kind fc.a1 fc.rg fc.j0 fc.h (0x800 + fc.sibOff) fc.dst = true)
    (s0 : MachineState) (v : Val) (s : MachineState) (hs : FoldInv fc s0 lam v s) :
    ∃ t, Steps image s ((if lam = 0 then 11 else 10) + xp fc.kind lam)
      ((if lam = 0 then 11 else 10) + xp fc.kind lam) t ∧
      fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = pad64 (fc.input lam v) ∧
      ∀ a, FoldInv fc s0 (lam + 1) (answerBytes 16 a) (writeHash t a) := by
  obtain ⟨hst, hec, h5, hK', hkeep', hglob, m1C0, msib0, msib1, mfr, hspc⟩ :=
    level_step fc hfc lam (by omega) hchk s0 v s hs
  simp only [if_neg (show ¬ (lam + 1 = fc.h) by omega)] at hst hec h5 hK' hkeep' hglob m1C0 msib0 msib1 mfr hspc
  set b := bitOf fc.E lam with hbdef
  set b' := bitOf fc.E (lam + 1) with hb'def
  set r := lvlExp fc.kind (if lam = 0 then fc.a1 else 64) fc.rg b fc.j0 fc.h lam
      (0x800 + fc.sibOff + 16 * lam) fc.dst b' with hr
  have hb2 := bitOf_lt fc.E lam
  have hb2' := bitOf_lt fc.E (lam + 1)
  have hlo := lo0_lt fc hfc
  have hE : fc.E < 2 ^ 11 := lt_of_lt_of_le hfc.2.2.1 (Nat.pow_le_pow_right (by decide) hfc.2.1)
  obtain ⟨hG, hK, h23, hN0, hN8, hv0, hv1, hvl, hF, hpc⟩ := hs
  simp only [lvlPost, if_neg (show ¬ (lam + 1 = fc.h) by omega)] at hK'
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0x1C0 := hK' (.x10, _) (by simp [fk])
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, _) (by simp [fk])
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * b') :=
    hK' (.x12, _) (List.mem_append_right _ (List.mem_singleton_self _))
  have h23' : (r.toState s).getReg .x23 = BitVec.ofNat 64 fc.E :=
    (hkeep' .x23 (by simp [fkeep]; split <;> simp)).trans h23
  have hj : fc.E / 2 ^ (lam + 1) ≤ fc.E := Nat.div_le_self _ _
  have m1C8 : (r.toState s).getMem (BitVec.ofNat 64 0x1C8) =
      BitVec.ofNat 64 (fc.tau % 2 ^ 32 + 2 ^ 32 * (fc.E / 2 ^ (lam + 1))) := by
    rw [PRes.toState_getMem, lvl_nb8, if_neg (by omega), srl_eval fc.E (lam + 1) hE (by have := hfc.2.1; omega) s h23,
      stMerge_eval _ _ _ (by omega) hN8]
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have mv0 : (r.toState s).getMem (BitVec.ofNat 64 (0x1E0 + 16 * b)) = vw0 v := by
    rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv0
  have mv1 : (r.toState s).getMem (BitVec.ofNat 64 (0x1E8 + 16 * b)) = vw1 v := by
    rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv1
  refine ⟨r.toState s, ?_, hec, h5, ?_, ?_, ?_⟩
  · have e1 : r.steps = (if lam = 0 then 11 else 10) + xp fc.kind lam := by
      simp only [hr, lvlExp, if_neg (show ¬ (lam + 1 = fc.h) by omega)]; split <;> omega
    have e2 : r.cycles = (if lam = 0 then 11 else 10) + xp fc.kind lam := by
      simp only [hr, lvlExp, if_neg (show ¬ (lam + 1 = fc.h) by omega)]; split <;> omega
    rw [e1, e2] at hst; exact hst
  · exact hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega)
  · rw [hashInput_ofNat _ 0x1C0 0 h10 h11 (by decide) (by decide),
      pad64_input fc hfc lam (by omega) v hvl]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero]
    have hlo' : twLo fc.t fc.f2 fc.tau (lam + 1) = fc.lo0 + 2 ^ 32 * (lam + 1) := by
      unfold twLo FCtx.lo0; have := hfc.2.1; have := hfc.2.2.2.1; have := hfc.2.2.2.2.1; omega
    have hhi : twHi fc.tau (fc.E / 2 ^ (lam + 1)) = fc.tau % 2 ^ 32 + 2 ^ 32 * (fc.E / 2 ^ (lam + 1)) := by
      unfold twHi; omega
    rw [hlo', hhi, m1C0, m1C8, mfr 0x1D0 (by omega) (by omega) (by omega) (by omega) (by omega),
      mfr 0x1D8 (by omega) (by omega) (by omega) (by omega) (by omega), hP 0x1D0 (by decide),
      hP 0x1D8 (by decide)]
    rcases (show b = 0 ∨ b = 1 by omega) with h0 | h1
    · rw [h0] at mv0 mv1 msib0 msib1
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceSub] at mv0 mv1 msib0 msib1
      rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h0]
    · rw [h1] at mv0 mv1 msib0 msib1
      simp only [Nat.mul_one, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] at mv0 mv1 msib0 msib1
      rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h1]
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x1E0 + 16 * b' ∨ 0x1E0 + 16 * b' + 32 ≤ A) =>
      writeHash_frame _ a _ A h12 hA (by omega) h
    refine ⟨Glob_writeHash hglob a _ h12 (by
        rcases (show b' = 0 ∨ b' = 1 by omega) with h | h <;> rw [h] <;> decide),
      ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_, ?_⟩
    · intro p hp
      rw [writeHash_getReg]
      simp only [show lam + 1 ≠ 0 by omega, if_false] at hp
      exact hK' p (List.mem_append_left _ hp)
    · rw [writeHash_getReg]; exact h23'
    · simp only [NBhdr, show lam + 1 ≠ 0 by omega, if_false]
      rw [wf 0x1C0 (by omega) (by omega), m1C0, BitVec.toNat_ofNat]; omega
    · rw [wf 0x1C8 (by omega) (by omega), m1C8, BitVec.toNat_ofNat]; omega
    · rw [writeHash_at0 _ a _ h12 (by omega)]; simp [vw0_answer]
    · rw [show 0x1E8 + 16 * bitOf fc.E (lam + 1) = 0x1E0 + 16 * b' + 8 by omega,
        writeHash_at8 _ a _ h12 (by omega)]; simp [vw1_answer]
    · refine FrameOK.trans (FrameOK.trans hF (fun r hr => hkeep' r hr) (fun A hA hA' => ?_))
        (fun r _ => writeHash_getReg _ _ _) (fun A hA hA' => wf A hA (by omega))
      exact mfr A hA (by omega) (by omega) (by omega) (by omega)
    · rw [writeHash_pc, PRes.toState_pc _ _ hspc]
      simp only [hr, lvlExp, if_neg (show ¬ (lam + 1 = fc.h) by omega)]
      rw [pcOf_add4]; rfl

theorem level_last (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam + 1 = fc.h)
    (hchk : foldCheck fc.kind fc.a1 fc.rg fc.j0 fc.h (0x800 + fc.sibOff) fc.dst = true)
    (s0 : MachineState) (v : Val) (s : MachineState) (hs : FoldInv fc s0 lam v s) :
    ∃ t, Steps image s (7 + xp fc.kind lam) (7 + xp fc.kind lam) t ∧ t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = pad64 (fc.input lam v) ∧ FoldEnd fc s0 t := by
  obtain ⟨hst, hec, h5, hK', hkeep', hglob, m1C0, msib0, msib1, mfr, hspc⟩ :=
    level_step fc hfc lam (by omega) hchk s0 v s hs
  simp only [if_pos hlam] at hst hec h5 hK' hkeep' hglob m1C0 msib0 msib1 mfr hspc
  set b := bitOf fc.E lam with hbdef
  set r := lvlExp fc.kind (if lam = 0 then fc.a1 else 64) fc.rg b fc.j0 fc.h lam
      (0x800 + fc.sibOff + 16 * lam) fc.dst 0 with hr
  have hb2 := bitOf_lt fc.E lam
  have hlo := lo0_lt fc hfc
  have hl0 : lam ≠ 0 := by have := hfc.1; omega
  obtain ⟨hG, hK, h23, hN0, hN8, hv0, hv1, hvl, hF, hpc⟩ := hs
  have hsafe := hfc.2.2.2.2.2.2.2.2.1
  simp only [lvlPost, if_pos hlam] at hK'
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0x1C0 := hK' (.x10, _) (by simp [fk])
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, _) (by simp [fk])
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 fc.dst :=
    hK' (.x12, _) (List.mem_append_right _ (List.mem_singleton_self _))
  have m1C8 : (r.toState s).getMem (BitVec.ofNat 64 0x1C8) = BitVec.ofNat 64 (fc.tau % 2 ^ 32) := by
    rw [PRes.toState_getMem, lvl_nb8, if_pos hlam]
    simp only [cw, Rv.E.eval]
    rw [stMerge_eval _ _ _ (by omega) hN8, Nat.mul_zero, Nat.add_zero]
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have mv0 : (r.toState s).getMem (BitVec.ofNat 64 (0x1E0 + 16 * b)) = vw0 v := by
    rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv0
  have mv1 : (r.toState s).getMem (BitVec.ofNat 64 (0x1E8 + 16 * b)) = vw1 v := by
    rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv1
  refine ⟨r.toState s, ?_, h5, ?_, ?_, ?_⟩
  · have e1 : r.steps = 7 + xp fc.kind lam := by simp only [hr, lvlExp, if_pos hlam, if_neg hl0]; omega
    have e2 : r.cycles = 7 + xp fc.kind lam := by simp only [hr, lvlExp, if_pos hlam, if_neg hl0]; omega
    rw [e1, e2] at hst; exact hst
  · have hs' := hsafe
    simp only [safeDest, Bool.and_eq_true, decide_eq_true_eq] at hs'
    exact hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega)
  · rw [hashInput_ofNat _ 0x1C0 0 h10 h11 (by decide) (by decide),
      pad64_input fc hfc lam (by omega) v hvl]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero]
    have hlo' : twLo fc.t fc.f2 fc.tau (lam + 1) = fc.lo0 + 2 ^ 32 * (lam + 1) := by
      unfold twLo FCtx.lo0; have := hfc.2.1; have := hfc.2.2.2.1; have := hfc.2.2.2.2.1; omega
    have hj : fc.E / 2 ^ (lam + 1) = 0 := Nat.div_eq_of_lt (by rw [hlam]; exact hfc.2.2.1)
    have hhi : twHi fc.tau (fc.E / 2 ^ (lam + 1)) = fc.tau % 2 ^ 32 := by
      unfold twHi; rw [hj]; omega
    rw [hlo', hhi, m1C0, m1C8, mfr 0x1D0 (by omega) (by omega) (by omega) (by omega) (by omega),
      mfr 0x1D8 (by omega) (by omega) (by omega) (by omega) (by omega), hP 0x1D0 (by decide),
      hP 0x1D8 (by decide)]
    rcases (show b = 0 ∨ b = 1 by omega) with h0 | h1
    · rw [h0] at mv0 mv1 msib0 msib1
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceSub] at mv0 mv1 msib0 msib1
      rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h0]
    · rw [h1] at mv0 mv1 msib0 msib1
      simp only [Nat.mul_one, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] at mv0 mv1 msib0 msib1
      rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h1]
  · refine ⟨hglob, hK', FrameOK.trans hF (fun r hr => hkeep' r hr) (fun A hA hA' => ?_), ?_,
      hec, by rw [m1C8, BitVec.toNat_ofNat]; omega⟩
    · exact mfr A hA (by omega) (by omega) (by omega) (by omega)
    · rw [PRes.toState_pc _ _ hspc]
      simp only [hr, lvlExp, if_pos hlam, if_neg hl0]
      rw [show fc.h - 1 = lam by omega]
      congr 1; rw [hbdef]; omega

/-! ## The whole fold -/

def FCtx.stepFn (fc : FCtx) : Val → Nat → OracleComp HashSpec Val := fun v lam =>
  let sib := fc.path.getD lam []
  let j := fc.E / 2 ^ (lam + 1)
  if fc.E / 2 ^ lam % 2 = 1 then hash16 (fc.node (lam + 1) j sib v)
  else hash16 (fc.node (lam + 1) j v sib)

theorem stepFn_eq (fc : FCtx) (lam : Nat) (hlam : lam < fc.h) (v : Val) :
    fc.stepFn v lam = hash16 (fc.input lam v) := by
  have : fc.path.getD lam [] = fc.sib lam := by
    simp [FCtx.path, FCtx.sib, List.getD_eq_getElem?_getD, List.getElem?_map, hlam]
  unfold FCtx.stepFn FCtx.input
  rw [this]
  split <;> rfl

theorem foldPath_eq (fc : FCtx) (v : Val) :
    foldPath fc.node fc.E v fc.path = (List.range' 0 fc.h).foldlM fc.stepFn v := by
  unfold foldPath
  rw [show fc.path.length = fc.h by simp [FCtx.path], List.range_eq_range']
  rfl

theorem xp_le (kind : Bool) (lam : Nat) : xp kind lam ≤ 1 := by unfold xp; split <;> omega

def levelCost (kind : Bool) (h lam : Nat) : Nat :=
  (if lam + 1 = h then 15 else if lam = 0 then 19 else 18) + xp kind lam

def foldCost (kind : Bool) (h lam k : Nat) : Nat := ((List.range' lam k).map (levelCost kind h)).sum

theorem fmt_input (fc : FCtx) (hfc : fc.ok) (ht1 : fc.t ≠ 1) (lam : Nat) (v : Val) :
    fmt (fc.input lam v) = pad64 (fc.input lam v) := by
  unfold FCtx.input FCtx.node nodeF
  split <;> exact fmt_th _ _ _ _ _ _ hfc.2.2.2.1 ht1

theorem fold_good (fc : FCtx) (hfc : fc.ok) (ht1 : fc.t ≠ 1)
    (hchk : foldCheck fc.kind fc.a1 fc.rg fc.j0 fc.h (0x800 + fc.sibOff) fc.dst = true) (s0 : MachineState)
    (K : Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ a u, FoldEnd fc s0 u → Good (writeHash u a) N C (K (answerBytes 16 a))) :
    ∀ k lam, lam + k = fc.h → 0 < k → ∀ v s, FoldInv fc s0 lam v s →
      Good s (N + 14 * k) (C + foldCost fc.kind fc.h lam k)
        (cc ((List.range' lam k).foldlM fc.stepFn v) K) := by
  intro k
  induction k with
  | zero => intro lam _ h; omega
  | succ k ih =>
    intro lam hk _ v s hs
    have hvl : v.length = 16 := hs.2.2.2.2.2.2.2.1
    have hblk : (pad64 (fc.input lam v)).blocks = 1 := by
      rw [pad64_input fc hfc lam (by omega) v hvl]; rfl
    rw [List.range'_succ, List.foldlM_cons, stepFn_eq fc lam (by omega), cc_bind]
    have hxp := xp_le fc.kind lam
    by_cases hlast : lam + 1 = fc.h
    · obtain rfl : k = 0 := by omega
      obtain ⟨t, hst, h5, hv, hin, hend⟩ := level_last fc hfc lam hlast hchk s0 v s hs
      simp only [List.range'_zero, List.foldlM_nil, cc_pure]
      have h3 := Good.hashP (K := K) (fmt_input fc hfc ht1 lam v) hend.2.2.2.2.1 h5 hv hin
        (fun a => hK a t hend)
      rw [hblk] at h3
      refine Good.steps' hst h3 (by omega) ?_
      simp [foldCost, levelCost, hlast]; omega
    · obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := level_lt fc hfc lam (by omega) hchk s0 v s hs
      have h3 := Good.hashP (K := fun v => cc ((List.range' (lam + 1) k).foldlM fc.stepFn v) K)
        (fmt_input fc hfc ht1 lam v) hf h5 hv hin (fun a => ih (lam + 1) (by omega) (by omega) _ _ (hpost a))
      rw [hblk] at h3
      refine Good.steps' hst h3 (by split <;> omega) ?_
      simp only [foldCost, List.range'_succ, List.map_cons, List.sum_cons, levelCost, if_neg hlast]
      split <;> omega

end SigGolfCandidate.Verify
