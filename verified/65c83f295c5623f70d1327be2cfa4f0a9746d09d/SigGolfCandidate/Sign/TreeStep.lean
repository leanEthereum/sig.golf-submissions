import SigGolfCandidate.Sign.Blocks
import SigGolfCandidate.Sign.Inv

/-!
# `sign`, tree_build: the chain steps (`tb_step_loop`, instructions 533 .. 550)

`steps_sim` : from `tb_step_loop` with `MU = 0` (value `v0` at `CB+32`), the machine refines the
seven chain steps `foldlM (step) (v0, v0) (range' 1 7)` of `buildChain`, including the capture of
the value at position `x` into the stage slot `SIGL + 8 + 16 I` (only in leaf `e`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Fixed parameters of the chain steps: layer, tree, capture leaf, current leaf, chain, digit. -/
structure StepPar where
  lay : Nat
  tau : Nat
  e : Nat
  ep : Nat
  i : Nat
  xi : Nat
  sigl : Nat

/-- Facts at the start of the step loop. -/
structure StepCtx (p : StepPar) (ts : MachineState) : Prop where
  hlay : p.lay < 7
  htau : p.tau < 2 ^ 30
  he : p.e < 32
  hep : p.ep < 32
  hi : p.i < 42
  hxi : p.xi < 8
  hsigl : p.sigl = 0x900 + 760 * p.lay
  x5 : ts.getReg .x5 = 0
  x11 : ts.getReg .x11 = BitVec.ofNat 64 64
  x13 : ts.getReg .x13 = BitVec.ofNat 64 p.e
  x18 : ts.getReg .x18 = BitVec.ofNat 64 p.sigl
  x20 : ts.getReg .x20 = BitVec.ofNat 64 p.ep
  x21 : ts.getReg .x21 = BitVec.ofNat 64 p.i
  x25 : ts.getReg .x25 = BitVec.ofNat 64 p.xi
  cb0 : lo32 (ts.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 (0x101 + 65536 * p.lay)
  cb8 : ts.getMem (BitVec.ofNat 64 0xC8) = BitVec.ofNat 64 (p.tau + 2 ^ 32 * p.ep)
  cbP : ts.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]

/-- Addresses written by the step loop. -/
def stepW (p : StepPar) (a : Nat) : Prop :=
  a = 0xC0 ∨ (0xE0 ≤ a ∧ a < 0x100) ∨
    (p.ep = p.e ∧ (a = p.sigl + 8 + 16 * p.i ∨ a = p.sigl + 16 + 16 * p.i))

def stepRegs : List Reg := [.x1, .x2, .x3, .x10, .x12, .x23, .x24]

/-- Invariant after `j` steps. -/
def StepInv (p : StepPar) (ts : MachineState) (j : Nat) (st : Val × Val) (t : MachineState) : Prop :=
  j ≤ 7 ∧ st.1.length = 16 ∧ st.2.length = 16 ∧
  t.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf st.1 ∧ t.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0] ∧
  t.pc = (if j < 7 then pcOf 533 else pcOf 551) ∧ t.getReg .x23 = BitVec.ofNat 64 j ∧
  t.getReg .x24 = BitVec.ofNat 64 (8 * p.i + j) ∧
  (p.ep = p.e → p.xi ≤ j →
    t.readWords (BitVec.ofNat 64 (p.sigl + 8 + 16 * p.i)) 2 = wordsOf st.2) ∧
  RegsEq ts t stepRegs ∧ Frame ts t (stepW p) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = lo32 (ts.getMem (BitVec.ofNat 64 0xC0))

/-- The loop test (`tb_cap1_2`, instruction 549). -/
theorem step_tail (p : StepPar) (ts : MachineState) (ctx : StepCtx p ts) (j : Nat) (hj : j < 7)
    (v cap : Val) (hv : v.length = 16) (hc : cap.length = 16) (t : MachineState)
    (tpc : t.pc = pcOf 549) (tv : t.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf v)
    (tz : t.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]) (t23 : t.getReg .x23 = BitVec.ofNat 64 (j + 1))
    (t24 : t.getReg .x24 = BitVec.ofNat 64 (8 * p.i + (j + 1)))
    (tcap : p.ep = p.e → p.xi ≤ j + 1 →
      t.readWords (BitVec.ofNat 64 (p.sigl + 8 + 16 * p.i)) 2 = wordsOf cap)
    (tregs : RegsEq ts t stepRegs) (tframe : Frame ts t (stepW p))
    (tlo : lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = lo32 (ts.getMem (BitVec.ofNat 64 0xC0))) :
    Sim image t 2 (pure (v, cap)) (StepInv p ts (j + 1)) := by
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have hi := ctx.hi
  have hs := symRun_sound blk549 codeAt_549 t tpc (by simp only [blk549.res, rv_simp])
  have hc2 : blk549.res.cycles = 2 := rfl
  rw [hc2] at hs
  set t1 := blk549.res.toState t with ht1
  have f1 : Frame t t1 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk549.res]
  have r1 : RegsEq t t1 [.x3] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  refine Sim.pure_steps hs ⟨by omega, hv, hc, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f1.readWords _ _ (by norm_num) (by simp), tv]
  · rw [f1.readWords _ _ (by norm_num) (by simp), tz]
  · simp only [ht1, blk549.res, rv_simp]
    bvsimp [t23, ofNat_bne_ofNat]
    by_cases h : j + 1 < 7
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · rw [r1.get .x23, t23]
  · rw [r1.get .x24, t24]
  · intro h1 h2
    rw [f1.readWords _ _ (by rw [ctx.hsigl]; omega) (by simp), tcap h1 h2]
  · exact (tregs.trans r1).mono (by decide)
  · exact (tframe.trans f1).mono (by intro x hx; rcases hx with h | h; exact h; exact h.elim)
  · rw [f1.getMem (by norm_num) (by simp), tlo]

/-- The capture copy (`CB+32 → SIGL + 8 + 16 I`, instructions 543 .. 548). -/
theorem step_capture (p : StepPar) (ts : MachineState) (ctx : StepCtx p ts) (t : MachineState)
    (tpc : t.pc = pcOf 543) (tregs : RegsEq ts t stepRegs) :
    ∃ t', Steps image t 6 6 t' ∧ t'.pc = pcOf 549 ∧ RegsEq t t' [.x1, .x2, .x3] ∧
      Frame t t' (fun x => x = p.sigl + 8 + 16 * p.i ∨ x = p.sigl + 16 + 16 * p.i) ∧
      t'.readWords (BitVec.ofNat 64 (p.sigl + 8 + 16 * p.i)) 2 =
        t.readWords (BitVec.ofNat 64 0xE0) 2 := by
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have hi := ctx.hi
  have t21 : t.getReg .x21 = BitVec.ofNat 64 p.i := by rw [tregs.get .x21, ctx.x21]
  have t18 : t.getReg .x18 = BitVec.ofNat 64 p.sigl := by rw [tregs.get .x18, ctx.x18]
  have hs := symRun_sound blk543 codeAt_543 t tpc (by
    simp only [blk543.res, rv_simp]; bvsimp [t21, t18, accessValid_ofNat]; omega)
  refine ⟨_, hs, by simp only [blk543.res, rv_simp], ?_, ?_, ?_⟩
  · intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro x hx hW
    simp only [blk543.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t21, t18, ofNat_eq_iff]
    omega
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    simp only [blk543.res, rv_simp]
    bvsimp [t21, t18, ofNat_eq_iff]
    simp (disch := bvomega) only [if_pos, if_neg]

theorem step_body (p : StepPar) (ts : MachineState) (ctx : StepCtx p ts) (j : Nat) (hj : j < 7)
    (st : Val × Val) (t : MachineState) (hinv : StepInv p ts j st t) :
    Sim image t 25 (do
        let v ← hash16 (chainInput p.lay p.tau p.ep p.i (1 + j) st.1)
        pure (v, if 1 + j = p.xi then v else st.2))
      (StepInv p ts (j + 1)) := by
  obtain ⟨-, hl1, hl2, tv, tz, tpc, t23, t24, tcap, tregs, tframe, tlo⟩ := hinv
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have hi := ctx.hi
  have htau := ctx.htau
  have hep := ctx.hep
  have hxi := ctx.hxi
  have he := ctx.he
  have tpc' : t.pc = pcOf 533 := by rw [tpc, if_pos hj]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5, ctx.x5]
  have tx11 : t.getReg .x11 = BitVec.ofNat 64 64 := by rw [tregs.get .x11, ctx.x11]
  -- block 533: step input
  have hs1 := symRun_sound blk533 codeAt_533 t tpc' (by simp only [blk533.res, rv_simp])
  have hc1 : blk533.res.cycles = 4 := rfl
  rw [hc1] at hs1
  set t1 := blk533.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0xC0) := by
    apply frame_toState; intro x hx hW
    simp only [blk533.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x12, .x23] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk533 codeAt_533 t (by simp only [blk533.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0xC0 := by simp only [ht1, blk533.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by rw [r1.get .x11, tx11]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0xE0 := by simp only [ht1, blk533.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have x23 : t1.getReg .x23 = BitVec.ofNat 64 (j + 1) := by
    simp only [ht1, blk533.res, rv_simp]; bvsimp [t23]
  have pc1 : t1.pc = pcOf 537 := by simp only [ht1, blk533.res, rv_simp]
  have mC0 : t1.getMem (BitVec.ofNat 64 0xC0) = twWord0 1 p.lay p.tau (8 * p.i + j) := by
    simp only [ht1, blk533.res, rv_simp]; bvsimp [t24]
    refine (word_of_halves _ (0x101 + 65536 * p.lay) (8 * p.i + j) (by rw [lo32_replace1, tlo, ctx.cb0])
      (by rw [hi32_replace1])).trans ?_
    unfold twWord0; congr 1
    rw [Nat.div_eq_of_lt (by omega : p.tau < 2 ^ 32)]; omega
  have hq : hashInput t1 = pad64 (chainInput p.lay p.tau p.ep p.i (1 + j) st.1) := by
    obtain ⟨hn, hw⟩ := words_th16 1 p.lay p.tau (8 * p.i + (1 + j) - 1) p.ep st.1 hl1
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [chainInput, hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 2 + 2 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, mC0, f1.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [stepW]; omega), ctx.cb8,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [stepW]; omega), ctx.cbP, tv, tz]
    simp only [twWords_eq, show 8 * p.i + (1 + j) - 1 = 8 * p.i + j by omega]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
    congr 1; omega
  have hb : (pad64 (chainInput p.lay p.tau p.ep p.i (1 + j) st.1)).blocks = 1 :=
    congrArg (· + 1) (words_th16 1 p.lay p.tau (8 * p.i + (1 + j) - 1) p.ep st.1 hl1).1
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 4 + 7 + 2) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set v := answerBytes 16 a with hv
  have hvl : v.length = 16 := by simp [hv]
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0xE0 ≤ x ∧ x < 0xE0 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have v2 : t2.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf v := writeHash_readWords_val t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 538 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  -- block 538: zero pad, P++, test EP = e
  have hs3 := symRun_sound blk538 codeAt_538 t2 pc2 (by simp only [blk538.res, rv_simp])
  have hc3 : blk538.res.cycles = 4 := rfl
  rw [hc3] at hs3
  set t3 := blk538.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun x => x = 0xF0 ∨ x = 0xF8) := by
    apply frame_toState; intro x hx hW
    simp only [blk538.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t2 t3 [.x24] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have rt3 : RegsEq t t3 ([.x10, .x12, .x23] ++ [] ++ [.x24]) :=
    (r1.trans (regsEq_writeHash _ _ [])).trans r3
  have x320 : t3.getReg .x20 = BitVec.ofNat 64 p.ep := by
    rw [rt3.get .x20, tregs.get .x20, ctx.x20]
  have x313 : t3.getReg .x13 = BitVec.ofNat 64 p.e := by
    rw [rt3.get .x13, tregs.get .x13, ctx.x13]
  have x323 : t3.getReg .x23 = BitVec.ofNat 64 (j + 1) := by
    rw [r3.get .x23, ht2, writeHash_getReg, x23]
  have t224 : t2.getReg .x24 = BitVec.ofNat 64 (8 * p.i + j) := by
    rw [ht2, writeHash_getReg, r1.get .x24, t24]
  have t220 : t2.getReg .x20 = BitVec.ofNat 64 p.ep := by
    rw [ht2, writeHash_getReg, r1.get .x20, tregs.get .x20, ctx.x20]
  have t213 : t2.getReg .x13 = BitVec.ofNat 64 p.e := by
    rw [ht2, writeHash_getReg, r1.get .x13, tregs.get .x13, ctx.x13]
  have x324 : t3.getReg .x24 = BitVec.ofNat 64 (8 * p.i + (j + 1)) := by
    simp only [ht3, blk538.res, rv_simp, t224, ofNat_add_ofNat]
    rw [show 8 * p.i + j + 1 = 8 * p.i + (j + 1) by ring]
  have v3 : t3.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf v := by
    rw [f3.readWords _ _ (by norm_num) (by intro i hi; omega), v2]
  have z3 : t3.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0] := by
    rw [readWords_ofNat_two]; simp only [ht3, blk538.res, rv_simp]; rfl
  have ft3 : Frame t t3 (fun x => x = 0xC0 ∨ (0xE0 ≤ x ∧ x < 0x100)) :=
    ((f1.trans f2).trans f3).mono (by intro x hx; omega)
  have fts3 : Frame ts t3 (stepW p) := (tframe.trans ft3).mono (by
    intro x hx; simp only [stepW] at hx ⊢; omega)
  have rts3 : RegsEq ts t3 stepRegs := (tregs.trans rt3).mono (by decide)
  have lo3 : lo32 (t3.getMem (BitVec.ofNat 64 0xC0)) = lo32 (ts.getMem (BitVec.ofNat 64 0xC0)) := by
    rw [f3.getMem (by norm_num) (by omega), f2.getMem (by norm_num) (by omega), mC0, ctx.cb0]
    simp only [twWord0, lo32_ofNat]
    apply BitVec.eq_of_toNat_eq; simp; omega
  have pc3 : t3.pc = if p.ep = p.e then pcOf 542 else pcOf 549 := by
    simp only [ht3, blk538.res, rv_simp, t220, t213, ofNat_bne_ofNat]
    by_cases h : p.ep = p.e
    · rw [if_pos h, if_neg (by simp; omega)]
    · rw [if_neg h, if_pos (by simp; omega)]
  have hcapold : p.ep = p.e → p.xi ≤ j →
      t3.readWords (BitVec.ofNat 64 (p.sigl + 8 + 16 * p.i)) 2 = wordsOf st.2 := by
    intro h1 h2
    rw [ft3.readWords _ _ (by omega) (by intro i hi; omega), tcap h1 h2]
  by_cases hep' : p.ep = p.e
  · -- capture leaf: test MU = X
    have hs4 := symRun_sound blk542 codeAt_542 t3 (by rw [pc3, if_pos hep'])
      (by simp only [blk542.res, rv_simp])
    have hc4 : blk542.res.cycles = 1 := rfl
    rw [hc4] at hs4
    set t4 := blk542.res.toState t3 with ht4
    have f4 : Frame t3 t4 (fun _ => False) := by
      apply frame_toState; intro x hx hW; simp [blk542.res]
    have r4 : RegsEq t3 t4 [] := by
      intro r hr; rw [ht4, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    have x325 : t3.getReg .x25 = BitVec.ofNat 64 p.xi := by
      rw [rt3.get .x25, tregs.get .x25, ctx.x25]
    have pc4 : t4.pc = if p.xi = j + 1 then pcOf 543 else pcOf 549 := by
      simp only [ht4, blk542.res, rv_simp]; bvsimp [x323, x325, ofNat_bne_ofNat]
      by_cases h : p.xi = j + 1
      · rw [if_pos h, if_neg (by simp; omega)]
      · rw [if_neg h, if_pos (by simp; omega)]
    have fts4 : Frame ts t4 (stepW p) := (fts3.trans f4).mono (by
      intro x hx; rcases hx with h | h; exact h; exact h.elim)
    by_cases hx1 : p.xi = j + 1
    · obtain ⟨t5, hs5, pc5, r5, f5, cap5⟩ := step_capture p ts ctx t4 (by rw [pc4, if_pos hx1])
        ((rts3.trans r4).mono (by decide))
      have := step_tail p ts ctx j hj v v hvl hvl t5 pc5
        (by rw [f5.readWords _ _ (by norm_num) (by intro i hi; omega),
          f4.readWords _ _ (by norm_num) (by simp), v3])
        (by rw [f5.readWords _ _ (by norm_num) (by intro i hi; omega),
          f4.readWords _ _ (by norm_num) (by simp), z3])
        (by rw [r5.get .x23, r4.get .x23, x323]) (by rw [r5.get .x24, r4.get .x24, x324])
        (fun _ _ => by rw [cap5, f4.readWords _ _ (by norm_num) (by simp), v3])
        (((rts3.trans r4).trans r5).mono (by decide))
        ((fts4.trans f5).mono (by intro x hx; simp only [stepW] at hx ⊢; omega))
        (by rw [f5.getMem (by norm_num) (by omega), f4.getMem (by norm_num) (by simp), lo3])
      rw [if_pos (by omega)]
      exact (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 this))).mono (by norm_num) (fun _ _ h => h)
    · have := step_tail p ts ctx j hj v st.2 hvl hl2 t4 (by rw [pc4, if_neg hx1])
        (by rw [f4.readWords _ _ (by norm_num) (by simp), v3])
        (by rw [f4.readWords _ _ (by norm_num) (by simp), z3])
        (by rw [r4.get .x23, x323]) (by rw [r4.get .x24, x324])
        (fun h1 h2 => by
          rw [f4.readWords _ _ (by omega) (by simp)]; exact hcapold h1 (by omega))
        ((rts3.trans r4).mono (by decide)) fts4
        (by rw [f4.getMem (by norm_num) (by simp), lo3])
      rw [if_neg (by omega)]
      exact (Sim.steps hs3 (Sim.steps hs4 this)).mono (by norm_num) (fun _ _ h => h)
  · have := step_tail p ts ctx j hj v (if 1 + j = p.xi then v else st.2) hvl
      (by split <;> assumption) t3 (by rw [pc3, if_neg hep']) v3 z3 x323 x324
      (fun h => absurd h hep') rts3 fts3 lo3
    exact (Sim.steps hs3 this).mono (by norm_num) (fun _ _ h => h)

/-- **Chain steps** `mu = 1 .. 7` (with capture). -/
theorem steps_sim (p : StepPar) (ts : MachineState) (ctx : StepCtx p ts) (v0 : Val)
    (h0 : StepInv p ts 0 (v0, v0) ts) :
    Sim image ts (7 * 25) ((List.range' 1 7).foldlM (fun (st : Val × Val) mu => do
        let v ← hash16 (chainInput p.lay p.tau p.ep p.i mu st.1)
        pure (v, if mu = p.xi then v else st.2)) (v0, v0)) (StepInv p ts 7) :=
  Sim.foldlM_range' 1 7 _ (v0, v0) (StepInv p ts) 25
    (fun j hj st t h => step_body p ts ctx j hj st t h) h0

end SigGolfCandidate.Sign
