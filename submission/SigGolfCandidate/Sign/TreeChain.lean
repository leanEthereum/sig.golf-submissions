import SigGolfCandidate.Sign.TreeStep

/-!
# `sign`, tree_build: the chains of one leaf (`tb_chain_loop`, instructions 515 .. 559)

`chains_sim` : from `tb_chain_loop` with `I = 0`, the machine refines the 42 chains of
`buildLeaf` (ends at `LB + 32 + 16 i`, captured values at `SIGL + 8 + 16 i` in leaf `e`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Parameters of the chains of leaf `ep` of tree `(lay, tau)` with capture leaf `e`. -/
structure LeafPar where
  lay : Nat
  tau : Nat
  e : Nat
  ep : Nat
  sigl : Nat

/-- Facts at the start of the chain loop of leaf `ep`. -/
structure ChainCtx (S : List Byte) (x : List Nat) (p : LeafPar) (tl : MachineState) : Prop where
  hlay : p.lay < 7
  htau : p.tau < 2 ^ 30
  he : p.e < 32
  hep : p.ep < 32
  hsigl : p.sigl = 0x900 + 760 * p.lay
  hx : ∀ i, x.getD i 0 < 8
  x5 : tl.getReg .x5 = 0
  x13 : tl.getReg .x13 = BitVec.ofNat 64 p.e
  x18 : tl.getReg .x18 = BitVec.ofNat 64 p.sigl
  x20 : tl.getReg .x20 = BitVec.ofNat 64 p.ep
  dig : ∀ i < 42, tl.getMem (BitVec.ofNat 64 (0x780 + 8 * i)) = BitVec.ofNat 64 (x.getD i 0)
  pb0 : lo32 (tl.getMem (BitVec.ofNat 64 0x6A0)) = BitVec.ofNat 32 (1 + 65536 * p.lay)
  pb8 : tl.getMem (BitVec.ofNat 64 0x6A8) = BitVec.ofNat 64 (p.tau + 2 ^ 32 * p.ep)
  pbP : tl.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : tl.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cb0 : lo32 (tl.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 (0x101 + 65536 * p.lay)
  cb8 : tl.getMem (BitVec.ofNat 64 0xC8) = BitVec.ofNat 64 (p.tau + 2 ^ 32 * p.ep)
  cbP : tl.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]

/-- Addresses written by the chain loop. -/
def chainW (p : LeafPar) (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0xC0 ∨ (0xE0 ≤ a ∧ a < 0x100) ∨ (0x360 ≤ a ∧ a < 0x360 + 672) ∨
    (p.ep = p.e ∧ p.sigl + 8 ≤ a ∧ a < p.sigl + 8 + 672)

def chainRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x21, .x23, .x24, .x25]

/-- Invariant after `i` chains. -/
def ChainInv (p : LeafPar) (tl : MachineState) (i : Nat) (st : List Val × List Val) (t : MachineState) :
    Prop :=
  i ≤ 42 ∧ st.1.length = i ∧ st.2.length = i ∧ (∀ v ∈ st.1, v.length = 16) ∧
  (∀ v ∈ st.2, v.length = 16) ∧ Slots t 0x360 st.1 ∧ (p.ep = p.e → Slots t (p.sigl + 8) st.2) ∧
  t.pc = (if i < 42 then pcOf 515 else pcOf 560) ∧ t.getReg .x21 = BitVec.ofNat 64 i ∧
  t.getReg .x24 = BitVec.ofNat 64 (8 * i) ∧
  RegsEq tl t chainRegs ∧ Frame tl t (chainW p) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A0)) = lo32 (tl.getMem (BitVec.ofNat 64 0x6A0)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = lo32 (tl.getMem (BitVec.ofNat 64 0xC0))

theorem buildChain_bind {β : Type} (S : List Byte) (lay tau e i xi : Nat)
    (g : Val × Val → OracleComp HashSpec β) :
    buildChain S lay tau e i xi >>= g =
      hash16 (prfInput S lay tau e i) >>= fun v =>
        (List.range' 1 7).foldlM (fun (st : Val × Val) mu => do
          let v ← hash16 (chainInput lay tau e i mu st.1)
          pure (v, if mu = xi then v else st.2)) (v, v) >>= g := by
  simp only [buildChain, bind_assoc]

/-- From the step loop to the end of chain `i` (steps, then instructions 551 .. 559). -/
theorem chain_rest (p : LeafPar) (tl : MachineState) (i xi : Nat) (hi : i < 42) (hxi : xi < 8)
    (st : List Val × List Val) (hl1 : st.1.length = i) (hl2 : st.2.length = i)
    (hv1 : ∀ v ∈ st.1, v.length = 16) (hv2 : ∀ v ∈ st.2, v.length = 16)
    (ts : MachineState) (sctx : StepCtx ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ ts) (v0 : Val)
    (h0 : StepInv ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ ts 0 (v0, v0) ts)
    (hends : Slots ts 0x360 st.1) (hcaps : p.ep = p.e → Slots ts (p.sigl + 8) st.2)
    (tregs : RegsEq tl ts chainRegs) (tframe : Frame tl ts (chainW p))
    (tlo1 : lo32 (ts.getMem (BitVec.ofNat 64 0x6A0)) = lo32 (tl.getMem (BitVec.ofNat 64 0x6A0)))
    (tlo2 : lo32 (ts.getMem (BitVec.ofNat 64 0xC0)) = lo32 (tl.getMem (BitVec.ofNat 64 0xC0))) :
    Sim image ts (7 * 25 + 9) ((List.range' 1 7).foldlM (fun (st : Val × Val) mu => do
        let v ← hash16 (chainInput p.lay p.tau p.ep i mu st.1)
        pure (v, if mu = xi then v else st.2)) (v0, v0) >>= fun q =>
          pure (st.1 ++ [q.1], st.2 ++ [q.2])) (ChainInv p tl (i + 1)) := by
  have hsig : p.sigl = 0x900 + 760 * p.lay := sctx.hsigl
  have hl : p.lay < 7 := sctx.hlay
  refine Sim.bind (steps_sim ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ ts sctx v0 h0)
    (fun q t5 h5 => ?_)
  obtain ⟨-, hq1, hq2, tv5, -, pc5, -, x524, cap5, sregs, sframe, slo⟩ := h5
  have pc5' : t5.pc = pcOf 551 := by rw [pc5]; rfl
  have x521 : t5.getReg .x21 = BitVec.ofNat 64 i := by rw [sregs.get .x21, sctx.x21]
  have hs6 := symRun_sound blk551 codeAt_551 t5 pc5' (by
    simp only [blk551.res, rv_simp]; bvsimp [x521, accessValid_ofNat]; omega)
  have hc6 : blk551.res.cycles = 9 := rfl
  rw [hc6] at hs6
  set t6 := blk551.res.toState t5 with ht6
  have f6 : Frame t5 t6 (fun x => x = 0x360 + 16 * i ∨ x = 0x360 + 16 * i + 8) := by
    apply frame_toState; intro x hx hW
    simp only [blk551.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [x521, ofNat_eq_iff]
    omega
  have r6 : RegsEq t5 t6 [.x1, .x2, .x3, .x21, .x24] := by
    intro r hr; rw [ht6, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have fs6 : Frame ts t6 (fun x => stepW ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ x ∨
      (x = 0x360 + 16 * i ∨ x = 0x360 + 16 * i + 8)) := sframe.trans f6
  refine Sim.pure_steps hs6 ⟨by omega, by simp [hl1], by simp [hl2], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hv1 v hv
    · simp at hv; subst hv; exact hq1
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hv2 v hv
    · simp at hv; subst hv; exact hq2
  · apply Slots.snoc
    · exact hends.frame fs6 (by omega) (by
        intro j hj; dsimp only [stepW]; constructor <;> omega)
    · rw [hl1, readWords_ofNat_two, ← tv5, readWords_ofNat_two]
      simp only [ht6, blk551.res, rv_simp]
      bvsimp [x521, ofNat_eq_iff]
      simp (disch := bvomega) only [if_pos, if_neg]
  · intro hee
    apply Slots.snoc
    · exact (hcaps hee).frame fs6 (by omega) (by
        intro j hj; dsimp only [stepW]; constructor <;> omega)
    · rw [hl2, f6.readWords _ _ (by omega) (by intro j hj; omega)]
      exact cap5 hee (show xi ≤ 7 by omega)
  · simp only [ht6, blk551.res, rv_simp]
    bvsimp [x521, ofNat_bne_ofNat]
    by_cases h : i + 1 < 42
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · simp only [ht6, blk551.res, rv_simp]; bvsimp [x521]
  · simp only [ht6, blk551.res, rv_simp]; bvsimp [x524]
    rw [show 8 * i + 7 + 1 = 8 * (i + 1) by ring]
  · exact ((tregs.trans sregs).trans r6).mono (by decide)
  · exact (tframe.trans fs6).mono (by
      intro x hx; dsimp only [chainW, stepW] at hx ⊢; omega)
  · rw [f6.getMem (by norm_num) (by omega), sframe.getMem (by norm_num) (by dsimp only [stepW]; omega),
      tlo1]
  · rw [f6.getMem (by norm_num) (by omega), slo, tlo2]

/-- The capture at `MU = 0` (instructions 527 .. 532, same code as 543 .. 548). -/
theorem chain_capture (sigl i : Nat) (hsig : sigl < 0x900 + 760 * 7) (hsig8 : sigl % 8 = 0) (hi : i < 42) (t : MachineState)
    (tpc : t.pc = pcOf 527) (t21 : t.getReg .x21 = BitVec.ofNat 64 i)
    (t18 : t.getReg .x18 = BitVec.ofNat 64 sigl) :
    ∃ t', Steps image t 6 6 t' ∧ t'.pc = pcOf 533 ∧ RegsEq t t' [.x1, .x2, .x3] ∧
      Frame t t' (fun x => x = sigl + 8 + 16 * i ∨ x = sigl + 16 + 16 * i) ∧
      t'.readWords (BitVec.ofNat 64 (sigl + 8 + 16 * i)) 2 = t.readWords (BitVec.ofNat 64 0xE0) 2 := by
  have hs := symRun_sound blk527 codeAt_527 t tpc (by
    simp only [blk527.res, rv_simp]; bvsimp [t21, t18, accessValid_ofNat]; omega)
  refine ⟨_, hs, by simp only [blk527.res, rv_simp], ?_, ?_, ?_⟩
  · intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro x hx hW
    simp only [blk527.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t21, t18, ofNat_eq_iff]
    omega
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    simp only [blk527.res, rv_simp]
    bvsimp [t21, t18, ofNat_eq_iff]
    simp (disch := bvomega) only [if_pos, if_neg]

theorem chain_body (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : LeafPar)
    (tl : MachineState) (ctx : ChainCtx S x p tl) (i : Nat) (hi : i < 42)
    (st : List Val × List Val) (t : MachineState) (hinv : ChainInv p tl i st t) :
    Sim image t (4 + (8 + (6 + (1 + (6 + (7 * 25 + 9))))))
      (do
        let (v, cv) ← buildChain S p.lay p.tau p.ep i (x.getD i 0)
        pure (st.1 ++ [v], st.2 ++ [cv]))
      (ChainInv p tl (i + 1)) := by
  obtain ⟨-, hl1, hl2, hv1, hv2, hends, hcaps, tpc, t21, t24, tregs, tframe, tlo1, tlo2⟩ := hinv
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have htau := ctx.htau
  have hep := ctx.hep
  have he := ctx.he
  have hxi := ctx.hx i
  have tpc' : t.pc = pcOf 515 := by rw [tpc, if_pos hi]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5, ctx.x5]
  have tx13 : t.getReg .x13 = BitVec.ofNat 64 p.e := by rw [tregs.get .x13, ctx.x13]
  have tx18 : t.getReg .x18 = BitVec.ofNat 64 p.sigl := by rw [tregs.get .x18, ctx.x18]
  have tx20 : t.getReg .x20 = BitVec.ofNat 64 p.ep := by rw [tregs.get .x20, ctx.x20]
  -- block 515: prf input
  have hs1 := symRun_sound blk515 codeAt_515 t tpc' (by simp only [blk515.res, rv_simp])
  have hc1 : blk515.res.cycles = 4 := rfl
  rw [hc1] at hs1
  set t1 := blk515.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x6A0) := by
    apply frame_toState; intro x hx hW
    simp only [blk515.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x11, .x12] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk515 codeAt_515 t (by simp only [blk515.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht1, blk515.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht1, blk515.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0xE0 := by simp only [ht1, blk515.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have pc1 : t1.pc = pcOf 519 := by simp only [ht1, blk515.res, rv_simp]
  have m6A0 : t1.getMem (BitVec.ofNat 64 0x6A0) = twWord0 0 p.lay p.tau i := by
    simp only [ht1, blk515.res, rv_simp]; bvsimp [t21]
    refine (word_of_halves _ (1 + 65536 * p.lay) i (by rw [lo32_replace1, tlo1, ctx.pb0])
      (by rw [hi32_replace1])).trans ?_
    unfold twWord0; congr 1
    rw [Nat.div_eq_of_lt (by omega : p.tau < 2 ^ 32)]; omega
  have hq1 : hashInput t1 = pad64 (prfInput S p.lay p.tau p.ep i) := by
    obtain ⟨hn, hw⟩ := words_prfInput S hS p.lay p.tau p.ep i
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m6A0, f1.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [chainW]; omega), ctx.pb8,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [chainW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [chainW]; omega), ctx.pbP, ctx.pbS]
    simp only [twWords_eq, List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
    congr 1; omega
  have hb1 : (pad64 (prfInput S p.lay p.tau p.ep i)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_prfInput S hS p.lay p.tau p.ep i).1]
  rw [buildChain_bind]
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 6 + (1 + (6 + (7 * 25 + 9)))) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq1 (fun a => ?_))).mono (by rw [hb1]) (fun _ _ h => h)
  set v0 := answerBytes 16 a with hv0
  have hv0l : v0.length = 16 := by simp [hv0]
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0xE0 ≤ x ∧ x < 0xE0 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have v2 : t2.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf v0 := writeHash_readWords_val t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 520 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have rt2 : RegsEq t t2 [.x10, .x11, .x12] := r1.trans (regsEq_writeHash _ _ []) |>.mono (by decide)
  have t221 : t2.getReg .x21 = BitVec.ofNat 64 i := by rw [rt2.get .x21, t21]
  -- block 520: zero pad, fetch digit, test EP = e
  have hs3 := symRun_sound blk520 codeAt_520 t2 pc2 (by
    simp only [blk520.res, rv_simp]; bvsimp [t221, accessValid_ofNat, ne_eq, ofNat_eq_iff]; omega)
  have hc3 : blk520.res.cycles = 6 := rfl
  rw [hc3] at hs3
  set t3 := blk520.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun x => x = 0xF0 ∨ x = 0xF8) := by
    apply frame_toState; intro x hx hW
    simp only [blk520.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t2 t3 [.x3, .x23, .x25] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft3 : Frame t t3 (fun x => x = 0x6A0 ∨ (0xE0 ≤ x ∧ x < 0x100)) :=
    ((f1.trans f2).trans f3).mono (by intro x hx; omega)
  have x325 : t3.getReg .x25 = BitVec.ofNat 64 (x.getD i 0) := by
    simp only [ht3, blk520.res, rv_simp]; bvsimp [t221]
    rw [show i * 8 + 1920 = 0x780 + 8 * i by ring, ((f1.trans f2).mono (fun x hx => hx)).getMem (by omega) (by omega),
      tframe.getMem (by omega) (by simp only [chainW]; omega), ctx.dig i hi]
  have x323 : t3.getReg .x23 = BitVec.ofNat 64 0 := by simp only [ht3, blk520.res, rv_simp]
  have v3 : t3.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf v0 := by
    rw [f3.readWords _ _ (by norm_num) (by intro i hi; omega), v2]
  have z3 : t3.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0] := by
    rw [readWords_ofNat_two]; simp only [ht3, blk520.res, rv_simp]; rfl
  have rt3 : RegsEq t t3 ([.x10, .x11, .x12] ++ [.x3, .x23, .x25]) := rt2.trans r3
  have pc3 : t3.pc = if p.ep = p.e then pcOf 526 else pcOf 533 := by
    have e20 : t2.getReg .x20 = BitVec.ofNat 64 p.ep := by rw [rt2.get .x20, tx20]
    have e13 : t2.getReg .x13 = BitVec.ofNat 64 p.e := by rw [rt2.get .x13, tx13]
    simp only [ht3, blk520.res, rv_simp, e20, e13, ofNat_bne_ofNat]
    by_cases h : p.ep = p.e
    · rw [if_pos h, if_neg (by simp; omega)]
    · rw [if_neg h, if_pos (by simp; omega)]
  -- common continuation from `tb_step_loop`
  have hrest : ∀ ts : MachineState, ts.pc = pcOf 533 → RegsEq t3 ts [.x1, .x2, .x3] →
      Frame t3 ts (fun x => p.ep = p.e ∧ (x = p.sigl + 8 + 16 * i ∨ x = p.sigl + 16 + 16 * i)) →
      (p.ep = p.e → x.getD i 0 ≤ 0 →
        ts.readWords (BitVec.ofNat 64 (p.sigl + 8 + 16 * i)) 2 = wordsOf v0) →
      Sim image ts (7 * 25 + 9) ((List.range' 1 7).foldlM (fun (st : Val × Val) mu => do
        let v ← hash16 (chainInput p.lay p.tau p.ep i mu st.1)
        pure (v, if mu = x.getD i 0 then v else st.2)) (v0, v0) >>= fun q =>
          pure (st.1 ++ [q.1], st.2 ++ [q.2])) (ChainInv p tl (i + 1)) := by
    intro ts tspc tsr tsf tscap
    have fts : Frame t ts (fun x => (x = 0x6A0 ∨ (0xE0 ≤ x ∧ x < 0x100)) ∨
        (p.ep = p.e ∧ (x = p.sigl + 8 + 16 * i ∨ x = p.sigl + 16 + 16 * i))) := ft3.trans tsf
    have rts : RegsEq t ts ([.x10, .x11, .x12] ++ [.x3, .x23, .x25] ++ [.x1, .x2, .x3]) :=
      rt3.trans tsr
    have sctx : StepCtx ⟨p.lay, p.tau, p.e, p.ep, i, x.getD i 0, p.sigl⟩ ts := by
      refine ⟨hl, htau, he, hep, hi, hxi, hsig, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [rts.get .x5, tx5]
      · rw [tsr.get .x11, r3.get .x11, ht2, writeHash_getReg, x11]
      · rw [rts.get .x13, tx13]
      · rw [rts.get .x18, tx18]
      · rw [rts.get .x20, tx20]
      · rw [rts.get .x21, t21]
      · rw [tsr.get .x25, x325]
      · rw [fts.getMem (by norm_num) (by omega), tlo2, ctx.cb0]
      · rw [fts.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [chainW]; omega),
          ctx.cb8]
      · rw [fts.readWords _ _ (by norm_num) (by intro j hj; omega),
          tframe.readWords _ _ (by norm_num) (by intro j hj; simp only [chainW]; omega), ctx.cbP]
    have h0 : StepInv ⟨p.lay, p.tau, p.e, p.ep, i, x.getD i 0, p.sigl⟩ ts 0 (v0, v0) ts := by
      refine ⟨by norm_num, hv0l, hv0l, ?_, ?_, by rw [tspc]; rfl, ?_, ?_, tscap,
        RegsEq.refl _ _, Frame.refl _ _, rfl⟩
      · rw [tsf.readWords _ _ (by norm_num) (by intro j hj; omega), v3]
      · rw [tsf.readWords _ _ (by norm_num) (by intro j hj; omega), z3]
      · rw [tsr.get .x23, x323]
      · show ts.getReg .x24 = BitVec.ofNat 64 (8 * i + 0)
        rw [rts.get .x24, t24, Nat.add_zero]
    exact chain_rest p tl i (x.getD i 0) hi hxi st hl1 hl2 hv1 hv2 ts sctx v0 h0
      (hends.frame fts (by omega) (by intro j hj; constructor <;> omega))
      (fun hee => (hcaps hee).frame fts (by omega) (by intro j hj; constructor <;> omega))
      ((tregs.trans rts).mono (by decide))
      ((tframe.trans fts).mono (by intro x hx; simp only [chainW] at hx ⊢; omega))
      (by rw [tsf.getMem (by norm_num) (by omega), f3.getMem (by norm_num) (by omega),
            f2.getMem (by norm_num) (by omega)]
          simp only [ht1, blk515.res, rv_simp]; bvsimp [t21]; rw [lo32_replace1, tlo1])
      (by rw [fts.getMem (by norm_num) (by omega), tlo2])
  by_cases hee : p.ep = p.e
  · have hs4 := symRun_sound blk526 codeAt_526 t3 (by rw [pc3, if_pos hee])
      (by simp only [blk526.res, rv_simp])
    have hc4 : blk526.res.cycles = 1 := rfl
    rw [hc4] at hs4
    set t4 := blk526.res.toState t3 with ht4
    have f4 : Frame t3 t4 (fun _ => False) := by
      apply frame_toState; intro x hx hW; simp [blk526.res]
    have r4 : RegsEq t3 t4 [] := by
      intro r hr; rw [ht4, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    have pc4 : t4.pc = if x.getD i 0 = 0 then pcOf 527 else pcOf 533 := by
      simp only [ht4, blk526.res, rv_simp, x323, x325, ofNat_bne_ofNat]
      by_cases h : x.getD i 0 = 0
      · rw [if_pos h, if_neg (by rw [bne_cond _ _ (by norm_num) (by omega)]; omega)]
      · rw [if_neg h, if_pos (by rw [bne_cond _ _ (by norm_num) (by omega)]; omega)]
    by_cases hx0 : x.getD i 0 = 0
    · obtain ⟨t5, hs5, pc5, r5, f5, cap5⟩ := chain_capture p.sigl i (by omega) (by omega) hi t4
        (by rw [pc4, if_pos hx0]) (by rw [r4.get .x21, rt3.get .x21, t21])
        (by rw [r4.get .x18, rt3.get .x18, tx18])
      have := hrest t5 pc5 ((r4.trans r5).mono (by decide))
        ((f4.trans f5).mono (by intro x hx; rcases hx with h | h; exact h.elim; exact ⟨hee, h⟩))
        (fun _ _ => by rw [cap5, f4.readWords _ _ (by norm_num) (by simp), v3])
      exact (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 this))).mono (by norm_num) (fun _ _ h => h)
    · have := hrest t4 (by rw [pc4, if_neg hx0]) (r4.mono (by decide))
        (f4.mono (by intro x hx; exact hx.elim)) (fun _ h => absurd (Nat.le_zero.mp h) hx0)
      exact (Sim.steps hs3 (Sim.steps hs4 this)).mono (by norm_num) (fun _ _ h => h)
  · have := hrest t3 (by rw [pc3, if_neg hee]) (RegsEq.refl _ _) (Frame.refl _ _)
      (fun h => absurd h hee)
    exact (Sim.steps hs3 this).mono (by norm_num) (fun _ _ h => h)

/-- **Chains** `i = 0 .. 41` of leaf `ep`. -/
theorem chains_sim (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : LeafPar)
    (tl : MachineState) (ctx : ChainCtx S x p tl) (hpc : tl.pc = pcOf 515)
    (h21 : tl.getReg .x21 = BitVec.ofNat 64 0) (h24 : tl.getReg .x24 = BitVec.ofNat 64 0) :
    Sim image tl (42 * 209) ((List.range nChains).foldlM (fun (st : List Val × List Val) i => do
        let (v, c) ← buildChain S p.lay p.tau p.ep i (x.getD i 0)
        pure (st.1 ++ [v], st.2 ++ [c])) ([], [])) (ChainInv p tl 42) := by
  unfold nChains
  exact Sim.foldlM_range 42 _ ([], []) (ChainInv p tl) 209
    (fun i hi st t h => chain_body S hS x p tl ctx i hi st t h)
    ⟨by norm_num, rfl, rfl, by simp, by simp, Slots.nil _ _, fun _ => Slots.nil _ _,
      by simpa using hpc, h21, by simpa using h24, RegsEq.refl _ _, Frame.refl _ _, rfl, rfl⟩

end SigGolfCandidate.Sign
