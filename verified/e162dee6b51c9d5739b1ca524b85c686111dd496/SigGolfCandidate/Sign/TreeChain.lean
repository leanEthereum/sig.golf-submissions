import SigGolfCandidate.Sign.TreeStep
import SigGolfCandidate.Sign.Pair

/-!
# `sign`, tree_build: the chains of one leaf (`tb_chain_loop`, instructions 517 .. 556)

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
  he : p.e < 64
  hep : p.ep < 64
  hsigl : p.sigl = 0x900 + 856 * p.lay
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
  cbP : tl.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0]

/-- Addresses written by the chain loop. -/
def chainW (p : LeafPar) (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0xC0 ∨ (0xF0 ≤ a ∧ a < 0x110) ∨ (0x140 ≤ a ∧ a < 0x160) ∨ (0x360 ≤ a ∧ a < 0x360 + 672) ∨
    (p.ep = p.e ∧ p.sigl + 8 ≤ a ∧ a < p.sigl + 8 + 672)

def chainRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x21, .x23, .x24, .x25, .x29]

/-- Invariant after `i` chains. -/
def ChainInv (p : LeafPar) (tl : MachineState) (i : Nat) (st : List Val × List Val) (t : MachineState) :
    Prop :=
  i ≤ 42 ∧ st.1.length = i ∧ st.2.length = i ∧ (∀ v ∈ st.1, v.length = 16) ∧
  (∀ v ∈ st.2, v.length = 16) ∧ Slots t 0x360 st.1 ∧ (p.ep = p.e → Slots t (p.sigl + 8) st.2) ∧
  t.pc = (if i < 42 then pcOf 486 else pcOf 541) ∧ t.getReg .x21 = BitVec.ofNat 64 i ∧
  t.getReg .x24 = BitVec.ofNat 64 (8 * i) ∧
  RegsEq tl t chainRegs ∧ Frame tl t (chainW p) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A0)) = lo32 (tl.getMem (BitVec.ofNat 64 0x6A0)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = lo32 (tl.getMem (BitVec.ofNat 64 0xC0))

/-- The paired-secret leaf body as a bind chain. -/
theorem chain_pair_spec (S : List Byte) (lay tau ep k : Nat) (x : List Nat) (st : List Val × List Val) :
    (do
      let (s0, s1) ← prf2 (prfInput S lay tau ep k)
      let (v0, c0) ← chainSteps lay tau ep (2 * k) (x.getD (2 * k) 0) s0
      let (v1, c1) ← chainSteps lay tau ep (2 * k + 1) (x.getD (2 * k + 1) 0) s1
      pure (st.1 ++ [v0, v1], st.2 ++ [c0, c1]) : OracleComp HashSpec (List Val × List Val)) =
    H (prfInput S lay tau ep k) >>= fun a =>
      (chainSteps lay tau ep (2 * k) (x.getD (2 * k) 0) (answerBytes 16 a) >>= fun q =>
        pure (st.1 ++ [q.1], st.2 ++ [q.2])) >>= fun r =>
      chainSteps lay tau ep (2 * k + 1) (x.getD (2 * k + 1) 0) (hiVal a) >>= fun q =>
        pure (r.1 ++ [q.1], r.2 ++ [q.2]) := by
  simp only [prf2_eq, bind_assoc, pure_bind, List.append_assoc, List.cons_append, List.nil_append]

/-- The secret region `SEC` is untouched. -/
def SecPres (s t : MachineState) : Prop :=
  ∀ x, x < 2 ^ 64 → 0x140 ≤ x → x < 0x160 → t.getMem (BitVec.ofNat 64 x) = s.getMem (BitVec.ofNat 64 x)

/-- From the step loop to the end of chain `i` (steps, then instructions 548 .. 556). -/
theorem chain_rest (p : LeafPar) (tl : MachineState) (i xi : Nat) (hi : i < 42) (hxi : xi < 8)
    (st : List Val × List Val) (hl1 : st.1.length = i) (hl2 : st.2.length = i)
    (hv1 : ∀ v ∈ st.1, v.length = 16) (hv2 : ∀ v ∈ st.2, v.length = 16)
    (ts : MachineState) (sctx : StepCtx ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ ts) (v0 : Val)
    (h0 : StepInv ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ ts 0 (v0, v0) ts)
    (hends : Slots ts 0x360 st.1) (hcaps : p.ep = p.e → Slots ts (p.sigl + 8) st.2)
    (tregs : RegsEq tl ts chainRegs) (tframe : Frame tl ts (chainW p))
    (tlo1 : lo32 (ts.getMem (BitVec.ofNat 64 0x6A0)) = lo32 (tl.getMem (BitVec.ofNat 64 0x6A0)))
    (tlo2 : lo32 (ts.getMem (BitVec.ofNat 64 0xC0)) = lo32 (tl.getMem (BitVec.ofNat 64 0xC0))) :
    Sim image ts (7 * 29 + 9) ((List.range' 1 7).foldlM (fun (st : Val × Val) mu => do
        let v ← hash16 (chainInput p.lay p.tau p.ep i mu st.1)
        pure (v, if mu = xi then v else st.2)) (v0, v0) >>= fun q =>
          pure (st.1 ++ [q.1], st.2 ++ [q.2]))
      (fun r t' => ChainInv p tl (i + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧ SecPres ts t') := by
  have hsig : p.sigl = 0x900 + 856 * p.lay := sctx.hsigl
  have hl : p.lay < 7 := sctx.hlay
  refine Sim.bind (steps_sim ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ ts sctx v0 h0)
    (fun q t5 h5 => ?_)
  obtain ⟨-, hq1, hq2, tv5, -, pc5, -, x524, cap5, sregs, sframe, slo⟩ := h5
  have pc5' : t5.pc = pcOf 532 := by rw [pc5]; rfl
  have x521 : t5.getReg .x21 = BitVec.ofNat 64 i := by rw [sregs.get .x21, sctx.x21]
  have hs6 := symRun_sound blk532 codeAt_532 t5 pc5' (by
    simp only [blk532.res, rv_simp]; bvsimp [x521, accessValid_ofNat]; omega)
  have hc6 : blk532.res.cycles = 9 := rfl
  rw [hc6] at hs6
  set t6 := blk532.res.toState t5 with ht6
  have f6 : Frame t5 t6 (fun x => x = 0x360 + 16 * i ∨ x = 0x360 + 16 * i + 8) := by
    apply frame_toState; intro x hx hW
    simp only [blk532.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [x521, ofNat_eq_iff]
    omega
  have r6 : RegsEq t5 t6 [.x1, .x2, .x3, .x21, .x24] := by
    intro r hr; rw [ht6, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have fs6 : Frame ts t6 (fun x => stepW ⟨p.lay, p.tau, p.e, p.ep, i, xi, p.sigl⟩ x ∨
      (x = 0x360 + 16 * i ∨ x = 0x360 + 16 * i + 8)) := sframe.trans f6
  refine Sim.pure_steps hs6 ⟨⟨by omega, by simp [hl1], by simp [hl2], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, by rw [r6.get .x11, sregs.get .x11, sctx.x11],
    fun x hx h1 h2 => fs6.getMem hx (by dsimp only [stepW]; omega)⟩
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
      simp only [ht6, blk532.res, rv_simp]
      bvsimp [x521, ofNat_eq_iff]
      simp (disch := bvomega) only [if_pos, if_neg]
  · intro hee
    apply Slots.snoc
    · exact (hcaps hee).frame fs6 (by omega) (by
        intro j hj; dsimp only [stepW]; constructor <;> omega)
    · rw [hl2, f6.readWords _ _ (by omega) (by intro j hj; omega)]
      exact cap5 hee (show xi ≤ 7 by omega)
  · simp only [ht6, blk532.res, rv_simp]
    bvsimp [x521, ofNat_bne_ofNat]
    by_cases h : i + 1 < 42
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · simp only [ht6, blk532.res, rv_simp]; bvsimp [x521]
  · simp only [ht6, blk532.res, rv_simp]; bvsimp [x524]
    rw [show 8 * i + 7 + 1 = 8 * (i + 1) by ring]
  · exact ((tregs.trans sregs).trans r6).mono (by decide)
  · exact (tframe.trans fs6).mono (by
      intro x hx; dsimp only [chainW, stepW] at hx ⊢; omega)
  · rw [f6.getMem (by norm_num) (by omega), sframe.getMem (by norm_num) (by dsimp only [stepW]; omega),
      tlo1]
  · rw [f6.getMem (by norm_num) (by omega), slo, tlo2]

/-- The capture at `MU = 0` (instructions 527 .. 532, same code as 540 .. 545). -/
theorem chain_capture (sigl i : Nat) (hsig : sigl < 0x900 + 856 * 7) (hsig8 : sigl % 8 = 0) (hi : i < 42) (t : MachineState)
    (tpc : t.pc = pcOf 507) (t21 : t.getReg .x21 = BitVec.ofNat 64 i)
    (t18 : t.getReg .x18 = BitVec.ofNat 64 sigl) :
    ∃ t', Steps image t 6 6 t' ∧ t'.pc = pcOf 513 ∧ RegsEq t t' [.x1, .x2, .x3] ∧
      Frame t t' (fun x => x = sigl + 8 + 16 * i ∨ x = sigl + 16 + 16 * i) ∧
      t'.readWords (BitVec.ofNat 64 (sigl + 8 + 16 * i)) 2 = t.readWords (BitVec.ofNat 64 0xF0) 2 := by
  have hs := symRun_sound blk507 codeAt_507 t tpc (by
    simp only [blk507.res, rv_simp]; bvsimp [t21, t18, accessValid_ofNat]; omega)
  refine ⟨_, hs, by simp only [blk507.res, rv_simp], ?_, ?_, ?_⟩
  · intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro x hx hW
    simp only [blk507.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t21, t18, ofNat_eq_iff]
    omega
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    simp only [blk507.res, rv_simp]
    bvsimp [t21, t18, ofNat_eq_iff]
    simp (disch := bvomega) only [if_pos, if_neg]

/-- Chain `i` of leaf `ep` from `prf_have` (instruction 492): its secret `s` at `SEC + 16 (i & 1)`. -/
theorem chain_B (x : List Nat) (p : LeafPar) (S : List Byte)
    (tl : MachineState) (ctx : ChainCtx S x p tl) (i : Nat) (hi : i < 42) (s : Val) (hs : s.length = 16)
    (st : List Val × List Val) (hl1 : st.1.length = i) (hl2 : st.2.length = i)
    (hv1 : ∀ v ∈ st.1, v.length = 16) (hv2 : ∀ v ∈ st.2, v.length = 16)
    (t : MachineState) (hends : Slots t 0x360 st.1) (hcaps : p.ep = p.e → Slots t (p.sigl + 8) st.2)
    (tpc : t.pc = pcOf 494) (t21 : t.getReg .x21 = BitVec.ofNat 64 i)
    (t24 : t.getReg .x24 = BitVec.ofNat 64 (8 * i)) (t11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (tsec : t.readWords (BitVec.ofNat 64 (0x140 + 16 * (i % 2))) 2 = wordsOf s)
    (tregs : RegsEq tl t chainRegs) (tframe : Frame tl t (chainW p))
    (tlo1 : lo32 (t.getMem (BitVec.ofNat 64 0x6A0)) = lo32 (tl.getMem (BitVec.ofNat 64 0x6A0)))
    (tlo2 : lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = lo32 (tl.getMem (BitVec.ofNat 64 0xC0))) :
    Sim image t (12 + (1 + (6 + (7 * 29 + 9))))
      (chainSteps p.lay p.tau p.ep i (x.getD i 0) s >>= fun q => pure (st.1 ++ [q.1], st.2 ++ [q.2]))
      (fun r t' => ChainInv p tl (i + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧ SecPres t t') := by
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have htau := ctx.htau
  have hep := ctx.hep
  have he := ctx.he
  have hxi := ctx.hx i
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5, ctx.x5]
  have tx13 : t.getReg .x13 = BitVec.ofNat 64 p.e := by rw [tregs.get .x13, ctx.x13]
  have tx18 : t.getReg .x18 = BitVec.ofNat 64 p.sigl := by rw [tregs.get .x18, ctx.x18]
  have tx20 : t.getReg .x20 = BitVec.ofNat 64 p.ep := by rw [tregs.get .x20, ctx.x20]
  have hi2 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  -- block 492: secret → CB+48, step setup, digit, test EP = e
  have hs3 := symRun_sound blk494 codeAt_494 t tpc (by
    simp only [blk494.res, rv_simp]
    rw [t21, secAddr i (by omega) 328 (by norm_num), secAddr i (by omega) 320 (by norm_num)]
    bvsimp [accessValid_ofNat, ne_eq, ofNat_eq_iff]; omega)
  have hc3 : blk494.res.cycles = 12 := rfl
  rw [hc3] at hs3
  set t3 := blk494.res.toState t with ht3
  have f3 : Frame t t3 (fun x => x = 0xF0 ∨ x = 0xF8) := by
    apply frame_toState; intro x hx hW
    simp only [blk494.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t t3 [.x1, .x2, .x3, .x10, .x12, .x23, .x25] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft3 : Frame t t3 (fun x => 0xF0 ≤ x ∧ x < 0x110) :=
    f3.mono (by intro x hx; omega)
  have x325 : t3.getReg .x25 = BitVec.ofNat 64 (x.getD i 0) := by
    simp only [ht3, blk494.res, rv_simp]; bvsimp [t21]
    rw [show i * 8 + 1920 = 0x780 + 8 * i by ring, tframe.getMem (by omega) (by simp only [chainW]; omega),
      ctx.dig i hi]
  have x323 : t3.getReg .x23 = BitVec.ofNat 64 0 := by simp only [ht3, blk494.res, rv_simp]
  have x312 : t3.getReg .x12 = BitVec.ofNat 64 0xF0 := by simp only [ht3, blk494.res, rv_simp]
  have v3 : t3.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf s := by
    rw [← tsec, readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht3, blk494.res, rv_simp, t21]
    rw [secAddr i (by omega) 328 (by norm_num), secAddr i (by omega) 320 (by norm_num)]
    simp (config := { decide := true }) only [↓reduceIte]
    rw [show 328 + 16 * (i % 2) = 0x140 + 16 * (i % 2) + 8 by omega]
  have z3 : t3.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0] := by
    rw [ft3.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [chainW]; omega), ctx.cbP]
  have pc3 : t3.pc = if p.ep = p.e then pcOf 506 else pcOf 513 := by
    simp only [ht3, blk494.res, rv_simp, tx20, tx13, ofNat_bne_ofNat]
    by_cases h : p.ep = p.e
    · rw [if_pos h, if_neg (by simp; omega)]
    · rw [if_neg h, if_pos (by simp; omega)]
  -- common continuation from `tb_step_loop`
  have hrest : ∀ ts : MachineState, ts.pc = pcOf 513 → RegsEq t3 ts [.x1, .x2, .x3] →
      Frame t3 ts (fun x => p.ep = p.e ∧ (x = p.sigl + 8 + 16 * i ∨ x = p.sigl + 16 + 16 * i)) →
      (p.ep = p.e → x.getD i 0 ≤ 0 →
        ts.readWords (BitVec.ofNat 64 (p.sigl + 8 + 16 * i)) 2 = wordsOf s) →
      Sim image ts (7 * 29 + 9)
        (chainSteps p.lay p.tau p.ep i (x.getD i 0) s >>= fun q => pure (st.1 ++ [q.1], st.2 ++ [q.2]))
        (fun r t' => ChainInv p tl (i + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧ SecPres t t') := by
    intro ts tspc tsr tsf tscap
    have fts : Frame t ts (fun x => (0xF0 ≤ x ∧ x < 0x110) ∨
        (p.ep = p.e ∧ (x = p.sigl + 8 + 16 * i ∨ x = p.sigl + 16 + 16 * i))) := ft3.trans tsf
    have rts : RegsEq t ts ([.x1, .x2, .x3, .x10, .x12, .x23, .x25] ++ [.x1, .x2, .x3]) :=
      r3.trans tsr
    have sctx : StepCtx ⟨p.lay, p.tau, p.e, p.ep, i, x.getD i 0, p.sigl⟩ ts := by
      refine ⟨hl, htau, he, hep, hi, hxi, hsig, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [rts.get .x5, tx5]
      · rw [rts.get .x11, t11]
      · rw [tsr.get .x12, x312]
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
    have h0 : StepInv ⟨p.lay, p.tau, p.e, p.ep, i, x.getD i 0, p.sigl⟩ ts 0 (s, s) ts := by
      refine ⟨by norm_num, hs, hs, ?_, ?_, by rw [tspc]; rfl, ?_, ?_, tscap,
        RegsEq.refl _ _, Frame.refl _ _, rfl⟩
      · rw [tsf.readWords _ _ (by norm_num) (by intro j hj; omega), v3]
      · rw [tsf.readWords _ _ (by norm_num) (by intro j hj; omega), z3]
      · rw [tsr.get .x23, x323]
      · show ts.getReg .x24 = BitVec.ofNat 64 (8 * i + 0)
        rw [rts.get .x24, t24, Nat.add_zero]
    have := chain_rest p tl i (x.getD i 0) hi hxi st hl1 hl2 hv1 hv2 ts sctx s h0
      (hends.frame fts (by omega) (by intro j hj; constructor <;> omega))
      (fun hee => (hcaps hee).frame fts (by omega) (by intro j hj; constructor <;> omega))
      ((tregs.trans rts).mono (by decide))
      ((tframe.trans fts).mono (by intro x hx; simp only [chainW] at hx ⊢; omega))
      (by rw [fts.getMem (by norm_num) (by omega), tlo1])
      (by rw [fts.getMem (by norm_num) (by omega), tlo2])
    unfold chainSteps
    exact this.mono (le_refl _) (fun r t' h => ⟨h.1, h.2.1, fun y hy h1 h2 => by
      rw [h.2.2 y hy h1 h2, fts.getMem hy (by omega)]⟩)
  by_cases hee : p.ep = p.e
  · have hs4 := symRun_sound blk506 codeAt_506 t3 (by rw [pc3, if_pos hee])
      (by simp only [blk506.res, rv_simp])
    have hc4 : blk506.res.cycles = 1 := rfl
    rw [hc4] at hs4
    set t4 := blk506.res.toState t3 with ht4
    have f4 : Frame t3 t4 (fun _ => False) := by
      apply frame_toState; intro x hx hW; simp [blk506.res]
    have r4 : RegsEq t3 t4 [] := by
      intro r hr; rw [ht4, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    have pc4 : t4.pc = if x.getD i 0 = 0 then pcOf 507 else pcOf 513 := by
      simp only [ht4, blk506.res, rv_simp, x323, x325, ofNat_bne_ofNat]
      by_cases h : x.getD i 0 = 0
      · rw [if_pos h, if_neg (by rw [bne_cond _ _ (by norm_num) (by omega)]; omega)]
      · rw [if_neg h, if_pos (by rw [bne_cond _ _ (by norm_num) (by omega)]; omega)]
    by_cases hx0 : x.getD i 0 = 0
    · obtain ⟨t5, hs5, pc5, r5, f5, cap5⟩ := chain_capture p.sigl i (by omega) (by omega) hi t4
        (by rw [pc4, if_pos hx0]) (by rw [r4.get .x21, r3.get .x21, t21])
        (by rw [r4.get .x18, r3.get .x18, tx18])
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

theorem chain_pair (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : LeafPar)
    (tl : MachineState) (ctx : ChainCtx S x p tl) (k : Nat) (hk : k < 21)
    (st : List Val × List Val) (t : MachineState) (hinv : ChainInv p tl (2 * k) st t) :
    Sim image t 480
      (do
        let (s0, s1) ← prf2 (prfInput S p.lay p.tau p.ep k)
        let (v0, c0) ← chainSteps p.lay p.tau p.ep (2 * k) (x.getD (2 * k) 0) s0
        let (v1, c1) ← chainSteps p.lay p.tau p.ep (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (st.1 ++ [v0, v1], st.2 ++ [c0, c1]))
      (ChainInv p tl (2 * k + 2)) := by
  rw [chain_pair_spec]
  obtain ⟨-, hl1, hl2, hv1, hv2, hends, hcaps, tpc, t21, t24, tregs, tframe, tlo1, tlo2⟩ := hinv
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have htau := ctx.htau
  have hep := ctx.hep
  have tpc' : t.pc = pcOf 486 := by rw [tpc, if_pos (by omega)]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5, ctx.x5]
  -- block 484: even
  have hs0 := symRun_sound blk486 codeAt_486 t tpc' (by simp only [blk486.res, rv_simp])
  have hc0 : blk486.res.cycles = 2 := rfl
  rw [hc0] at hs0
  set t1 := blk486.res.toState t with ht1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk486.res.st.mem = [] from rfl, memEval_nil]
  have r1 : RegsEq t t1 [.x3] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc1 : t1.pc = pcOf 488 := by
    simp only [ht1, blk486.res, rv_simp, t21]
    rw [and_one_ofNat _ (by omega), if_neg (by rw [ofNat_bne_ofNat]; simp)]
  -- block 486: the paired prf query
  have hs2 := symRun_sound blk488 codeAt_488 t1 pc1 (by simp only [blk488.res, rv_simp])
  have hc2 : blk488.res.cycles = 5 := rfl
  rw [hc2] at hs2
  set t2 := blk488.res.toState t1 with ht2
  have f2 : Frame t1 t2 (fun x => x = 0x6A0) := by
    apply frame_toState; intro x hx hW
    simp only [blk488.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r2 : RegsEq t1 t2 [.x3, .x10, .x11, .x12] := by
    intro r hr; rw [ht2, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e2 := symRun_ecall blk488 codeAt_488 t1 (by simp only [blk488.res, rv_simp]) rfl
  have x10 : t2.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht2, blk488.res, rv_simp]
  have x11 : t2.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht2, blk488.res, rv_simp]
  have x12 : t2.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht2, blk488.res, rv_simp]
  have x5 : t2.getReg .x5 = 0 := by rw [r2.get .x5, r1.get .x5, tx5]
  have pc2 : t2.pc = pcOf 493 := by simp only [ht2, blk488.res, rv_simp]
  have t121 : t1.getReg .x21 = BitVec.ofNat 64 (2 * k) := by rw [r1.get .x21, t21]
  have m6A0 : t2.getMem (BitVec.ofNat 64 0x6A0) = twWord0 0 p.lay p.tau k := by
    simp only [ht2, blk488.res, rv_simp, t121]
    bvsimp []
    rw [show 2 * k / 2 = k by omega]
    refine (word_of_halves _ (1 + 65536 * p.lay) k (by rw [lo32_replace1, m1, tlo1, ctx.pb0])
      (by rw [hi32_replace1])).trans ?_
    unfold twWord0; congr 1
    rw [Nat.div_eq_of_lt (by omega : p.tau < 2 ^ 32)]; omega
  have ft2 : Frame t t2 (fun x => x = 0x6A0) := fun z hz hW => by rw [f2.getMem hz hW, m1]
  have hq : hashInput t2 = pad64 (prfInput S p.lay p.tau p.ep k) := by
    obtain ⟨hn, hw⟩ := words_prfInput S hS p.lay p.tau p.ep k
    refine hashInput_eq_pad64 t2 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m6A0, ft2.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [chainW]; omega), ctx.pb8,
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [chainW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [chainW]; omega), ctx.pbP, ctx.pbS]
    simp only [twWords_eq, List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
    congr 1; omega
  have hb : (pad64 (prfInput S p.lay p.tau p.ep k)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_prfInput S hS p.lay p.tau p.ep k).1]
  refine (Sim.steps hs0 (Sim.steps hs2 (Sim.query_bind (W := 231 + (2 + 231)) e2 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (hq.trans (fmt_thInput _ _ _ _ _ _ (by decide)).symm) (fun a => ?_)))).mono
    (by rw [show prfInput S p.lay p.tau p.ep k = thInput (tweak 0 p.lay p.tau k p.ep) S from rfl] at *; rw [blocks_fmt_th _ _ _ _ _ _ (by decide)]
        rw [hb]; norm_num)
    (fun _ _ h => h)
  set t3 := writeHash t2 a with ht3
  have f3 : Frame t2 t3 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t2 a _ x12 (by norm_num)
  have pc3 : t3.pc = pcOf 494 := by rw [ht3, writeHash_pc, pc2]; apply BitVec.eq_of_toNat_eq; simp
  have g3 : ∀ q, t3.getReg q = t2.getReg q := fun q => by rw [ht3, writeHash_getReg]
  have ft3 : Frame t t3 (fun x => x = 0x6A0 ∨ (0x140 ≤ x ∧ x < 0x140 + 32)) := ft2.trans f3
  have rt3 : RegsEq tl t3 chainRegs := ((tregs.trans r1).trans r2 |>.trans
    (show RegsEq t2 t3 [] from fun q _ => g3 q)).mono (by decide)
  have hA := chain_B x p S tl ctx (2 * k) (by omega) (answerBytes 16 a) (by simp) st hl1 hl2 hv1 hv2 t3
    (hends.frame ft3 (by omega) (by intro i hi; constructor <;> omega))
    (fun hee => (hcaps hee).frame ft3 (by rw [ctx.hsigl]; omega) (by
      intro i hi; rw [ctx.hsigl]; constructor <;> omega))
    pc3 (by rw [g3, r2.get .x21, t121]) (by rw [g3, r2.get .x24, r1.get .x24, t24])
    (by rw [g3, x11])
    (by rw [show 0x140 + 16 * (2 * k % 2) = 0x140 by omega]; exact sec_lo t2 a x12)
    rt3 ((tframe.trans ft3).mono (by intro x hx; simp only [chainW] at hx ⊢; omega))
    (by rw [f3.getMem (by norm_num) (by omega), m6A0, ctx.pb0]; simp only [twWord0, lo32_ofNat]
        apply BitVec.eq_of_toNat_eq; simp; omega)
    (by rw [ft3.getMem (by norm_num) (by omega), tlo2])
  refine Sim.bind hA (fun r t4 h4 => ?_)
  obtain ⟨⟨-, hl14, hl24, hv14, hv24, hends4, hcaps4, tpc4, t421, t424, tregs4, tframe4, tlo14, tlo24⟩,
    x411, sec4⟩ := h4
  -- block 484: odd
  have hs5 := symRun_sound blk486 codeAt_486 t4 (by rw [tpc4, if_pos (by omega)])
    (by simp only [blk486.res, rv_simp])
  have hc5 : blk486.res.cycles = 2 := rfl
  rw [hc5] at hs5
  set t5 := blk486.res.toState t4 with ht5
  have m5 : ∀ z, t5.getMem z = t4.getMem z := fun z => by
    rw [ht5, Result.toState_getMem, show blk486.res.st.mem = [] from rfl, memEval_nil]
  have r5 : RegsEq t4 t5 [.x3] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc5 : t5.pc = pcOf 494 := by
    simp only [ht5, blk486.res, rv_simp, t421]
    rw [and_one_ofNat _ (by omega), if_pos (by rw [ofNat_bne_ofNat]; simp)]
  have fr5 : Frame t4 t5 (fun _ => False) := fun z _ _ => m5 _
  have hB := chain_B x p S tl ctx (2 * k + 1) (by omega) (hiVal a) (by simp) r hl14 hl24 hv14 hv24 t5
    (hends4.frame fr5 (by omega) (by simp)) (fun hee => (hcaps4 hee).frame fr5 (by rw [ctx.hsigl]; omega)
      (by simp)) pc5 (by rw [r5.get .x21, t421]) (by rw [r5.get .x24, t424]) (by rw [r5.get .x11, x411])
    (by
      rw [show 0x140 + 16 * ((2 * k + 1) % 2) = 0x150 by omega, readWords_ofNat_two, m5, m5,
        sec4 _ (by norm_num) (by norm_num) (by norm_num), sec4 _ (by norm_num) (by norm_num) (by norm_num),
        ← readWords_ofNat_two]
      exact sec_hi t2 a x12)
    ((tregs4.trans r5).mono (by decide))
    ((tframe4.trans fr5).mono (by intro x hx; rcases hx with h | h; exact h; exact h.elim))
    (by rw [m5, tlo14]) (by rw [m5, tlo24])
  exact (Sim.steps hs5 hB).mono (by norm_num) (fun _ _ h => h.1)

/-- **Chains** `i = 0 .. 41` of leaf `ep` (pairs `k = 0 .. 20`). -/
theorem chains_sim (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : LeafPar)
    (tl : MachineState) (ctx : ChainCtx S x p tl) (hpc : tl.pc = pcOf 486)
    (h21 : tl.getReg .x21 = BitVec.ofNat 64 0) (h24 : tl.getReg .x24 = BitVec.ofNat 64 0) :
    Sim image tl (21 * 480) ((List.range (nChains / 2)).foldlM (fun (st : List Val × List Val) k => do
        let (s0, s1) ← prf2 (prfInput S p.lay p.tau p.ep k)
        let (v0, c0) ← chainSteps p.lay p.tau p.ep (2 * k) (x.getD (2 * k) 0) s0
        let (v1, c1) ← chainSteps p.lay p.tau p.ep (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (st.1 ++ [v0, v1], st.2 ++ [c0, c1])) ([], [])) (ChainInv p tl 42) := by
  unfold nChains
  exact Sim.foldlM_range 21 _ ([], []) (fun k => ChainInv p tl (2 * k)) 480
    (fun k hk st t h => by rw [show 2 * (k + 1) = 2 * k + 2 by ring]; exact chain_pair S hS x p tl ctx k hk st t h)
    ⟨by norm_num, rfl, rfl, by simp, by simp, Slots.nil _ _, fun _ => Slots.nil _ _,
      by simpa using hpc, h21, by simpa using h24, RegsEq.refl _ _, Frame.refl _ _, rfl, rfl⟩

end SigGolfCandidate.Sign
