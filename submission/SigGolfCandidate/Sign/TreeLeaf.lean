import SigGolfCandidate.Sign.TreeChain

/-!
# `sign`, tree_build: the leaves (`tb_leaf_loop`, instructions 510 .. 563)

`leaves_sim` : from `tb_leaf_loop` with `EP = 0`, the machine refines `buildLeaves S lay tau h e x`:
leaf `j` in `TA + 16 j`, the captured chain values of leaf `e` at `SIGL + 8 + 16 i`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Parameters of a tree: layer, tree index, height, capture leaf, stage base. -/
structure TreePar where
  lay : Nat
  tau : Nat
  h : Nat
  e : Nat
  sigl : Nat

/-- Facts at the start of tree_build's leaf loop. -/
structure TreeCtx (S : List Byte) (x : List Nat) (p : TreePar) (tt : MachineState) : Prop where
  hlay : p.lay < 7
  htau : p.tau < 2 ^ 30
  hh : p.h ≤ 6
  he : p.e < 2 ^ p.h
  hsigl : p.sigl = 0x900 + 856 * p.lay
  hheight : p.h = height p.lay
  hx : ∀ i, x.getD i 0 < 8
  x5 : tt.getReg .x5 = 0
  x8 : tt.getReg .x8 = BitVec.ofNat 64 p.lay
  x9 : tt.getReg .x9 = BitVec.ofNat 64 p.h
  x13 : tt.getReg .x13 = BitVec.ofNat 64 p.e
  x17 : tt.getReg .x17 = BitVec.ofNat 64 (2 ^ p.h)
  x18 : tt.getReg .x18 = BitVec.ofNat 64 p.sigl
  x19 : tt.getReg .x19 = BitVec.ofNat 64 0x34100
  x30 : tt.getReg .x30 = BitVec.ofNat 64 p.tau
  dig : ∀ i < 42, tt.getMem (BitVec.ofNat 64 (0x780 + 8 * i)) = BitVec.ofNat 64 (x.getD i 0)
  pb0 : lo32 (tt.getMem (BitVec.ofNat 64 0x6A0)) = BitVec.ofNat 32 (1 + 65536 * p.lay)
  pbP : tt.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : tt.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cb0 : lo32 (tt.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 (0x101 + 65536 * p.lay)
  cbP : tt.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0]
  lb0 : tt.getMem (BitVec.ofNat 64 0x340) = twWord0 2 p.lay p.tau 0
  lbP : tt.readWords (BitVec.ofNat 64 0x350) 2 = [0, 0]
  nbP : tt.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0]

/-- Addresses written by the leaf loop. -/
def leavesW (p : TreePar) (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ (0xF0 ≤ a ∧ a < 0x110) ∨ (0x140 ≤ a ∧ a < 0x160) ∨ a = 0x348 ∨
    (0x360 ≤ a ∧ a < 0x360 + 672) ∨ (p.sigl + 8 ≤ a ∧ a < p.sigl + 8 + 672) ∨
    (0x34100 ≤ a ∧ a < 0x34100 + 16 * 65)

def leavesRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x20, .x21, .x23, .x24, .x25, .x29]

/-- Invariant after `j` leaves. -/
def TLeafInv (p : TreePar) (tt : MachineState) (j : Nat) (st : List Val × List Val) (t : MachineState) :
    Prop :=
  j ≤ 2 ^ p.h ∧ st.1.length = j ∧ (∀ v ∈ st.1, v.length = 16) ∧ Slots t 0x34100 st.1 ∧
  (p.e < j → st.2.length = 42 ∧ (∀ v ∈ st.2, v.length = 16) ∧ Slots t (p.sigl + 8) st.2) ∧
  t.pc = (if j < 2 ^ p.h then pcOf 479 else pcOf 548) ∧ t.getReg .x20 = BitVec.ofNat 64 j ∧
  RegsEq tt t leavesRegs ∧ Frame tt t (leavesW p) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A0)) = lo32 (tt.getMem (BitVec.ofNat 64 0x6A0)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = lo32 (tt.getMem (BitVec.ofNat 64 0xC0))

theorem buildLeaf_bind {β : Type} (S : List Byte) (lay tau e : Nat) (x : List Nat)
    (g : Val × List Val → OracleComp HashSpec β) :
    buildLeaf S lay tau e x >>= g =
      (List.range (nChains / 2)).foldlM (fun (st : List Val × List Val) k => do
        let (s0, s1) ← prf2 (prfInput S lay tau e k)
        let (v0, c0) ← chainSteps lay tau e (2 * k) (x.getD (2 * k) 0) s0
        let (v1, c1) ← chainSteps lay tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (st.1 ++ [v0, v1], st.2 ++ [c0, c1])) ([], []) >>= fun st =>
          hash16 (leafInput lay tau e st.1) >>= fun leaf => g (leaf, st.2) := by
  simp only [buildLeaf, bind_assoc, pure_bind]

theorem pow_le32 (h : Nat) (hh : h ≤ 6) : 2 ^ h ≤ 64 :=
  calc 2 ^ h ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hh
    _ = 64 := by norm_num

theorem tleaf_body (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : TreePar)
    (tt : MachineState) (ctx : TreeCtx S x p tt) (j : Nat) (hj : j < 2 ^ p.h)
    (st : List Val × List Val) (t : MachineState) (hinv : TLeafInv p tt j st t) :
    Sim image t (7 + (21 * 480 + (4 + (88 + 2))))
      (do
        let (leaf, c) ← buildLeaf S p.lay p.tau j x
        pure (st.1 ++ [leaf], if j = p.e then c else st.2))
      (TLeafInv p tt (j + 1)) := by
  obtain ⟨-, hl1, hv1, hsl, hcap, tpc, t20, tregs, tframe, tlo1, tlo2⟩ := hinv
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have htau := ctx.htau
  have h32 := pow_le32 p.h ctx.hh
  have he := ctx.he
  have tpc' : t.pc = pcOf 479 := by rw [tpc, if_pos hj]
  have tx30 : t.getReg .x30 = BitVec.ofNat 64 p.tau := by rw [tregs.get .x30, ctx.x30]
  -- block 510: leaf tweak words
  have hs1 := symRun_sound blk479 codeAt_479 t tpc' (by simp only [blk479.res, rv_simp])
  have hc1 : blk479.res.cycles = 7 := rfl
  rw [hc1] at hs1
  set tl := blk479.res.toState t with htl
  have f1 : Frame t tl (fun x => x = 0x6A8 ∨ x = 0xC8 ∨ x = 0x348) := by
    apply frame_toState; intro x hx hW
    simp only [blk479.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t tl [.x3, .x21, .x24] := by
    intro r hr; rw [htl, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have hw : ∀ a, a = 0x6A8 ∨ a = 0xC8 ∨ a = 0x348 →
      tl.getMem (BitVec.ofNat 64 a) = BitVec.ofNat 64 (p.tau + 2 ^ 32 * j) := by
    intro a ha
    simp only [htl, blk479.res, rv_simp]
    bvsimp [t20, tx30, ofNat_eq_iff]
    rw [ofNat_or_disjoint (j * 4294967296) p.tau 32 (by omega) (by omega) (by omega)]
    rcases ha with rfl | rfl | rfl <;> simp (disch := bvomega) only [if_pos, if_neg, if_true] <;>
      (congr 1; ring)
  have ft1 : Frame tt tl (leavesW p) := (tframe.trans f1).mono (by
    intro x hx; simp only [leavesW] at hx ⊢; omega)
  have rt1 : RegsEq tt tl leavesRegs := (tregs.trans r1).mono (by decide)
  have cctx : ChainCtx S x ⟨p.lay, p.tau, p.e, j, p.sigl⟩ tl := by
    refine ⟨hl, htau, show p.e < 64 by omega, show j < 64 by omega, hsig, ctx.hx, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rt1.get .x5, ctx.x5]
    · rw [rt1.get .x13, ctx.x13]
    · rw [rt1.get .x18, ctx.x18]
    · simp only [htl, blk479.res, rv_simp, t20]
    · intro i hi
      rw [ft1.getMem (by omega) (by simp only [leavesW]; omega), ctx.dig i hi]
    · rw [f1.getMem (by norm_num) (by omega), tlo1, ctx.pb0]
    · exact hw _ (Or.inl rfl)
    · rw [ft1.readWords _ _ (by norm_num) (by intro i hi; simp only [leavesW]; omega), ctx.pbP]
    · rw [ft1.readWords _ _ (by norm_num) (by intro i hi; simp only [leavesW]; omega), ctx.pbS]
    · rw [f1.getMem (by norm_num) (by omega), tlo2, ctx.cb0]
    · exact hw _ (Or.inr (Or.inl rfl))
    · rw [ft1.readWords _ _ (by norm_num) (by intro i hi; simp only [leavesW]; omega), ctx.cbP]
  rw [buildLeaf_bind]
  refine Sim.steps hs1 (Sim.bind (chains_sim S hS x ⟨p.lay, p.tau, p.e, j, p.sigl⟩ tl cctx
    (by simp only [htl, blk479.res, rv_simp]) (by simp only [htl, blk479.res, rv_simp])
    (by simp only [htl, blk479.res, rv_simp])) (fun cs t2 h2 => ?_))
  obtain ⟨-, hc1', hc2', hcv1, hcv2, hends, hcaps, pc2, -, -, cregs, cframe, clo1, clo2⟩ := h2
  have pc2' : t2.pc = pcOf 541 := by rw [pc2]; rfl
  have hcaps' : j = p.e → Slots t2 (p.sigl + 8) cs.2 := hcaps
  have rt2 : RegsEq tt t2 (leavesRegs ++ chainRegs) := rt1.trans cregs
  have x220 : t2.getReg .x20 = BitVec.ofNat 64 j := by
    rw [cregs.get .x20]; simp only [htl, blk479.res, rv_simp, t20]
  have x219 : t2.getReg .x19 = BitVec.ofNat 64 0x34100 := by rw [rt2.get .x19, ctx.x19]
  -- block 557: leaf hash
  have hs3 := symRun_sound blk541 codeAt_541 t2 pc2' (by simp only [blk541.res, rv_simp])
  have hc3 : blk541.res.cycles = 4 := rfl
  rw [hc3] at hs3
  set t3 := blk541.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk541.res]
  have r3 : RegsEq t2 t3 [.x3, .x10, .x11, .x12] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e3 := symRun_ecall blk541 codeAt_541 t2 (by simp only [blk541.res, rv_simp]) rfl
  have x10 : t3.getReg .x10 = BitVec.ofNat 64 0x340 := by simp only [ht3, blk541.res, rv_simp]
  have x11 : t3.getReg .x11 = BitVec.ofNat 64 704 := by simp only [ht3, blk541.res, rv_simp]
  have x12 : t3.getReg .x12 = BitVec.ofNat 64 (0x34100 + 16 * j) := by
    simp only [ht3, blk541.res, rv_simp]; bvsimp [x220, x219]; congr 1; ring
  have x5 : t3.getReg .x5 = 0 := by rw [r3.get .x5, rt2.get .x5, ctx.x5]
  have pc3 : t3.pc = pcOf 545 := by simp only [ht3, blk541.res, rv_simp]
  have fl3 : Frame tl t3 (chainW ⟨p.lay, p.tau, p.e, j, p.sigl⟩) := (cframe.trans f3).mono (by
    intro x hx; rcases hx with h | h; exact h; exact h.elim)
  have hq : hashInput t3 = pad64 (leafInput p.lay p.tau j cs.1) := by
    obtain ⟨hn, hw'⟩ := words_thVals 2 p.lay p.tau 0 j cs.1 hcv1 10 (by rw [hc1'])
    refine hashInput_eq_pad64 t3 _ 10 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [leafInput, hw', x10, show 8 * (10 + 1) = 1 + 1 + 2 + 2 * 42 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one,
      fl3.getMem (by norm_num) (by dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; omega),
      f1.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [leavesW]; omega),
      ctx.lb0, fl3.getMem (by norm_num) (by dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; omega), hw _ (Or.inr (Or.inr rfl)),
      fl3.readWords _ _ (by norm_num) (by intro i hi; dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; omega),
      ft1.readWords _ _ (by norm_num) (by intro i hi; simp only [leavesW]; omega), ctx.lbP,
      show (84 : Nat) = 2 * cs.1.length by rw [hc1'], f3.readWords _ _ (by rw [hc1']; norm_num) (by simp),
      readWords_slots t2 0x360 cs.1 hends]
    simp only [twWords_eq, twWord0, List.cons_append, List.nil_append, List.cons.injEq, true_and]
    refine ⟨?_, trivial⟩
    congr 1
    rw [Nat.mod_eq_of_lt (by omega : p.tau < 2 ^ 32), Nat.mod_eq_of_lt (by omega : j < 2 ^ 32)]
  have hb : (pad64 (leafInput p.lay p.tau j cs.1)).blocks = 11 :=
    congrArg (· + 1) (words_thVals 2 p.lay p.tau 0 j cs.1 hcv1 10 (by rw [hc1'])).1
  refine (Sim.steps hs3 (Sim.hash16_bind (W := 2) e3 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)
      (by norm_num)) hq (fmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set t4 := writeHash t3 a with ht4
  have f4 : Frame t3 t4 (fun x => 0x34100 + 16 * j ≤ x ∧ x < 0x34100 + 16 * j + 32) :=
    frame_writeHash t3 a _ x12 (by omega)
  have v4 : t4.readWords (BitVec.ofNat 64 (0x34100 + 16 * j)) 2 = wordsOf (answerBytes 16 a) :=
    writeHash_readWords_val t3 a _ x12 (by omega)
  have pc4 : t4.pc = pcOf 546 := by rw [ht4, writeHash_pc, pc3]; apply BitVec.eq_of_toNat_eq; simp
  have hs5 := symRun_sound blk546 codeAt_546 t4 pc4 (by simp only [blk546.res, rv_simp])
  have hc5 : blk546.res.cycles = 2 := rfl
  rw [hc5] at hs5
  set t5 := blk546.res.toState t4 with ht5
  have f5 : Frame t4 t5 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk546.res]
  have r5 : RegsEq t4 t5 [.x20] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have x420 : t4.getReg .x20 = BitVec.ofNat 64 j := by rw [ht4, writeHash_getReg, r3.get .x20, x220]
  have x417 : t4.getReg .x17 = BitVec.ofNat 64 (2 ^ p.h) := by
    rw [ht4, writeHash_getReg, r3.get .x17, rt2.get .x17, ctx.x17]
  have ftot : Frame t t5 (fun x => (x = 0x6A8 ∨ x = 0xC8 ∨ x = 0x348) ∨
      chainW ⟨p.lay, p.tau, p.e, j, p.sigl⟩ x ∨ (0x34100 + 16 * j ≤ x ∧ x < 0x34100 + 16 * j + 32)) :=
    (f1.trans (fl3.trans f4)).trans f5 |>.mono (by
      intro x hx; rcases hx with (h | h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact h.elim)
  refine Sim.pure_steps hs5 ⟨by omega, by simp [hl1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hv1 v hv
    · simp at hv; subst hv; simp
  · apply Slots.snoc
    · exact hsl.frame ftot (by omega) (by
        intro i hi; dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; constructor <;> omega)
    · rw [hl1, f5.readWords _ _ (by omega) (by simp), v4]
  · intro hej
    by_cases hje : j = p.e
    · rw [if_pos hje]
      refine ⟨hc2', hcv2, ?_⟩
      exact (hcaps' hje).frame ((f4.trans f5).mono (fun x hx => hx)) (by omega) (by
        intro i hi; rw [hc2'] at hi; constructor <;> (try simp only [or_false]) <;> omega)
    · rw [if_neg hje]
      obtain ⟨c1, c2, c3⟩ := hcap (by omega)
      refine ⟨c1, c2, c3.frame ftot (by omega) ?_⟩
      intro i hi; rw [c1] at hi; dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl]; constructor <;> omega
  · simp only [ht5, blk546.res, rv_simp, x420, x417, ofNat_add_ofNat, ofNat_bne_ofNat]
    by_cases h : j + 1 < 2 ^ p.h
    · rw [if_pos h, if_pos (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]
    · rw [if_neg h, if_neg (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]
  · simp only [ht5, blk546.res, rv_simp, x420, ofNat_add_ofNat]
  · exact ((((rt2.trans r3).trans (regsEq_writeHash _ _ [])).trans r5)).mono (by decide)
  · exact (tframe.trans ftot).mono (by intro x hx; simp only [leavesW] at hx ⊢; dsimp only [chainW, LeafPar.e, LeafPar.ep, LeafPar.sigl] at hx; omega)
  · rw [f5.getMem (by norm_num) (by simp), f4.getMem (by norm_num) (by omega),
      f3.getMem (by norm_num) (by simp), clo1, f1.getMem (by norm_num) (by omega), tlo1]
  · rw [f5.getMem (by norm_num) (by simp), f4.getMem (by norm_num) (by omega),
      f3.getMem (by norm_num) (by simp), clo2, f1.getMem (by norm_num) (by omega), tlo2]

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Cycle bound of one leaf. -/
def tleafCyc : Nat := 7 + (21 * 480 + (4 + (88 + 2)))

/-- **Leaves** `0 .. 2^h - 1` of a tree (with capture of leaf `e`). -/
theorem leaves_sim (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : TreePar)
    (tt : MachineState) (ctx : TreeCtx S x p tt) (hpc : tt.pc = pcOf 479)
    (h20 : tt.getReg .x20 = BitVec.ofNat 64 0) :
    Sim image tt (2 ^ p.h * tleafCyc) (buildLeaves S p.lay p.tau p.h p.e x) (TLeafInv p tt (2 ^ p.h)) := by
  unfold buildLeaves
  exact Sim.foldlM_range (2 ^ p.h) _ ([], []) (TLeafInv p tt) tleafCyc
    (fun j hj st t h => by unfold tleafCyc; exact tleaf_body S hS x p tt ctx j hj st t h)
    ⟨Nat.zero_le _, rfl, by simp, Slots.nil _ _, fun h => absurd h (by omega),
      by rw [hpc, if_pos (Nat.two_pow_pos _)], h20, RegsEq.refl _ _,
      Frame.refl _ _, rfl, rfl⟩

end SigGolfCandidate.Sign
