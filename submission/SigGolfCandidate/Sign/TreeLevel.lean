import SigGolfCandidate.Sign.TreeLeaf
import SigGolfCandidate.Sign.ForsLevel

/-!
# `sign`, tree_build: the levels (`tb_level_loop`, instructions 568 .. 606)

`tlevels_sim` : from `tb_level_loop` with `LAM = 1`, `NCNT = 2^h` and the leaves in `TA`, the
machine refines the level fold of `buildLevels (nodeInput lay tau) e h leaves`; the path node of
level `l` is staged at `SIGL + 680 + 16 l`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem seg587_eq : seg587 = nodeSegA := rfl
theorem seg603_eq : seg603 = nodeSegB := rfl

theorem codeAt_node587 : CodeAt image (pcOf 587) nodeSegA := seg587_eq ▸ codeAt_587
theorem codeAt_node603 : CodeAt image (pcOf (587 + 16)) nodeSegB := seg603_eq ▸ codeAt_603

/-- Facts at the start of the tree level loop. -/
structure TLevCtx (p : TreePar) (t0 : MachineState) : Prop where
  hlay : p.lay < 7
  htau : p.tau < 2 ^ 30
  hh : 1 ≤ p.h ∧ p.h ≤ 5
  he : p.e < 2 ^ p.h
  hsigl : p.sigl = 0x900 + 760 * p.lay
  x5 : t0.getReg .x5 = 0
  x8 : t0.getReg .x8 = BitVec.ofNat 64 p.lay
  x9 : t0.getReg .x9 = BitVec.ofNat 64 p.h
  x13 : t0.getReg .x13 = BitVec.ofNat 64 p.e
  x18 : t0.getReg .x18 = BitVec.ofNat 64 p.sigl
  x19 : t0.getReg .x19 = BitVec.ofNat 64 0x34100
  x30 : t0.getReg .x30 = BitVec.ofNat 64 p.tau
  nbP : t0.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0]

def tlevW (p : TreePar) (a : Nat) : Prop :=
  a = 0x1C0 ∨ a = 0x1C8 ∨ (0x1E0 ≤ a ∧ a < 0x200) ∨ (0x34100 ≤ a ∧ a < 0x34100 + 16 * 33) ∨
    (p.sigl + 680 ≤ a ∧ a < p.sigl + 760)

def tlevRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x15, .x16, .x17, .x29]

/-- Invariant after `j` levels. -/
def TLevInv (p : TreePar) (t0 : MachineState) (j : Nat) (st : List Val × List Val) (t : MachineState) :
    Prop :=
  j ≤ p.h ∧ st.1.length = 2 ^ (p.h - j) ∧ (∀ v ∈ st.1, v.length = 16) ∧ Slots t 0x34100 st.1 ∧
  st.2.length = j ∧ (∀ v ∈ st.2, v.length = 16) ∧ Slots t (p.sigl + 680) st.2 ∧
  t.pc = (if j < p.h then pcOf 568 else pcOf 607) ∧ t.getReg .x15 = BitVec.ofNat 64 (j + 1) ∧
  t.getReg .x17 = BitVec.ofNat 64 (2 ^ (p.h - j)) ∧
  RegsEq t0 t tlevRegs ∧ Frame t0 t (tlevW p)

theorem tlev_path_ne (sigl lay i j m : Nat) (hsig : sigl = 0x900 + 760 * lay) (hl : lay < 7)
    (hij : i < j) (hj : j < 5) (hm : m ≤ 16) :
    ((¬sigl + 680 + 16 * i = 448 ∧ ¬sigl + 680 + 16 * i = 456 ∧
        ¬sigl + 680 + 16 * i = sigl + 680 + 16 * j ∧ ¬sigl + 680 + 16 * i = sigl + 680 + 16 * j + 8) ∧
      ¬(213248 ≤ sigl + 680 + 16 * i ∧ sigl + 680 + 16 * i < 213248 + 32 * m) ∧
        ¬sigl + 680 + 16 * i = 456 ∧ ¬sigl + 680 + 16 * i = 480 ∧
          ¬sigl + 680 + 16 * i = 488 ∧ ¬sigl + 680 + 16 * i = 496 ∧ ¬sigl + 680 + 16 * i = 504) ∧
    ((¬sigl + 680 + 16 * i + 8 = 448 ∧ ¬sigl + 680 + 16 * i + 8 = 456 ∧
        ¬sigl + 680 + 16 * i + 8 = sigl + 680 + 16 * j ∧
          ¬sigl + 680 + 16 * i + 8 = sigl + 680 + 16 * j + 8) ∧
      ¬(213248 ≤ sigl + 680 + 16 * i + 8 ∧ sigl + 680 + 16 * i + 8 < 213248 + 32 * m) ∧
        ¬sigl + 680 + 16 * i + 8 = 456 ∧ ¬sigl + 680 + 16 * i + 8 = 480 ∧
          ¬sigl + 680 + 16 * i + 8 = 488 ∧ ¬sigl + 680 + 16 * i + 8 = 496 ∧
            ¬sigl + 680 + 16 * i + 8 = 504) := by
  subst hsig; omega

theorem tlevel_body (p : TreePar) (t0 : MachineState) (ctx : TLevCtx p t0) (j : Nat) (hj : j < p.h)
    (st : List Val × List Val) (t : MachineState) (hinv : TLevInv p t0 j st t) :
    Sim image t (19 + (2 ^ (p.h - 1 - j) * 25 + 2))
      (levelStep (nodeInput p.lay p.tau) p.e st (1 + j)) (TLevInv p t0 (j + 1)) := by
  obtain ⟨-, hlen, hvals, hslots, hplen, hpvals, hpath, tpc, t15, t17, tregs, tframe⟩ := hinv
  have hsig := ctx.hsigl
  have hl := ctx.hlay
  have htau := ctx.htau
  have hh := ctx.hh
  have he := ctx.he
  have tpc' : t.pc = pcOf 568 := by rw [tpc, if_pos hj]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5, ctx.x5]
  have tx8 : t.getReg .x8 = BitVec.ofNat 64 p.lay := by rw [tregs.get .x8, ctx.x8]
  have tx9 : t.getReg .x9 = BitVec.ofNat 64 p.h := by rw [tregs.get .x9, ctx.x9]
  have tx13 : t.getReg .x13 = BitVec.ofNat 64 p.e := by rw [tregs.get .x13, ctx.x13]
  have tx18 : t.getReg .x18 = BitVec.ofNat 64 p.sigl := by rw [tregs.get .x18, ctx.x18]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x34100 := by rw [tregs.get .x19, ctx.x19]
  have tx30 : t.getReg .x30 = BitVec.ofNat 64 p.tau := by rw [tregs.get .x30, ctx.x30]
  have hpow : 2 ^ (p.h - j) = 2 * 2 ^ (p.h - 1 - j) := by
    rw [show p.h - j = p.h - 1 - j + 1 by omega, Nat.pow_succ]; ring
  have hp32 : 2 ^ (p.h - j) ≤ 32 := pow_le32 _ (by omega)
  set sib := (p.e / 2 ^ j) ^^^ 1 with hsib
  have hsib_lt : sib < 2 ^ (p.h - j) := by
    apply xor1_lt _ _ _ (by omega)
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, show p.h - j + j = p.h by omega]
    exact he
  have hudiv : p.e / 2 ^ j ≤ p.e := Nat.div_le_self _ _
  have he32 : p.e < 32 := lt_of_lt_of_le he (pow_le32 _ hh.2)
  -- block 568: capture sibling, node tweak
  have hs1 := symRun_sound blk568 codeAt_568 t tpc' (by
    simp only [blk568.res, rv_simp]
    bvsimp [t15, tx13, tx18, tx19, accessValid_ofNat, ne_eq, ofNat_eq_iff]
    rw [← hsib]; omega)
  have hc1 : blk568.res.cycles = 19 := rfl
  rw [hc1] at hs1
  set t1 := blk568.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x1C0 ∨ x = 0x1C8 ∨ x = p.sigl + 680 + 16 * j ∨
      x = p.sigl + 680 + 16 * j + 8) := by
    apply frame_toState; intro x hx hW
    simp only [blk568.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t15, tx18, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x1, .x2, .x3, .x16, .x17, .x29] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc1 : t1.pc = pcOf 587 := by simp only [ht1, blk568.res, rv_simp]
  have y16 : t1.getReg .x16 = 0 := by simp only [ht1, blk568.res, rv_simp]
  have y17 : t1.getReg .x17 = BitVec.ofNat 64 (2 ^ (p.h - 1 - j)) := by
    simp only [ht1, blk568.res, rv_simp]
    bvsimp [t17]
    congr 1; rw [hpow]; omega
  have y19 : t1.getReg .x19 = BitVec.ofNat 64 0x34100 := by rw [r1.get .x19, tx19]
  have y5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have w448 : t1.getMem (BitVec.ofNat 64 448) = twWord0 3 p.lay p.tau (1 + j) := by
    simp only [ht1, blk568.res, rv_simp]
    bvsimp [t15, tx8, tx18, ofNat_eq_iff]
    rw [ofNat_or_disjoint ((j + 1) * 4294967296) (p.lay * 65536) 32 (by omega) (by omega) (by omega),
      ofNat_or_disjoint ((j + 1) * 4294967296 + p.lay * 65536) 769 16 (by omega) (by omega) (by omega)]
    unfold twWord0; congr 1
    rw [Nat.div_eq_of_lt (by omega : p.tau < 2 ^ 32), Nat.mod_eq_of_lt (a := p.lay) (by omega),
      Nat.mod_eq_of_lt (a := 1 + j) (by omega)]
    omega
  have w456 : lo32 (t1.getMem (BitVec.ofNat 64 456)) = BitVec.ofNat 32 p.tau := by
    simp only [ht1, blk568.res, rv_simp]
    bvsimp [t15, tx18, tx30, ofNat_eq_iff]
    rw [lo32_replace0]
  have hcap1 : t1.readWords (BitVec.ofNat 64 (p.sigl + 680 + 16 * j)) 2 =
      wordsOf (st.1.getD sib []) := by
    rw [← hslots.getD sib (by omega), readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht1, blk568.res, rv_simp]
    bvsimp [t15, tx13, tx18, tx19, ofNat_eq_iff]
    simp (disch := bvomega) only [if_pos, if_neg]
    have e : (p.e / 2 ^ j ^^^ 1) * 16 = 16 * sib := by rw [hsib, Nat.mul_comm]
    rw [e, Nat.add_comm (16 * sib) 213248]
  -- node loop
  let c : NodeCtx := ⟨3, p.lay, p.tau, 1 + j, 0x34100, 2 ^ (p.h - 1 - j)⟩
  have hnode := nodeLoop_sim codeAt_node587 codeAt_node603 c st.1 (by simp only [c]; rw [hlen, hpow])
    hvals (by simp only [c]; positivity) (by simp only [c]; norm_num) (by simp only [c])
    (by simp only [c]; omega) t1 pc1 y16 y17 y19 y5 w448 w456
    (by rw [f1.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [tlevW]; omega)]
        have := ctx.nbP; rw [readWords_ofNat_two] at this; simp only [List.cons.injEq] at this
        exact this.1)
    (by rw [f1.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [tlevW]; omega)]
        have := ctx.nbP; rw [readWords_ofNat_two] at this; simp only [List.cons.injEq] at this
        exact this.2.1)
    (hslots.frame f1 (by omega) (by intro i hi; constructor <;> ((try simp only); omega)))
  have hstep : levelStep (nodeInput p.lay p.tau) p.e st (1 + j) =
      buildLevel (nodeFmt 3 p.lay p.tau) (1 + j) st.1 >>= fun level =>
        pure (level, st.2 ++ [st.1.getD sib []]) := by
    simp only [levelStep, hsib, show 1 + j - 1 = j by omega]; rfl
  rw [hstep]
  refine Sim.steps hs1 (Sim.bind hnode (fun acc t2 hn => ?_))
  obtain ⟨-, hacc, haccv, haccs, -, pc2, x216, nregs, nframe⟩ := hn
  have pc2' : t2.pc = pcOf 605 := by rw [pc2, if_neg (lt_irrefl _)]
  have hs3 := symRun_sound blk605 codeAt_605 t2 pc2' (by simp only [blk605.res, rv_simp])
  have hc3 : blk605.res.cycles = 2 := rfl
  rw [hc3] at hs3
  set t3 := blk605.res.toState t2 with ht3
  have r3 : RegsEq t2 t3 [.x15] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk605.res]
  have x215 : t2.getReg .x15 = BitVec.ofNat 64 (j + 1) := by
    rw [nregs.toRegsEq.get .x15, r1.get .x15, t15]
  have x29 : t2.getReg .x9 = BitVec.ofNat 64 p.h := by
    rw [nregs.toRegsEq.get .x9, r1.get .x9, tx9]
  have ft13 : Frame t t3 (fun x => (x = 0x1C0 ∨ x = 0x1C8 ∨ x = p.sigl + 680 + 16 * j ∨
      x = p.sigl + 680 + 16 * j + 8) ∨ ((c.B ≤ x ∧ x < c.B + 32 * c.m) ∨ x = 456 ∨ x = 480 ∨
        x = 488 ∨ x = 496 ∨ x = 504)) := (f1.trans (nframe.toFrame.trans f3)).mono (by
      intro x hx; rcases hx with h | h | h; exact Or.inl h; exact Or.inr h; exact h.elim)
  refine Sim.pure_steps hs3 ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hacc, show p.h - (j + 1) = p.h - 1 - j by omega]
  · exact haccv
  · show Slots t3 0x34100 acc
    have hm32 : acc.length ≤ 32 := by
      rw [hacc]; have := pow_le32 (p.h - 1 - j) (by omega); simp only [c]; omega
    exact (show Slots t2 0x34100 acc from haccs).frame f3 (by omega) (by simp)
  · simp [hplen]
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hpvals v hv
    · simp at hv; subst hv
      simp only [List.getElem?_eq_getElem (show sib < st.1.length by omega), Option.getD_some]
      exact hvals _ (List.getElem_mem _)
  · apply Slots.snoc
    · have hb : p.sigl + 680 + 16 * st.2.length + 16 < 2 ^ 64 := by rw [hplen]; omega
      refine hpath.frame ft13 hb ?_
      intro i hi
      have hij : i < j := by rw [hplen] at hi; exact hi
      have hm16 : 2 ^ (p.h - 1 - j) ≤ 16 := by
        have := pow_le32 (p.h - j) (by omega); omega
      simp only [c, not_or]
      generalize 2 ^ (p.h - 1 - j) = m at hm16 ⊢
      exact tlev_path_ne p.sigl p.lay i j m hsig hl hij (by omega) hm16
    · rw [hplen, f3.readWords _ _ (by omega) (by simp),
        nframe.toFrame.readWords _ _ (by omega) (by intro i hi; simp only [c]; omega), hcap1]
  · simp only [ht3, blk605.res, rv_simp, x215, x29, ofNat_add_ofNat]
    rw [ofNat_slt_ofNat _ _ (by omega) (by omega)]
    by_cases h : j + 1 < p.h
    · rw [if_pos h]; simp; omega
    · rw [if_neg h]; simp; omega
  · simp only [ht3, blk605.res, rv_simp, x215, ofNat_add_ofNat]
  · rw [r3.get .x17, nregs.toRegsEq.get .x17, y17, show p.h - (j + 1) = p.h - 1 - j by omega]
  · exact (((tregs.trans r1).trans nregs.toRegsEq).trans r3).mono (by decide)
  · exact (tframe.trans ft13).mono (by
      intro x hx; simp only [tlevW, c] at hx ⊢; omega)

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- **Tree levels** `1 .. h` (with capture of the path of leaf `e`). -/
theorem tlevels_sim (p : TreePar) (t0 : MachineState) (ctx : TLevCtx p t0) (leaves : List Val)
    (hlen : leaves.length = 2 ^ p.h) (hvals : ∀ v ∈ leaves, v.length = 16)
    (hslots : Slots t0 0x34100 leaves) (hpc : t0.pc = pcOf 568) (h15 : t0.getReg .x15 = BitVec.ofNat 64 1)
    (h17 : t0.getReg .x17 = BitVec.ofNat 64 (2 ^ p.h)) :
    Sim image t0 (p.h * 421) ((List.range' 1 p.h).foldlM (levelStep (nodeInput p.lay p.tau) p.e)
      (leaves, [])) (TLevInv p t0 p.h) := by
  have hh := ctx.hh
  apply Sim.foldlM_range' 1 p.h _ _ (TLevInv p t0) 421
  · intro j hj st t h
    refine (tlevel_body p t0 ctx j hj st t h).mono ?_ (fun _ _ h => h)
    have : 2 ^ (p.h - 1 - j) ≤ 16 := by
      have := pow_le32 (p.h - j) (by omega)
      have hp : 2 ^ (p.h - j) = 2 * 2 ^ (p.h - 1 - j) := by
        rw [show p.h - j = p.h - 1 - j + 1 by omega, Nat.pow_succ]; ring
      omega
    omega
  · exact ⟨Nat.zero_le _, by simpa using hlen, hvals, hslots, rfl, by simp, Slots.nil _ _,
      by rw [hpc, if_pos (by omega)], h15, by simpa using h17, RegsEq.refl _ _, Frame.refl _ _⟩

end SigGolfCandidate.Sign
