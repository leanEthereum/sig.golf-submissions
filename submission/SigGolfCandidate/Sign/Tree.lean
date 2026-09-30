import SigGolfCandidate.Sign.TreeLevel

/-!
# `sign`, tree_build as a whole (instructions 510 .. 603)

`tree_sim` : from `tb_leaf_loop` (`EP = 0`) the machine refines `buildTree S lay tau h e x`: the
root in `TA[0]`, the captured chain values at `SIGL + 8`, the path at `SIGL + 680`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def treeW (p : TreePar) (a : Nat) : Prop := leavesW p a ∨ tlevW p a

def treeRegs : List Reg := leavesRegs ++ [.x15] ++ tlevRegs

/-- Result of tree_build. -/
def TreePost (p : TreePar) (tt : MachineState) (r : Val × List Val × List Val) (t : MachineState) :
    Prop :=
  t.pc = pcOf 587 ∧ r.1.length = 16 ∧ Slots t 0x34100 [r.1] ∧
  r.2.1.length = 42 ∧ (∀ v ∈ r.2.1, v.length = 16) ∧ Slots t (p.sigl + 8) r.2.1 ∧
  r.2.2.length = p.h ∧ (∀ v ∈ r.2.2, v.length = 16) ∧ Slots t (p.sigl + 680) r.2.2 ∧
  RegsEq tt t treeRegs ∧ Frame tt t (treeW p)

theorem buildTree_eq (S : List Byte) (lay tau h e : Nat) (x : List Nat) :
    buildTree S lay tau h e x =
      buildLeaves S lay tau h e x >>= fun q =>
        (List.range' 1 h).foldlM (levelStep (nodeInput lay tau) e) (q.1, []) >>= fun st =>
          pure (st.1.getD 0 [], q.2, st.2) := by
  simp only [buildTree, buildLevels, bind_assoc, pure_bind]

/-- Cycle bound of tree_build. -/
def treeCyc : Nat := 64 * tleafCyc + (1 + 6 * 853)

theorem tree_sim (S : List Byte) (hS : S.length = 32) (x : List Nat) (p : TreePar)
    (tt : MachineState) (ctx : TreeCtx S x p tt) (h1 : 1 ≤ p.h) (hpc : tt.pc = pcOf 479)
    (h20 : tt.getReg .x20 = BitVec.ofNat 64 0) :
    Sim image tt treeCyc (buildTree S p.lay p.tau p.h p.e x) (TreePost p tt) := by
  have hh := ctx.hh
  have h32 := pow_le32 p.h hh
  have hsig := ctx.hsigl
  have hlay := ctx.hlay
  rw [buildTree_eq]
  have hW : 2 ^ p.h * tleafCyc + (1 + p.h * 853) ≤ treeCyc := by
    unfold treeCyc
    have := Nat.mul_le_mul_right tleafCyc h32
    have := Nat.mul_le_mul_right 853 hh
    omega
  refine (Sim.bind (leaves_sim S hS x p tt ctx hpc h20) (fun q t2 h2 => ?_)).mono hW
    (fun _ _ h => h)
  obtain ⟨-, hlv, hlvv, hlvs, hcap, pc2, -, lregs, lframe, -, -⟩ := h2
  obtain ⟨hc1, hc2, hc3⟩ := hcap ctx.he
  have pc2' : t2.pc = pcOf 548 := by rw [pc2, if_neg (lt_irrefl _)]
  have hs3 := symRun_sound blk548 codeAt_548 t2 pc2' (by simp only [blk548.res, rv_simp])
  have hc67 : blk548.res.cycles = 1 := rfl
  rw [hc67] at hs3
  set t3 := blk548.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk548.res]
  have r3 : RegsEq t2 t3 [.x15] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have rt3 : RegsEq tt t3 (leavesRegs ++ [.x15]) := lregs.trans r3
  have ft3 : Frame tt t3 (leavesW p) := (lframe.trans f3).mono (by
    intro x hx; rcases hx with h | h; exact h; exact h.elim)
  have vctx : TLevCtx p t3 := by
    refine ⟨ctx.hlay, ctx.htau, ⟨h1, hh⟩, ctx.he, ctx.hsigl, ctx.hheight, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rt3.get .x5, ctx.x5]
    · rw [rt3.get .x8, ctx.x8]
    · rw [rt3.get .x9, ctx.x9]
    · rw [rt3.get .x13, ctx.x13]
    · rw [rt3.get .x18, ctx.x18]
    · rw [rt3.get .x19, ctx.x19]
    · rw [rt3.get .x30, ctx.x30]
    · have := ctx.hsigl
      rw [ft3.readWords _ _ (by norm_num) (by intro i hi; simp only [leavesW]; omega), ctx.nbP]
  refine (Sim.steps hs3 (Sim.bind (W₂ := 0) (tlevels_sim p t3 vctx q.1 hlv hlvv
    (hlvs.frame f3 (by omega) (by simp)) (by simp only [ht3, blk548.res, rv_simp])
    (by simp only [ht3, blk548.res, rv_simp]) (by rw [rt3.get .x17, ctx.x17]))
    (fun st t4 h4 => ?_))).mono (by omega) (fun _ _ h => h)
  obtain ⟨-, hl4, hv4, hs4, hp4, hpv4, hps4, pc4, -, -, vregs, vframe⟩ := h4
  refine Sim.pure ⟨by rw [pc4, if_neg (lt_irrefl _)], ?_, ?_, hc1, hc2, ?_, hp4, hpv4, hps4, ?_, ?_⟩
  · rw [getD_of_lt (by rw [hl4]; simp)]; exact hv4 _ (List.getElem_mem _)
  · intro i hi
    simp at hi; subst hi
    have := hs4.getD 0 (by rw [hl4]; simp)
    simpa using this
  · refine hc3.frame (f3.trans vframe) (by rw [hc1]; omega) ?_
    intro i hi; rw [hc1] at hi
    have := ctx.hsigl; have := ctx.hlay
    constructor <;> (simp only [tlevW, or_false, false_or]; omega)
  · exact (rt3.trans vregs).mono (by decide)
  · exact (ft3.trans (f3.trans vframe)).mono (by
      intro x hx; simp only [treeW]; rcases hx with h | h | h
      · exact Or.inl h
      · exact h.elim
      · exact Or.inr h)

end SigGolfCandidate.Sign
