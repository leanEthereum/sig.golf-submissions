import SigGolfCandidate.Sign.PorsTree

/-! # `sign`: the whole PORS tree (179 .. 237) as one simulation (`porsTree_sim`). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Addresses written by the PORS tree (leaves and levels). -/
def porsW (a : Nat) : Prop :=
  a = 0x6A8 ∨ a = 0xC8 ∨ (0xE0 ≤ a ∧ a < 0xF0) ∨ (0x140 ≤ a ∧ a < 0x160) ∨ (0x30000 ≤ a ∧ a < 0xB0000) ∨
    (0x3310 ≤ a ∧ a < 0x3400) ∨ a = 456 ∨ a = 480 ∨ a = 488 ∨ a = 496 ∨ a = 504

def porsRegs : List Reg := [.x1, .x2, .x3, .x9, .x10, .x11, .x12, .x13, .x15, .x16, .x17, .x18, .x19, .x20, .x25]

/-- After the PORS tree (at 238). -/
def PorsPost (L : List Nat) (t0 : MachineState) (r : List (List Val) × List Val) (t : MachineState) : Prop :=
  t.pc = pcOf 238 ∧ t.getReg .x19 = BitVec.ofNat 64 (lvBase 14) ∧ r.1.length = 15 ∧
  (∀ l, l < 15 → (r.1.getD l []).length = 2 ^ (14 - l) ∧ (∀ v ∈ r.1.getD l [], v.length = 16) ∧
    Slots t (lvBase l) (r.1.getD l [])) ∧
  r.2.length = 2 ^ 14 ∧ (∀ v ∈ r.2, v.length = 16) ∧
  (∀ s < 15, t.readWords (BitVec.ofNat 64 (0x3310 + 16 * s)) 2 = wordsOf (r.2.getD ((L.map keyV).getD s 0) [])) ∧
  RegsEq t0 t porsRegs ∧ Frame t0 t porsW

theorem buildPorsTree_eq (S : List Byte) (idx : Nat) :
    buildPorsTree S idx = buildPorsLeaves S idx >>= fun p =>
      buildAllLevels (porsNodeFmt idx) porsH p.1 >>= fun levels => pure (levels, p.2) := by
  unfold buildPorsTree; rfl

/-- **The PORS tree** from `por_leaf_loop` (179) to 238. -/
theorem porsTree_sim (S : List Byte) (hS : S.length = 32) (idx : Nat) (L : List Nat) (t0 : MachineState)
    (ctx : PLeafCtx S idx L t0) (lctx : PLevCtx idx t0) (hpc : t0.pc = pcOf 179)
    (h9 : t0.getReg .x9 = BitVec.ofNat 64 0) (hcap : CapInv (L.map keyV) 0 [] t0 0) :
    Sim image t0 (2 ^ 13 * 79 + (1 + 14 * (4 + (2 ^ 13 * 26 + 4)))) (buildPorsTree S idx) (PorsPost L t0) := by
  rw [buildPorsTree_eq]
  refine Sim.bind (porsLeaves_sim S hS idx L t0 ctx hpc h9 hcap) (fun p t1 h1 => ?_)
  obtain ⟨-, hl1, hl2, hv1, hv2, hsl1, ⟨c, hc, hclt, hcge, hcsl, -, -, -⟩, pc1, -, r1, f1, -, -⟩ := h1
  rw [if_neg (by norm_num)] at pc1
  -- all 15 captured
  have hc15 : c = 15 := by
    by_contra h
    have := hcge (by omega)
    have := vs_lt_T L ctx.hlen ctx.hlt c (by omega)
    omega
  subst hc15
  -- block 210
  have hs2 := symRun_sound blk210 codeAt_210 t1 pc1 (by simp only [blk210.res, rv_simp])
  set t2 := blk210.res.toState t1 with ht2
  have hc2 : blk210.res.cycles = 1 := rfl
  rw [hc2] at hs2
  have m2 : ∀ z, t2.getMem z = t1.getMem z := fun z => by
    rw [ht2, Result.toState_getMem, show blk210.res.st.mem = [] from rfl, memEval_nil]
  have r2 : RegsEq t1 t2 [.x15] := by
    intro q hq; rw [ht2, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have fr12 : Frame t0 t2 pleafW := fun a ha hW => by rw [m2]; exact f1 a ha hW
  have lctx2 : PLevCtx idx t2 := ⟨by rw [r2.get .x5, r1.get .x5 (by simp [pleafRegs]), lctx.x5],
    by rw [fr12.getMem (by norm_num) (by simp only [pleafW]; omega), lctx.nb0],
    by rw [fr12.getMem (by norm_num) (by simp only [pleafW]; omega), lctx.nb8],
    by rw [fr12.readWords _ _ (by norm_num) (by intro i hi; simp only [pleafW]; omega), lctx.nbP]⟩
  refine (Sim.steps hs2 (Sim.bind (W₂ := 0) (porsLevels_sim idx t2 lctx2 p.1 hl1 hv1
    (fun i hi => by
      rw [show lvBase 0 = 0x30000 from rfl, readWords_congr t1 t2 _ 2 (fun k _ => m2 _)]; exact hsl1 i hi)
    (by simp only [ht2, blk210.res, rv_simp]) (by simp only [ht2, blk210.res, rv_simp] <;> rfl)
    (by rw [r2.get .x17, r1.get .x17 (by simp [pleafRegs]), ctx.x17])
    (by rw [r2.get .x19, r1.get .x19 (by simp [pleafRegs]), ctx.x19]; rfl)) (fun levels t3 h3 => ?_))).mono
    (by omega) (fun _ _ h => h)
  obtain ⟨-, hl3, hlv3, pc3, -, -, x19, r3, f3, -⟩ := h3
  refine Sim.pure ⟨by simpa using pc3, x19, hl3, fun l hl => ?_, hl2, hv2, fun s hs => ?_,
    ((r1.trans r2).trans r3).mono (by decide), ?_⟩
  · have := hlv3 l (by omega)
    rw [getD_of_lt (by simp only; omega)]; exact this
  · rw [f3.readWords _ _ (by omega) (by intro i hi; simp only [plevW, lvBase]; omega),
      readWords_congr t1 t2 _ 2 (fun k _ => m2 _)]
    exact hcsl s hs
  · intro a ha hW
    rw [f3 a ha (by simp only [plevW, porsW, lvBase] at hW ⊢; omega), m2,
      f1 a ha (by simp only [pleafW, porsW] at hW ⊢; omega)]

end SigGolfCandidate.Sign
