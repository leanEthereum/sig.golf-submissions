import SigGolfCandidate.Sign.ForsLeaf
import SigGolfCandidate.Sign.TreeBuildNode

/-!
# `sign`, FORS levels (`fors_level_loop`, instructions 142 .. 181)

`forsLevels_sim` : from `fors_level_loop` with `LAM = 1`, `NCNT = 1024` and the 1024 leaves in
`FA`, the machine refines the level fold of `buildLevels (ftsNodeInput k idx) u 10 leaves`:
the root ends in `FA[0]` and the authentication path at `SIGL + 32 + 16 l`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem seg161_eq : seg161 = nodeSegA := rfl
theorem seg177_eq : seg177 = nodeSegB := rfl

theorem codeAt_node161 : CodeAt image (pcOf 161) nodeSegA := seg161_eq ▸ codeAt_161
theorem codeAt_node177 : CodeAt image (pcOf (161 + 16)) nodeSegB := seg177_eq ▸ codeAt_177

/-- Facts at the start of the level loop of tree `k`. -/
structure LevCtx (k idx u : Nat) (t0 : MachineState) : Prop where
  x5 : t0.getReg .x5 = 0
  x8 : t0.getReg .x8 = BitVec.ofNat 64 k
  x13 : t0.getReg .x13 = BitVec.ofNat 64 u
  x14 : t0.getReg .x14 = BitVec.ofNat 64 (0x801 + 2 ^ 24 * (idx / 2 ^ 32))
  x18 : t0.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k)
  x19 : t0.getReg .x19 = BitVec.ofNat 64 0x30000
  nb8 : lo32 (t0.getMem (BitVec.ofNat 64 0x1C8)) = BitVec.ofNat 32 idx
  nbP : t0.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0]

def levW (k : Nat) (a : Nat) : Prop :=
  a = 0x1C0 ∨ a = 0x1C8 ∨ (0x1E0 ≤ a ∧ a < 0x200) ∨ (0x30000 ≤ a ∧ a < 0x30000 + 16 * 1025) ∨
    (0x2650 + 176 * k + 32 ≤ a ∧ a < 0x2650 + 176 * k + 192)

def levRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x15, .x16, .x17, .x29]

/-- Invariant after `j` levels. -/
def LevInv (k : Nat) (t0 : MachineState) (j : Nat) (st : List Val × List Val) (t : MachineState) : Prop :=
  j ≤ 10 ∧ st.1.length = 2 ^ (10 - j) ∧ (∀ v ∈ st.1, v.length = 16) ∧ Slots t 0x30000 st.1 ∧
  st.2.length = j ∧ (∀ v ∈ st.2, v.length = 16) ∧ Slots t (0x2650 + 176 * k + 32) st.2 ∧
  t.pc = (if j < 10 then pcOf 142 else pcOf 182) ∧ t.getReg .x15 = BitVec.ofNat 64 (j + 1) ∧
  t.getReg .x17 = BitVec.ofNat 64 (2 ^ (10 - j)) ∧
  RegsEq t0 t levRegs ∧ Frame t0 t (levW k) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x1C8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x1C8))

theorem xor1_lt (a n : Nat) (ha : a < 2 ^ n) (hn : 1 ≤ n) : a ^^^ 1 < 2 ^ n :=
  Nat.xor_lt_two_pow ha (lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) hn))

theorem forsLevel_body (k idx u : Nat) (hk : k < 14) (hidx : idx < 2 ^ 34) (hu : u < 1024)
    (t0 : MachineState) (ctx : LevCtx k idx u t0) (j : Nat) (hj : j < 10)
    (st : List Val × List Val) (t : MachineState) (hinv : LevInv k t0 j st t) :
    Sim image t (19 + (2 ^ (9 - j) * 25 + 3))
      (levelStep (ftsNodeInput k idx) u st (1 + j)) (LevInv k t0 (j + 1)) := by
  obtain ⟨-, hlen, hvals, hslots, hplen, hpvals, hpath, tpc, t15, t17, tregs, tframe, tlo⟩ := hinv
  have tpc' : t.pc = pcOf 142 := by rw [tpc, if_pos hj]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by decide), ctx.x5]
  have tx8 : t.getReg .x8 = BitVec.ofNat 64 k := by rw [tregs.get .x8 (by decide), ctx.x8]
  have tx13 : t.getReg .x13 = BitVec.ofNat 64 u := by rw [tregs.get .x13 (by decide), ctx.x13]
  have tx14 : t.getReg .x14 = BitVec.ofNat 64 (0x801 + 2 ^ 24 * (idx / 2 ^ 32)) := by
    rw [tregs.get .x14 (by decide), ctx.x14]
  have tx18 : t.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) := by
    rw [tregs.get .x18 (by decide), ctx.x18]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x30000 := by rw [tregs.get .x19 (by decide), ctx.x19]
  have hpow : 2 ^ (10 - j) = 2 * 2 ^ (9 - j) := by
    rw [show 10 - j = 9 - j + 1 by omega, Nat.pow_succ]; ring
  have hp9 : 2 ^ (9 - j) ≤ 512 := by
    calc 2 ^ (9 - j) ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 512 := by norm_num
  set sib := (u / 2 ^ j) ^^^ 1 with hsib
  have hsib_lt : sib < 2 ^ (10 - j) := by
    apply xor1_lt _ _ _ (by omega)
    rw [Nat.div_lt_iff_lt_mul (by positivity), ← Nat.pow_add, show 10 - j + j = 10 by omega]
    exact hu
  have hsib' : sib < 1024 := lt_of_lt_of_le hsib_lt (by
    calc 2 ^ (10 - j) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 1024 := by norm_num)
  -- block 142: capture sibling, node tweak
  have hudiv : u / 2 ^ j ≤ u := Nat.div_le_self _ _
  have hs1 := symRun_sound blk142 codeAt_142 t tpc' (by
    simp only [blk142.res, rv_simp]
    bvsimp [t15, tx13, tx18, tx19, accessValid_ofNat]
    rw [← hsib]; omega)
  have hc1 : blk142.res.cycles = 19 := rfl
  rw [hc1] at hs1
  set t1 := blk142.res.toState t with ht1
  have hP : 0x2650 + 176 * k + 32 + 16 * j + 8 < 2 ^ 64 := by omega
  have f1 : Frame t t1 (fun x => x = 0x1C0 ∨ x = 0x2650 + 176 * k + 32 + 16 * j ∨
      x = 0x2650 + 176 * k + 32 + 16 * j + 8) := by
    apply frame_toState; intro x hx hW
    simp only [blk142.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t15, tx18, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x1, .x2, .x3, .x16, .x17, .x29] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc1 : t1.pc = pcOf 161 := by simp only [ht1, blk142.res, rv_simp]
  have y16 : t1.getReg .x16 = 0 := by simp only [ht1, blk142.res, rv_simp]
  have y17 : t1.getReg .x17 = BitVec.ofNat 64 (2 ^ (9 - j)) := by
    simp only [ht1, blk142.res, rv_simp]
    bvsimp [t17]
    congr 1; rw [hpow]; omega
  have y19 : t1.getReg .x19 = BitVec.ofNat 64 0x30000 := by rw [r1.get .x19, tx19]
  have y5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have w448 : t1.getMem (BitVec.ofNat 64 448) = twWord0 10 k idx (1 + j) := by
    simp only [ht1, blk142.res, rv_simp]
    bvsimp [t15, tx8, tx14, tx18, ofNat_eq_iff]
    unfold twWord0; congr 1
    have : idx / 2 ^ 32 < 4 := by omega
    rw [Nat.mod_eq_of_lt (a := idx / 2 ^ 32) (by omega), Nat.mod_eq_of_lt (a := k) (by omega),
      Nat.mod_eq_of_lt (a := 1 + j) (by omega)]
    omega
  have hcap1 : t1.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 32 + 16 * j)) 2 =
      wordsOf (st.1.getD sib []) := by
    rw [← hslots.getD sib (by omega), readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht1, blk142.res, rv_simp]
    bvsimp [t15, tx13, tx18, tx19, ofNat_eq_iff]
    simp (disch := bvomega) only [if_pos, if_neg]
    have e : (u / 2 ^ j ^^^ 1) * 16 = 16 * sib := by rw [hsib, Nat.mul_comm]
    rw [e, Nat.add_comm (16 * sib) 196608]
  -- node loop
  let c : NodeCtx := ⟨10, k, idx, 1 + j, 0x30000, 2 ^ (9 - j)⟩
  have hB : ∀ a, 0x2650 + 176 * k + 32 ≤ a → a < 0x2650 + 176 * k + 192 →
      ¬ ((c.B ≤ a ∧ a < c.B + 32 * c.m) ∨ a = 456 ∨ a = 480 ∨ a = 488 ∨ a = 496 ∨ a = 504) := by
    intro a h1 h2; simp only [c]; omega
  have hnode := nodeLoop_sim codeAt_node161 codeAt_node177 c st.1 (by simp only [c]; rw [hlen, hpow])
    hvals (by simp only [c]; positivity) (by simp only [c]; norm_num) (by simp only [c])
    (by simp only [c]; omega) t1 pc1 y16 y17 y19 y5 w448
    (by rw [f1.getMem (by norm_num) (by omega), tlo, ctx.nb8])
    (by rw [f1.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [levW]; omega)]
        have := ctx.nbP; rw [readWords_ofNat_two] at this; simp only [List.cons.injEq] at this
        exact this.1)
    (by rw [f1.getMem (by norm_num) (by omega), tframe.getMem (by norm_num) (by simp only [levW]; omega)]
        have := ctx.nbP; rw [readWords_ofNat_two] at this; simp only [List.cons.injEq] at this
        exact this.2.1)
    (hslots.frame f1 (by omega) (by intro i hi; constructor <;> ((try simp only); omega)))
  have hstep : levelStep (ftsNodeInput k idx) u st (1 + j) =
      buildLevel (nodeFmt 10 k idx) (1 + j) st.1 >>= fun level =>
        pure (level, st.2 ++ [st.1.getD sib []]) := by
    simp only [levelStep, hsib, show 1 + j - 1 = j by omega]; rfl
  rw [hstep]
  refine Sim.steps hs1 (Sim.bind hnode (fun acc t2 hn => ?_))
  obtain ⟨-, hacc, haccv, haccs, -, pc2, x216, nregs, nframe⟩ := hn
  have pc2' : t2.pc = pcOf 179 := by rw [pc2, if_neg (lt_irrefl _)]
  have hs3 := symRun_sound blk179 codeAt_179 t2 pc2' (by simp only [blk179.res, rv_simp])
  have hc3 : blk179.res.cycles = 3 := rfl
  rw [hc3] at hs3
  set t3 := blk179.res.toState t2 with ht3
  have r3 : RegsEq t2 t3 [.x3, .x15] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk179.res]
  have x215 : t2.getReg .x15 = BitVec.ofNat 64 (j + 1) := by
    rw [nregs.toRegsEq.get .x15, r1.get .x15, t15]
  have ft13 : Frame t t3 (fun x => (x = 0x1C0 ∨ x = 0x2650 + 176 * k + 32 + 16 * j ∨
      x = 0x2650 + 176 * k + 32 + 16 * j + 8) ∨ ((c.B ≤ x ∧ x < c.B + 32 * c.m) ∨ x = 456 ∨ x = 480 ∨
        x = 488 ∨ x = 496 ∨ x = 504) ∨ False) := f1.trans (nframe.toFrame.trans f3)
  refine Sim.pure_steps hs3 ⟨by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hacc, show 10 - (j + 1) = 9 - j by omega]
  · exact haccv
  · show Slots t3 0x30000 acc
    have hm512 : acc.length ≤ 512 := by rw [hacc]; exact hp9
    exact (show Slots t2 0x30000 acc from haccs).frame f3 (by omega) (by simp)
  · simp [hplen]
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hpvals v hv
    · simp at hv; subst hv
      simp only [List.getElem?_eq_getElem (show sib < st.1.length by omega), Option.getD_some]
      exact hvals _ (List.getElem_mem _)
  · apply Slots.snoc
    · exact hpath.frame ft13 (by omega) (by
        intro i hi; constructor <;> (simp only [c, or_false, not_or]; omega))
    · rw [hplen, f3.readWords _ _ (by omega) (by simp),
        nframe.toFrame.readWords _ _ (by omega) (by intro i hi; simp only [c]; omega), hcap1]
  · simp only [ht3, blk179.res, rv_simp, x215, ofNat_add_ofNat]
    rw [ofNat_slt_ofNat _ _ (by norm_num) (by omega)]
    by_cases h : j + 1 < 10
    · rw [if_pos h]; simp; omega
    · rw [if_neg h]; simp; omega
  · simp only [ht3, blk179.res, rv_simp, x215, ofNat_add_ofNat]
  · rw [r3.get .x17, nregs.toRegsEq.get .x17, y17, show 10 - (j + 1) = 9 - j by omega]
  · exact (((tregs.trans r1).trans nregs.toRegsEq).trans r3).mono (by decide)
  · exact (tframe.trans ft13).mono (by
      intro x hx; simp only [levW, c, or_false] at hx ⊢; omega)
  · rw [f3.getMem (by norm_num) (by simp), nframe.2, f1.getMem (by norm_num) (by omega), tlo]

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- **FORS levels** of tree `k` (from `fors_level_loop` with `LAM = 1`, `NCNT = 1024`). -/
theorem forsLevels_sim (k idx u : Nat) (hk : k < 14) (hidx : idx < 2 ^ 34) (hu : u < 1024)
    (t0 : MachineState) (ctx : LevCtx k idx u t0) (leaves : List Val) (hlen : leaves.length = 1024)
    (hvals : ∀ v ∈ leaves, v.length = 16) (hslots : Slots t0 0x30000 leaves)
    (hpc : t0.pc = pcOf 142) (h15 : t0.getReg .x15 = BitVec.ofNat 64 1)
    (h17 : t0.getReg .x17 = BitVec.ofNat 64 1024) :
    Sim image t0 (10 * 12822) ((List.range' 1 10).foldlM (levelStep (ftsNodeInput k idx) u)
      (leaves, [])) (LevInv k t0 10) := by
  apply Sim.foldlM_range' 1 10 _ _ (LevInv k t0) 12822
  · intro j hj st t h
    refine (forsLevel_body k idx u hk hidx hu t0 ctx j hj st t h).mono ?_ (fun _ _ h => h)
    have : 2 ^ (9 - j) ≤ 512 := by
      calc 2 ^ (9 - j) ≤ 2 ^ 9 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 512 := by norm_num
    omega
  · exact ⟨by norm_num, by simpa using hlen, hvals, hslots, rfl, by simp, Slots.nil _ _,
      by simpa using hpc, h15, by simpa using h17, RegsEq.refl _ _, Frame.refl _ _, rfl⟩

end SigGolfCandidate.Sign
