import SigGolfCandidate.Sign.Layer

/-!
# `sign`: FORS roots hash and layer-loop entry (instructions 232 .. 262)
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- From `pc 191` (after the FORS trees): the roots hash `M`, then the layer loop entry. -/
theorem roots_sim (S cache : List Byte) (idx : Nat) (hidx : idx < 2 ^ 34) (roots : List Val)
    (hlen : roots.length = 14) (hv : ∀ v ∈ roots, v.length = 16) (t : MachineState)
    (tpc : t.pc = pcOf 239) (t5 : t.getReg .x5 = 0)
    (t22 : t.getReg .x22 = BitVec.ofNat 64 idx) (hroots : Slots t 0x240 roots)
    (h8lo : lo32 (t.getMem (BitVec.ofNat 64 0x228)) = BitVec.ofNat 32 idx)
    (h8hi : hi32 (t.getMem (BitVec.ofNat 64 0x228)) = 0)
    (hP : t.readWords (BitVec.ofNat 64 0x230) 2 = [0, 0]) (hst : Statics S t) (hrg : RegionOk cache t) :
    Sim image t (10 + (8 * 4 + 20)) (hash16 (rootsInput idx roots))
      (fun M t' => LayHead S cache idx 4 M t' ∧ Frame t t' (fun a => a = 0x220 ∨ (0x120 ≤ a ∧ a < 0x140))) := by
  have hs1 := symRun_sound blk239 codeAt_239 t tpc (by simp only [blk239.res, rv_simp])
  have hc1 : blk239.res.cycles = 10 := rfl
  rw [hc1] at hs1
  set t1 := blk239.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x220) := by
    apply frame_toState; intro x hx hW
    simp only [blk239.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x3, .x10, .x11, .x12, .x29] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk239 codeAt_239 t (by simp only [blk239.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x220 := by simp only [ht1, blk239.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 256 := by simp only [ht1, blk239.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x120 := by simp only [ht1, blk239.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, t5]
  have pc1 : t1.pc = pcOf 249 := by simp only [ht1, blk239.res, rv_simp]
  have m220 : t1.getMem (BitVec.ofNat 64 0x220) = twWord0 11 0 idx 0 := by
    simp only [ht1, blk239.res, rv_simp, t22]
    bvsimp []
    refine (word_of_halves _ (idx / 2 ^ 32 * 2 ^ 24 + 2817) 0 ?_ ?_).trans ?_
    · simp only [ite_true, lo32_replace1, lo32_replace0, truncate32_ofNat]; rfl
    · simp only [ite_true, hi32_replace1]
    · unfold twWord0; apply ofNat_congr; omega
  have hq : hashInput t1 = pad64 (rootsInput idx roots) := by
    obtain ⟨hn, hw⟩ := words_thVals 11 0 idx 0 0 roots hv 3 (by rw [hlen])
    refine hashInput_eq_pad64 t1 _ 3 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [rootsInput, hw, x10, show 8 * (3 + 1) = 1 + 1 + 2 + 2 * 14 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m220, f1.getMem (a := 0x228) (by norm_num) (by norm_num),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega), hP,
      show (28 : Nat) = 2 * roots.length by rw [hlen],
      f1.readWords _ _ (by rw [hlen]; norm_num) (by intro i hi; rw [hlen] at hi; omega),
      readWords_slots t 0x240 roots hroots]
    simp only [twWords_eq, List.cons_append, List.nil_append, List.cons.injEq, true_and]
    refine ⟨?_, trivial⟩
    rw [word_of_halves _ idx 0 h8lo (by rw [h8hi]; rfl)]
    (try (apply ofNat_congr; omega))
  have hb : (pad64 (rootsInput idx roots)).blocks = 4 :=
    congrArg (· + 1) (words_thVals 11 0 idx 0 0 roots hv 3 (by rw [hlen])).1
  refine (Sim.steps hs1 (Sim.hash16 (W := 20) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x120 ≤ x ∧ x < 0x120 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 250 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have hs3 := symRun_sound blk250 codeAt_250 t2 pc2 (by simp only [blk250.res, rv_simp])
  have hc3 : blk250.res.cycles = 20 := rfl
  rw [hc3] at hs3
  set t3 := blk250.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk250.res]
  have r3 : RegsEq t2 t3 [.x7, .x8, .x18, .x26, .x27] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have rt3 : RegsEq t t3 ([.x3, .x10, .x11, .x12, .x29] ++ [] ++ [.x7, .x8, .x18, .x26, .x27]) :=
    (r1.trans (regsEq_writeHash _ _ [])).trans r3
  have ft3 : Frame t t3 (fun a => a = 0x220 ∨ (0x120 ≤ a ∧ a < 0x140)) :=
    ((f1.trans f2).trans f3).mono (by
      intro x hx
      rcases hx with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (by omega)
      · exact h.elim)
  refine Sim.pure_steps hs3 ⟨⟨by norm_num, hidx, by simp, by simp only [ht3, blk250.res, rv_simp],
    by rw [rt3.get .x5, t5], by simp only [ht3, blk250.res, rv_simp]; rfl, by simp only [ht3, blk250.res, rv_simp],
    by simp only [ht3, blk250.res, rv_simp], by rw [rt3.get .x22, t22],
    by simp only [ht3, blk250.res, rv_simp], by simp only [ht3, blk250.res, rv_simp],
    by rw [f3.readWords _ _ (by norm_num) (by simp), writeHash_readWords_val t1 a _ x12 (by norm_num)],
    hst.frame ft3 (by intro a ha h; simp only [staticA] at ha; omega),
    hrg.frame ft3 (by intro a ha h; simp only [regionA] at ha; omega)⟩, ft3⟩

end SigGolfCandidate.Sign
