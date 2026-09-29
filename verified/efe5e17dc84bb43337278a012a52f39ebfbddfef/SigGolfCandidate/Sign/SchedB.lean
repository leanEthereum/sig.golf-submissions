import SigGolfCandidate.Sign.SchedA

/-! # `sign` schedule, part B: one height step and the inner loop (see `Sched.lean`). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem schedStep_nil (st : SchedState) (E cnt tt h : Nat) (hs : st.stack = []) :
    schedStep (st, E, cnt, tt) h = ({ st with reads := st.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)] }, E / 2, cnt + 1, tt) := by
  simp only [schedStep, hs]

theorem schedStep_ne (st : SchedState) (E cnt tt h Q : Nat) (rest : List Nat) (hs : st.stack = Q :: rest) (hQ : Q ≠ E) :
    schedStep (st, E, cnt, tt) h = ({ st with reads := st.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)] }, E / 2, cnt + 1, tt) := by
  simp only [schedStep, hs, if_neg hQ]

theorem schedStep_eq (st : SchedState) (E cnt tt h Q : Nat) (rest : List Nat) (hs : st.stack = Q :: rest) (hQ : Q = E) :
    schedStep (st, E, cnt, tt) h = ({ st with segs := st.segs ++ [cnt ||| 16 ||| 32 * tt], stack := rest },
      E / 2, 0, E / 2 % 2) := by
  simp only [schedStep, hs, if_pos hQ]

/-- One height step (`sch_h` 263 .. `sch_next` 287) at height `h < top`. -/
theorem sch_step (levels : List (List Val)) (hlen : ∀ l, l < 15 → (levels.getD l []).length = 2 ^ (14 - l))
    (hvv : ∀ l, l < 15 → ∀ v ∈ levels.getD l [], v.length = 16)
    (X : SchedState × Nat × Nat × Nat)
    (h top : Nat) (hh : h < top) (htop : top ≤ 14) (R0 : Nat) (hR0 : R0 + 14 ≤ 210)
    (t : MachineState) (tpc : t.pc = pcOf 263)
    (t19 : t.getReg .x19 = BitVec.ofNat 64 h) (t20 : t.getReg .x20 = BitVec.ofNat 64 top)
    (t18 : t.getReg .x18 = BitVec.ofNat 64 X.2.1) (hE1 : 2 ^ (14 - h) ≤ X.2.1) (hE2 : X.2.1 < 2 ^ (15 - h))
    (t30 : t.getReg .x30 = BitVec.ofNat 64 0xB0000)
    (hst : StackAt X.1.stack t) (hrd : ReadsAt levels X.1.reads t) (hR : X.1.reads.length ≤ R0 + h)
    (hlvt : ∀ l (hl : l < 15), Slots t (lvBase l) (levels.getD l [])) :
    ∃ k c t', Steps image t k c t' ∧ c ≤ 20 ∧ t'.pc = pcOf 263 ∧
      t'.getReg .x19 = BitVec.ofNat 64 (h + 1) ∧ t'.getReg .x20 = BitVec.ofNat 64 top ∧
      t'.getReg .x18 = BitVec.ofNat 64 (schedStep X h).2.1 ∧ t'.getReg .x30 = BitVec.ofNat 64 0xB0000 ∧
      (schedStep X h).2.1 = X.2.1 / 2 ∧
      StackAt (schedStep X h).1.stack t' ∧ ReadsAt levels (schedStep X h).1.reads t' ∧
      (schedStep X h).1.reads.length ≤ R0 + (h + 1) ∧ X.1.reads.length ≤ (schedStep X h).1.reads.length ∧
      RegsEq t t' [.x1, .x2, .x3, .x15, .x18, .x19, .x21, .x23, .x25, .x26, .x29] ∧
      Frame t t' (fun a => 0x3400 + 16 * X.1.reads.length ≤ a ∧ a < 0x3400 + 16 * (schedStep X h).1.reads.length) := by
  obtain ⟨st, E, cnt, tt⟩ := X
  simp only at t18 hE1 hE2 hst hrd hR ⊢
  have hst' := hst
  obtain ⟨hsl, h23, hsm, hs0, hsv⟩ := hst
  have hE0 : 1 ≤ E := le_trans Nat.one_le_two_pow hE1
  have hE15 : E < 2 ^ 15 := lt_of_lt_of_le hE2 (Nat.pow_le_pow_right (by norm_num) (by omega))
  -- block 263: h < top
  have hs1 := symRun_sound blk263 codeAt_263 t tpc (by simp only [blk263.res, rv_simp])
  set t1 := blk263.res.toState t with ht1
  have pc1 : t1.pc = pcOf 264 := by
    simp only [ht1, blk263.res, rv_simp, t19, t20]
    rw [ofNat_slt_ofNat _ _ (by omega) (by omega), if_neg (by simp; omega)]
  have g1 : ∀ q, t1.getReg q = t.getReg q := fun q => by
    rw [ht1, Result.toState_getReg]; cases q <;> rfl
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk263.res.st.mem = [] from rfl, memEval_nil]
  -- block 264: compare the stack top
  have hs2 := symRun_sound blk264 codeAt_264 t1 pc1 (by
    simp only [blk264.res, rv_simp, g1, h23, accessValid_ofNat]; omega)
  set t2 := blk264.res.toState t1 with ht2
  have r2 : RegsEq t1 t2 [.x3] := by
    intro q hq; rw [ht2, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have m2 : ∀ z, t2.getMem z = t.getMem z := fun z => by
    rw [ht2, Result.toState_getMem, show blk264.res.st.mem = [] from rfl, memEval_nil, m1]
  have hc1 : blk263.res.cycles = 1 := rfl
  have hc2 : blk264.res.cycles = 2 := rfl
  rw [hc1] at hs1
  rw [hc2] at hs2
  have g2 : ∀ q, q ≠ .x3 → t2.getReg q = t.getReg q := fun q hq => by rw [r2.get q (by simp [hq]), g1]
  have pc2 : ∀ w : Word, t.getMem (BitVec.ofNat 64 (0x760 + 8 * st.stack.length)) = w →
      t2.pc = if w != BitVec.ofNat 64 E then pcOf 271 else pcOf 266 := by
    intro w hw
    simp only [ht2, blk264.res, rv_simp, g1, h23, t18, m1, hw]
  -- the fold case (shared)
  have hfold : st.reads.length < 210 → t2.pc = pcOf 271 →
      ∃ k c t', Steps image t k c t' ∧ c ≤ 20 ∧ t'.pc = pcOf 263 ∧
        t'.getReg .x19 = BitVec.ofNat 64 (h + 1) ∧ t'.getReg .x20 = BitVec.ofNat 64 top ∧
        t'.getReg .x18 = BitVec.ofNat 64 (E / 2) ∧ t'.getReg .x30 = BitVec.ofNat 64 0xB0000 ∧
        StackAt st.stack t' ∧ ReadsAt levels (st.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)]) t' ∧
        RegsEq t t' [.x1, .x2, .x3, .x15, .x18, .x19, .x21, .x23, .x25, .x26, .x29] ∧
        Frame t t' (fun a => 0x3400 + 16 * st.reads.length ≤ a ∧ a < 0x3400 + 16 * (st.reads.length + 1)) := by
    intro hlt hpc
    obtain ⟨t3, hs3, pc3, x19', x18', rd3, r3, f3⟩ := sch_fold levels hlen hvv st E h (by omega) hE1 hE2 t2 hpc
      (by rw [g2 _ (by decide), t19]) (by rw [g2 _ (by decide), t18]) (by rw [g2 _ (by decide), t30])
      ⟨hrd.1, by rw [g2 _ (by decide), hrd.2.1], fun r hr => by
        rw [readWords_congr t t2 _ 2 (fun k _ => m2 _)]; exact hrd.2.2.1 r hr, hrd.2.2.2⟩
      hlt (fun l hl i hi => by rw [readWords_congr t t2 _ 2 (fun k _ => m2 _)]; exact hlvt l hl i hi)
    have rt0 := ((show RegsEq t t1 [] from fun q _ => g1 q).trans r2).trans r3
    have rt : RegsEq t t3 [.x1, .x2, .x3, .x15, .x18, .x19, .x21, .x23, .x25, .x26, .x29] := rt0.mono (by decide)
    refine ⟨_, _, t3, hs1.trans (hs2.trans hs3), by omega, pc3, x19', by rw [rt.get .x20, t20], x18',
      by rw [rt.get .x30, t30], ⟨hsl, by rw [rt0.get .x23, h23], fun i hi => ?_, ?_, hsv⟩, rd3, rt, ?_⟩
    · rw [f3.getMem (by omega) (by omega), m2]; exact hsm i hi
    · rw [f3.getMem (by norm_num) (by omega), m2, hs0]
    · intro a ha hW; rw [f3 a ha hW, m2]
  rcases hsk : st.stack with _ | ⟨Q, rest⟩
  · -- empty stack: fold
    have hm0 : t.getMem (BitVec.ofNat 64 (0x760 + 8 * st.stack.length)) = 0 := by rw [hsk]; exact hs0
    have hlt : st.reads.length < 210 := by omega
    obtain ⟨k, c, t3, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hfold hlt (by
      rw [pc2 0 hm0, if_pos (by rw [show (0 : Word) = BitVec.ofNat 64 0 from rfl, ofNat_bne_ofNat]; simp; omega)])
    rw [schedStep_nil st E cnt tt h hsk]
    exact ⟨k, c, t3, a1, a2, a3, a4, a5, a6, a7, rfl, by simp only [hsk] at a8 ⊢; exact a8, a9, by simp; omega,
      by simp, a10, by simpa using a11⟩
  · have hQ := hsv Q (by rw [hsk]; simp)
    have hmq : t.getMem (BitVec.ofNat 64 (0x760 + 8 * st.stack.length)) = BitVec.ofNat 64 Q := by
      have := hsm 0 (by rw [hsk]; simp)
      simp only [Nat.sub_zero] at this; rw [this]; simp [hsk]
    by_cases hQE : Q = E
    · -- merge
      have pcm : t2.pc = pcOf 266 := by
        rw [pc2 _ hmq, if_neg (by rw [ofNat_bne_ofNat]; simp; omega)]
      obtain ⟨t3, hs3, pc3, x19', x18', st3, r3, m3⟩ := sch_merge Q rest E h (by omega) t2 pcm
        (by rw [g2 _ (by decide), t19]) (by rw [g2 _ (by decide), t18])
        (by
          rw [← hsk]
          exact ⟨hsl, by rw [g2 _ (by decide), h23], fun i hi => by rw [m2]; exact hsm i hi, by rw [m2, hs0], hsv⟩)
      rw [schedStep_eq st E cnt tt h Q rest hsk hQE]
      have rt0 := ((show RegsEq t t1 [] from fun q _ => g1 q).trans r2).trans r3
      have rt : RegsEq t t3 [.x1, .x2, .x3, .x15, .x18, .x19, .x21, .x23, .x25, .x26, .x29] := rt0.mono (by decide)
      refine ⟨_, _, t3, hs1.trans (hs2.trans hs3), by omega, pc3, x19', by rw [rt.get .x20, t20], x18',
        by rw [rt.get .x30, t30], rfl, st3,
        ⟨hrd.1, by rw [rt0.get .x29, hrd.2.1], fun r hr => by
          rw [readWords_congr t t3 _ 2 (fun k _ => by rw [m3, m2])]; exact hrd.2.2.1 r hr, hrd.2.2.2⟩,
        by simp; omega, by simp, rt, fun a ha hW => by rw [m3, m2]⟩
    · -- fold
      have hlt : st.reads.length < 210 := by omega
      obtain ⟨k, c, t3, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11⟩ := hfold hlt (by
        rw [pc2 _ hmq, if_pos (by rw [ofNat_bne_ofNat]; simp; omega)])
      rw [schedStep_ne st E cnt tt h Q rest hsk hQE]
      exact ⟨k, c, t3, a1, a2, a3, a4, a5, a6, a7, rfl, by simp only [hsk] at a8 ⊢; exact a8, a9, by simp; omega,
        by simp, a10, by simpa using a11⟩

theorem schedStep_stack_len (X : SchedState × Nat × Nat × Nat) (h : Nat) :
    (schedStep X h).1.stack.length ≤ X.1.stack.length := by
  obtain ⟨st, E, cnt, tt⟩ := X
  rcases hs : st.stack with _ | ⟨Q, rest⟩
  · rw [schedStep_nil st E cnt tt h hs]; simp [hs]
  · by_cases hQ : Q = E
    · rw [schedStep_eq st E cnt tt h Q rest hs hQ]; simp [hs]
    · rw [schedStep_ne st E cnt tt h Q rest hs hQ]; simp [hs]

theorem foldl_stack_len (X : SchedState × Nat × Nat × Nat) (l : List Nat) :
    (l.foldl schedStep X).1.stack.length ≤ X.1.stack.length := by
  induction l generalizing X with
  | nil => simp
  | cons h l ih => rw [List.foldl_cons]; exact le_trans (ih _) (schedStep_stack_len X h)

/-- The inner loop `sch_h` from height `h` to `top` (then `sch_end`, 288). -/
theorem sch_inner (levels : List (List Val)) (hlen : ∀ l, l < 15 → (levels.getD l []).length = 2 ^ (14 - l))
    (hvv : ∀ l, l < 15 → ∀ v ∈ levels.getD l [], v.length = 16)
    (top : Nat) (htop : top ≤ 14) (R0 : Nat) (hR0 : R0 + 14 ≤ 210) :
    ∀ n h (X : SchedState × Nat × Nat × Nat) (t : MachineState), h + n = top → t.pc = pcOf 263 →
    t.getReg .x19 = BitVec.ofNat 64 h → t.getReg .x20 = BitVec.ofNat 64 top →
    t.getReg .x18 = BitVec.ofNat 64 X.2.1 → 2 ^ (14 - h) ≤ X.2.1 → X.2.1 < 2 ^ (15 - h) →
    t.getReg .x30 = BitVec.ofNat 64 0xB0000 →
    StackAt X.1.stack t → ReadsAt levels X.1.reads t → X.1.reads.length ≤ R0 + h →
    (∀ l (hl : l < 15), Slots t (lvBase l) (levels.getD l [])) →
    ∃ k c t', Steps image t k c t' ∧ c ≤ 20 * n + 1 ∧ t'.pc = pcOf 288 ∧
      t'.getReg .x18 = BitVec.ofNat 64 ((List.range' h n).foldl schedStep X).2.1 ∧
      2 ^ (14 - top) ≤ ((List.range' h n).foldl schedStep X).2.1 ∧
      ((List.range' h n).foldl schedStep X).2.1 < 2 ^ (15 - top) ∧
      t'.getReg .x30 = BitVec.ofNat 64 0xB0000 ∧
      StackAt ((List.range' h n).foldl schedStep X).1.stack t' ∧
      ReadsAt levels ((List.range' h n).foldl schedStep X).1.reads t' ∧
      ((List.range' h n).foldl schedStep X).1.reads.length ≤ R0 + top ∧
      X.1.reads.length ≤ ((List.range' h n).foldl schedStep X).1.reads.length ∧
      RegsEq t t' [.x1, .x2, .x3, .x15, .x18, .x19, .x21, .x23, .x25, .x26, .x29] ∧
      Frame t t' (fun a => 0x3400 + 16 * X.1.reads.length ≤ a ∧
        a < 0x3400 + 16 * ((List.range' h n).foldl schedStep X).1.reads.length) := by
  intro n
  induction n with
  | zero =>
    intro h X t hn tpc t19 t20 t18 hE1 hE2 t30 hst hrd hR hlvt
    have hs1 := symRun_sound blk263 codeAt_263 t tpc (by simp only [blk263.res, rv_simp])
    have hc1 : blk263.res.cycles = 1 := rfl
    rw [hc1] at hs1
    set t1 := blk263.res.toState t with ht1
    have g1 : ∀ q, t1.getReg q = t.getReg q := fun q => by
      rw [ht1, Result.toState_getReg]; cases q <;> rfl
    have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
      rw [ht1, Result.toState_getMem, show blk263.res.st.mem = [] from rfl, memEval_nil]
    simp only [List.range'_zero, List.foldl_nil]
    rw [show h = top by omega] at hE1 hE2 hR
    refine ⟨_, _, t1, hs1, by omega, ?_, by rw [g1, t18], hE1, hE2, by rw [g1, t30],
      ⟨hst.1, by rw [g1, hst.2.1], fun i hi => by rw [m1]; exact hst.2.2.1 i hi, by rw [m1, hst.2.2.2.1], hst.2.2.2.2⟩,
      ⟨hrd.1, by rw [g1, hrd.2.1], fun r hr => by
        rw [readWords_congr t t1 _ 2 (fun k _ => m1 _)]; exact hrd.2.2.1 r hr, hrd.2.2.2⟩, hR, le_refl _,
      fun q _ => g1 q, fun a ha hW => m1 _⟩
    simp only [ht1, blk263.res, rv_simp, t19, t20]
    rw [ofNat_slt_ofNat _ _ (by omega) (by omega), if_pos (by simp; omega)]
  | succ n ih =>
    intro h X t hn tpc t19 t20 t18 hE1 hE2 t30 hst hrd hR hlvt
    obtain ⟨k1, c1, t1, s1, hc1, pc1, x19, x20, x18, x30, hE, st1, rd1, hR1, hmono1, r1, f1⟩ :=
      sch_step levels hlen hvv X h top (by omega) htop R0 hR0 t tpc t19 t20 t18 hE1 hE2 t30 hst hrd hR hlvt
    have hm : 2 ^ (15 - h) = 2 * 2 ^ (14 - h) := by rw [← Nat.pow_succ']; congr 1; omega
    have hm' : 2 ^ (14 - h) = 2 * 2 ^ (14 - (h + 1)) := by rw [← Nat.pow_succ']; congr 1; omega
    obtain ⟨k2, c2, t2, s2, hc2, pc2, a1, a2, a3, a4, a5, a6, a7, a8, r2, f2⟩ :=
      ih (h + 1) (schedStep X h) t1 (by omega) pc1 x19 x20 x18
        (by rw [hE]; omega)
        (by rw [hE, show 15 - (h + 1) = 14 - h by omega]; omega) x30 st1 rd1 hR1
        (fun l hl i hi => by
          rw [f1.readWords _ _ (by
            have := lvBase_le l (by omega)
            have : i < 2 ^ (14 - l) := by rw [hlen l hl] at hi; exact hi
            omega) (by
            intro k hk
            have := lvBase_le l (by omega)
            have := lvBase_ge l
            have : i < 2 ^ (14 - l) := by rw [hlen l hl] at hi; exact hi
            omega)]
          exact hlvt l hl i hi)
    rw [List.range'_succ, List.foldl_cons]
    refine ⟨_, _, t2, s1.trans s2, by omega, pc2, a1, a2, a3, a4, a5, a6, a7, le_trans hmono1 a8,
      (r1.trans r2).mono (by decide), (f1.trans f2).mono (by intro a ha; omega)⟩

end SigGolfCandidate.Sign
