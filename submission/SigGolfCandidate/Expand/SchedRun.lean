import SigGolfCandidate.Expand.SchedBase

/-!
# `expand`: the schedule loop (`sch_*`, instructions 72 .. 131)

The machine follows `ref.schedule` on the sorted leaves `v_s = A s / 256` step by step. `HM` is
the invariant at `sch_h` (instruction 95, height `h` of leaf `s`, reference inner state `x`), `LM`
the one at `sch_leaf` (instruction 81, reference state `st` before leaf `s`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- The top height of leaf `s` (the machine reads the sentinel `2^14` after the last leaf). -/
def topM (A : Nat → Nat) (s : Nat) : Nat :=
  if s + 1 < 15 then bitLen (lv A s ^^^ lv A (s + 1)) - 1 else porsH

/-- Invariant at `sch_h` (instruction 95). -/
structure HM (A : Nat → Nat) (sig : List Byte) (t0 : MachineState) (s h : Nat)
    (x : SchedState × Nat × Nat × Nat) (u : MachineState) : Prop where
  pc : u.pc = pcOf 95
  x8 : u.getReg .x8 = BitVec.ofNat 64 s
  x9 : u.getReg .x9 = BitVec.ofNat 64 (lv A s)
  x20 : u.getReg .x20 = BitVec.ofNat 64 (topM A s)
  x19 : u.getReg .x19 = BitVec.ofNat 64 h
  x18 : u.getReg .x18 = BitVec.ofNat 64 x.2.1
  x15 : u.getReg .x15 = BitVec.ofNat 64 x.2.2.2
  x21 : u.getReg .x21 = BitVec.ofNat 64 x.2.2.1
  x23 : u.getReg .x23 = BitVec.ofNat 64 (0x760 + 8 * x.1.stack.length)
  x24 : u.getReg .x24 = BitVec.ofNat 64 (2 ^ 14)
  x29 : u.getReg .x29 = BitVec.ofNat 64 (0x3400 + 16 * x.1.reads.length)
  x30 : u.getReg .x30 = BitVec.ofNat 64 (0x910 + (segStream sig x.1.segs).length)
  x31 : u.getReg .x31 = BitVec.ofNat 64 (0x910 + (segStream sig x.1.segs).length + 8 + 16 * x.2.2.1)
  stack : StackOK u x.1.stack
  stackb : ∀ q ∈ x.1.stack, q < 2 ^ 15
  slen : x.1.stack.length ≤ s
  stream : StreamOK u (curStream sig x.1.segs x.2.2.1)
  nsum : nsum x.1.segs + x.2.2.1 = x.1.reads.length
  hE : x.2.1 = anc (lv A s) h
  cnt : x.2.2.1 ≤ h
  ht : x.2.2.2 ≤ 1
  hs : s < 15
  htop : h ≤ topM A s
  frame : Frame t0 u SW

/-- Facts about the state at the start of the schedule. -/
structure SchCtx (A : Nat → Nat) (sig : List Byte) (t0 : MachineState) : Prop where
  arr : ArrOk t0 A
  lt : ∀ p < 15, A p < 2 ^ 22
  sent : t0.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22)
  sigok : SigOK t0 sig
  siglen : sig.length = 6100

theorem topM_le (A : Nat → Nat) (hlt : ∀ p < 15, A p < 2 ^ 22) (s : Nat) : topM A s ≤ 14 := by
  unfold topM; split
  · have := bitLen_le (Nat.xor_lt_two_pow (lv_lt hlt (s := s) (by omega)) (lv_lt hlt (s := s + 1) (by omega)))
    omega
  · decide

/-- `sch_next` (117 .. 118): `h++`, back to `sch_h`. -/
theorem sch_next (u : MachineState) (hpc : u.pc = pcOf 117) (h : Nat)
    (h19 : u.getReg .x19 = BitVec.ofNat 64 h) :
    Run u 2 (fun v => v.pc = pcOf 95 ∧ v.getReg .x19 = BitVec.ofNat 64 (h + 1) ∧
      RegsEq u v [.x19] ∧ ∀ a, v.getMem a = u.getMem a) := by
  refine Run.of (symRun_sound blk117 codeAt_117 u hpc (by simp only [blk117.res, rv_simp])) (le_refl _)
    ⟨by simp only [blk117.res, rv_simp], by simp only [blk117.res, rv_simp, h19]; ex_bvsimp [],
      by regs_eq, toState_getMem_nil rfl u⟩

theorem sch_step (A : Nat → Nat) (sig : List Byte) (t0 : MachineState) (hc : SchCtx A sig t0)
    (s h : Nat) (x : SchedState × Nat × Nat × Nat) (u : MachineState) (hm : HM A sig t0 s h x u)
    (hh : h < topM A s) (hr : (schedStep x h).1.reads.length ≤ 120)
    (hg : (schedStep x h).1.segs.length + 1 ≤ 29) :
    Run u 16 (HM A sig t0 s (h + 1) (schedStep x h)) := by
  obtain ⟨st, E, cnt, t⟩ := x
  obtain ⟨hpc, h8, h9, h20, h19, h18, h15, h21, h23, h24, h29, h30, h31, hstk, hstkb, hslen, hstr,
    hns, hE, hcnt, htt, hs, htp, hfr⟩ := hm
  dsimp only at h18 h15 h21 h23 h29 h30 h31 hstk hstkb hslen hstr hns hE hcnt htt
  have htop14 := topM_le A hc.lt s
  refine (Run.blk blk95 codeAt_95 hpc (by simp only [blk95.res, rv_simp]) (B := 15) ?_).mono
    (by rw [show blk95.res.cycles = 1 from rfl]) (fun _ h => h)
  set u1 := blk95.res.toState u with hu1
  have p1 : u1.pc = pcOf 96 := by
    simp only [hu1, blk95.res, rv_simp, h19, h20]
    rw [ofNat_slt_ofNat _ _ (by omega) (by omega)]; simp [hh]
  have r1 : RegsEq u u1 [] := by regs_eq
  have m1 : ∀ a, u1.getMem a = u.getMem a := toState_getMem_nil rfl u
  have hobl2 : blk96.res.obligs u1 := by
    simp only [blk96.res, rv_simp, r1.get .x23 (by simp), h23]; ex_bvsimp [accessValid_ofNat]; omega
  refine (Run.blk blk96 codeAt_96 p1 hobl2 (B := 13) ?_).mono
    (by rw [show blk96.res.cycles = 2 from rfl]) (fun _ h => h)
  set u2 := blk96.res.toState u1 with hu2
  have r2 : RegsEq u u2 [.x3] := by
    have : RegsEq u1 u2 [.x3] := by regs_eq
    exact (r1.trans this).mono (fun r hr => by simpa using hr)
  have m2 : ∀ a, u2.getMem a = u.getMem a := fun a => by rw [toState_getMem_nil rfl, m1]
  -- the top of the stack
  have hEpos : 0 < E := by rw [hE]; exact anc_pos (lv_lt hc.lt hs) (by unfold porsH; omega)
  have hElt : E < 2 ^ 15 := by
    rw [hE]; have := (anc_bounds (lv_lt hc.lt hs) (g := h) (by unfold porsH; omega)).2
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by unfold porsH; omega))
  have htopv : u.getMem (BitVec.ofNat 64 (0x760 + 8 * st.stack.length)) =
      BitVec.ofNat 64 (st.stack.headD 0) := by
    cases hst : st.stack with
    | nil => simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]; rw [hstk.1]; rfl
    | cons Q rest =>
      have := hstk.2 0 (by simp [hst]); simp only [hst, Nat.sub_zero, List.getD_cons_zero] at this
      exact this
  have hQb : st.stack.headD 0 < 2 ^ 15 := by
    cases hst : st.stack with
    | nil => simp
    | cons Q rest => exact hstkb Q (by simp [hst])
  have p2 : u2.pc = if st.stack.headD 0 = E then pcOf 98 else pcOf 109 := by
    simp only [hu2, blk96.res, rv_simp, r1.get .x23 (by simp), r1.get .x18 (by simp), h23, h18]
    rw [m1, htopv, ofNat_bne_ofNat]
    generalize st.stack.headD 0 = q at hQb ⊢
    rw [Nat.mod_eq_of_lt (a := q) (by omega), Nat.mod_eq_of_lt (a := E) (by omega)]
    by_cases hq : q = E <;> simp [hq]
  have hnsr : nsum st.segs ≤ 120 := by
    have := (schedStep_mono (st, E, cnt, t) h).1; dsimp only at this; omega
  have hL := length_segStream sig hc.siglen st.segs hnsr
  by_cases hq : st.stack.headD 0 = E
  · -- merge
    rw [if_pos hq] at p2
    obtain ⟨Q, rest, hst, hQE⟩ : ∃ Q rest, st.stack = Q :: rest ∧ Q = E := by
      cases hst : st.stack with
      | nil => rw [hst] at hq; simp at hq; omega
      | cons Q rest => rw [hst] at hq; exact ⟨Q, rest, rfl, hq⟩
    rw [schedStep_merge st E cnt t h Q rest hst hQE] at hr hg ⊢
    dsimp only at hr hg
    simp only [List.length_append, List.length_singleton] at hg
    have hc16 : cnt < 16 := by omega
    have hrl : rest.length ≤ 13 := by have := hslen; rw [hst] at this; simp at this; omega
    set b := cnt ||| 16 ||| 32 * t with hbdef
    have hbv : b = cnt + 16 + 32 * t := segByte_merge cnt t hc16 htt
    have hb16 : b % 16 = cnt := by omega
    have hL' := length_segStream sig hc.siglen (st.segs ++ [b]) (by rw [nsum_snoc]; omega)
    rw [nsum_snoc, hb16] at hL'
    simp only [List.length_append, List.length_singleton] at hL'
    have hobl3 : blk98.res.obligs u2 := by
      simp only [blk98.res, rv_simp, r2.get .x30 (by simp), h30]; ex_bvsimp [accessValid_ofNat]; omega
    refine (Run.blk blk98 codeAt_98 p2 hobl3 (B := 2) ?_).mono
      (by rw [show blk98.res.cycles = 11 by kernel_rfl]) (fun _ h => h)
    set u3 := blk98.res.toState u2 with hu3
    have p3 : u3.pc = pcOf 117 := by simp only [hu3, blk98.res, rv_simp]
    have r3 : RegsEq u2 u3 [.x15, .x18, .x21, .x23, .x25, .x30, .x31] := by regs_eq
    have y19 : u3.getReg .x19 = BitVec.ofNat 64 h := by rw [r3.get .x19 (by simp), r2.get .x19 (by simp), h19]
    have hwb : (u2.getReg .x15 <<< 5 ||| u2.getReg .x21 ||| 16#64).truncate 8 = byte b := by
      rw [r2.get .x15 (by simp), r2.get .x21 (by simp), h15, h21, ofNat_shiftLeft,
        ofNat_or_ofNat _ _ (by omega) (by omega),
        show (16#64 : Word) = BitVec.ofNat 64 16 from rfl, ofNat_or_ofNat _ _ (by
          have : t * 2 ^ 5 ||| cnt < 2 ^ 6 := Nat.or_lt_two_pow (by omega) (by omega)
          omega) (by omega), truncate8_ofNat]
      unfold byte; congr 1
      rw [hbdef]
      interval_cases t <;> interval_cases cnt <;> rfl
    have hm3 : ∀ y : Nat, y < 2 ^ 64 → u3.getMem (BitVec.ofNat 64 y) =
        if y = 0x910 + (segStream sig st.segs).length then
          replaceByte (u2.getMem (BitVec.ofNat 64 y)) 0 (byte b) else u2.getMem (BitVec.ofNat 64 y) := by
      intro y hy
      rw [hu3, toState_getMem_one rfl]
      simp only [Addr.eval, Rv.E.eval, BinOp.eval, StoreKind.merge, Option.map, BitVec.add_zero]
      rw [show ((5#64 : Word).toNat % 64) = 5 from rfl, hwb, r2.get .x30 (by simp), h30]
      by_cases hy' : y = 0x910 + (segStream sig st.segs).length
      · subst hy'; simp
      · rw [if_neg hy', if_neg (by rw [ofNat_eq_iff]; omega)]
    refine (sch_next u3 p3 h y19).mono (le_refl _) (fun u4 ⟨p4, y19', r4, m4⟩ => ?_)
    have m42 : ∀ y : Nat, y < 2 ^ 64 → y ≠ 0x910 + (segStream sig st.segs).length →
        u4.getMem (BitVec.ofNat 64 y) = u.getMem (BitVec.ofNat 64 y) := by
      intro y hy hne; rw [m4, hm3 y hy, if_neg hne, m2]
    have g : ∀ r : Reg, r ∉ [.x15, .x18, .x21, .x23, .x25, .x30, .x31, .x3, .x19] →
        u4.getReg r = u.getReg r := by
      intro r hr
      rw [r4.get r (by simp at hr ⊢; tauto), r3.get r (by simp at hr ⊢; tauto), r2.get r (by simp at hr ⊢; tauto)]
    have y3 : ∀ r : Reg, r = .x15 ∨ r = .x18 ∨ r = .x21 ∨ r = .x23 ∨ r = .x30 ∨ r = .x31 →
        u4.getReg r = u3.getReg r := fun r hr => r4.get r (by rcases hr with h | h | h | h | h | h <;> subst h <;> decide)
    refine ⟨p4, by rw [g .x8 (by decide), h8], by rw [g .x9 (by decide), h9],
      by rw [g .x20 (by decide), h20], y19', ?_, ?_, ?_, ?_, by rw [g .x24 (by decide), h24],
      by rw [g .x29 (by decide), h29], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, by dsimp only; omega,
      by dsimp only; omega, hs, by omega, ?_⟩
    · -- x18
      rw [y3 .x18 (by simp)]; simp only [hu3, blk98.res, rv_simp, r2.get .x18 (by simp), h18]; ex_bvsimp []
    · -- x15
      rw [y3 .x15 (by simp)]; simp only [hu3, blk98.res, rv_simp, r2.get .x18 (by simp), h18]; ex_bvsimp []
      rw [Nat.and_one_is_mod]
    · rw [y3 .x21 (by simp)]; simp only [hu3, blk98.res, rv_simp]
    · rw [y3 .x23 (by simp)]; simp only [hu3, blk98.res, rv_simp, r2.get .x23 (by simp), h23, hst]
      (try ex_bvsimp []); (try simp only [List.length_cons])
      rw [show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_sub_ofNat _ _ (by omega) (by omega)]
      exact ofNat_congr (by omega)
    · rw [y3 .x30 (by simp)]; simp only [hu3, blk98.res, rv_simp, r2.get .x31 (by simp), h31]
      exact ofNat_congr (by omega)
    · rw [y3 .x31 (by simp)]; simp only [hu3, blk98.res, rv_simp, r2.get .x31 (by simp), h31]
      ex_bvsimp []; exact ofNat_congr (by omega)
    · -- stack
      refine ⟨by rw [m42 _ (by omega) (by omega)]; exact hstk.1, fun i hi => ?_⟩
      dsimp only at hi ⊢
      have := hstk.2 (i + 1) (by rw [hst]; simp; omega)
      rw [hst] at this; simp only [List.length_cons, List.getD_cons_succ] at this
      rw [m42 _ (by omega) (by omega), ← this]; congr 3; omega
    · intro q hq; exact hstkb q (by rw [hst]; exact List.mem_cons_of_mem _ hq)
    · dsimp only; have := hslen; rw [hst] at this; simp at this; omega
    · exact stream_sb (P := (segStream sig st.segs).length) (by rw [hL]; omega) (by omega) hstr
        (fun y hy => by rw [m4]; exact hm3 y hy) (fun i => curStream_emit sig st.segs b cnt hb16 i)
    · rw [nsum_snoc, hb16]; exact hns
    · rw [hE, anc_succ]
    · exact frame_of_writes hfr (fun y hy hW => m42 y hy (by unfold SW at hW; omega))
  · -- fold
    rw [if_neg hq] at p2
    have hnot : ∀ Q rest, st.stack = Q :: rest → Q ≠ E := by
      intro Q rest hst hQ; apply hq; rw [hst]; exact hQ
    rw [schedStep_fold st E cnt t h hnot] at hr hg ⊢
    dsimp only at hr hg
    simp only [List.length_append, List.length_singleton] at hr
    have hlc : (curStream sig st.segs cnt).length = (segStream sig st.segs).length + 8 + 16 * cnt := by
      rw [curStream, List.length_append, List.length_append, length_items sig hc.siglen _ _ (by omega)]
      simp [zeros]
    have hLm : (segStream sig st.segs).length % 8 = 0 := by rw [hL]; omega
    have hobl3 : blk109.res.obligs u2 := by
      simp only [blk109.res, rv_simp, r2.get .x31 (by simp), r2.get .x29 (by simp), h31, h29]
      ex_bvsimp [accessValid_ofNat]; omega
    refine (Run.blk blk109 codeAt_109 p2 hobl3 (B := 2) ?_).mono
      (by rw [show blk109.res.cycles = 8 by kernel_rfl]; try omega) (fun _ h => h)
    set u3 := blk109.res.toState u2 with hu3
    have p3 : u3.pc = pcOf 117 := by simp only [hu3, blk109.res, rv_simp]
    have r3 : RegsEq u2 u3 [.x1, .x2, .x18, .x21, .x29, .x31] := by regs_eq
    have y19 : u3.getReg .x19 = BitVec.ofNat 64 h := by rw [r3.get .x19 (by simp), r2.get .x19 (by simp), h19]
    set L := (segStream sig st.segs).length with hLdef
    set r := st.reads.length with hrdef
    have hm3 : ∀ y : Nat, y < 2 ^ 64 → u3.getMem (BitVec.ofNat 64 y) =
        if y = 0x910 + (L + 8 + 16 * cnt) + 8 then u.getMem (BitVec.ofNat 64 (0x3400 + 16 * r + 8))
        else if y = 0x910 + (L + 8 + 16 * cnt) then u.getMem (BitVec.ofNat 64 (0x3400 + 16 * r))
        else u2.getMem (BitVec.ofNat 64 y) := by
      intro y hy
      rw [hu3, toState_getMem_two rfl]
      simp only [Addr.eval, Rv.E.eval, BinOp.eval, Option.map, BitVec.add_zero, r2.get .x31 (by simp),
        r2.get .x29 (by simp), h31, h29, m2]
      rw [show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat]
      by_cases e1 : y = 0x910 + (L + 8 + 16 * cnt) + 8
      · rw [if_pos (ofNat_congr (by omega)), if_pos e1]; exact congrArg _ (ofNat_add_ofNat _ 8)
      · rw [if_neg (by rw [ofNat_eq_iff]; omega), if_neg e1]
        by_cases e2 : y = 0x910 + (L + 8 + 16 * cnt)
        · rw [if_pos (ofNat_congr (by omega)), if_pos e2]
        · rw [if_neg (by rw [ofNat_eq_iff]; omega), if_neg e2]
    refine (sch_next u3 p3 h y19).mono (le_refl _) (fun u4 ⟨p4, y19', r4, m4⟩ => ?_)
    have m42 : ∀ y : Nat, y < 2 ^ 64 → (y < 0x910 + L + 8 + 16 * cnt ∨ 0x910 + L + 8 + 16 * cnt + 16 ≤ y) →
        u4.getMem (BitVec.ofNat 64 y) = u.getMem (BitVec.ofNat 64 y) := by
      intro y hy hne; rw [m4, hm3 y hy, if_neg (by omega), if_neg (by omega), m2]
    have g : ∀ r : Reg, r ∉ [.x1, .x2, .x18, .x21, .x29, .x31, .x3, .x19] → u4.getReg r = u.getReg r := by
      intro r hr
      rw [r4.get r (by simp at hr ⊢; tauto), r3.get r (by simp at hr ⊢; tauto), r2.get r (by simp at hr ⊢; tauto)]
    have y3 : ∀ r : Reg, r = .x18 ∨ r = .x21 ∨ r = .x29 ∨ r = .x31 → u4.getReg r = u3.getReg r :=
      fun r hr => r4.get r (by rcases hr with h | h | h | h <;> subst h <;> decide)
    refine ⟨p4, by rw [g .x8 (by decide), h8], by rw [g .x9 (by decide), h9],
      by rw [g .x20 (by decide), h20], y19', ?_, by rw [g .x15 (by decide), h15], ?_,
      by rw [g .x23 (by decide), h23], by rw [g .x24 (by decide), h24], ?_,
      by rw [g .x30 (by decide), h30], ?_, ?_, hstkb, hslen, ?_, ?_, ?_, by dsimp only; omega,
      htt, hs, by omega, ?_⟩
    · rw [y3 .x18 (by simp)]; simp only [hu3, blk109.res, rv_simp, r2.get .x18 (by simp), h18]; ex_bvsimp []
    · rw [y3 .x21 (by simp)]; simp only [hu3, blk109.res, rv_simp, r2.get .x21 (by simp), h21]; ex_bvsimp []
    · rw [y3 .x29 (by simp)]; simp only [hu3, blk109.res, rv_simp, r2.get .x29 (by simp), h29]; ex_bvsimp []
      simp only [List.length_append, List.length_singleton]; exact ofNat_congr (by ring)
    · rw [y3 .x31 (by simp)]; simp only [hu3, blk109.res, rv_simp, r2.get .x31 (by simp), h31]; ex_bvsimp []
      exact ofNat_congr (by ring)
    · dsimp only
      refine ⟨by rw [m42 _ (by omega) (by omega)]; exact hstk.1, fun i hi => ?_⟩
      rw [m42 _ (by omega) (by omega)]; exact hstk.2 i hi
    · dsimp only
      rw [curStream_succ]
      refine stream_sd2 (P := L + 8 + 16 * cnt) (by omega) (by omega) (by rw [hlc]) 
        (length_sigAuth sig hc.siglen _ (by omega)) hstr (fun y hy => by rw [m4, hm3 y hy, m2]) ?_ ?_
      · intro k hk
        rw [hfr _ (by omega) (by unfold SW; omega), show 0x3400 + 16 * r = 0x3300 + (256 + 16 * r) by ring,
          sig_dword_byte hc.sigok _ _ (by omega) hk (by omega), getD_sigAuth sig hc.siglen _ _ (by omega) (by omega),
          show nsum st.segs + cnt = r from hns]
      · intro k hk
        rw [hfr _ (by omega) (by unfold SW; omega), show 0x3400 + 16 * r + 8 = 0x3300 + (256 + 16 * r + 8) by ring,
          sig_dword_byte hc.sigok _ _ (by omega) hk (by omega), getD_sigAuth sig hc.siglen _ _ (by omega) (by omega),
          show nsum st.segs + cnt = r from hns]
        congr 1; ring
    · dsimp only; simp only [List.length_append, List.length_singleton]; omega
    · dsimp only; rw [hE, anc_succ]
    · exact frame_of_writes hfr (fun y hy hW => m42 y hy (by unfold SW at hW; omega))



/-- The `bitlen_2` loop (instructions 88 .. 90): `a3 >>= 1; s4++` until `a3 = 0`. -/
theorem bitlen2_loop : ∀ y, 0 < y → y < 2 ^ 64 → ∀ (u : MachineState) (w : Word), u.pc = pcOf 88 →
    u.getReg .x13 = BitVec.ofNat 64 y → u.getReg .x20 = w →
    Run u (3 * bitLen y) (fun v => v.pc = pcOf 91 ∧ v.getReg .x20 = w + BitVec.ofNat 64 (bitLen y) ∧
      RegsEq u v [.x13, .x20] ∧ ∀ a, v.getMem a = u.getMem a) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy hy64 u w upc u13 u20
    have hb := bitLen_half y hy
    refine (Run.blk blk88 codeAt_88 upc (by simp only [blk88.res, rv_simp]) (B := 3 * bitLen (y / 2)) ?_).mono
      (by rw [show blk88.res.cycles = 3 from rfl]; omega) (fun _ h => h)
    set v := blk88.res.toState u with hv
    have v13 : v.getReg .x13 = BitVec.ofNat 64 (y / 2) := by
      simp only [hv, blk88.res, rv_simp, u13]; ex_bvsimp []
    have v20 : v.getReg .x20 = w + 1#64 := by simp only [hv, blk88.res, rv_simp, u20]
    have rv : RegsEq u v [.x13, .x20] := by regs_eq
    have vm : ∀ a, v.getMem a = u.getMem a := toState_getMem_nil rfl u
    have vpc : v.pc = if y / 2 = 0 then pcOf 91 else pcOf 88 := by
      simp only [hv, blk88.res, rv_simp, u13]; ex_bvsimp [ofNat_bne_ofNat]
      by_cases h : y / 2 = 0 <;> simp [h]
    by_cases h0 : y / 2 = 0
    · rw [if_pos h0] at vpc
      refine Run.done' ⟨vpc, ?_, rv, vm⟩
      rw [v20, hb, h0]; rfl
    · rw [if_neg h0] at vpc
      have := ih (y / 2) (by omega) (by omega) (by omega) v (w + 1#64) vpc v13 v20
      refine this.mono (le_refl _) (fun x ⟨h1, h2, h3, h4⟩ => ⟨h1, ?_, ?_, fun a => by rw [h4, vm]⟩)
      · rw [h2, hb, BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
      · exact (rv.trans h3).mono (fun r hr => by simp at hr ⊢; tauto)



/-- Invariant at `sch_leaf` (instruction 81) before leaf `s` (`s < 15`), or at 132 after the last
leaf (`s = 15`). -/
structure LM (A : Nat → Nat) (sig : List Byte) (t0 : MachineState) (s : Nat) (st : SchedState)
    (u : MachineState) : Prop where
  pc : u.pc = if s < 15 then pcOf 81 else pcOf 132
  x8 : u.getReg .x8 = BitVec.ofNat 64 s
  x23 : u.getReg .x23 = BitVec.ofNat 64 (0x760 + 8 * st.stack.length)
  x24 : u.getReg .x24 = BitVec.ofNat 64 (2 ^ 14)
  x29 : u.getReg .x29 = BitVec.ofNat 64 (0x3400 + 16 * st.reads.length)
  x30 : u.getReg .x30 = BitVec.ofNat 64 (0x910 + (segStream sig st.segs).length)
  x31 : u.getReg .x31 = BitVec.ofNat 64 (0x910 + (segStream sig st.segs).length + 8)
  stack : StackOK u st.stack
  stackb : ∀ q ∈ st.stack, q < 2 ^ 15
  slen : st.stack.length ≤ s
  stream : StreamOK u (curStream sig st.segs 0)
  nsum : nsum st.segs = st.reads.length
  hs : s ≤ 15
  frame : Frame t0 u SW

theorem keys_frame {A : Nat → Nat} {sig : List Byte} {t0 u : MachineState} (hc : SchCtx A sig t0)
    (hf : Frame t0 u SW) (p : Nat) (hp : p < 16) :
    u.getMem (BitVec.ofNat 64 (0x6E0 + 8 * p)) = BitVec.ofNat 64 (if p < 15 then A p else 2 ^ 22) := by
  rw [hf _ (by omega) (by unfold SW; omega)]
  split
  · exact hc.arr p (by omega)
  · rw [show 0x6E0 + 8 * p = 0x758 by omega]; exact hc.sent

theorem leaf_start (A : Nat → Nat) (sig : List Byte) (t0 : MachineState) (hc : SchCtx A sig t0)
    (hd : ∀ s < 14, lv A s ≠ lv A (s + 1)) (s : Nat) (hs : s < 15) (st : SchedState) (u : MachineState)
    (hl : LM A sig t0 s st u) :
    Run u 56 (HM A sig t0 s 0 (st, porsT ||| lv A s, 0, (porsT ||| lv A s) % 2)) := by
  obtain ⟨hpc, h8, h23, h24, h29, h30, h31, hstk, hstkb, hslen, hstr, hns, hs', hfr⟩ := hl
  rw [if_pos hs] at hpc
  have hobl : blk81.res.obligs u := by
    simp only [blk81.res, rv_simp, h8]; ex_bvsimp [accessValid_ofNat]; omega
  refine (Run.blk blk81 codeAt_81 hpc hobl (B := 49) ?_).mono
    (by rw [show blk81.res.cycles = 7 by kernel_rfl]) (fun _ h => h)
  set u1 := blk81.res.toState u with hu1
  have k0 := keys_frame hc hfr s (by omega)
  have k1 := keys_frame hc hfr (s + 1) (by omega)
  have hA := hc.lt s hs
  have hlvs := lv_lt hc.lt hs
  obtain ⟨Z, k1', hZb, hZne, hZ⟩ : ∃ Z, u.getMem (BitVec.ofNat 64 (0x6E0 + 8 * (s + 1))) = BitVec.ofNat 64 Z ∧
      Z < 2 ^ 22 + 1 ∧ Z / 256 ≠ lv A s ∧ Z = if s + 1 < 15 then A (s + 1) else 2 ^ 22 := by
    refine ⟨_, k1, ?_, ?_, rfl⟩
    · split
      · have := hc.lt (s + 1) (by omega); omega
      · omega
    · split
      · intro h0; exact hd s (by omega) (by unfold lv; exact h0.symm)
      · unfold lv at hlvs ⊢; omega
  rw [if_pos hs] at k0
  set y := Z / 256 ^^^ lv A s with hy
  have hylt : y < 2 ^ 15 := by
    have h1 : Z / 256 < 2 ^ 15 := by omega
    have h2 : lv A s < 2 ^ 15 := by omega
    exact Nat.xor_lt_two_pow h1 h2
  have hypos : 0 < y := by
    rcases Nat.eq_zero_or_pos y with h0 | h0
    · exfalso; rw [hy, nat_xor_eq_zero] at h0; exact hZne h0
    · exact h0
  have p1 : u1.pc = pcOf 88 := by simp only [hu1, blk81.res, rv_simp]
  have y13 : u1.getReg .x13 = BitVec.ofNat 64 y := by
    simp only [hu1, blk81.res, rv_simp, h8]; ex_bvsimp []
    rw [show s * 8 + 1768 = 0x6E0 + 8 * (s + 1) by ring, show s * 8 + 1760 = 0x6E0 + 8 * s by ring, k0, k1']
    ex_bvsimp [lv]; rfl
  have y20 : u1.getReg .x20 = 18446744073709551615#64 := by simp only [hu1, blk81.res, rv_simp]
  have y9 : u1.getReg .x9 = BitVec.ofNat 64 (lv A s) := by
    simp only [hu1, blk81.res, rv_simp, h8]; ex_bvsimp []
    rw [show s * 8 + 1760 = 0x6E0 + 8 * s by ring, k0]; ex_bvsimp [lv]
  have r1 : RegsEq u u1 [.x3, .x9, .x13, .x20] := by regs_eq
  have m1 : ∀ a, u1.getMem a = u.getMem a := toState_getMem_nil rfl u
  have hbl := bitlen2_loop y hypos (by omega) u1 _ p1 y13 y20
  have hbly : bitLen y ≤ 15 := bitLen_le hylt
  refine (Run.bind (B₂ := 4) hbl (fun u2 ⟨p2, y20', r2, m2⟩ => ?_)).mono (by omega) (fun _ h => h)
  refine Run.of (symRun_sound blk91 codeAt_91 u2 p2 (by simp only [blk91.res, rv_simp])) (by decide) ?_
  set u3 := blk91.res.toState u2 with hu3
  have r3 : RegsEq u2 u3 [.x15, .x18, .x19, .x21] := by regs_eq
  have m3 : ∀ a, u3.getMem a = u.getMem a := fun a => by rw [toState_getMem_nil rfl, m2, m1]
  have g : ∀ r : Reg, r ∉ [.x3, .x9, .x13, .x20, .x15, .x18, .x19, .x21] → u3.getReg r = u.getReg r := by
    intro r hr
    rw [r3.get r (by simp at hr ⊢; tauto), r2.get r (by simp at hr ⊢; tauto), r1.get r (by simp at hr ⊢; tauto)]
  have z9 : u2.getReg .x9 = BitVec.ofNat 64 (lv A s) := by rw [r2.get .x9 (by simp), y9]
  have z24 : u2.getReg .x24 = BitVec.ofNat 64 (2 ^ 14) := by rw [r2.get .x24 (by simp), r1.get .x24 (by simp), h24]
  have hor : lv A s ||| 2 ^ 14 = porsT ||| lv A s := Nat.or_comm _ _
  have hor2 : porsT ||| lv A s = porsT + lv A s := or_porsT hlvs
  refine ⟨by simp only [hu3, blk91.res, rv_simp], by rw [g .x8 (by decide), h8], ?_, ?_, ?_, ?_, ?_, ?_,
    by rw [g .x23 (by decide), h23], by rw [g .x24 (by decide), h24], by rw [g .x29 (by decide), h29],
    by rw [g .x30 (by decide), h30], by rw [g .x31 (by decide), h31]; simp, ?_, hstkb, by dsimp only; omega, ?_,
    by dsimp only; omega, by dsimp only; rw [anc_zero, hor2], le_refl _, by dsimp only; omega, hs,
    Nat.zero_le _, ?_⟩
  · rw [r3.get .x9 (by simp), z9]
  · rw [r3.get .x20 (by simp), y20']
    have hbl1 : 1 ≤ bitLen y := by rw [bitLen_pos (by omega)]; omega
    have key : bitLen y - 1 = topM A s := by
      unfold topM
      split
      · rw [hy, hZ, if_pos (by omega), Nat.xor_comm]; rfl
      · rw [hy, hZ, if_neg (by omega)]
        have hx : (2 : Nat) ^ 22 / 256 ^^^ lv A s = 2 ^ 14 + lv A s := by
          have := Nat.two_pow_add_eq_or_of_lt (i := 14) hlvs 1
          rw [Nat.mul_one] at this
          rw [show (2 : Nat) ^ 22 / 256 = 2 ^ 14 by norm_num, this]
          apply Nat.eq_of_testBit_eq; intro i
          simp only [Nat.testBit_xor, Nat.testBit_or]
          by_cases hi : i = 14
          · subst hi; rw [Nat.testBit_lt_two_pow hlvs]; simp
          · rw [Nat.testBit_two_pow_of_ne (Ne.symm hi)]; simp
        rw [hx, bitLen_pos (by omega)]
        have := (Nat.log2_eq_iff (show 2 ^ 14 + lv A s ≠ 0 by omega) (k := 14)).2 ⟨by omega, by omega⟩
        rw [this]; rfl
    rw [← key]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · simp only [hu3, blk91.res, rv_simp]
  · simp only [hu3, blk91.res, rv_simp, z9, z24]
    rw [ofNat_or_ofNat _ _ (by omega) (by norm_num), hor]
  · simp only [hu3, blk91.res, rv_simp, z9, z24]
    rw [ofNat_or_ofNat _ _ (by omega) (by norm_num), hor, show (1#64 : Word) = BitVec.ofNat 64 1 from rfl,
      ofNat_and_ofNat _ _ (by rw [hor2]; unfold porsT porsH; omega) (by norm_num), Nat.and_one_is_mod]
  · simp only [hu3, blk91.res, rv_simp]
  · exact ⟨by rw [m3]; exact hstk.1, fun i hi => by rw [m3]; exact hstk.2 i hi⟩
  · intro i hi; rw [getByte_ofNat _ _ (by omega), m3, ← getByte_ofNat _ _ (by omega)]; exact hstr i hi
  · exact frame_of_writes hfr (fun y hy _ => m3 _)



theorem leaf_close (A : Nat → Nat) (sig : List Byte) (t0 : MachineState) (s : Nat) (hs : s < 15)
    (st : SchedState) (u : MachineState) (hpc : u.pc = pcOf 129) (h8 : u.getReg .x8 = BitVec.ofNat 64 s)
    (h23 : u.getReg .x23 = BitVec.ofNat 64 (0x760 + 8 * st.stack.length))
    (h24 : u.getReg .x24 = BitVec.ofNat 64 (2 ^ 14))
    (h29 : u.getReg .x29 = BitVec.ofNat 64 (0x3400 + 16 * st.reads.length))
    (h30 : u.getReg .x30 = BitVec.ofNat 64 (0x910 + (segStream sig st.segs).length))
    (h31 : u.getReg .x31 = BitVec.ofNat 64 (0x910 + (segStream sig st.segs).length + 8))
    (hstk : StackOK u st.stack) (hstkb : ∀ q ∈ st.stack, q < 2 ^ 15) (hslen : st.stack.length ≤ s + 1)
    (hstr : StreamOK u (curStream sig st.segs 0)) (hns : nsum st.segs = st.reads.length)
    (hfr : Frame t0 u SW) :
    Run u 3 (LM A sig t0 (s + 1) st) := by
  refine Run.of (symRun_sound blk129 codeAt_129 u hpc (by simp only [blk129.res, rv_simp])) (le_refl _) ?_
  set v := blk129.res.toState u with hv
  have r : RegsEq u v [.x8, .x17] := by regs_eq
  have m : ∀ a, v.getMem a = u.getMem a := toState_getMem_nil rfl u
  refine ⟨?_, ?_, by rw [r.get .x23 (by simp), h23], by rw [r.get .x24 (by simp), h24],
    by rw [r.get .x29 (by simp), h29], by rw [r.get .x30 (by simp), h30], by rw [r.get .x31 (by simp), h31],
    ⟨by rw [m]; exact hstk.1, fun i hi => by rw [m]; exact hstk.2 i hi⟩, hstkb, hslen,
    fun i hi => by rw [getByte_ofNat _ _ (by omega), m, ← getByte_ofNat _ _ (by omega)]; exact hstr i hi,
    hns, by omega, frame_of_writes hfr (fun y hy _ => m _)⟩
  · simp only [hv, blk129.res, rv_simp, h8]; ex_bvsimp [ofNat_bne_ofNat]
    by_cases h : s + 1 < 15 <;> simp [h] <;> omega
  · simp only [hv, blk129.res, rv_simp, h8]; ex_bvsimp []

/-- The end of leaf `s`: its last segment, then the push (unless `s` is the last leaf). -/
def leafEnd (s : Nat) (x : SchedState × Nat × Nat × Nat) : SchedState :=
  let st := { x.1 with segs := x.1.segs ++ [x.2.2.1 ||| 32 * x.2.2.2] }
  if s + 1 < 15 then { st with stack := (x.2.1 ^^^ 1) :: st.stack } else st

theorem leaf_end (A : Nat → Nat) (sig : List Byte) (t0 : MachineState) (hc : SchCtx A sig t0)
    (s : Nat) (x : SchedState × Nat × Nat × Nat) (u : MachineState) (hm : HM A sig t0 s (topM A s) x u)
    (hr : x.1.reads.length ≤ 120) (hg : x.1.segs.length + 1 ≤ 29) :
    Run u 14 (LM A sig t0 (s + 1) (leafEnd s x)) := by
  obtain ⟨st, E, cnt, t⟩ := x
  obtain ⟨hpc, h8, h9, h20, h19, h18, h15, h21, h23, h24, h29, h30, h31, hstk, hstkb, hslen, hstr,
    hns, hE, hcnt, htt, hs, htp, hfr⟩ := hm
  dsimp only at h18 h15 h21 h23 h29 h30 h31 hstk hstkb hslen hstr hns hE hcnt htt hr hg ⊢
  have htop14 := topM_le A hc.lt s
  refine (Run.blk blk95 codeAt_95 hpc (by simp only [blk95.res, rv_simp]) (B := 13) ?_).mono
    (by rw [show blk95.res.cycles = 1 from rfl]) (fun _ h => h)
  set u1 := blk95.res.toState u with hu1
  have p1 : u1.pc = pcOf 119 := by
    simp only [hu1, blk95.res, rv_simp, h19, h20]
    rw [ofNat_slt_ofNat _ _ (by omega) (by omega)]; simp
  have r1 : RegsEq u u1 [] := by regs_eq
  have m1 : ∀ a, u1.getMem a = u.getMem a := toState_getMem_nil rfl u
  have hnsr : nsum st.segs ≤ 120 := by omega
  have hL := length_segStream sig hc.siglen st.segs hnsr
  have hc16 : cnt < 16 := by omega
  set b := cnt ||| 32 * t with hbdef
  have hbv : b = cnt + 32 * t := segByte_end cnt t hc16 htt
  have hb16 : b % 16 = cnt := by omega
  have hEpos : 0 < E := by rw [hE]; exact anc_pos (lv_lt hc.lt hs) (by unfold porsH; omega)
  have hElt : E < 2 ^ 15 := by
    rw [hE]; have := (anc_bounds (lv_lt hc.lt hs) (g := topM A s) (by unfold porsH; omega)).2
    exact lt_of_lt_of_le this (Nat.pow_le_pow_right (by norm_num) (by unfold porsH; omega))
  have hobl2 : blk119.res.obligs u1 := by
    simp only [blk119.res, rv_simp, r1.get .x30 (by simp), h30]; ex_bvsimp [accessValid_ofNat]; omega
  refine (Run.blk blk119 codeAt_119 p1 hobl2 (B := 6) ?_).mono
    (by rw [show blk119.res.cycles = 7 by kernel_rfl]) (fun _ h => h)
  set u2 := blk119.res.toState u1 with hu2
  have r2 : RegsEq u u2 [.x17, .x25, .x30, .x31] := by
    have : RegsEq u1 u2 [.x17, .x25, .x30, .x31] := by regs_eq
    exact (r1.trans this).mono (fun r hr => by simpa using hr)
  have hwb : (u1.getReg .x15 <<< ((5#64 : Word).toNat % 64) ||| u1.getReg .x21).truncate 8 = byte b := by
    rw [show ((5#64 : Word).toNat % 64) = 5 from rfl, r1.get .x15 (by simp), r1.get .x21 (by simp), h15, h21,
      ofNat_shiftLeft, ofNat_or_ofNat _ _ (by omega) (by omega), truncate8_ofNat]
    unfold byte; congr 1
    rw [hbdef]
    interval_cases t <;> interval_cases cnt <;> rfl
  have hm2 : ∀ y : Nat, y < 2 ^ 64 → u2.getMem (BitVec.ofNat 64 y) =
      if y = 0x910 + (segStream sig st.segs).length then
        replaceByte (u.getMem (BitVec.ofNat 64 y)) 0 (byte b) else u.getMem (BitVec.ofNat 64 y) := by
    intro y hy
    rw [hu2, toState_getMem_one rfl]
    simp only [Addr.eval, Rv.E.eval, BinOp.eval, StoreKind.merge, BitVec.add_zero]
    rw [hwb, r1.get .x30 (by simp), h30, m1]
    by_cases hy' : y = 0x910 + (segStream sig st.segs).length
    · subst hy'; simp
    · rw [if_neg hy', if_neg (by rw [ofNat_eq_iff]; omega), m1]
  have p2 : u2.pc = if s = 14 then pcOf 129 else pcOf 126 := by
    simp only [hu2, blk119.res, rv_simp, r1.get .x8 (by simp), h8]; ex_bvsimp [ofNat_beq_ofNat]
    by_cases h : s = 14 <;> simp [h]
  have hL' := length_segStream sig hc.siglen (st.segs ++ [b]) (by rw [nsum_snoc]; omega)
  rw [nsum_snoc, hb16] at hL'
  simp only [List.length_append, List.length_singleton] at hL'
  have m2x : ∀ y : Nat, y < 2 ^ 64 → y ≠ 0x910 + (segStream sig st.segs).length →
      u2.getMem (BitVec.ofNat 64 y) = u.getMem (BitVec.ofNat 64 y) := fun y hy hne => by rw [hm2 y hy, if_neg hne]
  have s30 : u2.getReg .x30 = BitVec.ofNat 64 (0x910 + (segStream sig (st.segs ++ [b])).length) := by
    simp only [hu2, blk119.res, rv_simp, r1.get .x31 (by simp), h31]; exact ofNat_congr (by omega)
  have s31 : u2.getReg .x31 = BitVec.ofNat 64 (0x910 + (segStream sig (st.segs ++ [b])).length + 8) := by
    simp only [hu2, blk119.res, rv_simp, r1.get .x31 (by simp), h31]; ex_bvsimp []; exact ofNat_congr (by omega)
  have sstr : StreamOK u2 (curStream sig (st.segs ++ [b]) 0) :=
    stream_sb (P := (segStream sig st.segs).length) (by rw [hL]; omega) (by omega) hstr hm2
      (fun i => curStream_emit sig st.segs b cnt hb16 i)
  have sns : nsum (st.segs ++ [b]) = st.reads.length := by rw [nsum_snoc, hb16]; exact hns
  have sfr : Frame t0 u2 SW := frame_of_writes hfr (fun y hy hW => m2x y hy (by unfold SW at hW; omega))
  unfold leafEnd
  dsimp only
  by_cases hs14 : s = 14
  · rw [if_pos hs14] at p2
    rw [if_neg (by omega)]
    refine (leaf_close A sig t0 s hs { segs := st.segs ++ [b], reads := st.reads, stack := st.stack } u2 p2 (by rw [r2.get .x8 (by simp), h8])
      (by rw [r2.get .x23 (by simp), h23]) (by rw [r2.get .x24 (by simp), h24])
      (by rw [r2.get .x29 (by simp), h29]) s30 s31
      ⟨by rw [m2x _ (by omega) (by omega)]; exact hstk.1, fun i hi => by
        dsimp only at hi ⊢; rw [m2x _ (by omega) (by omega)]; exact hstk.2 i hi⟩ hstkb (by dsimp only; omega)
        sstr sns sfr).mono
      (by omega) (fun _ h => h)
  · rw [if_neg hs14] at p2
    rw [if_pos (by omega)]
    have hobl3 : blk126.res.obligs u2 := by
      simp only [blk126.res, rv_simp, r2.get .x23 (by simp), h23]; ex_bvsimp [accessValid_ofNat]; omega
    refine (Run.blk blk126 codeAt_126 p2 hobl3 (B := 3) ?_).mono
      (by rw [show blk126.res.cycles = 3 by kernel_rfl]) (fun _ h => h)
    set u3 := blk126.res.toState u2 with hu3
    have r3 : RegsEq u2 u3 [.x3, .x23] := by regs_eq
    have hm3 : ∀ y : Nat, y < 2 ^ 64 → u3.getMem (BitVec.ofNat 64 y) =
        if y = 0x760 + 8 * (st.stack.length + 1) then BitVec.ofNat 64 (E ^^^ 1) else u2.getMem (BitVec.ofNat 64 y) := by
      intro y hy
      rw [hu3, toState_getMem_one rfl]
      simp only [Addr.eval, Rv.E.eval, BinOp.eval, Option.map, r2.get .x23 (by simp), h23,
        r2.get .x18 (by simp), h18]
      rw [show (8#64 : Word) = BitVec.ofNat 64 8 from rfl, ofNat_add_ofNat,
        show (1#64 : Word) = BitVec.ofNat 64 1 from rfl, ofNat_xor_ofNat _ _ (by omega) (by omega)]
      by_cases hy' : y = 0x760 + 8 * (st.stack.length + 1)
      · rw [if_pos (ofNat_congr (by omega)), if_pos hy']
      · rw [if_neg (by rw [ofNat_eq_iff]; omega), if_neg hy']
    have hxor : E ^^^ 1 < 2 ^ 15 := Nat.xor_lt_two_pow hElt (by norm_num)
    refine leaf_close A sig t0 s hs { segs := st.segs ++ [b], reads := st.reads, stack := (E ^^^ 1) :: st.stack } u3 (by simp only [hu3, blk126.res, rv_simp])
      (by rw [r3.get .x8 (by simp), r2.get .x8 (by simp), h8]) ?_
      (by rw [r3.get .x24 (by simp), r2.get .x24 (by simp), h24])
      (by rw [r3.get .x29 (by simp), r2.get .x29 (by simp), h29])
      (by rw [r3.get .x30 (by simp), s30]) (by rw [r3.get .x31 (by simp), s31]) ?_ ?_ (by simp; omega) ?_ sns ?_
    · simp only [hu3, blk126.res, rv_simp, r2.get .x23 (by simp), h23]; ex_bvsimp []
      simp only [List.length_cons]; exact ofNat_congr (by ring)
    · refine ⟨by rw [hm3 _ (by omega), if_neg (by omega), m2x _ (by omega) (by omega)]; exact hstk.1, ?_⟩
      intro i hi
      simp only [List.length_cons] at hi ⊢
      rw [hm3 _ (by omega)]
      by_cases hi0 : i = 0
      · subst hi0; rw [if_pos (by omega)]; rfl
      · rw [if_neg (by omega), m2x _ (by omega) (by omega)]
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [List.getD_cons_succ, ← hstk.2 j (by omega)]; congr 3; omega
    · intro q hq; rcases List.mem_cons.mp hq with rfl | hq
      · exact hxor
      · exact hstkb q hq
    · intro i hi
      rw [getByte_ofNat _ _ (by omega), hm3 _ (by omega), if_neg (by omega), ← getByte_ofNat _ _ (by omega)]
      exact sstr i hi
    · exact frame_of_writes sfr (fun y hy hW => by rw [hm3 y hy, if_neg (by unfold SW at hW; omega)])



theorem sch_inner (A : Nat → Nat) (sig : List Byte) (t0 : MachineState) (hc : SchCtx A sig t0) (s : Nat) :
    ∀ n h (x : SchedState × Nat × Nat × Nat) (u : MachineState), h + n = topM A s → HM A sig t0 s h x u →
      ((List.range' h n).foldl schedStep x).1.reads.length ≤ 120 →
      ((List.range' h n).foldl schedStep x).1.segs.length + 1 ≤ 29 →
      Run u (16 * n) (HM A sig t0 s (h + n) ((List.range' h n).foldl schedStep x)) := by
  intro n
  induction n with
  | zero => intro h x u _ hm _ _; simpa using Run.done hm
  | succ n ih =>
    intro h x u hn hm hr hg
    rw [List.range'_succ, List.foldl_cons] at hr hg ⊢
    have hmo := fold_mono (List.range' (h + 1) n) (schedStep x h)
    have := Run.bind (sch_step A sig t0 hc s h x u hm (by omega) (by omega) (by omega))
      (fun v hv => ih (h + 1) (schedStep x h) v (by omega) hv hr hg)
    refine this.mono (by ring_nf; omega) (fun v hv => by rwa [show h + 1 + n = h + (n + 1) by ring] at hv)

/-- The sorted leaf values. -/
def vsOf (A : Nat → Nat) : List Nat := (List.range 15).map (lv A)

theorem vsOf_getD (A : Nat → Nat) (s : Nat) (hs : s < 15) : (vsOf A).getD s 0 = lv A s := by
  simp [vsOf, List.getD_eq_getElem?_getD, hs]

theorem schedLeaf_eq (A : Nat → Nat) (st : SchedState) (s : Nat) (hs : s < 15) :
    schedLeaf (vsOf A) st s =
      leafEnd s ((List.range (topM A s)).foldl schedStep (st, porsT ||| lv A s, 0, (porsT ||| lv A s) % 2)) := by
  have hlen : (vsOf A).length = 15 := by simp [vsOf]
  have htop : (if s + 1 < (vsOf A).length then bitLen ((vsOf A).getD s 0 ^^^ (vsOf A).getD (s + 1) 0) - 1
      else porsH) = topM A s := by
    unfold topM; rw [hlen]; split
    · rw [vsOf_getD A s hs, vsOf_getD A (s + 1) (by omega)]
    · rfl
  unfold schedLeaf
  simp only [hlen]
  rw [vsOf_getD A s hs]
  rw [show (if s + 1 < 15 then bitLen (lv A s ^^^ (vsOf A).getD (s + 1) 0) - 1 else porsH) = topM A s by
    rw [← htop, hlen, vsOf_getD A s hs]]
  generalize (List.range (topM A s)).foldl schedStep (st, porsT ||| lv A s, 0, (porsT ||| lv A s) % 2) = y
  obtain ⟨a, b, c, d⟩ := y
  rfl

theorem leaf_mono (vs : List Nat) (st : SchedState) (s : Nat) :
    st.reads.length ≤ (schedLeaf vs st s).reads.length ∧ st.segs.length < (schedLeaf vs st s).segs.length := by
  unfold schedLeaf
  dsimp only
  generalize hy : (List.range _).foldl schedStep (st, porsT ||| vs.getD s 0, 0, (porsT ||| vs.getD s 0) % 2) = y
  have := fold_mono (List.range (if s + 1 < vs.length then bitLen (vs.getD s 0 ^^^ vs.getD (s + 1) 0) - 1
    else porsH)) (st, porsT ||| vs.getD s 0, 0, (porsT ||| vs.getD s 0) % 2)
  rw [hy] at this
  obtain ⟨a, b, c, d⟩ := y
  dsimp only at this ⊢
  split <;> simp <;> omega

/-- One leaf. -/
theorem sch_leaf (A : Nat → Nat) (sig : List Byte) (t0 : MachineState) (hc : SchCtx A sig t0)
    (hd : ∀ s < 14, lv A s ≠ lv A (s + 1)) (s : Nat) (hs : s < 15) (st : SchedState) (u : MachineState)
    (hl : LM A sig t0 s st u) (hr : (schedLeaf (vsOf A) st s).reads.length ≤ 120)
    (hg : (schedLeaf (vsOf A) st s).segs.length ≤ 29) :
    Run u (56 + 16 * 14 + 14) (LM A sig t0 (s + 1) (schedLeaf (vsOf A) st s)) := by
  rw [schedLeaf_eq A st s hs] at hr hg ⊢
  have htop := topM_le A hc.lt s
  set x0 : SchedState × Nat × Nat × Nat := (st, porsT ||| lv A s, 0, (porsT ||| lv A s) % 2)
  have hF : (List.range (topM A s)).foldl schedStep x0 = (List.range' 0 (topM A s)).foldl schedStep x0 := by
    rw [List.range_eq_range']
  have hr' : ((List.range (topM A s)).foldl schedStep x0).1.reads.length ≤ 120 := by
    unfold leafEnd at hr; split at hr <;> simpa using hr
  have hg' : ((List.range (topM A s)).foldl schedStep x0).1.segs.length + 1 ≤ 29 := by
    unfold leafEnd at hg; split at hg <;> simpa using hg
  rw [hF] at hr' hg' ⊢
  refine (Run.bind (leaf_start A sig t0 hc hd s hs st u hl) (fun v hv => Run.bind
    (sch_inner A sig t0 hc s (topM A s) 0 x0 v (by omega) hv hr' hg') (fun w hw =>
      leaf_end A sig t0 hc s _ w (by simpa using hw) hr' hg'))).mono (by omega) (fun _ h => h)



theorem leaves_mono (vs : List Nat) (L : List Nat) : ∀ st : SchedState,
    st.reads.length ≤ (L.foldl (schedLeaf vs) st).reads.length ∧
      st.segs.length ≤ (L.foldl (schedLeaf vs) st).segs.length := by
  induction L with
  | nil => intro st; simp
  | cons s L ih =>
    intro st; rw [List.foldl_cons]
    have h1 := leaf_mono vs st s; have h2 := ih (schedLeaf vs st s); omega

theorem sch_leaves (A : Nat → Nat) (sig : List Byte) (t0 : MachineState) (hc : SchCtx A sig t0)
    (hd : ∀ s < 14, lv A s ≠ lv A (s + 1)) :
    ∀ k s (st : SchedState) (u : MachineState), s + k = 15 → LM A sig t0 s st u →
      ((List.range' s k).foldl (schedLeaf (vsOf A)) st).reads.length ≤ 120 →
      ((List.range' s k).foldl (schedLeaf (vsOf A)) st).segs.length ≤ 29 →
      Run u (k * 294) (LM A sig t0 15 ((List.range' s k).foldl (schedLeaf (vsOf A)) st)) := by
  intro k
  induction k with
  | zero => intro s st u hk hl _ _; rw [show s = 15 by omega] at hl; simpa using Run.done hl
  | succ k ih =>
    intro s st u hk hl hr hg
    rw [List.range'_succ, List.foldl_cons] at hr hg ⊢
    have hmo := leaves_mono (vsOf A) (List.range' (s + 1) k) (schedLeaf (vsOf A) st s)
    have := Run.bind (sch_leaf A sig t0 hc hd s (by omega) st u hl (by omega) (by omega))
      (fun v hv => ih (s + 1) _ v (by omega) hv hr hg)
    exact this.mono (by ring_nf; omega) (fun _ h => h)

/-- The whole schedule loop (instructions 72 .. 131) from its start. -/
theorem sch_run (A : Nat → Nat) (sig : List Byte) (t0 : MachineState) (hc : SchCtx A sig t0)
    (hd : ∀ s < 14, lv A s ≠ lv A (s + 1)) (hpc : t0.pc = pcOf 72)
    (hz : ∀ i < 2152, t0.getByte (BitVec.ofNat 64 (0x910 + i)) = 0)
    (hr : (schedule (vsOf A)).2.length ≤ 120) (hg : (schedule (vsOf A)).1.length ≤ 29) :
    Run t0 (9 + 15 * 294) (LM A sig t0 15 ((List.range 15).foldl (schedLeaf (vsOf A)) ⟨[], [], []⟩)) := by
  refine Run.blk blk72 codeAt_72 hpc (by simp only [blk72.res, rv_simp]) ?_
  set u := blk72.res.toState t0 with hu
  have hm : ∀ y : Nat, y < 2 ^ 64 → u.getMem (BitVec.ofNat 64 y) =
      if y = 0x760 then 0 else t0.getMem (BitVec.ofNat 64 y) := by
    intro y hy
    rw [hu, toState_getMem_one rfl]
    simp only [Addr.eval, Rv.E.eval]
    by_cases h : y = 0x760
    · subst h; simp
    · rw [if_neg h]
      exact if_neg (fun hh => h (by rw [show (1888#64 : Word) = BitVec.ofNat 64 1888 from rfl, ofNat_eq_iff] at hh; omega))
  have hlen : (vsOf A).length = 15 := by simp [vsOf]
  have hsch : schedule (vsOf A) = (((List.range 15).foldl (schedLeaf (vsOf A)) ⟨[], [], []⟩).segs,
      ((List.range 15).foldl (schedLeaf (vsOf A)) ⟨[], [], []⟩).reads) := by
    unfold schedule; rw [hlen]
  rw [hsch] at hr hg
  simp only at hr hg
  have h0 : LM A sig t0 0 ⟨[], [], []⟩ u := by
    refine ⟨by simp only [hu, blk72.res, rv_simp] <;> rfl, by simp only [hu, blk72.res, rv_simp] <;> rfl,
      by simp only [hu, blk72.res, rv_simp] <;> rfl, by simp only [hu, blk72.res, rv_simp] <;> rfl,
      by simp only [hu, blk72.res, rv_simp] <;> rfl, by simp only [hu, blk72.res, rv_simp] <;> rfl,
      by simp only [hu, blk72.res, rv_simp] <;> rfl, ⟨by rw [hm _ (by omega), if_pos rfl], fun i hi => by simp at hi⟩,
      by simp, by simp, ?_, by simp [nsum], by omega, ?_⟩
    · intro i hi
      rw [getByte_ofNat _ _ (by omega), hm _ (by omega), if_neg (by omega), ← getByte_ofNat _ _ (by omega), hz i hi]
      simp only [curStream, segStream, List.foldl_nil, items, List.range_zero, List.map_nil,
        List.flatten_nil, List.append_nil, List.nil_append]
      rw [getD_zeros]
    · exact frame_of_writes (Frame.refl t0 SW) (fun y hy hW => by rw [hm y hy, if_neg (by unfold SW at hW; omega)])
  have := sch_leaves A sig t0 hc hd 15 0 ⟨[], [], []⟩ u (by omega) h0 (by rw [← List.range_eq_range']; exact hr)
    (by rw [← List.range_eq_range']; exact hg)
  rw [← List.range_eq_range'] at this
  exact this.mono (le_refl _) (fun _ h => h)


end SigGolfCandidate.Expand
