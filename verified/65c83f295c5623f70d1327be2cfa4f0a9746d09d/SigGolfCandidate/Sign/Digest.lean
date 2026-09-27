import SigGolfCandidate.Sign.Blocks
import SigGolfCandidate.Sign.Inv

/-!
# `sign`, phase 1: the digest search (`dig_loop`, instructions 27 .. 45)

`digLoop_sim` : from `dig_loop` with counter `a`, the machine refines `searchDigest S m a (2^20 - a)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Facts about the buffers used by the digest search (at the start of the loop). -/
structure DigMem (S mm : List Byte) (u : MachineState) : Prop where
  rbS : u.readWords (BitVec.ofNat 64 0x640) 4 = wordsOf S
  rbM : u.readWords (BitVec.ofNat 64 0x660) 4 = wordsOf mm
  rbZ : u.readWords (BitVec.ofNat 64 0x680) 4 = [0, 0, 0, 0]
  rbP : u.readWords (BitVec.ofNat 64 0x628) 3 = [0, 0, 0]
  rb0 : lo32 (u.getMem (BitVec.ofNat 64 0x620)) = BitVec.ofNat 32 0x701
  db0 : u.readWords (BitVec.ofNat 64 0) 4 = [twWord0 12 0 0 0, 0, 0, 0]
  dbM : u.readWords (BitVec.ofNat 64 0x40) 4 = wordsOf mm
  dbZ : u.readWords (BitVec.ofNat 64 0x60) 4 = [0, 0, 0, 0]

/-- Addresses written by the digest search. -/
def digW (a : Nat) : Prop := a = 0x620 ∨ (0x20 ≤ a ∧ a < 0x40) ∨ (0x160 ≤ a ∧ a < 0x180)

def digRegs : List Reg := [.x3, .x6, .x10, .x11, .x12]

/-- Loop invariant at `dig_loop` with counter `a`. -/
def DigInv (u : MachineState) (a : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf 27 ∧ t.getReg .x6 = BitVec.ofNat 64 a ∧ a < 2 ^ 20 ∧ RegsEq u t digRegs ∧
    Frame u t digW ∧ lo32 (t.getMem (BitVec.ofNat 64 0x620)) = lo32 (u.getMem (BitVec.ofNat 64 0x620))

/-- Result of the digest search. -/
def DigPost (u : MachineState) : Option (Val × Nat) → MachineState → Prop
  | none, t => t.pc = pcOf 45 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1
  | some (rho, N), t => t.pc = pcOf 46 ∧ RegsEq u t digRegs ∧ Frame u t digW ∧
      rho.length = 16 ∧ t.readWords (BitVec.ofNat 64 0x20) 2 = wordsOf rho ∧
      (∃ ans : BitVec 256, N = ans.toNat % 2 ^ 184 ∧
        t.readWords (BitVec.ofNat 64 0x160) 3 =
          [ans.extractLsb' 0 64, ans.extractLsb' 64 64, ans.extractLsb' 128 64]) ∧
      uOf N 14 = 0

theorem admissible_iff (ans : BitVec 256) :
    (ans.extractLsb' 128 64 <<< 8 >>> 54 = BitVec.ofNat 64 0) ↔ uOf (ans.toNat % 2 ^ 184) 14 = 0 := by
  rw [← BitVec.toNat_inj]
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, BitVec.toNat_ofNat, uOf, totalH, ftsA,
    BitVec.toNat_zero, Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceMod]
  have := ans.isLt
  constructor <;> intro h <;> omega

theorem pcOf_eq (i : Nat) (h : 0x1000 + 4 * i < 2 ^ 64) (w : Word) (hw : w.toNat = 0x1000 + 4 * i) :
    w = pcOf i := by
  apply BitVec.eq_of_toNat_eq; rw [hw]; simp; omega

theorem pcOf_add4 (i : Nat) : pcOf i + 4 = pcOf (i + 1) := by
  apply BitVec.eq_of_toNat_eq; simp; omega

/-- One trial: from `dig_loop` (counter `a`) the rnd hash, the digest hash, and the test;
`rest` is what follows a non-admissible trial (from instruction 41). -/
theorem digTrial (sk : SecretKey) (m : Message) (u : MachineState)
    (hmem : DigMem (toList sk) (toList m) u) (hx5 : u.getReg .x5 = 0) (a : Nat) (t : MachineState)
    (hinv : DigInv u a t) (rest : OracleComp HashSpec (Option (Val × Nat))) (Wr : Nat)
    (hrest : ∀ t', t'.pc = pcOf 41 → t'.getReg .x6 = BitVec.ofNat 64 a → RegsEq u t' digRegs →
      Frame u t' digW → lo32 (t'.getMem (BitVec.ofNat 64 0x620)) = lo32 (u.getMem (BitVec.ofNat 64 0x620)) →
      Sim image t' Wr rest (DigPost u)) :
    Sim image t (44 + Wr) (hash16 (rndInput (toList sk) (toList m) a) >>= fun rho =>
      (liftM (HashSpec.query (pad64 (digestInput rho (toList m)))) : OracleComp HashSpec _) >>= fun ans =>
        if admissible (ans.toNat % 2 ^ 184) then pure (some (rho, ans.toNat % 2 ^ 184)) else rest)
      (DigPost u) := by
  have hS : (toList sk).length = 32 := length_toList sk
  have hm : (toList m).length = 32 := length_toList m
  obtain ⟨tpc, t6, ha, tregs, tframe, tlo⟩ := hinv
  -- block 27
  have hs1 := symRun_sound blk27 codeAt_27 t tpc (by simp only [blk27.res, rv_simp])
  set t1 := blk27.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x620) := by
    apply frame_toState; intro x hx hW
    simp only [blk27.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x11, .x12] := by
    intro r hr; simp only [ht1, Result.toState_getReg]
    cases r <;> simp_all [blk27.res, rv_simp] <;> rfl
  have e1 : fetch image t1 = some (.base .ECALL) := symRun_ecall blk27 codeAt_27 t (by simp only [blk27.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x620 := by simp only [ht1, blk27.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 128 := by simp only [ht1, blk27.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x20 := by simp only [ht1, blk27.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tregs.get .x5, hx5]
  have pc1 : t1.pc = pcOf 31 := by simp only [ht1, blk27.res, rv_simp]
  have m620 : t1.getMem (BitVec.ofNat 64 0x620) = twWord0 7 0 0 a := by
    rvs [ht1, blk27.res, t6]
    refine (word_of_halves _ 0x701 a (by rw [lo32_replace1, tlo, hmem.rb0]) (by rw [hi32_replace1])).trans ?_
    unfold twWord0; congr 1
  have hq1 : hashInput t1 = pad64 (rndInput (toList sk) (toList m) a) := by
    obtain ⟨hn, hw⟩ := words_rndInput _ _ hS hm a
    refine hashInput_eq_pad64 t1 _ 1 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (1 + 1) = 1 + 3 + 4 + 4 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, m620]
    rw [f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega),
      hmem.rbP, hmem.rbS, hmem.rbM, hmem.rbZ]
    simp [twWords_eq]
  have hc1 : blk27.res.cycles = 4 := rfl
  rw [hc1] at hs1
  have hb1 : (pad64 (rndInput (toList sk) (toList m) a)).blocks = 2 := by
    simp [pad64, Query.blocks, (words_rndInput _ _ hS hm a).1]
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 4 + (16 + (4 + Wr))) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq1 (fun ans1 => ?_))).mono (by rw [hb1]; omega) (fun _ _ h => h)
  -- after the rnd hash
  set rho := answerBytes 16 ans1 with hrho
  set t2 := writeHash t1 ans1 with ht2
  have f2 : Frame t1 t2 (fun x => 0x20 ≤ x ∧ x < 0x20 + 32) := frame_writeHash t1 ans1 0x20 x12 (by norm_num)
  have v2 : t2.readWords (BitVec.ofNat 64 0x20) 2 = wordsOf rho := writeHash_readWords_val t1 ans1 0x20 x12 (by norm_num)
  have pc2 : t2.pc = pcOf 32 := by rw [ht2, writeHash_pc, pc1, pcOf_add4]
  have hs2 := symRun_sound blk32 codeAt_32 t2 pc2 (by simp only [blk32.res, rv_simp])
  set t3 := blk32.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun x => x = 0x30 ∨ x = 0x38) := by
    apply frame_toState; intro x hx hW
    simp only [blk32.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t2 t3 [.x10, .x12] := by
    intro r hr; simp only [ht3, Result.toState_getReg]
    cases r <;> simp_all [blk32.res, rv_simp]
  have e3 : fetch image t3 = some (.base .ECALL) := symRun_ecall blk32 codeAt_32 t2 (by simp only [blk32.res, rv_simp]) rfl
  have y10 : t3.getReg .x10 = BitVec.ofNat 64 0 := by simp only [ht3, blk32.res, rv_simp]
  have y11 : t3.getReg .x11 = BitVec.ofNat 64 128 := by rw [r3.get .x11, ht2, writeHash_getReg, x11]
  have y12 : t3.getReg .x12 = BitVec.ofNat 64 0x160 := by simp only [ht3, blk32.res, rv_simp]
  have y5 : t3.getReg .x5 = 0 := by rw [r3.get .x5, ht2, writeHash_getReg, x5]
  have pc3 : t3.pc = pcOf 36 := by simp only [ht3, blk32.res, rv_simp]
  have z3 : t3.readWords (BitVec.ofNat 64 0x30) 2 = [0, 0] := by
    rw [readWords_ofNat_two]; simp only [ht3, blk32.res, rv_simp]; rfl
  -- frame from u to t3 outside digW
  have fu3 : Frame u t3 digW := (((tframe.trans f1).trans f2).trans f3).mono (by
    intro x hx; simp only [digW, false_or, or_false] at hx ⊢; omega)
  have hlen : rho.length = 16 := by simp [hrho]
  have hq2 : hashInput t3 = pad64 (digestInput rho (toList m)) := by
    obtain ⟨hn, hw⟩ := words_digestInput _ _ hlen hm
    refine hashInput_eq_pad64 t3 _ 1 hn (by rw [y11]) (by norm_num) (by rw [y10]; decide) ?_
    rw [hw, y10, show 8 * (1 + 1) = 4 + 2 + 2 + 4 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [fu3.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega), hmem.db0,
      f3.readWords _ _ (by norm_num) (by intro i hi; omega), v2, z3,
      fu3.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega), hmem.dbM,
      fu3.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega), hmem.dbZ]
    simp [twWords_eq, twWord0]
  have hc2 : blk32.res.cycles = 4 := rfl
  rw [hc2] at hs2
  have hb2 : (pad64 (digestInput rho (toList m))).blocks = 2 := by
    simp [pad64, Query.blocks, (words_digestInput _ _ hlen hm).1]
  refine (Sim.steps hs2 (Sim.query_bind (W := 4 + Wr) e3 y5
    (hashArgs_of y10 y11 y12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq2 (fun ans2 => ?_))).mono (by rw [hb2]) (fun _ _ h => h)
  -- after the digest hash
  set t4 := writeHash t3 ans2 with ht4
  have f4 : Frame t3 t4 (fun x => 0x160 ≤ x ∧ x < 0x160 + 32) :=
    frame_writeHash t3 ans2 0x160 y12 (by norm_num)
  have pc4 : t4.pc = pcOf 37 := by rw [ht4, writeHash_pc, pc3, pcOf_add4]
  have w4 : ∀ k, k < 3 → t4.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = ans2.extractLsb' (64 * k) 64 := by
    intro k hk
    rw [ht4, writeHash_getMem_ofNat t3 ans2 0x160 _ y12 (by norm_num) (by omega)]
    interval_cases k <;> simp
  have hs3 := symRun_sound blk37 codeAt_37 t4 pc4 (by simp only [blk37.res, rv_simp])
  have hc3 : blk37.res.cycles = 4 := rfl
  rw [hc3] at hs3
  set t5 := blk37.res.toState t4 with ht5
  have f5 : Frame t4 t5 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk37.res]
  have r5 : RegsEq t4 t5 [.x3] := by
    intro r hr; simp only [ht5, Result.toState_getReg]
    cases r <;> simp_all [blk37.res, rv_simp]
  have fu5 : Frame u t5 digW := ((fu3.trans f4).trans f5).mono (by
    intro x hx; simp only [digW, false_or, or_false] at hx ⊢; omega)
  have ru5 : RegsEq u t5 digRegs := (((((tregs.trans r1).trans (regsEq_writeHash _ _ [])).trans r3).trans
    (regsEq_writeHash _ _ [])).trans r5).mono (by decide)
  have pc5 : t5.pc = if admissible (ans2.toNat % 2 ^ 184) then pcOf 46 else pcOf 41 := by
    have h368 := w4 2 (by norm_num)
    simp only [Nat.reduceMul, Nat.reduceAdd] at h368
    simp only [ht5, blk37.res, rv_simp, h368]
    simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, admissible, beq_iff_eq]
    by_cases h : uOf (ans2.toNat % 2 ^ 184) 14 = 0
    · rw [if_pos ((admissible_iff ans2).mpr h), if_pos (by simpa using h)]
    · rw [if_neg (mt (admissible_iff ans2).mp h), if_neg (by simpa using h)]
  by_cases hadm : admissible (ans2.toNat % 2 ^ 184) = true
  · rw [if_pos hadm]
    refine (Sim.pure_steps hs3 ?_).mono (by omega) (fun _ _ h => h)
    refine ⟨by rw [pc5, if_pos hadm], ru5, fu5, hlen, ?_, ⟨ans2, rfl, ?_⟩, ?_⟩
    · rw [f5.readWords _ _ (by norm_num) (by simp), f4.readWords _ _ (by norm_num) (by intro i hi; omega),
        f3.readWords _ _ (by norm_num) (by intro i hi; omega), v2]
    · rw [f5.readWords _ _ (by norm_num) (by simp)]
      simp only [readWords_ofNat_succ, MachineState.readWords]
      have := w4 0 (by norm_num); have := w4 1 (by norm_num); have := w4 2 (by norm_num)
      simp_all
    · simpa [admissible] using hadm
  · rw [if_neg hadm]
    refine Sim.steps hs3 (hrest t5 (by rw [pc5, if_neg hadm]) ?_ ru5 fu5 ?_)
    · rw [r5.get .x6, ht4, writeHash_getReg, r3.get .x6, ht2, writeHash_getReg, r1.get .x6, t6]
    · rw [f5.getMem (by norm_num) (by simp), f4.getMem (by norm_num) (by omega),
        f3.getMem (by norm_num) (by omega), f2.getMem (by norm_num) (by omega)]
      simp only [ht1, blk27.res, rv_simp, ite_true, lo32_replace1, Nat.reduceDiv]
      exact tlo

theorem searchDigest_succ (S mm : List Byte) (a f : Nat) :
    searchDigest S mm a (f + 1) = (hash16 (rndInput S mm a) >>= fun rho =>
      (liftM (HashSpec.query (pad64 (digestInput rho mm))) : OracleComp HashSpec _) >>= fun ans =>
        if admissible (ans.toNat % 2 ^ 184) then pure (some (rho, ans.toNat % 2 ^ 184))
        else searchDigest S mm (a + 1) f) := by
  simp only [searchDigest, digest, H, bind_assoc, pure_bind]

/-- After a non-admissible trial (instruction 41): `a += 1`, back to the loop or fail. -/
theorem digNext (u : MachineState) (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20)) (a : Nat)
    (ha : a < 2 ^ 20) (t : MachineState) (tpc : t.pc = pcOf 41) (t6 : t.getReg .x6 = BitVec.ofNat 64 a)
    (tregs : RegsEq u t digRegs) (tframe : Frame u t digW)
    (tlo : lo32 (t.getMem (BitVec.ofNat 64 0x620)) = lo32 (u.getMem (BitVec.ofNat 64 0x620))) :
    ∃ t', Steps image t 2 2 t' ∧
      (a + 1 < 2 ^ 20 → DigInv u (a + 1) t') ∧ (a + 1 = 2 ^ 20 → t'.pc = pcOf 43) ∧
      RegsEq t t' [.x6] := by
  have hs := symRun_sound blk41 codeAt_41 t tpc (by simp only [blk41.res, rv_simp])
  have r41 : RegsEq t (blk41.res.toState t) [.x6] := by
    intro r hr
    rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  refine ⟨_, hs, ?_, ?_, r41⟩
  · intro h
    refine ⟨?_, ?_, h, ?_, ?_, ?_⟩
    · simp only [blk41.res, rv_simp, t6, tregs.get .x7 (by simp [digRegs]), hx7, ofNat_add_ofNat,
        ofNat_bne_ofNat]
      rw [if_pos (by simp; omega)]
    · simp only [blk41.res, rv_simp, t6, ofNat_add_ofNat]
    · exact (tregs.trans r41).mono (by intro r hr; simp [digRegs] at hr ⊢; tauto)
    · intro x hx hW
      rw [Result.toState_getMem, show blk41.res.st.mem = [] from rfl, memEval_nil]; exact tframe x hx hW
    · rw [Result.toState_getMem, show blk41.res.st.mem = [] from rfl, memEval_nil]; exact tlo
  · intro h
    simp only [blk41.res, rv_simp, t6, tregs.get .x7 (by simp [digRegs]), hx7, ofNat_add_ofNat,
      ofNat_bne_ofNat]
    rw [if_neg (by simp; omega)]

/-- The digest search. -/
theorem digLoop_sim (sk : SecretKey) (m : Message) (u : MachineState)
    (hmem : DigMem (toList sk) (toList m) u) (hx5 : u.getReg .x5 = 0)
    (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20)) :
    ∀ fuel a t, a + (fuel + 1) = 2 ^ 20 → DigInv u a t →
      Sim image t ((fuel + 1) * 46 + 2) (searchDigest (toList sk) (toList m) a (fuel + 1))
        (DigPost u) := by
  have hS : (toList sk).length = 32 := length_toList sk
  have hm : (toList m).length = 32 := length_toList m
  intro fuel
  induction fuel with
  | zero =>
    intro a t ha hinv
    rw [searchDigest_succ]
    refine (digTrial sk m u hmem hx5 a t hinv _ 4 ?_).mono (by omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe tlo
    obtain ⟨t'', hs, -, hfail, -⟩ := digNext u hx7 a (by omega) t' tpc t6 tregs tframe tlo
    have hs43 := symRun_sound blk43 codeAt_43 t'' (hfail (by omega)) (by simp only [blk43.res, rv_simp])
    have hc : blk43.res.cycles = 2 := rfl
    rw [hc] at hs43
    have := Sim.steps hs (Sim.pure_steps (a := (none : Option (Val × Nat))) (Q := DigPost u) hs43
      ⟨by simp only [blk43.res, rv_simp], by simp only [blk43.res, rv_simp],
       by simp only [blk43.res, rv_simp]⟩)
    simpa [searchDigest] using this
  | succ f ih =>
    intro a t ha hinv
    rw [searchDigest_succ]
    refine (digTrial sk m u hmem hx5 a t hinv _ (2 + ((f + 1) * 46 + 2)) ?_).mono (by ring_nf; omega)
      (fun _ _ h => h)
    intro t' tpc t6 tregs tframe tlo
    obtain ⟨t'', hs, hinv', -, -⟩ := digNext u hx7 a (by omega) t' tpc t6 tregs tframe tlo
    exact Sim.steps hs (ih (a + 1) t'' (by omega) (hinv' (by omega)))

end SigGolfCandidate.Sign
