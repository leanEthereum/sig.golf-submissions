import SigGolfCandidate.Verify.Init

/-! # The prologue: counter range check and message digest; the digest check and FORS tree 0 -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

theorem or_low (y : Nat) (k : Nat) : (y ||| (2 ^ k - 1)) = 2 ^ k - 1 ↔ y < 2 ^ k := by
  constructor
  · intro h
    have := @Nat.left_le_or y (2 ^ k - 1)
    have := Nat.two_pow_pos k
    omega
  · intro h
    have h1 := Nat.or_lt_two_pow h (show 2 ^ k - 1 < 2 ^ k by have := Nat.two_pow_pos k; omega)
    have h2 := @Nat.right_le_or y (2 ^ k - 1)
    omega

theorem or4_lt (a b c d n : Nat) : (a ||| b ||| c ||| d) < 2 ^ n ↔ a < 2 ^ n ∧ b < 2 ^ n ∧ c < 2 ^ n ∧ d < 2 ^ n := by
  constructor
  · intro h
    have h1 := @Nat.left_le_or (a ||| b ||| c) d
    have h2 := @Nat.left_le_or (a ||| b) c
    have h3 := @Nat.left_le_or a b
    have h4 := @Nat.right_le_or (a ||| b ||| c) d
    have h5 := @Nat.right_le_or (a ||| b) c
    have h6 := @Nat.right_le_or a b
    omega
  · rintro ⟨h1, h2, h3, h4⟩
    exact Nat.or_lt_two_pow (Nat.or_lt_two_pow (Nat.or_lt_two_pow h1 h2) h3) h4

theorem mask_or (x : Nat) :
    (x ||| ctrMask) = ctrMask ↔ x % 2 ^ 32 < 2 ^ 20 ∧ x / 2 ^ 32 < 2 ^ 20 := by
  have hM : ctrMask % 2 ^ 32 = 2 ^ 20 - 1 ∧ ctrMask / 2 ^ 32 = 2 ^ 20 - 1 := by decide
  constructor
  · intro h
    have e1 := congrArg (· % 2 ^ 32) h
    have e2 := congrArg (· / 2 ^ 32) h
    simp only [Nat.or_mod_two_pow, Nat.or_div_two_pow, hM.1, hM.2] at e1 e2
    exact ⟨(or_low _ 20).mp e1, (or_low _ 20).mp e2⟩
  · rintro ⟨h1, h2⟩
    have e1 : (x ||| ctrMask) % 2 ^ 32 = ctrMask % 2 ^ 32 := by
      rw [Nat.or_mod_two_pow, hM.1, (or_low _ 20).mpr h1]
    have e2 : (x ||| ctrMask) / 2 ^ 32 = ctrMask / 2 ^ 32 := by
      rw [Nat.or_div_two_pow, hM.2, (or_low _ 20).mpr h2]
    have := Nat.div_add_mod (x ||| ctrMask) (2 ^ 32)
    have := Nat.div_add_mod ctrMask (2 ^ 32)
    omega

theorem ctr_word (wl : List Byte) (hwl : wl.length = 7756) (s : MachineState) (hW : WitOK wl s)
    (i : Nat) (hi : i < 4) :
    (s.getMem (BitVec.ofNat 64 (9776 + 8 * i))).toNat =
      witCounter wl (2 * i) + 2 ^ 32 * leNat (slice wl (7728 + 8 * i + 4) 4) := by
  rw [show 9776 + 8 * i = 0x800 + (7728 + 8 * i) by omega, wit_word hW _ (by omega) (by omega),
    w64_toNat _ (by simp [slice]), leNat_slice8 _ _ (by omega)]
  simp only [witCounter, witCounters]
  congr 3; omega

theorem leNat4_lt (l : List Byte) (o : Nat) : leNat (slice l o 4) < 2 ^ 32 := by
  have := leNat_lt (slice l o 4)
  have l4 : (slice l o 4).length ≤ 4 := by simp [slice]
  exact lt_of_lt_of_le this (le_trans (Nat.pow_le_pow_right (by decide) l4) (by norm_num))

theorem ctr_iff (wl : List Byte) (hwl : wl.length = 7756) (s : MachineState) (hW : WitOK wl s) :
    ctrOrE.eval s = BitVec.ofNat 64 ctrMask ↔ countersOk wl = true := by
  have e : ctrOrE.eval s = s.getMem (BitVec.ofNat 64 9776) ||| s.getMem (BitVec.ofNat 64 9784) |||
      s.getMem (BitVec.ofNat 64 9792) ||| (extractWord32 (s.getMem (BitVec.ofNat 64 9800)) 0).zeroExtend 64 |||
      BitVec.ofNat 64 ctrMask := rfl
  have w0 := ctr_word wl hwl s hW 0 (by decide)
  have w1 := ctr_word wl hwl s hW 1 (by decide)
  have w2 := ctr_word wl hwl s hW 2 (by decide)
  have w3 := ctr_word wl hwl s hW 3 (by decide)
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at w0 w1 w2 w3
  have z3 : leNat (slice wl 7756 4) = 0 := by
    simp [slice, List.drop_eq_nil_of_le (show wl.length ≤ 7756 by omega), leNat]
  rw [z3] at w3
  have c0 := leNat4_lt wl 7732; have c1 := leNat4_lt wl 7740; have c2 := leNat4_lt wl 7748
  have d0 : witCounter wl 0 < 2 ^ 32 := witCounter_lt wl 0
  have d2 : witCounter wl 2 < 2 ^ 32 := witCounter_lt wl 2
  have d4 : witCounter wl 4 < 2 ^ 32 := witCounter_lt wl 4
  have d6 : witCounter wl 6 < 2 ^ 32 := witCounter_lt wl 6
  have k1 : witCounter wl 1 = leNat (slice wl 7732 4) := rfl
  have k3 : witCounter wl 3 = leNat (slice wl 7740 4) := rfl
  have k5 : witCounter wl 5 = leNat (slice wl 7748 4) := rfl
  rw [e]
  constructor
  · intro h
    have h' := congrArg BitVec.toNat h
    simp only [BitVec.toNat_or, BitVec.toNat_ofNat, extractWord32, BitVec.truncate_eq_setWidth,
      BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at h'
    rw [w0, w1, w2, w3, show ctrMask % 2 ^ 64 = ctrMask from rfl] at h'
    have := (mask_or _).mp h'
    simp only [Nat.or_mod_two_pow, Nat.or_div_two_pow, or4_lt] at this
    simp only [countersOk, nLayers, cMax, List.all, List.range, List.range.loop, decide_eq_true_eq,
      Bool.and_eq_true]
    rw [k1, k3, k5]
    generalize witCounter wl 0 = x0 at *; generalize witCounter wl 2 = x2 at *
    generalize witCounter wl 4 = x4 at *; generalize witCounter wl 6 = x6 at *
    generalize leNat (slice wl 7732 4) = x1 at *; generalize leNat (slice wl 7740 4) = x3 at *
    generalize leNat (slice wl 7748 4) = x5 at *
    norm_num at this c0 c1 c2 d0 d2 d4 d6 ⊢
    omega
  · intro h
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_or, BitVec.toNat_ofNat, extractWord32, BitVec.truncate_eq_setWidth,
      BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [w0, w1, w2, w3, show ctrMask % 2 ^ 64 = ctrMask from rfl]
    apply (mask_or _).mpr
    simp only [Nat.or_mod_two_pow, Nat.or_div_two_pow, or4_lt]
    simp only [countersOk, nLayers, cMax, List.all, List.range, List.range.loop, decide_eq_true_eq,
      Bool.and_eq_true] at h
    rw [k1, k3, k5] at h
    generalize witCounter wl 0 = x0 at *; generalize witCounter wl 2 = x2 at *
    generalize witCounter wl 4 = x4 at *; generalize witCounter wl 6 = x6 at *
    generalize leNat (slice wl 7732 4) = x1 at *; generalize leNat (slice wl 7740 4) = x3 at *
    generalize leNat (slice wl 7748 4) = x5 at *
    norm_num at h c0 c1 c2 d0 d2 d4 d6 ⊢
    omega

def DigestOut (d : DCtx) (s : MachineState) : Prop :=
  Glob d.wl d.pk s ∧ KnownOK dgK s ∧ s.getMem (BitVec.ofNat 64 0x160) = d.a.extractLsb' 0 64 ∧
  s.getMem (BitVec.ofNat 64 0x168) = d.a.extractLsb' 64 64 ∧
  s.getMem (BitVec.ofNat 64 0x170) = d.a.extractLsb' 128 64 ∧
  (s.getMem (BitVec.ofNat 64 0xC0)).toNat < 2 ^ 32 ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧
  (s.getMem (BitVec.ofNat 64 0x220)).toNat < 2 ^ 32 ∧ (s.getMem (BitVec.ofNat 64 0x228)).toNat < 2 ^ 32 ∧
  s.pc = pcOf 63

theorem start_step (ml pkl wl : List Byte) (hml : ml.length = 32) (hwl : wl.length = 7756)
    (s : MachineState) (hs : InitOK ml pkl wl s) :
    (countersOk wl = false → ∃ t, Steps image s 54 54 t ∧ fetch image t = some (.base .ECALL) ∧
        t.getReg .x5 = 1 ∧ t.getReg .x10 = 1) ∧
    (countersOk wl = true → ∃ t, Steps image s 62 62 t ∧ fetch image t = some (.base .ECALL) ∧
        t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
        hashInput t = pad64 (digestInput (witRho wl) ml) ∧
        ∀ a, DigestOut ⟨wl, pkl, a⟩ (writeHash t a)) := by
  obtain ⟨hK, hpc, hW, hPk, hM, hZ⟩ := hs
  obtain ⟨r1, r2, r3, r4, r5⟩ := top_runs
  have hctr := ctr_iff wl hwl s hW
  constructor
  · intro hc
    obtain ⟨hst, hec⟩ := run_post' r5 rfl s hpc hK (by
      intro b hb
      simp only [startRejExp, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval]
      rw [bne_iff_ne, ne_eq]
      intro h; rw [hctr.mp h] at hc; cases hc)
    exact ⟨_, hst, hec rfl, rfl, rfl⟩
  · intro hc
    obtain ⟨hst, hec⟩ := run_post' r4 rfl s hpc hK (by
      intro b hb
      simp only [startOkExp, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval]
      rw [bne_eq_false_iff_eq]; exact hctr.mpr hc)
    set r := startOkExp with hr
    have hkg : knownB globK r = true := by decide
    have hK' := knownB_ok hkg s
    have hkd : knownB dgK r = true := by decide
    have hKd := knownB_ok hkd s
    have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0 := hKd (.x10, 0) (by simp [dgK])
    have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (1 + 1)) := hKd (.x11, 128) (by simp [dgK])
    have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 0x160 := hKd (.x12, 0x160) (by simp [dgK])
    have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 40⟩, ldE 2056), (⟨none, BitVec.ofNat 64 32⟩, ldE 2048),
        (⟨none, BitVec.ofNat 64 0⟩, cw 3073)] := rfl
    have mfr : ∀ A, A < 2 ^ 64 → A ≠ 40 → A ≠ 32 → A ≠ 0 →
        (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3
      rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by
        rw [hmem]; simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;> simp <;> omega)]
    have hG : Glob wl pkl (r.toState s) := by
      refine ⟨hK', ?_, ?_, ?_⟩
      · intro j hj; rw [mfr _ (by omega) (by omega) (by omega) (by omega)]; exact hW j hj
      · exact ⟨(mfr 0xA0 (by omega) (by omega) (by omega) (by omega)).trans hPk.1,
          (mfr 0xA8 (by omega) (by omega) (by omega) (by omega)).trans hPk.2⟩
      · intro a ha
        simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at ha
        rw [mfr _ (by omega) (by omega) (by omega) (by omega)]
        exact hZ a (by omega) (by omega)
    refine ⟨r.toState s, hst, hec rfl, hK' (.x5, 0) (by simp [globK]),
      hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide), ?_, ?_⟩
    · have hrho : (witRho wl).length = 16 := by unfold witRho; apply length_slice16; omega
      rw [hashInput_ofNat _ 0 1 h10 h11 (by decide) (by decide), pad64_digestInput _ _ hrho hml]
      congr 1
      simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
        Nat.mul_zero, Nat.zero_add, wordsOfN, List.cons_append, List.nil_append, List.cons.injEq]
      have w0 := hW 0 (by decide); have w1 := hW 1 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at w0 w1
      have m0 := hM 0 (by decide); have m1 := hM 1 (by decide); have m2 := hM 2 (by decide)
      have m3 := hM 3 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at m0 m1 m2 m3
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
      · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
          memEval_cons_eq _ _ _ _ _ rfl]; rfl
      · rw [mfr 8 (by omega) (by omega) (by omega) (by omega), hZ 8 (by omega) (by omega)]; rfl
      · rw [mfr 16 (by omega) (by omega) (by omega) (by omega), hZ 16 (by omega) (by omega)]
      · rw [mfr 24 (by omega) (by omega) (by omega) (by omega), hZ 24 (by omega) (by omega)]
      · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]
        simp only [ldE, cw, Rv.E.eval]
        rw [show (2048 : Nat) = 0x800 + 8 * 0 from rfl, w0, witRho, vw0_slice]
      · rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
        simp only [ldE, cw, Rv.E.eval]
        rw [show (2056 : Nat) = 0x800 + 8 from rfl, w1, witRho, vw1_slice]
      · rw [mfr 48 (by omega) (by omega) (by omega) (by omega), hZ 48 (by omega) (by omega)]
      · rw [mfr 56 (by omega) (by omega) (by omega) (by omega), hZ 56 (by omega) (by omega)]
      · rw [mfr 64 (by omega) (by omega) (by omega) (by omega), m0]; rfl
      · rw [mfr 72 (by omega) (by omega) (by omega) (by omega), m1]; rfl
      · rw [mfr 80 (by omega) (by omega) (by omega) (by omega), m2]; simp [slice, List.drop_drop]
      · rw [mfr 88 (by omega) (by omega) (by omega) (by omega), m3]; simp [slice, List.drop_drop]
      · rw [mfr 96 (by omega) (by omega) (by omega) (by omega), hZ 96 (by omega) (by omega)]
      · rw [mfr 104 (by omega) (by omega) (by omega) (by omega), hZ 104 (by omega) (by omega)]
      · rw [mfr 112 (by omega) (by omega) (by omega) (by omega), hZ 112 (by omega) (by omega)]
      · rw [mfr 120 (by omega) (by omega) (by omega) (by omega), hZ 120 (by omega) (by omega)]
    · intro a
      have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x160 ∨ 0x160 + 32 ≤ A) =>
        writeHash_frame _ a 0x160 A h12 hA (by omega) h
      refine ⟨Glob_writeHash hG a _ h12 (by decide), Known_writeHash hKd a,
        writeHash_at0 _ a _ h12 (by omega), writeHash_at8 _ a _ h12 (by omega), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := writeHash_getMem_ofNat (r.toState s) a 0x160 0x170 h12 (by omega) (by omega)
        rw [this, if_neg (by omega), if_pos rfl]
      · rw [wf 0xC0 (by omega) (by omega), mfr 0xC0 (by omega) (by omega) (by omega) (by omega),
          hZ _ (by omega) (by omega)]; decide
      · rw [wf 0xF0 (by omega) (by omega), mfr 0xF0 (by omega) (by omega) (by omega) (by omega),
          hZ _ (by omega) (by omega)]
      · rw [wf 0xF8 (by omega) (by omega), mfr 0xF8 (by omega) (by omega) (by omega) (by omega),
          hZ _ (by omega) (by omega)]
      · rw [wf 0x220 (by omega) (by omega), mfr 0x220 (by omega) (by omega) (by omega) (by omega),
          hZ _ (by omega) (by omega)]; decide
      · rw [wf 0x228 (by omega) (by omega), mfr 0x228 (by omega) (by omega) (by omega) (by omega),
          hZ _ (by omega) (by omega)]; decide
      · rw [writeHash_pc, PRes.toState_pc, show r.pc = pcOf 62 from rfl, pcOf_add4]

theorem wLdE_eval (d : DCtx) (s : MachineState) (h0 : s.getMem (BitVec.ofNat 64 0x160) = d.a.extractLsb' 0 64)
    (h1 : s.getMem (BitVec.ofNat 64 0x168) = d.a.extractLsb' 64 64)
    (h2 : s.getMem (BitVec.ofNat 64 0x170) = d.a.extractLsb' 128 64) :
    ∀ i, i < 3 → (wLdE i).eval s = BitVec.ofNat 64 (d.A / 2 ^ (64 * i) % 2 ^ 64) := by
  intro i hi
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
  interval_cases i <;>
    simp [wLdE, ldE, cw, Rv.E.eval, h0, h1, h2, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, DCtx.A]

theorem dgpost_step (d : DCtx) (hwl : d.wl.length = 7756) (s : MachineState) (hs : DigestOut d s) :
    (admissible (d.A % 2 ^ 184) = false → ∃ t, Steps image s 6 6 t ∧ fetch image t = some (.base .ECALL) ∧
        t.getReg .x5 = 1 ∧ t.getReg .x10 = 1) ∧
    (admissible (d.A % 2 ^ 184) = true → ∃ t, Steps image s 30 30 t ∧ fetch image t = some (.base .ECALL) ∧
        t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
        hashInput t = pad64 (ftsLeafInput 0 d.idx (d.u 0) (witFtsSecret d.wl 0)) ∧
        ∀ ans, LeafDoneF d 0 [] (answerBytes 16 ans) (writeHash t ans)) := by
  obtain ⟨hG, hK, h0, h1, h2, hC0, hF0, hF8, hR0, hR8, hpc⟩ := hs
  obtain ⟨r1, r2, r3, r4, r5⟩ := top_runs
  have hw := wLdE_eval d s h0 h1 h2
  have hadm : admE.eval s = BitVec.ofNat 64 (d.A / 2 ^ 174 % 1024) := admE_eval d.A s (by
    have := hw 2 (by decide); simpa using this)
  have hadm' : admissible (d.A % 2 ^ 184) = decide (d.A / 2 ^ 174 % 1024 = 0) := by
    simp only [admissible, uOf, totalH, ftsA]
    rw [beq_eq_decide]
    congr 1
    apply propext
    constructor <;> intro h <;> omega
  have hzero : (BitVec.ofNat 64 (d.A / 2 ^ 174 % 1024) = 0) ↔ d.A / 2 ^ 174 % 1024 = 0 := by
    rw [show (0 : Word) = BitVec.ofNat 64 0 from rfl, ofNat_eq_iff (by omega) (by omega)]
  constructor
  · intro hna
    obtain ⟨hst, hec⟩ := run_post' r3 rfl s hpc hK (by
      intro b hb
      simp only [dgRejExp, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      rw [br_eq_zero, hadm]
      simp only [decide_eq_false_iff_not, decide_eq_true_eq]
      rw [show (0 : Word) = BitVec.ofNat 64 0 from rfl,
        ofNat_eq_iff (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by norm_num)) (by norm_num)]
      rw [hadm'] at hna
      simpa using hna)
    exact ⟨_, hst, hec rfl, rfl, rfl⟩
  · intro ha
    obtain ⟨hst, hec⟩ := run_post' r2 rfl s hpc hK (by
      intro b hb
      simp only [dgOkExp, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      rw [br_eq_zero, hadm]
      simp only [decide_eq_false_iff_not, decide_eq_true_eq]
      rw [show (0 : Word) = BitVec.ofNat 64 0 from rfl,
        ofNat_eq_iff (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by norm_num)) (by norm_num)]
      rw [hadm'] at ha
      simpa using ha)
    set r := dgOkExp with hr
    have hok : resOK r = true := by decide
    have hkn : knownB forsLeafK r = true := by decide
    have hK' := knownB_ok hkn s
    have hglob := Glob_toState hG r.st r.pc (by simp only [resOK, Bool.and_eq_true] at hok; exact hok.1.1)
      (by simp only [resOK, Bool.and_eq_true] at hok; exact hok.1.2)
    have hidx := d_idx_lt d
    have hu : u0E.eval s = BitVec.ofNat 64 (d.u 0) := uExprW_eval wLdE d.A s hw 0 (by decide)
    have hul := d_u_lt d 0
    obtain ⟨hgp, hsll⟩ := gpF_eval u0E (d.u 0) hul s hu
    have hie : idxE.eval s = BitVec.ofNat 64 d.idx := idxE_eval d.A s (by simpa using hw 0 (by decide))
    have hfe : fw0E.eval s = BitVec.ofNat 64 (d.fw 0) := by
      rw [fw0E_eval d.A s (by simpa using hw 0 (by decide))]; rfl
    have hfwl := d_fw_lt d 0 (by decide)
    have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0xC0 := hK' (.x10, 0xC0) (by simp [forsLeafK])
    have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, 64) (by simp [forsLeafK])
    have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * (d.u 0 % 2)) := by
      rw [PRes.toState_getReg]; simp only [hr, dgOkExp]
      simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
      rw [show (Rv.E.bin .add (gpF u0E) (cw 480)).eval s = (gpF u0E).eval s + BitVec.ofNat 64 480
        from rfl, hgp, BitVec.ofNat_add_ofNat]; congr 1; omega
    have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 232⟩, ldE 2072), (⟨none, BitVec.ofNat 64 224⟩, ldE 2064),
        (⟨none, BitVec.ofNat 64 200⟩, .bin (.st .w 4) (stW0 200 idxE) u0E),
        (⟨none, BitVec.ofNat 64 192⟩, stW0 192 fw0E),
        (⟨none, BitVec.ofNat 64 552⟩, stW0 552 idxE), (⟨none, BitVec.ofNat 64 456⟩, stW0 456 idxE)] := rfl
    have mfr : ∀ A, A < 2 ^ 64 → A ≠ 232 → A ≠ 224 → A ≠ 200 → A ≠ 192 → A ≠ 552 → A ≠ 456 →
        (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4 h5 h6
      rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by
        rw [hmem]; simp only [List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp <;> omega)]
    have mC0 : (r.toState s).getMem (BitVec.ofNat 64 192) = BitVec.ofNat 64 (d.fw 0) := by
      rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]
      apply BitVec.eq_of_toNat_eq
      rw [show (stW0 192 fw0E).eval s = StoreKind.merge .w (s.getMem (BitVec.ofNat 64 192)) 0 (fw0E.eval s)
        from rfl, merge_w0_toNat, hfe]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.div_eq_of_lt hC0]; omega
    have mC8 : (r.toState s).getMem (BitVec.ofNat 64 200) = BitVec.ofNat 64 (d.idx % 2 ^ 32 + 2 ^ 32 * d.u 0) := by
      rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_eq _ _ _ _ _ rfl]
      apply BitVec.eq_of_toNat_eq
      rw [show (Rv.E.bin (.st .w 4) (stW0 200 idxE) u0E).eval s =
        StoreKind.merge .w (StoreKind.merge .w (s.getMem (BitVec.ofNat 64 200)) 0 (idxE.eval s)) 4 (u0E.eval s)
        from rfl, merge_w4_toNat, merge_w0_toNat, hie, hu]
      simp only [BitVec.toNat_ofNat]
      omega
    have mR8 : (r.toState s).getMem (BitVec.ofNat 64 552) = BitVec.ofNat 64 (d.idx % 2 ^ 32) := by
      rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_eq _ _ _ _ _ rfl]
      apply BitVec.eq_of_toNat_eq
      rw [show (stW0 552 idxE).eval s = StoreKind.merge .w (s.getMem (BitVec.ofNat 64 552)) 0 (idxE.eval s)
        from rfl, merge_w0_toNat, hie]
      simp only [BitVec.toNat_ofNat]
      rw [Nat.div_eq_of_lt hR8]; omega
    have mN8 : ((r.toState s).getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = d.idx % 2 ^ 32 := by
      rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]
      rw [show (stW0 456 idxE).eval s = StoreKind.merge .w (s.getMem (BitVec.ofNat 64 456)) 0 (idxE.eval s)
        from rfl, merge_w0_toNat, hie]
      simp only [BitVec.toNat_ofNat]
      omega
    have hsl : (witFtsSecret d.wl 0).length = 16 := by unfold witFtsSecret; apply length_slice16; omega
    have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
    refine ⟨r.toState s, hst, hec rfl, hK' (.x5, 0) (by simp [forsLeafK, globK]),
      hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
        (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega), ?_, ?_⟩
    · rw [hashInput_ofNat _ 0xC0 0 h10 h11 (by decide) (by decide), pad64_ftsLeafInput _ _ _ _ hsl]
      congr 1
      simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
        Nat.mul_zero, List.cons.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
      · rw [mC0]; congr 1; unfold twLo DCtx.fw; omega
      · rw [mC8]; congr 1; unfold twHi; omega
      · rw [mfr 0xD0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hP _ (by decide)
      · rw [mfr 0xD8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hP _ (by decide)
      · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]
        simp only [ldE, cw, Rv.E.eval]
        rw [show (2064 : Nat) = 0x800 + 16 from rfl, wit_word hG.2.1 _ (by omega) (by omega), witFtsSecret,
          show 16 + 176 * 0 = 16 from rfl, vw0_slice]
      · rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
        simp only [ldE, cw, Rv.E.eval]
        rw [show (2072 : Nat) = 0x800 + 24 from rfl, wit_word hG.2.1 _ (by omega) (by omega), witFtsSecret,
          show 16 + 176 * 0 = 16 from rfl, vw1_slice]
      · rw [mfr 0xF0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF0
      · rw [mfr 0xF8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF8
    · intro ans
      have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x1E0 + 16 * (d.u 0 % 2) ∨ 0x1E0 + 16 * (d.u 0 % 2) + 32 ≤ A) =>
        writeHash_frame _ ans _ A h12 hA (by omega) h
      have rg : ∀ x, (writeHash (r.toState s) ans).getReg x = (r.st.regs.get x).eval s := fun x => by
        rw [writeHash_getReg, PRes.toState_getReg]
      refine ⟨Glob_writeHash hglob ans _ h12 (by
          rcases Nat.mod_two_eq_zero_or_one (d.u 0) with h | h <;> rw [h] <;> decide),
        Known_writeHash hK' ans, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun j hj => by simp at hj,
          fun v hv => by simp at hv, ?_, ?_⟩, rfl, by rw [writeHash_getReg]; exact h12, ?_, ?_,
        (writeHash_at0 _ ans _ h12 (by omega)).trans (vw0_answer ans).symm, ?_, by simp, ?_, ?_⟩
      · rw [rg]; simp only [hr, dgOkExp]; simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
        simp only [wLdE, ldE, cw, Rv.E.eval]; exact h0
      · rw [rg]; simp only [hr, dgOkExp]; simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
        simp only [wLdE, ldE, cw, Rv.E.eval]; exact h1
      · rw [rg]; simp only [hr, dgOkExp]; simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
        simp only [wLdE, ldE, cw, Rv.E.eval]; exact h2
      · rw [rg]; simp only [hr, dgOkExp]; simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
        exact hie
      · rw [rg]; simp only [hr, dgOkExp]; simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
        exact hfe
      · rw [rg]; simp only [hr, dgOkExp]; simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
        rfl
      · rw [wf 0xC0 (by omega) (by omega), mC0, BitVec.toNat_ofNat]; omega
      · rw [wf 0xC8 (by omega) (by omega), mC8, BitVec.toNat_ofNat]; omega
      · rw [wf 0xF0 (by omega) (by omega), mfr 0xF0 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)]; exact hF0
      · rw [wf 0xF8 (by omega) (by omega), mfr 0xF8 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)]; exact hF8
      · rw [wf 0x220 (by omega) (by omega), mfr 0x220 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega)]; exact hR0
      · rw [wf 0x228 (by omega) (by omega), mR8]
      · rw [rg]; simp only [hr, dgOkExp]; simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
        exact hu
      · rw [rg]; simp only [hr, dgOkExp]; simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
        exact hsll
      · rw [show 0x1E8 + 16 * (d.u 0 % 2) = 0x1E0 + 16 * (d.u 0 % 2) + 8 by omega,
          writeHash_at8 _ ans _ h12 (by omega)]; exact (vw1_answer ans).symm
      · rw [wf 0x1C8 (by omega) (by omega)]; exact mN8
      · rw [writeHash_pc, PRes.toState_pc, show r.pc = pcOf 96 from rfl, pcOf_add4]; rfl

end SigGolfCandidate.Verify
