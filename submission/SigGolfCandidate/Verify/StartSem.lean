import SigGolfCandidate.Verify.ForsArith
import SigGolfCandidate.Verify.ForsCheck
import SigGolfCandidate.Verify.Init

/-! # The prologue: counter range check and message digest -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

theorem or3_lt (a b c n : Nat) : (a ||| b ||| c) < 2 ^ n ↔ a < 2 ^ n ∧ b < 2 ^ n ∧ c < 2 ^ n := by
  constructor
  · intro h
    have h2 := @Nat.left_le_or (a ||| b) c
    have h3 := @Nat.left_le_or a b
    have h5 := @Nat.right_le_or (a ||| b) c
    have h6 := @Nat.right_le_or a b
    omega
  · rintro ⟨h1, h2, h3⟩
    exact Nat.or_lt_two_pow (Nat.or_lt_two_pow h1 h2) h3

theorem ctr_word (wl : List Byte) (hwl : wl.length = 6404) (s : MachineState) (hW : WitOK wl s)
    (i : Nat) (hi : i < 2) :
    (s.getMem (BitVec.ofNat 64 (8432 + 8 * i))).toNat =
      witCounter wl (2 * i) + 2 ^ 32 * witCounter wl (2 * i + 1) := by
  rw [show 8432 + 8 * i = 0x800 + (6384 + 8 * i) by omega, wit_word hW _ (by omega) (by omega),
    w64_toNat _ (by simp [slice]), leNat_slice8 _ _ (by omega)]
  simp only [witCounter, witCounters_eq]
  rw [show 6384 + 4 * (2 * i) = 6384 + 8 * i by omega,
    show 6384 + 4 * (2 * i + 1) = 6384 + 8 * i + 4 by omega]

theorem ctr_word4 (wl : List Byte) (hwl : wl.length = 6404) (s : MachineState) (hW : WitOK wl s) :
    ((extractWord32 (s.getMem (BitVec.ofNat 64 8448)) 0).zeroExtend 64).toNat = witCounter wl 4 := by
  rw [show (8448 : Nat) = 0x800 + 6400 from rfl, wit_word hW _ (by omega) (by omega)]
  simp only [extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [w64_toNat _ (by simp [slice]), leNat_slice8 _ _ (by omega)]
  have z : leNat (slice wl (6400 + 4) 4) = 0 := by
    simp [slice, List.drop_eq_nil_of_le (show wl.length ≤ 6404 by omega), leNat]
  rw [z]
  simp only [witCounter, witCounters_eq]
  have := leNat_lt (slice wl 6400 4)
  have l4 : (slice wl 6400 4).length ≤ 4 := by simp [slice]
  have : leNat (slice wl 6400 4) < 2 ^ 32 :=
    lt_of_lt_of_le this (le_trans (Nat.pow_le_pow_right (by decide) l4) (by norm_num))
  norm_num
  omega

theorem ctr_iff (wl : List Byte) (hwl : wl.length = 6404) (s : MachineState) (hW : WitOK wl s) :
    ctrE'.eval s = 0 ↔ countersOk wl = true := by
  have e : ctrE'.eval s = (ctrX.eval s ||| (ctrX.eval s <<< ((BitVec.ofNat 64 32).toNat % 64))) >>>
      ((BitVec.ofNat 64 54).toNat % 64) := rfl
  have ex : ctrX.eval s = s.getMem (BitVec.ofNat 64 8432) ||| s.getMem (BitVec.ofNat 64 8440) |||
      (extractWord32 (s.getMem (BitVec.ofNat 64 8448)) 0).zeroExtend 64 := rfl
  have hx := (ctrX.eval s).isLt
  have hsh : ctrE'.eval s = 0 ↔ (ctrX.eval s).toNat % 2 ^ 32 < 2 ^ 22 ∧ (ctrX.eval s).toNat / 2 ^ 32 < 2 ^ 22 := by
    rw [e, ← ctr_shift_iff _ hx]
    constructor
    · intro h
      have := congrArg BitVec.toNat h
      simpa [BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        Nat.shiftRight_eq_div_pow] using this
    · intro h
      apply BitVec.eq_of_toNat_eq
      simpa [BitVec.toNat_ushiftRight, BitVec.toNat_or, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
        Nat.shiftRight_eq_div_pow] using h
  rw [hsh, ex]
  have w0 := ctr_word wl hwl s hW 0 (by decide)
  have w1 := ctr_word wl hwl s hW 1 (by decide)
  have w4 := ctr_word4 wl hwl s hW
  simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceMul, Nat.reduceAdd] at w0 w1
  have d0 := witCounter_lt wl 0; have d1 := witCounter_lt wl 1; have d2 := witCounter_lt wl 2
  have d3 := witCounter_lt wl 3; have d4 := witCounter_lt wl 4
  simp only [BitVec.toNat_or]
  rw [w0, w1, w4]
  simp only [Nat.or_mod_two_pow, Nat.or_div_two_pow, or3_lt]
  simp only [countersOk, nLayers, cMax, List.all, List.range, List.range.loop, decide_eq_true_eq,
    Bool.and_eq_true]
  generalize witCounter wl 0 = x0 at *; generalize witCounter wl 1 = x1 at *
  generalize witCounter wl 2 = x2 at *; generalize witCounter wl 3 = x3 at *
  generalize witCounter wl 4 = x4 at *
  norm_num at d0 d1 d2 d3 d4 ⊢
  rw [Nat.mod_eq_of_lt d4, Nat.div_eq_of_lt d4]
  omega

/-- FORS context: witness, public key and the digest answer `a`. -/
structure DCtx where
  wl : List Byte
  pk : List Byte
  a : BitVec 256

def DCtx.A (d : DCtx) : Nat := d.a.toNat

def DigestOut (d : DCtx) (s : MachineState) : Prop :=
  Glob gkD d.wl d.pk s ∧ KnownOK dgK s ∧ s.getMem (BitVec.ofNat 64 0x160) = d.a.extractLsb' 0 64 ∧
  s.getMem (BitVec.ofNat 64 0x168) = d.a.extractLsb' 64 64 ∧
  s.getMem (BitVec.ofNat 64 0x170) = d.a.extractLsb' 128 64 ∧
  (s.getMem (BitVec.ofNat 64 0xC0)).toNat < 2 ^ 32 ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧
  (s.getMem (BitVec.ofNat 64 0x220)).toNat < 2 ^ 32 ∧ (s.getMem (BitVec.ofNat 64 0x228)).toNat < 2 ^ 32 ∧
  s.pc = pcOf 31

theorem init_glob (ml pkl wl : List Byte) (s : MachineState) (hs : InitOK ml pkl wl s) :
    Glob [] wl pkl s := by
  obtain ⟨-, -, hW, hPk, -, hZ⟩ := hs
  refine ⟨fun p hp => by simp at hp, hW, hPk, ?_⟩
  intro a ha
  simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at ha
  exact hZ a (by omega) (by omega)

theorem start_step (ml pkl wl : List Byte) (hml : ml.length = 32) (hwl : wl.length = 6404)
    (s : MachineState) (hs : InitOK ml pkl wl s) :
    (countersOk wl = false → ∃ t, Steps image s 23 23 t ∧ fetch image t = some (.base .ECALL) ∧
        t.getReg .x5 = 1 ∧ t.getReg .x10 = 1) ∧
    (countersOk wl = true → ∃ t, Steps image s 30 30 t ∧ fetch image t = some (.base .ECALL) ∧
        t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
        hashInput t = pad64 (digestInput (witRho wl) ml) ∧
        ∀ a, DigestOut ⟨wl, pkl, a⟩ (writeHash t a)) := by
  have hG0 := init_glob ml pkl wl s hs
  obtain ⟨hK, hpc, hW, hPk, hM, hZ⟩ := hs
  have hctr := ctr_iff wl hwl s hW
  constructor
  · intro hc
    obtain ⟨u, hu⟩ := spec_run (show specB [] (runAt k0 [] 0 [.br true]) specStartRej [] [] = true by
      have := topCheck_ok; simp only [topCheck, Bool.and_eq_true] at this; exact this.1.1.1.2) s hpc hK (by
      intro b hb
      simp only [specStartRej, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval, E.eval]
      rw [bne_iff_ne, ne_eq]
      intro h; rw [hctr.mp h] at hc; cases hc)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [specStartRej, rejK]),
      hu.regs (.x10, cw 1) (by simp [specStartRej, rejK])⟩
  · intro hc
    obtain ⟨u, hu⟩ := spec_run (show specB gkD (runAt k0 [] 0 [.br false]) specStartOk dgK [] = true by
      have := topCheck_ok; simp only [topCheck, Bool.and_eq_true] at this; exact this.1.1.1.1) s hpc hK (by
      intro b hb
      simp only [specStartOk, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval, E.eval]
      rw [bne_eq_false_iff_eq]; exact hctr.mpr hc)
    have hKd := hu.known
    have h10 : u.getReg .x10 = BitVec.ofNat 64 0 := hKd (.x10, 0) (by simp [dgK])
    have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (1 + 1)) := hKd (.x11, 128) (by simp [dgK])
    have h12 : u.getReg .x12 = BitVec.ofNat 64 0x160 := hKd (.x12, 0x160) (by simp [dgK])
    have hmem := hu.mem
    have mfr : ∀ A, A < 2 ^ 64 → A ≠ 40 → A ≠ 32 → A ≠ 0 →
        u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3
      rw [hmem, memEval_frame_ofNat _ _ _ hA (by
        simp only [specStartOk, List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;> simp <;> omega)]
    have hG : Glob gkD wl pkl u := hu.glob _ _ _ hG0
    refine ⟨u, hu.steps, hu.ecall rfl, hKd (.x5, 0) (by simp [dgK, gkD, baseK]),
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
      · rw [hmem]; simp only [specStartOk]
        rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
          memEval_cons_eq _ _ _ _ _ rfl]; rfl
      · rw [mfr 8 (by omega) (by omega) (by omega) (by omega), hZ 8 (by omega) (by omega)]; rfl
      · rw [mfr 16 (by omega) (by omega) (by omega) (by omega), hZ 16 (by omega) (by omega)]
      · rw [mfr 24 (by omega) (by omega) (by omega) (by omega), hZ 24 (by omega) (by omega)]
      · rw [hmem]; simp only [specStartOk]
        rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]
        simp only [ldE, cw, Rv.E.eval]
        rw [show (2048 : Nat) = 0x800 + 8 * 0 from rfl, w0, witRho, vw0_slice]
      · rw [hmem]; simp only [specStartOk]
        rw [memEval_cons_eq _ _ _ _ _ rfl]
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
      · have := writeHash_getMem_ofNat u a 0x160 0x170 h12 (by omega) (by omega)
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
      · rw [writeHash_pc, hu.pc rfl, pcOf_add4]; rfl

end SigGolfCandidate.Verify
