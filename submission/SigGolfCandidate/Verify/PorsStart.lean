import SigGolfCandidate.Verify.PorsDefs
import SigGolfCandidate.Verify.Init

/-! # The prologue (counter range check, message digest) and the PORS setup -/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

/-! ## The counter check -/

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

theorem ctr_word (wl : List Byte) (hwl : wl.length = 6348) (s : MachineState) (hW : WitOK wl s)
    (i : Nat) (hi : i < 2) :
    (s.getMem (BitVec.ofNat 64 (8376 + 8 * i))).toNat =
      witCounter wl (2 * i) + 2 ^ 32 * witCounter wl (2 * i + 1) := by
  rw [show 8376 + 8 * i = 0x800 + (6328 + 8 * i) by omega, wit_word hW _ (by omega) (by omega),
    w64_toNat _ (by simp [slice]), leNat_slice8 _ _ (by omega)]
  simp only [witCounter, witCounters_eq]
  rw [show 6328 + 4 * (2 * i) = 6328 + 8 * i by omega,
    show 6328 + 4 * (2 * i + 1) = 6328 + 8 * i + 4 by omega]

theorem ctr_word4 (wl : List Byte) (hwl : wl.length = 6348) (s : MachineState) (hW : WitOK wl s) :
    ((extractWord32 (s.getMem (BitVec.ofNat 64 8392)) 0).zeroExtend 64).toNat = witCounter wl 4 := by
  rw [show (8392 : Nat) = 0x800 + 6344 from rfl, wit_word hW _ (by omega) (by omega)]
  simp only [extractWord32, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [w64_toNat _ (by simp [slice]), leNat_slice8 _ _ (by omega)]
  have z : leNat (slice wl (6344 + 4) 4) = 0 := by
    simp [slice, List.drop_eq_nil_of_le (show wl.length ≤ 6348 by omega), leNat]
  rw [z]
  simp only [witCounter, witCounters_eq]
  have := leNat_lt (slice wl 6344 4)
  have l4 : (slice wl 6344 4).length ≤ 4 := by simp [slice]
  have : leNat (slice wl 6344 4) < 2 ^ 32 :=
    lt_of_lt_of_le this (le_trans (Nat.pow_le_pow_right (by decide) l4) (by norm_num))
  norm_num
  omega

theorem ctr_iff (wl : List Byte) (hwl : wl.length = 6348) (s : MachineState) (hW : WitOK wl s) :
    ctrE'.eval s = 0 ↔ countersOk wl = true := by
  have e : ctrE'.eval s = (ctrX.eval s ||| (ctrX.eval s <<< ((BitVec.ofNat 64 32).toNat % 64))) >>>
      ((BitVec.ofNat 64 54).toNat % 64) := rfl
  have ex : ctrX.eval s = s.getMem (BitVec.ofNat 64 8376) ||| s.getMem (BitVec.ofNat 64 8384) |||
      (extractWord32 (s.getMem (BitVec.ofNat 64 8392)) 0).zeroExtend 64 := rfl
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

/-! ## The digest -/

/-- After the digest hash (answer `P.a` in DO): the untouched memory below the witness is zero. -/
def DigestOut (P : PCtx) (s : MachineState) : Prop :=
  Glob gkD P.wl P.pk s ∧ KnownOK dgK s ∧
  (∀ i, i < 4 → s.getMem (BitVec.ofNat 64 (0x160 + 8 * i)) = P.a.extractLsb' (64 * i) 64) ∧
  (∀ A, A < 0x800 → A % 8 = 0 → 0x60 ≤ A → A ≠ 0xA0 → A ≠ 0xA8 → (A < 0x160 ∨ 0x180 ≤ A) →
    s.getMem (BitVec.ofNat 64 A) = 0) ∧
  s.pc = pcOf 29

/-- The digest block `tw(12, 0, 0, 0, 0) || rho || m` as words. -/
theorem fmt_digestInput_words (rho m : List Byte) (hr : rho.length = 16) (hm : m.length = 32) :
    fmt (digestInput rho m) = queryOfWords 0
      ([BitVec.ofNat 64 (twLo 12 0 0 0), BitVec.ofNat 64 (twHi 0 0), vw0 rho, vw1 rho] ++ wordsOfN 4 m) := by
  rw [fmt_digestInput _ _ hr hm]
  have hl : (tweak 12 0 0 0 0 ++ rho ++ m).length ≤ 8 * 8 := by simp [length_tweak, hr, hm]
  have hw : wordsOfN 8 (tweak 12 0 0 0 0 ++ rho ++ m) =
      [BitVec.ofNat 64 (twLo 12 0 0 0), BitVec.ofNat 64 (twHi 0 0), vw0 rho, vw1 rho] ++ wordsOfN 4 m := by
    rw [List.append_assoc, show 8 = 2 + (2 + 4) from rfl,
      wordsOfN_append 2 _ _ _ (by simp [length_tweak]), wordsOfN_val_append rho hr, wordsOfN_tweak]
    rfl
  unfold queryOfWords ofList
  rw [← hw, wordsToNat_wordsOfN 8 _ hl]

theorem init_glob (ml pkl wl : List Byte) (s : MachineState) (hs : InitOK ml pkl wl s) :
    Glob [] wl pkl s := by
  obtain ⟨-, -, hW, hPk, -, hZ⟩ := hs
  refine ⟨fun p hp => by simp at hp, hW, hPk, ?_⟩
  intro a ha
  simp only [pSlots, List.mem_cons, List.not_mem_nil, or_false] at ha
  exact hZ a (by omega) (by omega)

theorem startCheck_parts :
    specB gkD (runAt k0 [] 0 [.br false]) specStartOk dgK [] = true ∧
    specB [] (runAt k0 [] 0 [.br true]) specStartRej [] [] = true ∧
    specB gkD (runAt dgK [leafPc 0] 29 []) setupSpec setupPost [] = true := by
  have := startCheck_ok
  simp only [startCheck, Bool.and_eq_true] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem start_step (ml pkl wl : List Byte) (hml : ml.length = 32) (hwl : wl.length = 6348)
    (s : MachineState) (hs : InitOK ml pkl wl s) :
    (countersOk wl = false → ∃ t, Steps image s 20 20 t ∧ fetch image t = some (.base .ECALL) ∧
        t.getReg .x5 = 1 ∧ t.getReg .x10 = 1) ∧
    (countersOk wl = true → ∃ t, Steps image s 28 28 t ∧ fetch image t = some (.base .ECALL) ∧
        t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
        hashInput t = fmt (digestInput (witRho wl) ml) ∧
        ∀ a, DigestOut ⟨wl, pkl, a⟩ (writeHash t a)) := by
  have hG0 := init_glob ml pkl wl s hs
  obtain ⟨hK, hpc, hW, hPk, hM, hZ⟩ := hs
  have hctr := ctr_iff wl hwl s hW
  obtain ⟨cOk, cRej, -⟩ := startCheck_parts
  constructor
  · intro hc
    obtain ⟨u, hu⟩ := spec_run cRej s hpc hK (by
      intro b hb
      simp only [specStartRej, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval, E.eval]
      rw [bne_iff_ne, ne_eq]
      intro h; rw [hctr.mp h] at hc; cases hc)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [specStartRej]),
      hu.regs (.x10, cw 1) (by simp [specStartRej])⟩
  · intro hc
    obtain ⟨u, hu⟩ := spec_run cOk s hpc hK (by
      intro b hb
      simp only [specStartOk, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval, E.eval]
      rw [bne_eq_false_iff_eq]; exact hctr.mpr hc)
    have hKd := hu.known
    have h10 : u.getReg .x10 = BitVec.ofNat 64 0x20 := hKd (.x10, 0x20) (by simp [dgK])
    have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hKd (.x11, 64) (by simp [dgK])
    have h12 : u.getReg .x12 = BitVec.ofNat 64 0x160 := hKd (.x12, 0x160) (by simp [dgK])
    have hmem := hu.mem
    have mfr : ∀ A, A < 2 ^ 64 → A ≠ 56 → A ≠ 48 → A ≠ 32 →
        u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3
      rw [hmem, memEval_frame_ofNat _ _ _ hA (by
        simp only [specStartOk, List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl) <;> simp <;> omega)]
    have hG : Glob gkD wl pkl u := hu.glob _ _ _ hG0
    refine ⟨u, hu.steps, hu.ecall rfl, hKd (.x5, 0) (by simp [dgK, gkD, baseK]),
      hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide), ?_, ?_⟩
    · have hrho : (witRho wl).length = 16 := by unfold witRho; apply length_slice16; omega
      rw [hashInput_ofNat _ 0x20 0 h10 h11 (by decide) (by decide), fmt_digestInput_words _ _ hrho hml]
      congr 1
      simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
        Nat.mul_zero, Nat.zero_add, wordsOfN, List.cons_append, List.nil_append, List.cons.injEq]
      have w0 := hW 0 (by decide); have w1 := hW 1 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd] at w0 w1
      have m0 := hM 0 (by decide); have m1 := hM 1 (by decide); have m2 := hM 2 (by decide)
      have m3 := hM 3 (by decide)
      simp only [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.reduceAdd, Nat.reduceMul] at m0 m1 m2 m3
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
      · rw [hmem]; simp only [specStartOk]
        rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
          memEval_cons_eq _ _ _ _ _ rfl]; rfl
      · rw [mfr 40 (by omega) (by omega) (by omega) (by omega), hZ 40 (by omega) (by omega)]; rfl
      · rw [hmem]; simp only [specStartOk]
        rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]
        simp only [ldE, cw, Rv.E.eval]
        rw [show (2048 : Nat) = 0x800 + 8 * 0 from rfl, w0, witRho, vw0_slice]
      · rw [hmem]; simp only [specStartOk]
        rw [memEval_cons_eq _ _ _ _ _ rfl]
        simp only [ldE, cw, Rv.E.eval]
        rw [show (2056 : Nat) = 0x800 + 8 from rfl, w1, witRho, vw1_slice]
      · rw [mfr 64 (by omega) (by omega) (by omega) (by omega), m0]; rfl
      · rw [mfr 72 (by omega) (by omega) (by omega) (by omega), m1]; rfl
      · rw [mfr 80 (by omega) (by omega) (by omega) (by omega), m2]; simp [slice, List.drop_drop]
      · rw [mfr 88 (by omega) (by omega) (by omega) (by omega), m3]; simp [slice, List.drop_drop]
    · intro a
      have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x160 ∨ 0x160 + 32 ≤ A) =>
        writeHash_frame _ a 0x160 A h12 hA (by omega) h
      refine ⟨Glob_writeHash hG a _ h12 (by decide), Known_writeHash hKd a, ?_, ?_, ?_⟩
      · intro i hi
        have := writeHash_getMem_ofNat u a 0x160 (0x160 + 8 * i) h12 (by omega) (by omega)
        rw [this]
        interval_cases i <;> simp
      · intro A hA h8 h60 hA0 hA8 hr
        rw [wf A (by omega) (by omega), mfr A (by omega) (by omega) (by omega) (by omega)]
        exact hZ A hA (by omega)
      · rw [writeHash_pc, hu.pc rfl, pcOf_add4]; rfl

/-! ## The setup -/

theorem wLdE_eval (P : PCtx) (s : MachineState)
    (hd : ∀ i, i < 4 → s.getMem (BitVec.ofNat 64 (0x160 + 8 * i)) = P.a.extractLsb' (64 * i) 64) :
    ∀ i, i < 4 → (wLdE i).eval s = BitVec.ofNat 64 (P.A / 2 ^ (64 * i) % 2 ^ 64) := by
  intro i hi
  apply BitVec.eq_of_toNat_eq
  simp only [wLdE, ldE, cw, Rv.E.eval]
  rw [hd i hi, ext_toNat, BitVec.toNat_ofNat, Nat.mod_mod]
  rfl

theorem setup_const : (psetupMem.all fun p => p.1.base.isNone) = true := by decide +kernel

theorem setup_look (s : MachineState) (u : MachineState)
    (hmem : ∀ A, u.getMem A = memEval s psetupMem A) (A : Nat) (hA : A < 2 ^ 64) :
    u.getMem (BitVec.ofNat 64 A) = match memLook psetupMem A with
      | some v => v.eval s
      | none => s.getMem (BitVec.ofNat 64 A) := by
  rw [hmem]; exact memEval_look s _ A hA setup_const

theorem setup_none : ∀ a ∈ zeroP, (memLook psetupMem a).isNone = true := by decide +kernel

theorem halfP_lt : ∀ a ∈ halfP, a < 0x800 := by decide
theorem zeroP_lt : ∀ a ∈ zeroP, a < 0x800 := by decide
theorem zeroP_rest : ∀ a ∈ zeroP, a ∉ pSlots →
    a % 8 = 0 ∧ 0x60 ≤ a ∧ a ≠ 0xA0 ∧ a ≠ 0xA8 ∧ (a < 0x160 ∨ 0x180 ≤ a) := by decide

/-- `memLook ws A = some e`, as a Boolean check. -/
def memLookB (ws : SymMem) (A : Nat) (e : E) : Bool :=
  match memLook ws A with
  | some v => E.beq v e
  | none => false

theorem look_some {ws : SymMem} {A : Nat} {e : E} (h : memLookB ws A e = true) :
    memLook ws A = some e := by
  unfold memLookB at h
  split at h
  · rename_i v hv; rw [hv, E.beq_eq h]
  · cases h

theorem setup_blkB : ∀ i, i < 14 → memLookB psetupMem (PSB + 80 * i) nbW0E = true ∧
    memLookB psetupMem (PSB + 80 * i + 8) (stW0 (PSB + 80 * i + 8) idxE) = true := by decide +kernel

theorem setup_blk (i : Nat) (hi : i < 14) : memLook psetupMem (PSB + 80 * i) = some nbW0E ∧
    memLook psetupMem (PSB + 80 * i + 8) = some (stW0 (PSB + 80 * i + 8) idxE) :=
  ⟨look_some (setup_blkB i hi).1, look_some (setup_blkB i hi).2⟩

theorem setup_pindB : ∀ r, r < 15 → memLookB psetupMem (PIND + 8 * r) (pindE r) = true := by decide +kernel

theorem setup_pind (r : Nat) (hr : r < 15) : memLook psetupMem (PIND + 8 * r) = some (pindE r) :=
  look_some (setup_pindB r hr)

theorem twLo_idx (t idx : Nat) (ht : t < 256) (hidx : idx < 2 ^ 34) :
    twLo t 0 idx 0 = 1 + 256 * t + 2 ^ 24 * (idx / 2 ^ 32) := by
  unfold twLo; omega

theorem stW0_low (s : MachineState) (a : Nat) (v : E) (V : Nat) (hv : v.eval s = BitVec.ofNat 64 V)
    (hV : V < 2 ^ 64) : ((stW0 a v).eval s).toNat % 2 ^ 32 = V % 2 ^ 32 := by
  show (StoreKind.merge .w (s.getMem (BitVec.ofNat 64 a)) 0 (v.eval s)).toNat % 2 ^ 32 = _
  rw [merge_w0_toNat, hv, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hV]
  omega

theorem setup_step (P : PCtx) (_hP : P.ok) (s : MachineState) (hs : DigestOut P s) :
    ∃ u, Steps image s 108 108 u ∧ S0 P u ∧ LeafIn P u 0 ⟨wStream, 0, 0, 0, [], []⟩ u := by
  obtain ⟨hG, hK, hd, hZ, hpc⟩ := hs
  obtain ⟨-, -, cSet⟩ := startCheck_parts
  obtain ⟨u, hu⟩ := spec_run cSet s hpc hK (by simp [setupSpec])
  have hw := wLdE_eval P s hd
  have hidx : idxE.eval s = BitVec.ofNat 64 P.idx := by
    rw [idxE_eval P.A s (by simpa using hw 0 (by decide))]; rfl
  have hhi : hiE.eval s = BitVec.ofNat 64 (2 ^ 24 * (P.idx / 2 ^ 32)) :=
    hiE_eval P.A s (by simpa using hw 0 (by decide))
  have hil := P.idx_lt
  have hlook := setup_look s u hu.mem
  have hGu : Glob gkD P.wl P.pk u := hu.glob _ _ _ hG
  have hK' := hu.known
  have nbw : nbW0E.eval s = BitVec.ofNat 64 (twLo 10 0 P.idx 0) := by
    show hiE.eval s + BitVec.ofNat 64 0xA01 = _
    rw [hhi, BitVec.ofNat_add_ofNat, twLo_idx _ _ (by decide) hil]; congr 1; omega
  have S : S0 P u := by
    refine ⟨hGu.2.1, hGu.2.2.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro a ha
      have hn := setup_none a ha
      have ha' : a < 2 ^ 64 := by have := zeroP_lt a ha; omega
      rw [hlook a ha']
      split
      · rename_i v hv; rw [hv] at hn; cases hn
      · by_cases hp : a ∈ pSlots
        · exact hG.2.2.2 a hp
        · obtain ⟨h1, h2, h3, h4, h5⟩ := zeroP_rest a ha hp
          exact hZ a (zeroP_lt a ha) h1 h2 h3 h4 h5
    · rw [hlook 0xC0 (by omega), look_some (e := .bin .add hiE (cw 0x901)) (by decide +kernel)]
      show hiE.eval s + BitVec.ofNat 64 0x901 = _
      rw [hhi, BitVec.ofNat_add_ofNat, twLo_idx _ _ (by decide) hil]; congr 1; omega
    · rw [hlook 0x1C0 (by omega), look_some (e := nbW0E) (by decide +kernel)]; exact nbw
    · intro i hi
      rw [hlook _ (by unfold PSB; omega), (setup_blk i hi).1]; exact nbw
    · intro a ha
      have ha' : a < 2 ^ 64 := by have := halfP_lt a ha; omega
      rw [hlook a ha']
      have key : memLook psetupMem a = some (stW0 a idxE) := by
        simp only [halfP, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, List.mem_map,
          List.mem_range] at ha
        rcases ha with (rfl | rfl) | ⟨i, hi, rfl⟩
        · exact look_some (by decide +kernel)
        · exact look_some (by decide +kernel)
        · exact (setup_blk i hi).2
      rw [key]
      exact stW0_low s a idxE _ hidx (by omega)
    · rw [hlook 0x240 (by omega), look_some (e := .c (-1#64)) (by decide +kernel)]; rfl
    · intro r hr
      by_cases h15 : r < 15
      · rw [hlook _ (by unfold PIND; omega), setup_pind r h15]
        show (pindE r).eval s = _
        rw [pindE_eval P.A s hw r h15]
        congr 1
        simp only [PCtx.v, leavesOf, porsK]
        rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_eq_getElem?_getD, List.getElem?_map,
          List.getElem?_range (by omega)]
        simp [leafOf, totalH, porsH]
      · have : r = 15 := by omega
        subst this
        rw [hlook _ (by unfold PIND; omega), look_some (e := cw 0x4000) (by decide +kernel)]
        simp only [PCtx.v, leavesOf, porsK, cw, Rv.E.eval]
        rw [List.getD_append_right _ _ _ _ (by simp)]
        simp [porsT, porsH]
  refine ⟨u, hu.steps, S, ⟨⟨⟨fun p hp => hK' p (by simp [setupPost] at hp ⊢; tauto), PFrame.refl u⟩, S, ?_⟩,
    hu.pc rfl, ?_, ?_, ?_, fun i hi => by simp at hi, fun h => by omega, ?_⟩⟩
  · rw [hu.regs (.x22, idxE) (by simp [setupSpec]), hidx]
  · rw [hK' (.x14, 0x830) (by simp [setupPost])]; rfl
  · rw [hK' (.x29, 0) (by simp [setupPost])]; rfl
  · rw [hK' (.x15, BitVec.ofNat 64 EMPTY) (by simp [setupPost])]; rfl
  · simp [SegBnd, wStream, wSec, porsK]

end SigGolfCandidate.Verify
