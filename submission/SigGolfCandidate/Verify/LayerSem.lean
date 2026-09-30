import SigGolfCandidate.Verify.LayArith
import SigGolfCandidate.Verify.LayerCheck
import SigGolfCandidate.Verify.ChainHead

/-! # Hypertree layers: route + encoding, encoding check and dispatch of chain 0 -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

structure LCtx where
  wl : List Byte
  pk : List Byte
  lay : Nat
  idx : Nat

def LCtx.ok (L : LCtx) : Prop := L.lay < 5 ∧ L.idx < 2 ^ 34 ∧ L.wl.length = 6404
def LCtx.e (L : LCtx) : Nat := L.idx / 2 ^ layS L.lay % 2 ^ heightL L.lay
def LCtx.tau (L : LCtx) : Nat := L.idx / 2 ^ (layS L.lay + heightL L.lay)
def LCtx.gk (L : LCtx) : List (Reg × Word) := if L.lay = 4 then gkF else gkL

/-- At the start of the precode of layer `lay` (either stream), with the message `M` in EB+32. -/
def LayerIn (L : LCtx) (M : Val) (s : MachineState) : Prop :=
  Glob L.gk L.wl L.pk s ∧ KnownOK (preK L.lay) s ∧
  s.getReg (routeReg L.lay) = BitVec.ofNat 64 (routeIn L.idx L.lay) ∧
  s.getMem (BitVec.ofNat 64 0x120) = vw0 M ∧ s.getMem (BitVec.ofNat 64 0x128) = vw1 M ∧
  M.length = 16 ∧ (L.lay < 4 → CBZ s) ∧ (s.getMem (BitVec.ofNat 64 0xC0)).toNat / 2 ^ 48 = 0 ∧
  ∃ t, t < 2 ∧ s.pc = pcOf (preStart L.lay t)

/-- After the encoding hash (answer `a` in EO). -/
def EncOut (L : LCtx) (t : Nat) (a : BitVec 256) (s : MachineState) : Prop :=
  Glob gkL L.wl L.pk s ∧ KnownOK (bK L.lay) s ∧
  s.getReg .x23 = BitVec.ofNat 64 (L.e + 2 ^ heightL L.lay) ∧ s.getReg .x30 = BitVec.ofNat 64 L.tau ∧
  s.getReg .x31 = BitVec.ofNat 64 (L.tau + 2 ^ 32 * L.e) ∧
  s.getMem (BitVec.ofNat 64 320) = a.extractLsb' 0 64 ∧
  s.getMem (BitVec.ofNat 64 328) = a.extractLsb' 64 64 ∧
  (L.lay < 4 → CBZ s) ∧ (s.getMem (BitVec.ofNat 64 0xC0)).toNat / 2 ^ 48 = 0 ∧
  s.pc = pcOf (encPc L.lay t + 1)

/-! ## The per-layer check, by parts -/

section
variable {lay : Nat} (hl : lay < 5)
include hl

theorem lc_stream {t : Nat} (ht : t < 2) :
    specB gkL (runAt (preK lay) [] (preStart lay t) []) (specA lay t) (bK lay) [] = true ∧
    specB gkL (runAt (bK lay) [] (encPc lay t + 1) [.br false, .br false, .jmp]) (specBok lay t)
      (chKa lay) [.x22, .x23, .x30, .x31] = true ∧
    specB [] (runAt (bK lay) [] (encPc lay t + 1) [.br true]) specRej1 [] [] = true ∧
    specB [] (runAt (bK lay) [] (encPc lay t + 1) [.br false, .br true]) specRej2 [] [] = true ∧
    (lay = 0 → specB [] (runAt cmpK [] (cmpPc t) [.br false, .br false]) (specAcc t) [] [] = true ∧
      specB [] (runAt cmpK [] (cmpPc t) [.br true]) (specCR1 t) [] [] = true ∧
      specB [] (runAt cmpK [] (cmpPc t) [.br false, .br true]) (specCR2 t) [] [] = true) := by
  have h := layerCheck_at lay hl
  simp only [layerCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h.1 t ht
  refine ⟨h1, h2, h3, h4, fun h0 => ?_⟩
  subst h0
  simp only [bne_self_eq_false, Bool.false_or, Bool.and_eq_true] at h5
  exact ⟨h5.1.1, h5.1.2, h5.2⟩

theorem lc_leaf (d : Bool) :
    specB gkL (runAt (headK lay 42) [] (nextPc' lay 41) [.br d]) (specLeaf lay d)
      (leafPost lay) leafKeep = true := by
  have h := layerCheck_at lay hl
  simp only [layerCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  cases d
  · simpa using h.2 0 (by omega)
  · simpa using h.2 1 (by omega)

end

theorem e_lt (L : LCtx) (hL : L.ok) : L.e < 2048 := e_lt32 L.lay L.idx hL.1

theorem hWord_lt (lay : Nat) (h : lay < 5) : hWord lay < 2 ^ 32 := by unfold hWord; omega

/-! ## Route and encoding -/

theorem enc_step (L : LCtx) (hL : L.ok) (M : Val) (s : MachineState) (hs : LayerIn L M s) :
    ∃ t, t < 2 ∧ ∃ u, Steps image s (stepsA L.lay) (stepsA L.lay) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧
      hashInput u = pad64 (encInput L.lay L.tau L.e M (witCounter L.wl L.lay)) ∧
      ∀ a, EncOut L t a (writeHash u a) := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  obtain ⟨hG, hK, hR, hM0, hM1, hMl, hZ, hC0, t, ht, hpc⟩ := hs
  obtain ⟨u, hu⟩ := spec_run (lc_stream hlay ht).1 s hpc hK (by simp [specA])
  have hK' := hu.known
  have gk : ∀ p ∈ gkL, p ∈ bK L.lay := fun p hp => by simp [bK, hp]
  have h10 : u.getReg .x10 = BitVec.ofNat 64 0x100 := hK' (.x10, 0x100) (by simp [bK])
  have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, 64) (by simp [bK])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 0x140 := hK' (.x12, 0x140) (by simp [bK])
  have hx31 : (x31Er L.lay).eval s = BitVec.ofNat 64 (L.tau + 2 ^ 32 * L.e) :=
    x31Er_eval L.idx L.lay hlay hidx s hR
  have htau : L.tau < 2 ^ 30 := tau_lt L.lay L.idx hlay hidx
  have he := e_lt L ⟨hlay, hidx, hwl⟩
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have hmem := hu.mem
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 312 → A ≠ 304 → A ≠ 264 → A ≠ 256 →
      u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [hmem, memEval_frame_ofNat _ _ _ hA (by
      simp only [specA, List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp <;> omega)]
  have hm : ∀ A, u.getMem A = memEval s (specA L.lay t).mem A := hmem
  refine ⟨t, ht, u, hu.steps, hu.ecall rfl, hK' (.x5, 0) (gk _ (by simp [gkL, baseK])),
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide), ?_, ?_⟩
  · rw [hashInput_ofNat _ 0x100 0 h10 h11 (by decide) (by decide), pad64_encInput _ _ _ _ hMl]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero, List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [hm]; simp only [specA]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
        memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
      simp only [Rv.E.eval, cw]
      congr 1; unfold twLo hWord; rw [Nat.div_eq_of_lt (by omega : L.tau < 2 ^ 32)]; omega
    · rw [hm]; simp only [specA]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
        memEval_cons_eq _ _ _ _ _ rfl, hx31]
      congr 1; unfold twHi; omega
    · rw [mfr 0x110 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0x118 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0x120 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hM0
    · rw [mfr 0x128 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hM1
    · rw [hm]; simp only [specA]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
      apply BitVec.eq_of_toNat_eq
      rw [ctrE_eval L.lay hlay L.wl hwl s hG.2.1, BitVec.toNat_ofNat]
      have := witCounter_lt L.wl L.lay
      omega
    · rw [hm]; simp only [specA]; rw [memEval_cons_eq _ _ _ _ _ rfl]; rfl
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x140 ∨ 0x140 + 32 ≤ A) =>
      writeHash_frame _ a 0x140 A h12 hA (by omega) h
    refine ⟨Glob_writeHash (hu.glob _ _ _ hG) a _ h12 (by decide), Known_writeHash hK' a, ?_, ?_, ?_,
      writeHash_at0 _ a _ h12 (by omega), writeHash_at8 _ a _ h12 (by omega), ?_, ?_, ?_⟩
    · rw [writeHash_getReg, hu.regs (.x23, uHE L.lay) (by simp [specA]), uHE_eval L.idx L.lay hlay hidx s hR]
      rfl
    · rw [writeHash_getReg, hu.regs (.x30, tauEr L.lay) (by simp [specA]), tauEr_eval L.idx L.lay hlay hidx s hR]
      rfl
    · rw [writeHash_getReg, hu.regs (.x31, x31Er L.lay) (by simp [specA]), hx31]
    · intro h6
      exact ⟨by rw [wf 0xE0 (by omega) (by omega), mfr 0xE0 (by omega) (by omega) (by omega) (by omega)
          (by omega)]; exact (hZ h6).1,
        by rw [wf 0xE8 (by omega) (by omega), mfr 0xE8 (by omega) (by omega) (by omega) (by omega)
          (by omega)]; exact (hZ h6).2⟩
    · rw [wf 0xC0 (by omega) (by omega), mfr 0xC0 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hC0
    · rw [writeHash_pc, hu.pc rfl, pcOf_add4]; rfl


/-! ## The encoding check and the dispatch of chain 0 -/

def LCtx.cctx (L : LCtx) (a : BitVec 256) : CCtx :=
  ⟨L.wl, L.pk, L.lay, L.tau, L.e, a.extractLsb' 0 64, a.extractLsb' 64 64⟩

theorem slice0_answer (a : BitVec 256) : leNat (slice (answerBytes 16 a) 0 8) = (a.extractLsb' 0 64).toNat := by
  rw [← vw0_answer, vw0, w64_toNat _ (by simp)]; rfl

theorem slice8_answer (a : BitVec 256) : leNat (slice (answerBytes 16 a) 8 8) = (a.extractLsb' 64 64).toNat := by
  rw [← vw1_answer, vw1, w64_toNat _ (by simp)]
  simp only [slice]
  rw [List.take_of_length_le (by simp)]

theorem digits_getD (d0 d1 : Nat) (i : Nat) (hi : i < 42) :
    (digitsOfWord d0 ++ digitsOfWord d1).getD i 0 =
      (if i < 21 then d0 else d1) / 8 ^ (i % 21) % 8 := by
  simp only [List.getD_eq_getElem?_getD, digitsOfWord]
  split
  · rw [List.getElem?_append_left (by simp; omega)]
    simp [List.getElem?_map, show i < 21 by omega, Nat.mod_eq_of_lt (show i < 21 by omega)]
  · rw [List.getElem?_append_right (by simp; omega), show i % 21 = i - 21 by omega]
    simp [List.getElem?_map, show i - 21 < 21 by omega]

theorem maskD0_eval (s : MachineState) (D : E) (W : Word) (hD : D.eval s = W) :
    (maskD 0 D).eval s = BitVec.ofNat 64 (16 * maskV 0 W.toNat) := by
  simp only [maskD, maskV, show isSingle 0 = false from rfl, if_false, Bool.false_eq_true,
    show 0 % 21 = 0 from rfl, if_true, mkBin_eval, E.eval, BinOp.eval, cw, hD]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [show (1008 : Nat) % 2 ^ 64 = 1008 from rfl, land1008]
  simp only [Nat.reducePow, Nat.reduceMod, Nat.pow_zero, Nat.div_one]
  omega

theorem setup_C0 (lay : Nat) (s : MachineState) :
    memEval s (setupMem lay) (BitVec.ofNat 64 192) =
      (E.bin (.st .b 5) (stW0 192 (cw (hWord lay))) (cw 0)).eval s := by
  unfold setupMem; split <;>
    simp only [List.cons_append, List.nil_append] <;>
    (repeat rw [memEval_cons_ne _ _ _ _ _ (by bvne)]) <;> rw [memEval_cons_eq _ _ _ _ _ rfl]

theorem setup_C8 (lay : Nat) (s : MachineState) :
    memEval s (setupMem lay) (BitVec.ofNat 64 200) = (E.reg .x31).eval s := by
  unfold setupMem; split <;>
    simp only [List.cons_append, List.nil_append] <;>
    (repeat rw [memEval_cons_ne _ _ _ _ _ (by bvne)]) <;> rw [memEval_cons_eq _ _ _ _ _ rfl]

theorem setup_Z6 (lay : Nat) (s : MachineState) (h : lay = 4) (A : Nat) (hA : A = 224 ∨ A = 232) :
    memEval s (setupMem lay) (BitVec.ofNat 64 A) = 0 := by
  subst h
  simp only [setupMem, if_true, List.cons_append, List.nil_append]
  rcases hA with rfl | rfl
  · rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_eq _ _ _ _ _ rfl]; rfl
  · rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]; rfl

theorem setup_fr (lay : Nat) (s : MachineState) (h : lay ≠ 4) (A : Nat) (hA : A < 2 ^ 64)
    (h1 : A ≠ 192) (h2 : A ≠ 200) :
    memEval s (setupMem lay) (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  simp only [setupMem, if_neg h, List.nil_append, List.cons_append]
  rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne)]; rfl

theorem setup_word (lay : Nat) (hlay : lay < 5) (s : MachineState)
    (h48 : (s.getMem (BitVec.ofNat 64 0xC0)).toNat / 2 ^ 48 = 0) :
    ((E.bin (.st .b 5) (stW0 192 (cw (hWord lay))) (cw 0)).eval s).toNat =
      hWord lay + 2 ^ 32 * ((s.getMem (BitVec.ofNat 64 0xC0)).toNat / 2 ^ 32 % 256) := by
  show (StoreKind.merge .b (StoreKind.merge .w (s.getMem (BitVec.ofNat 64 192)) 0 (BitVec.ofNat 64 (hWord lay)))
    5 (BitVec.ofNat 64 0)).toNat = _
  simp only [StoreKind.merge]
  rw [replaceByte_toNat _ _ (by omega)]
  have := merge_w0_toNat (s.getMem (BitVec.ofNat 64 192)) (BitVec.ofNat 64 (hWord lay))
  simp only [StoreKind.merge, show (0 : Nat) / 4 = 0 from rfl] at this
  rw [this]
  have hw := hWord_lt lay hlay
  simp only [BitVec.toNat_ofNat, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth] at h48 ⊢
  generalize (s.getMem (BitVec.ofNat 64 192)).toNat = w at *
  norm_num at hw h48 ⊢
  omega

theorem encpost_step (L : LCtx) (hL : L.ok) (t : Nat) (ht : t < 2) (a : BitVec 256) (s : MachineState)
    (hs : EncOut L t a s) :
    (decodeDigits (answerBytes 16 a) = none →
      ∃ k, k ≤ 27 ∧ ∃ u, Steps image s k k u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (∀ xs, decodeDigits (answerBytes 16 a) = some xs →
      ∃ u, Steps image s (stepsB L.lay) (stepsB L.lay) u ∧ EntInv (L.cctx a) 0 [] u ∧
        (L.cctx a).ok ∧ (∀ i < 42, xs.getD i 0 = dig (L.cctx a) i) ∧ xs.sum = targetSum ∧
        xs.length = 42) := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  obtain ⟨-, hBok, hR1, hR2, -⟩ := lc_stream hlay ht
  obtain ⟨hG, hK, h23, h30, h31, hD0, hD1, hZ, hC0, hpc⟩ := hs
  have hor : CmpOp.lt.eval (orE.eval s) ((E.c 0).eval s) =
      decide (2 ^ 63 ≤ (a.extractLsb' 0 64).toNat ∨ 2 ^ 63 ≤ (a.extractLsb' 64 64).toNat) := by
    rw [show orE.eval s = s.getMem (BitVec.ofNat 64 320) ||| s.getMem (BitVec.ofNat 64 328) from rfl,
      hD0, hD1]
    exact lt_or_eval _ _
  have hdA : dA s = (a.extractLsb' 0 64).toNat := by simp only [dA, hD0]
  have hdB : dB s = (a.extractLsb' 64 64).toNat := by simp only [dB, hD1]
  unfold decodeDigits
  simp only [slice0_answer, slice8_answer]
  constructor
  · intro hnone
    by_cases hlt : (a.extractLsb' 0 64).toNat < 2 ^ 63 ∧ (a.extractLsb' 64 64).toNat < 2 ^ 63
    · rw [if_pos hlt] at hnone
      have hsum : ¬ (digitsOfWord (a.extractLsb' 0 64).toNat ++ digitsOfWord (a.extractLsb' 64 64).toNat).sum
          = target := by intro h; rw [if_pos h] at hnone; cases hnone
      obtain ⟨u, hu⟩ := spec_run hR2 s hpc hK (by
        intro b hb
        simp only [specRej2, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · simp only [Br.holds, CmpOp.eval, bne_iff_ne, ne_eq]
          intro h
          apply hsum
          have := (swS_eq s (by omega) (by omega)).mp h
          rwa [hdA, hdB] at this
        · simp only [Br.holds]; rw [hor]; exact decide_eq_false (by omega))
      exact ⟨27, le_refl _, u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [specRej2, rejK]),
        hu.regs (.x10, cw 1) (by simp [specRej2, rejK])⟩
    · obtain ⟨u, hu⟩ := spec_run hR1 s hpc hK (by
        intro b hb
        simp only [specRej1, List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb
        simp only [Br.holds]; rw [hor]; exact decide_eq_true (by omega))
      exact ⟨7, by omega, u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [specRej1, rejK]),
        hu.regs (.x10, cw 1) (by simp [specRej1, rejK])⟩
  · intro xs hxs
    by_cases hlt : (a.extractLsb' 0 64).toNat < 2 ^ 63 ∧ (a.extractLsb' 64 64).toNat < 2 ^ 63
    · rw [if_pos hlt] at hxs
      by_cases hsum : (digitsOfWord (a.extractLsb' 0 64).toNat ++
          digitsOfWord (a.extractLsb' 64 64).toNat).sum = target
      · rw [if_pos hsum] at hxs
        cases hxs
        obtain ⟨u, hu⟩ := spec_run hBok s hpc hK (by
          intro b hb
          simp only [specBok, List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · simp only [Br.holds, CmpOp.eval, bne_eq_false_iff_eq]
            apply (swS_eq s (by omega) (by omega)).mpr
            rw [hdA, hdB]; exact hsum
          · simp only [Br.holds]; rw [hor]; exact decide_eq_false (by omega))
        set c := L.cctx a with hc
        have hcok : c.ok := ⟨hlay, by have := tau_lt L.lay L.idx hlay hidx; simp [hc, LCtx.cctx, LCtx.tau]; omega,
          by have := e_lt L ⟨hlay, hidx, hwl⟩; simp [hc, LCtx.cctx]; omega, hwl, hlt.1, hlt.2⟩
        have hmem := hu.mem
        obtain ⟨ht4, ht1, htb, hB, -, -⟩ := tabOk_spec (tabOk_at L.lay 0 hlay (by omega))
        have hD0' : d0E.eval s = a.extractLsb' 0 64 := hD0
        have hr0 : (rE0 L.lay).eval s = BitVec.ofNat 64 (rOf c 0) := by
          simp only [rE0, mkBin_eval, BinOp.eval, cw, E.eval]
          rw [maskD0_eval s _ _ hD0', BitVec.ofNat_add_ofNat, rOf,
            entIdx_mask c hcok 0 (by omega) (Or.inl rfl), Nat.add_comm]
          rfl
        have he := entIdx_spec c 0 (by omega)
        have hsn : nEnt 0 ≤ 64 := by decide
        have hoff : chainAddr L.lay 0 = 0x800 + (witLayerOff L.lay + 16 * 0) := by
          unfold chainAddr; rw [witLayerOff_eq _ hlay]; omega
        have hlb := layBody_le _ hlay
        have hw0 := setup_word L.lay hlay s hC0
        refine ⟨u, hu.steps, ⟨hu.glob _ _ _ hG, hu.known, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ⟨?_, ?_⟩,
          ?_, fun j hj => by simp at hj, rfl, by simp, ?_, ?_, ?_⟩, hcok, ?_, hsum,
          by simp [digitsOfWord]⟩
        · rw [hu.regs (.x16, d0E) (by simp [specBok])]; exact hD0
        · rw [hu.regs (.x17, d1E) (by simp [specBok])]; exact hD1
        · rw [hu.keep .x23 (by simp)]; exact h23
        · rw [hu.keep .x30 (by simp)]; exact h30
        · rw [hu.keep .x31 (by simp)]; exact h31
        · rw [hmem]; simp only [specBok]; rw [setup_C0, hw0]
          simp only [hc, LCtx.cctx, hWord]; omega
        · rw [hmem]; simp only [specBok]; rw [setup_C8]; simp only [E.eval]; rw [h31]; rfl
        · rw [hmem]; simp only [specBok]; rw [setup_C0, hw0]; unfold hWord; omega
        · unfold CBi; rw [hmem]; simp only [specBok]; rw [setup_C0, hw0]; unfold hWord; omega
        · rw [hu.regs (.x15, cw (bVal L.lay 0)) (by simp [specBok])]; rfl
        · rw [hu.regs (.x14, rE0 L.lay) (by simp [specBok]), hr0]
        · by_cases h6 : L.lay = 4
          · unfold CBZ; rw [hmem, hmem]; simp only [specBok]
            exact ⟨setup_Z6 _ _ h6 224 (by omega), setup_Z6 _ _ h6 232 (by omega)⟩
          · unfold CBZ; rw [hmem, hmem]; simp only [specBok]
            rw [setup_fr _ _ h6 0xE0 (by omega) (by omega) (by omega),
              setup_fr _ _ h6 0xE8 (by omega) (by omega) (by omega)]
            exact hZ (by omega)
        · rw [hu.regs (.x1, ldE (chainAddr L.lay 0)) (by simp [specBok])]
          simp only [ldE, cw, E.eval, hc, LCtx.cctx]
          rw [hoff, wit_word hG.2.1 _ (by have := witLayerOff_eq _ hlay; omega) (by have := witLayerOff_eq _ hlay; omega),
            witChain, vw0_slice]
        · rw [hu.regs (.x2, ldE (chainAddr L.lay 0 + 8)) (by simp [specBok])]
          simp only [ldE, cw, E.eval, hc, LCtx.cctx]
          rw [hoff, show 0x800 + (witLayerOff L.lay + 16 * 0) + 8 = 0x800 + (witLayerOff L.lay + 16 * 0 + 8)
            by omega, wit_word hG.2.1 _ (by have := witLayerOff_eq _ hlay; omega) (by have := witLayerOff_eq _ hlay; omega),
            witChain, vw1_slice]
        · rw [hu.spc _ rfl]
          simp only [mkBin_eval, mkAdd_eval, BinOp.eval, E.eval]
          rw [hr0, rOf, show c.lay = L.lay from rfl, add_sub_ofNat _ _ _ hB (by omega) (by omega),
            even_andNot1 _ (by omega), pcOf_entry _ _ _ ht4 ht1]
        · intro i hi
          rw [digits_getD _ _ i hi]; unfold dig; simp only [hc, LCtx.cctx]; split <;> rfl
      · rw [if_neg hsum] at hxs; cases hxs
    · rw [if_neg hlt] at hxs; cases hxs

end SigGolfCandidate.Verify
