import SigGolfCandidate.Verify.Arith2
import SigGolfCandidate.Verify.FoldSem

/-! # Hypertree layers: route + encoding, encoding check, leaf, fold setup -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

macro "bvne" : tactic => `(tactic| (intro h; have h' := congrArg BitVec.toNat h; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at h'; omega))

structure LCtx where
  wl : List Byte
  pk : List Byte
  lay : Nat
  idx : Nat

def LCtx.ok (L : LCtx) : Prop := L.lay < 7 ∧ L.idx < 2 ^ 34 ∧ L.wl.length = 7756
def LCtx.e (L : LCtx) : Nat := L.idx / 2 ^ layS L.lay % 2 ^ layH L.lay
def LCtx.tau (L : LCtx) : Nat := L.idx / 2 ^ (layS L.lay + layH L.lay)

def LayerIn (L : LCtx) (M : Val) (s : MachineState) : Prop :=
  Glob L.wl L.pk s ∧ KnownOK globK s ∧ s.getReg .x22 = BitVec.ofNat 64 L.idx ∧
  s.getMem (BitVec.ofNat 64 0x120) = vw0 M ∧ s.getMem (BitVec.ofNat 64 0x128) = vw1 M ∧
  M.length = 16 ∧ s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧
  s.pc = pcOf (layerPc L.lay)

def EncOut (L : LCtx) (a : BitVec 256) (s : MachineState) : Prop :=
  Glob L.wl L.pk s ∧ KnownOK encK s ∧ s.getReg .x22 = BitVec.ofNat 64 L.idx ∧
  s.getReg .x23 = BitVec.ofNat 64 L.e ∧ s.getReg .x30 = BitVec.ofNat 64 L.tau ∧
  s.getReg .x31 = BitVec.ofNat 64 (L.tau + 2 ^ 32 * L.e) ∧
  s.getMem (BitVec.ofNat 64 0x140) = a.extractLsb' 0 64 ∧
  s.getMem (BitVec.ofNat 64 0x148) = a.extractLsb' 64 64 ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧
  s.pc = pcOf (encPostPc L.lay)

theorem layerCheck_at (lay : Nat) (h : lay < 7) : layerCheck lay = true := by
  have := layerCheck_all
  simp only [List.all_eq_true, List.mem_range] at this
  exact this lay h

theorem okRunK_spec {o : Option PRes} {e : PRes} {post : List (Reg × Word)} {keep : List Reg}
    (h : okRunK o e post keep = true) :
    o = some e ∧ resOK e = true ∧ knownB post e = true ∧ keepB keep e = true := by
  simp only [okRunK, Bool.and_eq_true] at h
  exact ⟨optBeq_eq h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem e_lt (L : LCtx) (hL : L.ok) : L.e < 32 := by
  unfold LCtx.e
  have := Nat.mod_lt (L.idx / 2 ^ layS L.lay) (show 0 < 2 ^ layH L.lay from Nat.two_pow_pos _)
  have : 2 ^ layH L.lay ≤ 32 := by
    calc 2 ^ layH L.lay ≤ 2 ^ 5 := Nat.pow_le_pow_right (by decide) (layH_le _)
      _ = 32 := rfl
  omega

theorem enc_step (L : LCtx) (hL : L.ok) (M : Val) (s : MachineState) (hs : LayerIn L M s) :
    ∃ t, Steps image s (encSteps L.lay) (encSteps L.lay) t ∧ fetch image t = some (.base .ECALL) ∧
      t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = pad64 (encInput L.lay L.tau L.e M (witCounter L.wl L.lay)) ∧
      ∀ a, EncOut L a (writeHash t a) := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  have hchk := layerCheck_at L.lay hlay
  simp only [layerCheck, Bool.and_eq_true] at hchk
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okRunK_spec hchk.1.1.1.1.1
  obtain ⟨hG, hK, h22, hM0, hM1, hMl, hF0, hF8, hpc⟩ := hs
  set r := encExp L.lay with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, encExp])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0x100 := hK' (.x10, 0x100) (by simp [encK])
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, 64) (by simp [encK])
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 0x140 := hK' (.x12, 0x140) (by simp [encK])
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0x138⟩, .c 0),
     (⟨none, BitVec.ofNat 64 0x130⟩, .bin (.st .w 4) (stW0 0x130 (ctrE L.lay)) (.c 0)),
     (⟨none, BitVec.ofNat 64 0x108⟩, x31E L.lay),
     (⟨none, BitVec.ofNat 64 0x100⟩, cw (0x401 + 65536 * L.lay))] := by simp [hr, encExp]
  have hx31 : (x31E L.lay).eval s = BitVec.ofNat 64 (L.tau + 2 ^ 32 * L.e) :=
    x31E_eval L.lay L.idx hlay hidx s h22
  have htau : L.tau < 2 ^ 30 := tau_lt L.lay L.idx hlay hidx
  have he := e_lt L ⟨hlay, hidx, hwl⟩
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0x138 → A ≠ 0x130 → A ≠ 0x108 → A ≠ 0x100 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by
      rw [hmem]; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp <;> omega)]
  refine ⟨r.toState s, hst, hec rfl, hK' (.x5, 0) (by simp [encK, globK]),
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide), ?_, ?_⟩
  · rw [hashInput_ofNat _ 0x100 0 h10 h11 (by decide) (by decide), pad64_encInput _ _ _ _ hMl]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero]
    simp only [List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne),
        memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
        memEval_cons_eq _ _ _ _ _ rfl]
      simp only [Rv.E.eval, cw]
      congr 1; unfold twLo; rw [Nat.div_eq_of_lt (by omega : L.tau < 2 ^ 32)]; omega
    · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne),
        memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl, hx31]
      congr 1; unfold twHi; omega
    · rw [mfr 0x110 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0x118 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0x120 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hM0
    · rw [mfr 0x128 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hM1
    · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne),
        memEval_cons_eq _ _ _ _ _ rfl]
      apply BitVec.eq_of_toNat_eq
      simp only [Rv.E.eval, BinOp.eval, stW0, ldE, cw]
      rw [merge_w4_toNat, merge_w0_toNat, ctrE_eval L.lay hlay L.wl hwl s hG.2.1]
      have := witCounter_lt L.wl L.lay
      simp only [BitVec.toNat_ofNat, BitVec.toNat_zero]
      generalize witCounter L.wl L.lay = W at *
      norm_num at this ⊢
      rw [show BitVec.toNat (0 : Word) = 0 from rfl]
      omega
    · rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]; rfl
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x140 ∨ 0x140 + 32 ≤ A) =>
      writeHash_frame _ a 0x140 A h12 hA (by omega) h
    refine ⟨Glob_writeHash (hglob _ _ hG) a _ h12 (by decide), Known_writeHash hK' a, ?_, ?_, ?_, ?_,
      writeHash_at0 _ a _ h12 (by omega), writeHash_at8 _ a _ h12 (by omega), ?_, ?_, ?_⟩
    · rw [writeHash_getReg, hkeep' .x22 (by simp)]; exact h22
    · rw [writeHash_getReg, PRes.toState_getReg]; simp only [hr, encExp]
      simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
      rw [uE_eval L.lay L.idx hlay hidx s h22]; rfl
    · rw [writeHash_getReg, PRes.toState_getReg]; simp only [hr, encExp]
      simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
      rw [tauE_eval L.lay L.idx hlay hidx s h22]; rfl
    · rw [writeHash_getReg, PRes.toState_getReg]; simp only [hr, encExp]
      rw [RegFile.get_set_self _ _ (by decide), hx31]
    · rw [wf 0xF0 (by omega) (by omega), mfr 0xF0 (by omega) (by omega) (by omega) (by omega)
        (by omega)]; exact hF0
    · rw [wf 0xF8 (by omega) (by omega), mfr 0xF8 (by omega) (by omega) (by omega) (by omega)
        (by omega)]; exact hF8
    · rw [writeHash_pc, PRes.toState_pc]; simp only [hr, encExp]; rw [pcOf_add4]; rfl

/-! ## The encoding check -/

def LCtx.cctx (L : LCtx) (a : BitVec 256) : CCtx :=
  ⟨L.wl, L.pk, L.lay, L.tau, L.e, L.idx, a.extractLsb' 0 64, a.extractLsb' 64 64⟩

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

theorem Good.reject {s : MachineState} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) : Good s 1 1 (pure (false, 0)) := by
  have := Good.halt hf h5
  rw [h10] at this
  exact this

theorem encpost_step (L : LCtx) (hL : L.ok) (a : BitVec 256) (s : MachineState) (hs : EncOut L a s) :
    (decodeDigits (answerBytes 16 a) = none →
      ∃ k, k ≤ 28 ∧ ∃ t, Steps image s k k t ∧ fetch image t = some (.base .ECALL) ∧
        t.getReg .x5 = 1 ∧ t.getReg .x10 = 1) ∧
    (∀ xs, decodeDigits (answerBytes 16 a) = some xs →
      ∃ t, Steps image s (encPostSteps L.lay) (encPostSteps L.lay) t ∧ HeadInv (L.cctx a) 0 [] t ∧
        (∀ i < 42, xs.getD i 0 = dig (L.cctx a) i) ∧ xs.sum = 170 ∧ xs.length = 42) := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  have hchk := layerCheck_at L.lay hlay
  simp only [layerCheck, Bool.and_eq_true] at hchk
  obtain ⟨hG, hK, h22, h23, h30, h31, hD0, hD1, hF0, hF8, hpc⟩ := hs
  have hor : CmpOp.lt.eval (orE.eval s) ((E.c 0).eval s) =
      decide (2 ^ 63 ≤ (a.extractLsb' 0 64).toNat ∨ 2 ^ 63 ≤ (a.extractLsb' 64 64).toNat) := by
    rw [show orE.eval s = s.getMem (BitVec.ofNat 64 0x140) ||| s.getMem (BitVec.ofNat 64 0x148) from rfl,
      hD0, hD1]
    exact lt_or_eval _ _
  have hsw : swX25.eval s = 0 ↔ swarOf (a.extractLsb' 0 64).toNat (a.extractLsb' 64 64).toNat = 170 := by
    rw [swX25_eq_zero]; simp only [dA, dB, hD0, hD1]
  unfold decodeDigits
  simp only [slice0_answer, slice8_answer]
  constructor
  · intro hnone
    by_cases hlt : (a.extractLsb' 0 64).toNat < 2 ^ 63 ∧ (a.extractLsb' 64 64).toNat < 2 ^ 63
    · -- digit sum check fails
      rw [if_pos hlt] at hnone
      have hsum : ¬ (digitsOfWord (a.extractLsb' 0 64).toNat ++ digitsOfWord (a.extractLsb' 64 64).toNat).sum
          = target := by intro h; rw [if_pos h] at hnone; cases hnone
      have hrun := optBeq_eq hchk.1.1.2
      obtain ⟨hst, hec⟩ := run_post' (r := encRej2Exp) hrun rfl s hpc hK (by
        intro b hb
        simp only [encRej2Exp, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · rw [br_ne_zero]
          apply decide_eq_true
          intro h0; apply hsum
          rw [← swar_nat _ _ hlt.1 hlt.2]; exact hsw.mp h0
        · simp only [Br.holds]; rw [hor]; exact decide_eq_false (by omega))
      exact ⟨28, le_refl _, _, hst, hec rfl, rfl, rfl⟩
    · have hrun := optBeq_eq hchk.1.1.1.2
      obtain ⟨hst, hec⟩ := run_post' (r := encRej1Exp) hrun rfl s hpc hK (by
        intro b hb
        simp only [encRej1Exp, List.mem_cons, List.not_mem_nil, or_false] at hb
        subst hb
        simp only [Br.holds]; rw [hor]; exact decide_eq_true (by omega))
      exact ⟨7, by omega, _, hst, hec rfl, rfl, rfl⟩
  · intro xs hxs
    by_cases hlt : (a.extractLsb' 0 64).toNat < 2 ^ 63 ∧ (a.extractLsb' 64 64).toNat < 2 ^ 63
    · rw [if_pos hlt] at hxs
      by_cases hsum : (digitsOfWord (a.extractLsb' 0 64).toNat ++
          digitsOfWord (a.extractLsb' 64 64).toNat).sum = target
      · rw [if_pos hsum] at hxs
        cases hxs
        obtain ⟨hrun, hok, hkn, hkeep⟩ := okRunK_spec hchk.1.1.1.1.2
        set r := encOkExp L.lay with hr
        obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by
          intro b hb
          simp only [hr, encOkExp, List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · rw [br_ne_zero]
            apply decide_eq_false
            exact not_not.mpr (hsw.mpr (by rw [swarOf, swar_nat _ _ hlt.1 hlt.2]; exact hsum))
          · simp only [Br.holds]; rw [hor]; exact decide_eq_false (by omega))
        have hK' := knownB_ok hkn s
        have hkeep' := keepB_ok hkeep s
        have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0xC8⟩, .reg .x31),
            (⟨none, BitVec.ofNat 64 0xC0⟩, stW0 0xC0 (cw (0x101 + 65536 * L.lay)))] := by
          simp [hr, encOkExp]
        have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0xC8 → A ≠ 0xC0 →
            (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
          intro A hA h1 h2
          rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by
            rw [hmem]; simp only [List.mem_cons, List.not_mem_nil, or_false]
            rintro p (rfl | rfl) <;> simp <;> omega)]
        refine ⟨r.toState s, hst, ⟨hglob _ _ hG, hK', ?_, ?_, ?_, ?_, fun j hj => by simp at hj, rfl,
          by simp, ?_⟩, ?_, hsum, by simp [digitsOfWord]⟩
        · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [PRes.toState_getReg]; simp only [hr, encOkExp]
            simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
            exact hD0
          · rw [PRes.toState_getReg]; simp only [hr, encOkExp]
            simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
            exact hD1
          · rw [hkeep' .x22 (by simp)]; exact h22
          · rw [hkeep' .x23 (by simp)]; exact h23
          · rw [hkeep' .x30 (by simp)]; exact h30
          · rw [hkeep' .x31 (by simp)]; exact h31
        · refine ⟨?_, ?_⟩
          · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne),
              memEval_cons_eq _ _ _ _ _ rfl]
            simp only [stW0, ldE, cw, Rv.E.eval, BinOp.eval]
            rw [merge_w0_toNat, BitVec.toNat_ofNat]
            simp only [LCtx.cctx]
            norm_num
            omega
          · rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
            simp only [Rv.E.eval]; exact h31
        · rw [mfr 0xF0 (by omega) (by omega) (by omega)]; exact hF0
        · rw [mfr 0xF8 (by omega) (by omega) (by omega)]; exact hF8
        · rw [PRes.toState_pc]; simp [hr, encOkExp, headOrLeaf, LCtx.cctx]
        · intro i hi
          rw [digits_getD _ _ i hi]; unfold dig LCtx.cctx; split <;> rfl
      · rw [if_neg hsum] at hxs; cases hxs
    · rw [if_neg hlt] at hxs; cases hxs

end SigGolfCandidate.Verify
