import SigGolfCandidate.Verify.Arith3
import SigGolfCandidate.Verify.FoldCheck
import SigGolfCandidate.Verify.LeafSem

/-! # FORS trees: header (leaf hash), fold setup, folds -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

macro "bvne" : tactic => `(tactic| (intro h; have h' := congrArg BitVec.toNat h; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at h'; omega))

/-- FORS context: witness, public key and the digest answer `a`. -/
structure DCtx where
  wl : List Byte
  pk : List Byte
  a : BitVec 256

def DCtx.A (d : DCtx) : Nat := d.a.toNat
def DCtx.idx (d : DCtx) : Nat := d.A % 2 ^ 34
def DCtx.u (d : DCtx) (k : Nat) : Nat := d.A / 2 ^ (34 + 10 * k) % 1024
def DCtx.fw (d : DCtx) (k : Nat) : Nat := 2305 + 65536 * k + 2 ^ 24 * (d.idx / 2 ^ 32)

def forsHd (k : Nat) : Nat := if k < 14 then forsPc k - 1 else 2085

def RBOk (roots : List Val) (s : MachineState) : Prop :=
  ∀ j, j < roots.length → s.getMem (BitVec.ofNat 64 (0x240 + 16 * j)) = vw0 (roots.getD j []) ∧
    s.getMem (BitVec.ofNat 64 (0x248 + 16 * j)) = vw1 (roots.getD j [])

/-- Registers and memory carried through a FORS tree. -/
def ForsCarry (d : DCtx) (k : Nat) (roots : List Val) (s : MachineState) : Prop :=
  s.getReg .x16 = d.a.extractLsb' 0 64 ∧ s.getReg .x17 = d.a.extractLsb' 64 64 ∧
  s.getReg .x25 = d.a.extractLsb' 128 64 ∧ s.getReg .x22 = BitVec.ofNat 64 d.idx ∧
  s.getReg .x29 = BitVec.ofNat 64 (d.fw k) ∧ s.getReg .x31 = BitVec.ofNat 64 65536 ∧
  (s.getMem (BitVec.ofNat 64 0xC0)).toNat < 2 ^ 32 ∧
  (s.getMem (BitVec.ofNat 64 0xC8)).toNat % 2 ^ 32 = d.idx % 2 ^ 32 ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧
  RBOk roots s ∧ (∀ v ∈ roots, v.length = 16) ∧
  (s.getMem (BitVec.ofNat 64 0x220)).toNat < 2 ^ 32 ∧
  s.getMem (BitVec.ofNat 64 0x228) = BitVec.ofNat 64 (d.idx % 2 ^ 32)

def ForsIn (d : DCtx) (k : Nat) (roots : List Val) (s : MachineState) : Prop :=
  Glob d.wl d.pk s ∧ KnownOK forsK s ∧ ForsCarry d (k - 1) roots s ∧ roots.length = k ∧
  (s.getMem (BitVec.ofNat 64 0x1C8)).toNat % 2 ^ 32 = d.idx % 2 ^ 32 ∧ s.pc = pcOf (forsHd k)

def LeafDoneF (d : DCtx) (k : Nat) (roots : List Val) (v : Val) (s : MachineState) : Prop :=
  Glob d.wl d.pk s ∧ KnownOK forsLeafK s ∧ ForsCarry d k roots s ∧ roots.length = k ∧
  s.getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * (d.u k % 2)) ∧
  s.getReg .x23 = BitVec.ofNat 64 (d.u k) ∧ s.getReg .x24 = BitVec.ofNat 64 (16 * d.u k) ∧
  s.getMem (BitVec.ofNat 64 (0x1E0 + 16 * (d.u k % 2))) = vw0 v ∧
  s.getMem (BitVec.ofNat 64 (0x1E8 + 16 * (d.u k % 2))) = vw1 v ∧ v.length = 16 ∧
  (s.getMem (BitVec.ofNat 64 0x1C8)).toNat % 2 ^ 32 = d.idx % 2 ^ 32 ∧
  s.pc = pcOf (forsPc k - 1 + headSteps k + 1)

theorem forsCheck_at (k : Nat) (hk : k < 14) : forsCheck k = true := by
  have := forsCheck_all
  simp only [List.all_eq_true, List.mem_range] at this
  exact this k hk

theorem d_u_lt (d : DCtx) (k : Nat) : d.u k < 1024 := Nat.mod_lt _ (by decide)
theorem d_idx_lt (d : DCtx) : d.idx < 2 ^ 34 := Nat.mod_lt _ (by decide)

theorem wRegE_eval (d : DCtx) (s : MachineState) (h16 : s.getReg .x16 = d.a.extractLsb' 0 64)
    (h17 : s.getReg .x17 = d.a.extractLsb' 64 64) (h25 : s.getReg .x25 = d.a.extractLsb' 128 64) :
    ∀ i, i < 3 → (wRegE i).eval s = BitVec.ofNat 64 (d.A / 2 ^ (64 * i) % 2 ^ 64) := by
  intro i hi
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
  interval_cases i <;>
    simp [wRegE, Rv.E.eval, h16, h17, h25, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, DCtx.A]

theorem d_fw_lt (d : DCtx) (k : Nat) (hk : k < 14) : d.fw k < 2 ^ 32 := by
  have := d_idx_lt d
  unfold DCtx.fw
  have : d.idx / 2 ^ 32 < 4 := by omega
  omega

theorem uk_eval (d : DCtx) (k : Nat) (hk : k < 14) (s : MachineState)
    (h16 : s.getReg .x16 = d.a.extractLsb' 0 64) (h17 : s.getReg .x17 = d.a.extractLsb' 64 64)
    (h25 : s.getReg .x25 = d.a.extractLsb' 128 64) :
    (uE' k).eval s = BitVec.ofNat 64 (d.u k) :=
  uExprW_eval wRegE d.A s (wRegE_eval d s h16 h17 h25) k hk

theorem header_step (d : DCtx) (hwl : d.wl.length = 7756) (k : Nat) (hk1 : 1 ≤ k) (hk : k < 14)
    (roots : List Val) (s : MachineState) (hs : ForsIn d k roots s) :
    ∃ t, Steps image s (headSteps k) (headSteps k) t ∧ fetch image t = some (.base .ECALL) ∧
      t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = pad64 (ftsLeafInput k d.idx (d.u k) (witFtsSecret d.wl k)) ∧
      ∀ ans, LeafDoneF d k roots (answerBytes 16 ans) (writeHash t ans) := by
  have hchk := forsCheck_at k hk
  simp only [forsCheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hchk
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okRunK_spec (hchk.1.resolve_left (by omega))
  obtain ⟨hG, hK, ⟨h16, h17, h25, h22, h29, h31, hC0, hC8, hF0, hF8, hRB, hrv, hR0, hR8⟩,
    hlen, hN8, hpc⟩ := hs
  have hpc' : s.pc = pcOf (forsPc k - 1) := by rw [hpc, forsHd, if_pos hk]
  set r := headExp k with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc' hK (by simp [hr, headExp])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have hu := uk_eval d k hk s h16 h17 h25
  have hul := d_u_lt d k
  obtain ⟨hgp, hsll⟩ := gpF_eval (uE' k) (d.u k) hul s hu
  have hfwl := d_fw_lt d k hk
  have hfw : (Rv.E.bin .add (.reg .x29) (.reg .x31)).eval s = BitVec.ofNat 64 (d.fw k) := by
    show s.getReg .x29 + s.getReg .x31 = _
    rw [h29, h31, BitVec.ofNat_add_ofNat]; congr 1; unfold DCtx.fw; cases k <;> simp_all <;> omega
  have hidx := d_idx_lt d
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0xC0 := hK' (.x10, 0xC0) (by simp [forsLeafK])
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, 64) (by simp [forsLeafK])
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * (d.u k % 2)) := by
    rw [PRes.toState_getReg]; simp only [hr, headExp]
    simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
    rw [show (Rv.E.bin .add (gpF (uE' k)) (cw 480)).eval s = (gpF (uE' k)).eval s + BitVec.ofNat 64 480
      from rfl, hgp, BitVec.ofNat_add_ofNat]; congr 1; omega
  have sa : 0x800 + 16 + 176 * k = 0x800 + (16 + 176 * k) := by omega
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0xE8⟩, ldE (0x800 + 16 + 176 * k + 8)),
      (⟨none, BitVec.ofNat 64 0xE0⟩, ldE (0x800 + 16 + 176 * k)),
      (⟨none, BitVec.ofNat 64 0xC8⟩, .bin (.st .w 4) (ldE 0xC8) (uE' k)),
      (⟨none, BitVec.ofNat 64 0xC0⟩, stW0 0xC0 (.bin .add (.reg .x29) (.reg .x31)))] := by
    simp [hr, headExp]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0xE8 → A ≠ 0xE0 → A ≠ 0xC8 → A ≠ 0xC0 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by
      rw [hmem]; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp <;> omega)]
  have m0 : (r.toState s).getMem (BitVec.ofNat 64 0xC0) = BitVec.ofNat 64 (d.fw k) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
    apply BitVec.eq_of_toNat_eq
    rw [show (stW0 0xC0 (.bin .add (.reg .x29) (.reg .x31))).eval s =
      StoreKind.merge .w (s.getMem (BitVec.ofNat 64 0xC0)) 0 ((Rv.E.bin .add (.reg .x29) (.reg .x31)).eval s)
      from rfl, merge_w0_toNat, hfw]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.div_eq_of_lt hC0]; omega
  have m8 : (r.toState s).getMem (BitVec.ofNat 64 0xC8) =
      BitVec.ofNat 64 (d.idx % 2 ^ 32 + 2 ^ 32 * d.u k) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_eq _ _ _ _ _ rfl]
    apply BitVec.eq_of_toNat_eq
    rw [show (Rv.E.bin (.st .w 4) (ldE 0xC8) (uE' k)).eval s =
      StoreKind.merge .w (s.getMem (BitVec.ofNat 64 0xC8)) 4 ((uE' k).eval s) from rfl,
      merge_w4_toNat, hu, hC8]
    simp only [BitVec.toNat_ofNat]
    omega
  have hs0 : witFtsSecret d.wl k = slice d.wl (16 + 176 * k) 16 := rfl
  have hsl : (witFtsSecret d.wl k).length = 16 := by rw [hs0]; apply length_slice16; omega
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  refine ⟨r.toState s, hst, hec rfl, hK' (.x5, 0) (by simp [forsLeafK, globK]),
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega), ?_, ?_⟩
  · rw [hashInput_ofNat _ 0xC0 0 h10 h11 (by decide) (by decide), pad64_ftsLeafInput _ _ _ _ hsl]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero, List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [m0]; congr 1; unfold twLo DCtx.fw; omega
    · rw [m8]; congr 1; unfold twHi; omega
    · rw [mfr 0xD0 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0xD8 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
      simp only [ldE, cw, Rv.E.eval]
      rw [sa, wit_word hG.2.1 _ (by omega) (by omega), hs0, vw0_slice]
    · rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
      simp only [ldE, cw, Rv.E.eval]
      rw [show 0x800 + 16 + 176 * k + 8 = 0x800 + (16 + 176 * k + 8) by omega,
        wit_word hG.2.1 _ (by omega) (by omega), hs0, vw1_slice]
    · rw [mfr 0xF0 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF0
    · rw [mfr 0xF8 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF8
  · intro ans
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x1E0 + 16 * (d.u k % 2) ∨ 0x1E0 + 16 * (d.u k % 2) + 32 ≤ A) =>
      writeHash_frame _ ans _ A h12 hA (by omega) h
    have kp : ∀ x ∈ forsKeep, (writeHash (r.toState s) ans).getReg x = s.getReg x := fun x hx => by
      rw [writeHash_getReg]; exact hkeep' x hx
    refine ⟨Glob_writeHash (hglob _ _ hG) ans _ h12 (by
        rcases Nat.mod_two_eq_zero_or_one (d.u k) with h | h <;> rw [h] <;> decide),
      Known_writeHash hK' ans, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrv, ?_, ?_⟩, hlen,
      by rw [writeHash_getReg]; exact h12, ?_, ?_, (writeHash_at0 _ ans _ h12 (by omega)).trans (vw0_answer ans).symm,
      ?_, by simp, ?_, ?_⟩
    · rw [kp .x16 (by simp [forsKeep])]; exact h16
    · rw [kp .x17 (by simp [forsKeep])]; exact h17
    · rw [kp .x25 (by simp [forsKeep])]; exact h25
    · rw [kp .x22 (by simp [forsKeep])]; exact h22
    · rw [writeHash_getReg, PRes.toState_getReg]; simp only [hr, headExp]
      simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
      exact hfw
    · rw [kp .x31 (by simp [forsKeep])]; exact h31
    · rw [wf 0xC0 (by omega) (by omega), m0, BitVec.toNat_ofNat]; omega
    · rw [wf 0xC8 (by omega) (by omega), m8, BitVec.toNat_ofNat]; omega
    · rw [wf 0xF0 (by omega) (by omega), mfr 0xF0 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF0
    · rw [wf 0xF8 (by omega) (by omega), mfr 0xF8 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF8
    · intro j hj
      rw [wf _ (by omega) (by omega), wf _ (by omega) (by omega),
        mfr _ (by omega) (by omega) (by omega) (by omega) (by omega),
        mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hRB j hj
    · rw [wf 0x220 (by omega) (by omega), mfr 0x220 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hR0
    · rw [wf 0x228 (by omega) (by omega), mfr 0x228 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hR8
    · rw [writeHash_getReg, PRes.toState_getReg]; simp only [hr, headExp]
      simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
      exact hu
    · rw [writeHash_getReg, PRes.toState_getReg]; simp only [hr, headExp]
      simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
      exact hsll
    · rw [show 0x1E8 + 16 * (d.u k % 2) = 0x1E0 + 16 * (d.u k % 2) + 8 by omega,
        writeHash_at8 _ ans _ h12 (by omega)]; exact (vw1_answer ans).symm
    · rw [wf 0x1C8 (by omega) (by omega), mfr 0x1C8 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hN8
    · rw [writeHash_pc, PRes.toState_pc]; simp only [hr, headExp]; rw [pcOf_add4]

/-! ## Fold setup and the end of a tree -/

def forsFC (d : DCtx) (k : Nat) : FCtx :=
  ⟨d.wl, d.pk, d.u k, 10, forsFoldPc k, 10, k, d.idx, 32 + 176 * k, 0x240 + 16 * k⟩

theorem forsFC_ok (d : DCtx) (hwl : d.wl.length = 7756) (k : Nat) (hk : k < 14) : (forsFC d k).ok := by
  have := d_u_lt d k
  refine ⟨by simp [forsFC], by simp [forsFC], by simp [forsFC]; omega, by simp [forsFC],
    by simp [forsFC]; omega, hwl, by simp [forsFC]; omega, by simp [forsFC]; omega, ?_,
    by simp [forsFC]; omega, ?_⟩
  · simp only [forsFC]; interval_cases k <;> decide
  · simp only [forsFC]; interval_cases k <;> decide

theorem forsFC_check (d : DCtx) (k : Nat) (hk : k < 14) :
    foldCheck (forsFC d k).base (forsFC d k).h (0x800 + (forsFC d k).sibOff) (forsFC d k).dst = true := by
  have := forsFoldOk_all
  simp only [List.all_eq_true, List.mem_range] at this
  have h := this k hk
  simp only [forsFoldOk] at h
  simp only [forsFC]
  rw [show 0x800 + (32 + 176 * k) = 0x800 + 32 + 176 * k by omega]
  exact h

theorem fsetupF_step (d : DCtx) (k : Nat) (hk : k < 14) (roots : List Val) (v : Val)
    (s : MachineState) (hs : LeafDoneF d k roots v s) :
    ∃ t, Steps image s 3 3 t ∧ FoldInv (forsFC d k) t 0 v t ∧ ForsCarry d k roots t ∧
      roots.length = k := by
  have hchk := forsCheck_at k hk
  simp only [forsCheck, Bool.and_eq_true] at hchk
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okRunK_spec hchk.2
  obtain ⟨hG, hK, ⟨h16, h17, h25, h22, h29, h31, hC0, hC8, hF0, hF8, hRB, hrv, hR0, hR8⟩, hlen,
    h12, h23, h24, hv0, hv1, hvl, hN8, hpc⟩ := hs
  set r := fsetupFExp k with hr
  obtain ⟨hst, -, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, fsetupFExp])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have hfwl := d_fw_lt d k hk
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0x1C0⟩, stW0 0x1C0 (.bin .add (.reg .x29) (cw 256)))] := by
    simp [hr, fsetupFExp]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0x1C0 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by rw [hmem]; simp; omega)]
  have h12' : (r.toState s).getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * (d.u k % 2)) := by
    rw [PRes.toState_getReg]
    have : r.st.regs.get .x12 = .reg .x12 := by simp only [hr, fsetupFExp]; rfl
    rw [this]; exact h12
  have hbit : bitOf (d.u k) 0 = d.u k % 2 := by simp [bitOf]
  have kp : ∀ x, x ∈ forsKeep ++ [.x23, .x24, .x29] → (r.toState s).getReg x = s.getReg x := hkeep'
  refine ⟨r.toState s, hst, ⟨hglob _ _ hG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hvl,
    ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrv, ?_, ?_⟩, hlen⟩
  · intro p hp
    simp only [foldK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp | hp | hp
    · exact hK' p (by simp [hp])
    · subst hp; exact hK' _ (by simp)
    · subst hp; exact hK' _ (by simp)
    · subst hp; rw [h12']; simp [forsFC, hbit]
  · rw [kp .x23 (by simp [forsKeep])]; exact h23
  · rw [kp .x24 (by simp [forsKeep])]; exact h24
  · rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
    rw [show (stW0 0x1C0 (.bin .add (.reg .x29) (cw 256))).eval s =
      StoreKind.merge .w (s.getMem (BitVec.ofNat 64 0x1C0)) 0 (s.getReg .x29 + BitVec.ofNat 64 256)
      from rfl, merge_w0_toNat, h29, BitVec.ofNat_add_ofNat]
    simp only [BitVec.toNat_ofNat, FCtx.lo0, forsFC, DCtx.fw]
    have := d_idx_lt d
    have : d.idx / 2 ^ 32 < 4 := by omega
    omega
  · rw [mfr 0x1C8 (by omega) (by omega)]; exact hN8
  · simp only [forsFC, hbit]; rw [mfr _ (by omega) (by omega)]; exact hv0
  · simp only [forsFC, hbit]; rw [mfr _ (by omega) (by omega)]; exact hv1
  · rw [PRes.toState_pc]; simp [hr, fsetupFExp, forsFC, foldPc]
  · rw [kp .x16 (by simp [forsKeep])]; exact h16
  · rw [kp .x17 (by simp [forsKeep])]; exact h17
  · rw [kp .x25 (by simp [forsKeep])]; exact h25
  · rw [kp .x22 (by simp [forsKeep])]; exact h22
  · rw [kp .x29 (by simp [forsKeep])]; exact h29
  · rw [kp .x31 (by simp [forsKeep])]; exact h31
  · rw [mfr 0xC0 (by omega) (by omega)]; exact hC0
  · rw [mfr 0xC8 (by omega) (by omega)]; exact hC8
  · rw [mfr 0xF0 (by omega) (by omega)]; exact hF0
  · rw [mfr 0xF8 (by omega) (by omega)]; exact hF8
  · intro j hj; rw [mfr _ (by omega) (by omega), mfr _ (by omega) (by omega)]; exact hRB j hj
  · rw [mfr 0x220 (by omega) (by omega)]; exact hR0
  · rw [mfr 0x228 (by omega) (by omega)]; exact hR8

theorem forsHd_link (k : Nat) (hk : k < 14) :
    foldPc (forsFoldPc k) (10 - 1) + 9 + 1 = forsHd (k + 1) := by
  interval_cases k <;> decide

theorem tree_end (d : DCtx) (k : Nat) (hk : k < 14) (roots : List Val) (t u : MachineState)
    (hc : ForsCarry d k roots t) (hlen : roots.length = k) (hu : FoldEnd (forsFC d k) t u)
    (ans : BitVec 256) : ForsIn d (k + 1) (roots ++ [answerBytes 16 ans]) (writeHash u ans) := by
  obtain ⟨hG, hK, hF, hpc, -, hN8⟩ := hu
  obtain ⟨h16, h17, h25, h22, h29, h31, hC0, hC8, hF0, hF8, hRB, hrv, hR0, hR8⟩ := hc
  have h12 : u.getReg .x12 = BitVec.ofNat 64 (0x240 + 16 * k) :=
    hK (.x12, _) (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))))
  have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x240 + 16 * k ∨ 0x240 + 16 * k + 32 ≤ A) =>
    writeHash_frame u ans _ A h12 hA (by omega) h
  have fr : ∀ A, A < 2 ^ 64 → (A < 0x1C0 ∨ 0x210 ≤ A) → (A + 8 ≤ 0x240 + 16 * k ∨ 0x240 + 16 * k + 32 ≤ A) →
      (writeHash u ans).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2; rw [wf A hA h2]; exact hF.2 A hA h1
  have kr : ∀ x ∈ keepRegs, (writeHash u ans).getReg x = t.getReg x := fun x hx => by
    rw [writeHash_getReg]; exact hF.1 x hx
  refine ⟨Glob_writeHash hG ans _ h12 (by interval_cases k <;> decide), ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [hlen], ?_, ?_⟩
  · intro p hp; rw [writeHash_getReg]
    simp only [forsK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp
    · exact hK p (List.mem_append_left _ hp)
    · subst hp; exact hK _ (by simp)
  · rw [kr .x16 (by simp [keepRegs])]; exact h16
  · rw [kr .x17 (by simp [keepRegs])]; exact h17
  · rw [kr .x25 (by simp [keepRegs])]; exact h25
  · rw [kr .x22 (by simp [keepRegs])]; exact h22
  · rw [kr .x29 (by simp [keepRegs])]; simpa using h29
  · rw [kr .x31 (by simp [keepRegs])]; exact h31
  · rw [fr 0xC0 (by omega) (by omega) (by omega)]; exact hC0
  · rw [fr 0xC8 (by omega) (by omega) (by omega)]; exact hC8
  · rw [fr 0xF0 (by omega) (by omega) (by omega)]; exact hF0
  · rw [fr 0xF8 (by omega) (by omega) (by omega)]; exact hF8
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjk : j < k
    · rw [fr _ (by omega) (by omega) (by omega), fr _ (by omega) (by omega) (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact hRB j (by omega)
    · have : j = k := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      refine ⟨(writeHash_at0 _ ans _ h12 (by omega)).trans (vw0_answer ans).symm, ?_⟩
      rw [show 0x248 + 16 * j = 0x240 + 16 * j + 8 by omega, writeHash_at8 _ ans _ h12 (by omega)]
      exact (vw1_answer ans).symm
  · intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact hrv v h
    · rw [List.mem_singleton.mp h]; simp
  · rw [fr 0x220 (by omega) (by omega) (by omega)]; exact hR0
  · rw [fr 0x228 (by omega) (by omega) (by omega)]; exact hR8
  · rw [wf 0x1C8 (by omega) (by omega)]; exact hN8
  · rw [writeHash_pc, hpc, pcOf_add4]
    simp only [forsFC]
    rw [forsHd_link k hk]

end SigGolfCandidate.Verify
