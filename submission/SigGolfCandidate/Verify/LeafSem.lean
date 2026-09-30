import SigGolfCandidate.Verify.LayerSem
import SigGolfCandidate.Verify.FoldCheck

/-! # The OTS leaf hash and the fold setup of a layer -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem flat_get? (f g : Val → Word) : ∀ (vs : List Val) (m : Nat), m < 2 * vs.length →
    ((vs.map fun v => [f v, g v]).flatten)[m]? =
      some (if m % 2 = 0 then f (vs.getD (m / 2) []) else g (vs.getD (m / 2) [])) := by
  intro vs
  induction vs with
  | nil => intro m h; simp at h
  | cons v vs ih =>
    intro m h
    simp only [List.map_cons, List.flatten_cons, List.cons_append, List.nil_append]
    rcases m with _ | _ | m
    · simp
    · simp
    · simp only [List.getElem?_cons_succ]
      rw [ih m (by simp at h; omega)]
      congr 1
      rw [show (m + 1 + 1) / 2 = m / 2 + 1 by omega, List.getD_cons_succ,
        show (m + 1 + 1) % 2 = m % 2 by omega]

theorem length_flat (f g : Val → Word) (vs : List Val) :
    ((vs.map fun v => [f v, g v]).flatten).length = 2 * vs.length := by
  induction vs with
  | nil => rfl
  | cons v vs ih => simp [List.flatten_cons] at ih ⊢; omega

macro "bvne" : tactic => `(tactic| (intro h; have h' := congrArg BitVec.toNat h; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at h'; omega))

def LeafDone (L : LCtx) (v : Val) (s : MachineState) : Prop :=
  Glob L.wl L.pk s ∧ KnownOK leafK s ∧ s.getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * (L.e % 2)) ∧
  s.getReg .x22 = BitVec.ofNat 64 L.idx ∧ s.getReg .x23 = BitVec.ofNat 64 L.e ∧
  s.getReg .x24 = BitVec.ofNat 64 (16 * L.e) ∧ s.getReg .x30 = BitVec.ofNat 64 L.tau ∧
  s.getMem (BitVec.ofNat 64 (0x1E0 + 16 * (L.e % 2))) = vw0 v ∧
  s.getMem (BitVec.ofNat 64 (0x1E8 + 16 * (L.e % 2))) = vw1 v ∧ v.length = 16 ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧
  s.pc = pcOf (leafPc L.lay + leafSteps L.lay + 1)

theorem gpLeaf_eval (u : Nat) (hu : u < 32) (s : MachineState) (h23 : s.getReg .x23 = BitVec.ofNat 64 u) :
    gpLeaf.eval s = BitVec.ofNat 64 (16 * (u % 2)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [gpLeaf, Rv.E.eval, BinOp.eval, cw, h23, BitVec.toNat_and, BitVec.toNat_shiftLeft,
    BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [show (16 : Nat) % 2 ^ 64 = 16 by rfl, show (4 : Nat) % 2 ^ 64 % 64 = 4 by rfl,
    Nat.mod_eq_of_lt (show u < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show u * 2 ^ 4 < 2 ^ 64 by omega),
    land16]
  omega

theorem sll4_eval (u : Nat) (hu : u < 32) (s : MachineState) (h23 : s.getReg .x23 = BitVec.ofNat 64 u) :
    (E.bin .sll (.reg .x23) (cw 4)).eval s = BitVec.ofNat 64 (16 * u) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Rv.E.eval, BinOp.eval, cw, h23, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [show (4 : Nat) % 2 ^ 64 % 64 = 4 by rfl, Nat.mod_eq_of_lt (show u < 2 ^ 64 by omega)]
  omega

theorem leaf_step (L : LCtx) (hL : L.ok) (a : BitVec 256) (ends : List Val) (s : MachineState)
    (hs : HeadInv (L.cctx a) 42 ends s) :
    ∃ t, Steps image s (leafSteps L.lay) (leafSteps L.lay) t ∧ fetch image t = some (.base .ECALL) ∧
      t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = pad64 (leafInput L.lay L.tau L.e ends) ∧
      ∀ ans, LeafDone L (answerBytes 16 ans) (writeHash t ans) := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  have hchk := layerCheck_at L.lay hlay
  simp only [layerCheck, Bool.and_eq_true] at hchk
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okRun_spec hchk.1.2
  obtain ⟨hG, hK, hR, hCB, hF0, hF8, hLB, hlen, hvs, hpc⟩ := hs
  obtain ⟨h16, h17, h22, h23, h30, h31⟩ := hR
  have hpc' : s.pc = pcOf (leafPc L.lay) := by rw [hpc]; simp [headOrLeaf, leafPc, LCtx.cctx]
  set r := leafExp L.lay with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc' hK (by simp [hr, leafExp])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have he := e_lt L ⟨hlay, hidx, hwl⟩
  have htau : L.tau < 2 ^ 30 := tau_lt L.lay L.idx hlay hidx
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0x340 := hK' (.x10, 0x340) (by simp [leafK])
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (10 + 1)) := hK' (.x11, 704) (by simp [leafK])
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * (L.e % 2)) := by
    rw [PRes.toState_getReg]; simp only [hr, leafExp]
    simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
    simp only [Rv.E.eval, BinOp.eval, cw]
    rw [gpLeaf_eval L.e he s h23, BitVec.ofNat_add_ofNat]; congr 1; omega
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0x348⟩, .reg .x31),
      (⟨none, BitVec.ofNat 64 0x340⟩, cw (0x201 + 65536 * L.lay))] := by simp [hr, leafExp]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0x348 → A ≠ 0x340 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by
      rw [hmem]; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) <;> simp <;> omega)]
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  refine ⟨r.toState s, ?_, hec (by simp [hr, leafExp]), hK' (.x5, 0) (by simp [leafK, globK]),
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega), ?_, ?_⟩
  · simpa [hr, leafExp] using hst
  · have hends : ∀ v ∈ ends, v.length = 16 := hvs
    rw [hashInput_ofNat _ 0x340 10 h10 h11 (by decide) (by decide),
      pad64_leafInput _ _ _ _ (by rw [hlen]) hends]
    congr 1
    rw [show 8 * (10 + 1) = 4 + 84 by rfl, List.range_add, List.map_append]
    congr 1
    · simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
        Nat.mul_zero, List.cons.injEq]
      refine ⟨?_, ?_, ?_, ?_, trivial⟩
      · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne),
          memEval_cons_eq _ _ _ _ _ rfl]
        simp only [Rv.E.eval, cw]
        congr 1; unfold twLo; simp only [LCtx.cctx] at *; rw [Nat.div_eq_of_lt (by omega : L.tau < 2 ^ 32)]; omega
      · rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
        simp only [Rv.E.eval]; rw [h31]
        simp only [CCtx.x31, LCtx.cctx]; congr 1; unfold twHi; omega
      · rw [mfr 0x350 (by omega) (by omega) (by omega)]; exact hP _ (by decide)
      · rw [mfr 0x358 (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · apply List.ext_getElem?
      intro m
      rw [List.map_map]
      by_cases hm : m < 84
      · rw [List.getElem?_map, List.getElem?_range hm, flat_get? _ _ _ _ (by rw [hlen]; omega)]
        simp only [Option.map_some, Function.comp, Option.some.injEq]
        rw [mfr _ (by omega) (by omega) (by omega)]
        obtain ⟨hl0, hl1⟩ := hLB (m / 2) (by rw [hlen]; omega)
        split
        · rw [show 0x340 + 8 * (4 + m) = 0x360 + 16 * (m / 2) by omega]; exact hl0
        · rw [show 0x340 + 8 * (4 + m) = 0x368 + 16 * (m / 2) by omega]; exact hl1
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
          (by rw [length_flat, hlen]; omega)]
  · intro ans
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x1E0 + 16 * (L.e % 2) ∨ 0x1E0 + 16 * (L.e % 2) + 32 ≤ A) =>
      writeHash_frame _ ans _ A h12 hA (by omega) h
    refine ⟨Glob_writeHash (hglob _ _ hG) ans _ h12 (by
        rcases Nat.mod_two_eq_zero_or_one L.e with h | h <;> rw [h] <;> decide),
      Known_writeHash hK' ans, by rw [writeHash_getReg]; exact h12, ?_, ?_, ?_, ?_,
      (writeHash_at0 _ ans _ h12 (by omega)).trans (vw0_answer ans).symm, ?_, by simp, ?_, ?_, ?_⟩
    · rw [writeHash_getReg, hkeep' .x22 (by simp [layRegs])]; exact h22
    · rw [writeHash_getReg, hkeep' .x23 (by simp [layRegs])]; exact h23
    · rw [writeHash_getReg, PRes.toState_getReg]; simp only [hr, leafExp]
      simp (disch := decide) only [RegFile.get_set_ne, RegFile.get_set_self]
      exact sll4_eval L.e he s h23
    · rw [writeHash_getReg, hkeep' .x30 (by simp [layRegs])]; exact h30
    · rw [show 0x1E8 + 16 * (L.e % 2) = 0x1E0 + 16 * (L.e % 2) + 8 by omega,
        writeHash_at8 _ ans _ h12 (by omega)]; exact (vw1_answer ans).symm
    · rw [wf 0xF0 (by omega) (by omega), mfr 0xF0 (by omega) (by omega) (by omega)]; exact hF0
    · rw [wf 0xF8 (by omega) (by omega), mfr 0xF8 (by omega) (by omega) (by omega)]; exact hF8
    · rw [writeHash_pc, PRes.toState_pc]; simp only [hr, leafExp]; rw [pcOf_add4]

/-! ## Fold setup -/

def layFC (L : LCtx) : FCtx :=
  ⟨L.wl, L.pk, L.e, layH L.lay, layFoldPc L.lay, 3, L.lay, L.tau, 2480 + 752 * L.lay + 672,
    if L.lay = 0 then 0x180 else 0x120⟩

theorem layFC_ok (L : LCtx) (hL : L.ok) : (layFC L).ok := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  have hH := layH_le L.lay
  refine ⟨?_, ?_, ?_, by simp [layFC], ?_, hwl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [layFC]
  · unfold layH; split <;> omega
  · omega
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · omega
  · omega
  · unfold layH; split <;> omega
  · split <;> decide
  · split <;> omega
  · interval_cases L.lay <;> decide

theorem layFC_check (L : LCtx) (hL : L.ok) :
    foldCheck (layFC L).base (layFC L).h (0x800 + (layFC L).sibOff) (layFC L).dst = true := by
  have := layFoldOk_all
  simp only [List.all_eq_true, List.mem_range] at this
  exact this L.lay hL.1

theorem fsetup_step (L : LCtx) (hL : L.ok) (v : Val) (s : MachineState) (hs : LeafDone L v s) :
    ∃ t, Steps image s (leafSteps L.lay - 3) (leafSteps L.lay - 3) t ∧ FoldInv (layFC L) t 0 v t ∧
      t.getReg .x22 = BitVec.ofNat 64 L.idx ∧
      t.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ t.getMem (BitVec.ofNat 64 0xF8) = 0 := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  have hchk := layerCheck_at L.lay hlay
  simp only [layerCheck, Bool.and_eq_true] at hchk
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okFold_spec hchk.2
  obtain ⟨hG, hK, h12, h22, h23, h24, h30, hv0, hv1, hvl, hF0, hF8, hpc⟩ := hs
  set r := fsetupExp L.lay with hr
  obtain ⟨hst, -, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, fsetupExp])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have htau : L.tau < 2 ^ 30 := tau_lt L.lay L.idx hlay hidx
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0x1C8⟩, stW0 0x1C8 (.reg .x30)),
      (⟨none, BitVec.ofNat 64 0x1C0⟩, stW0 0x1C0 (cw (0x301 + 65536 * L.lay)))] := by
    simp [hr, fsetupExp]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0x1C8 → A ≠ 0x1C0 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by
      rw [hmem]; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) <;> simp <;> omega)]
  have h12' : (r.toState s).getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * (L.e % 2)) := by
    rw [PRes.toState_getReg]
    have : r.st.regs.get .x12 = .reg .x12 := by simp only [hr, fsetupExp]; rfl
    rw [this]; exact h12
  have hbit : bitOf L.e 0 = L.e % 2 := by simp [bitOf]
  refine ⟨r.toState s, ?_, ⟨hglob _ _ hG, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hvl, ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩,
    ?_⟩, ?_, ?_, ?_⟩
  · simpa [hr, fsetupExp] using hst
  · intro p hp
    simp only [foldK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp | hp | hp
    · exact hK' p (by simp [hp])
    · subst hp; exact hK' _ (by simp)
    · subst hp; exact hK' _ (by simp)
    · subst hp; rw [h12']; simp [layFC, hbit]
  · rw [hkeep' .x23 (by simp [keepRegs])]; exact h23
  · rw [hkeep' .x24 (by simp [keepRegs])]; exact h24
  · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
    simp only [stW0, ldE, cw, Rv.E.eval, BinOp.eval]
    rw [merge_w0_toNat, BitVec.toNat_ofNat]
    simp only [FCtx.lo0, layFC]
    rw [Nat.div_eq_of_lt (show L.tau < 2 ^ 32 by omega)]
    norm_num; omega
  · rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
    simp only [stW0, ldE, cw, Rv.E.eval, BinOp.eval]
    rw [merge_w0_toNat, h30, BitVec.toNat_ofNat]
    simp only [layFC]
    norm_num
  · simp only [layFC, hbit]
    rw [mfr _ (by omega) (by omega) (by omega)]; exact hv0
  · simp only [layFC, hbit]
    rw [mfr _ (by omega) (by omega) (by omega)]; exact hv1
  · rw [PRes.toState_pc]; simp [hr, fsetupExp, layFC, foldPc]
  · rw [hkeep' .x22 (by simp [keepRegs])]; exact h22
  · rw [mfr 0xF0 (by omega) (by omega) (by omega)]; exact hF0
  · rw [mfr 0xF8 (by omega) (by omega) (by omega)]; exact hF8

end SigGolfCandidate.Verify
