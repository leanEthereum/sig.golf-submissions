import SigGolfCandidate.Verify.LayerSem
import SigGolfCandidate.Verify.FoldCheck
import SigGolfCandidate.Verify.FoldSem

/-! # The OTS leaf hash of a layer, into its fold region -/

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

theorem sll63_lt (u : Nat) (hu : u < 2 ^ 64) (s : MachineState) (h23 : s.getReg .x23 = BitVec.ofNat 64 u) :
    CmpOp.lt.eval ((E.bin .sll (.reg .x23) (cw 63)).eval s) ((E.c 0).eval s) = decide (u % 2 = 1) := by
  simp only [CmpOp.eval, E.eval, BinOp.eval, cw, h23]
  rw [show (0 : Word) = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  rw [Nat.mod_eq_of_lt hu]
  norm_num
  omega

def layFC (L : LCtx) : FCtx :=
  ⟨L.wl, L.pk, L.e, heightL L.lay, false, 8 - L.lay, 0, 704, 3, L.lay, L.tau, 2480 + 752 * L.lay + 672,
    if L.lay = 0 then 0x180 else 0x120⟩

theorem layFC_ok (L : LCtx) (hL : L.ok) : (layFC L).ok := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  refine ⟨?_, ?_, ?_, by simp [layFC], ?_, hwl, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [layFC]
  · unfold heightL; split <;> omega
  · unfold heightL; split <;> omega
  · exact Nat.mod_lt _ (Nat.two_pow_pos _)
  · omega
  · omega
  · unfold heightL; split <;> omega
  · split <;> decide
  · split <;> omega
  · omega

theorem layFC_check (L : LCtx) (hL : L.ok) :
    foldCheck (layFC L).kind (layFC L).a1 (layFC L).rg (layFC L).j0 (layFC L).h
      (0x800 + (layFC L).sibOff) (layFC L).dst = true := by
  have := layFoldOk_at L.lay hL.1
  simp only [layFoldOk] at this
  simp only [layFC, heightL]
  rw [show 0x800 + (2480 + 752 * L.lay + 672) = 0x800 + (2480 + 752 * L.lay + 672) from rfl]
  exact this

/-- Carried through the leaf and the fold of layer `lay` to the precode of layer `lay - 1`. -/
def LeafCarry (L : LCtx) (s : MachineState) : Prop :=
  s.getReg .x26 = BitVec.ofNat 64 (h3Word L.lay) ∧ s.getReg .x27 = BitVec.ofNat 64 (hWord L.lay) ∧
  s.getReg .x15 = BitVec.ofNat 64 (bVal L.lay 41) ∧ s.getReg .x30 = BitVec.ofNat 64 L.tau ∧ CBZ s

theorem leaf_step (L : LCtx) (hL : L.ok) (a : BitVec 256) (ends : List Val) (s : MachineState)
    (hs : HeadInv (L.cctx a) 42 ends s) :
    ∃ u, Steps image s 10 10 u ∧ fetch image u = some (.base .ECALL) ∧
      u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧
      hashInput u = pad64 (leafInput L.lay L.tau L.e ends) ∧
      ∀ ans, FoldInv (layFC L) (writeHash u ans) 0 (answerBytes 16 ans) (writeHash u ans) ∧
        LeafCarry L (writeHash u ans) := by
  obtain ⟨hlay, hidx, hwl⟩ := hL
  obtain ⟨hG, hK, hR, hCB, hZ, hLB, hlen, hvs, ⟨tt, -, hpc⟩, -⟩ := hs
  obtain ⟨h16, h17, h23, h30, h31⟩ := hR
  have hpc' : s.pc = pcOf (nextPc' L.lay 41) := by rw [hpc]; simp [headPc, LCtx.cctx]
  have he := e_lt L
  have htau : L.tau < 2 ^ 30 := tau_lt L.lay L.idx hlay hidx
  set d := decide (L.e % 2 = 1) with hd
  obtain ⟨u, hu⟩ := spec_run (lc_leaf hlay d) s hpc' hK (by
    intro b hb
    simp only [specLeaf, List.mem_cons, List.not_mem_nil, or_false] at hb
    subst hb
    simp only [Br.holds]
    exact sll63_lt L.e (by omega) s h23)
  have hK' := hu.known
  have hdv : (if d then 1 else 0) = L.e % 2 := by
    rw [hd]; split <;> simp_all <;> omega
  have h10 : u.getReg .x10 = BitVec.ofNat 64 0x340 := hu.regs (.x10, cw 832) (by simp [specLeaf])
  have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (10 + 1)) := hu.regs (.x11, cw 704) (by simp [specLeaf])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * (L.e % 2)) := by
    rw [hu.regs (.x12, cw (480 + 16 * (if d then 1 else 0))) (by simp [specLeaf]), ← hdv]; rfl
  have hmem := hu.mem
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 456 → A ≠ 448 → A ≠ 840 → A ≠ 832 →
      u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [hmem, memEval_frame_ofNat _ _ _ hA (by
      simp only [specLeaf, List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp <;> omega)]
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  refine ⟨u, hu.steps, hu.ecall rfl, hK' (.x5, 0) (by simp [leafPost, fk, gkOf, gkL, baseK]),
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega), ?_, ?_⟩
  · have hends : ∀ v ∈ ends, v.length = 16 := hvs
    rw [hashInput_ofNat _ 0x340 10 h10 h11 (by decide) (by decide),
      pad64_leafInput _ _ _ _ (by rw [hlen]) hends]
    congr 1
    rw [show 8 * (10 + 1) = 4 + 84 by rfl, List.range_add, List.map_append]
    congr 1
    · simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
        Nat.mul_zero, List.cons.injEq]
      refine ⟨?_, ?_, ?_, ?_, trivial⟩
      · rw [hmem]; simp only [specLeaf]
        rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
          memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
        simp only [Rv.E.eval, cw]
        congr 1; unfold twLo hWord; rw [Nat.div_eq_of_lt (by omega : L.tau < 2 ^ 32)]; omega
      · rw [hmem]; simp only [specLeaf]
        rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
          memEval_cons_eq _ _ _ _ _ rfl]
        (try simp only [Rv.E.eval]); rw [h31]
        simp only [CCtx.x31, LCtx.cctx]; congr 1; unfold twHi; omega
      · rw [mfr 0x350 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
      · rw [mfr 0x358 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · apply List.ext_getElem?
      intro m
      rw [List.map_map]
      by_cases hm : m < 84
      · rw [List.getElem?_map, List.getElem?_range hm, flat_get? _ _ _ _ (by rw [hlen]; omega)]
        simp only [Option.map_some, Function.comp, Option.some.injEq]
        rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]
        obtain ⟨hl0, hl1⟩ := hLB (m / 2) (by rw [hlen]; omega)
        split
        · rw [show 0x340 + 8 * (4 + m) = 0x360 + 16 * (m / 2) by omega]; exact hl0
        · rw [show 0x340 + 8 * (4 + m) = 0x368 + 16 * (m / 2) by omega]; exact hl1
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
          (by rw [length_flat, hlen]; omega)]
  · intro ans
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x1E0 + 16 * (L.e % 2) ∨ 0x1E0 + 16 * (L.e % 2) + 32 ≤ A) =>
      writeHash_frame _ ans _ A h12 hA (by omega) h
    have hbit : bitOf L.e 0 = L.e % 2 := by simp [bitOf]
    have hK2 := KnownOK_append.mp hK'
    refine ⟨⟨Glob_writeHash (hu.glob _ _ _ hG) ans _ h12 (by
        rcases Nat.mod_two_eq_zero_or_one L.e with h | h <;> rw [h] <;> decide),
      ?_, ?_, ?_, ?_, ?_, ?_, by simp, ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · have := Known_writeHash hK2.1 ans
      simpa [layFC] using this
    · rw [writeHash_getReg, hu.keep .x23 (by simp [leafKeep])]; exact h23
    · simp only [NBhdr, layFC, if_true, Bool.false_eq_true, if_false]
      rw [wf 0x1C0 (by omega) (by omega), hmem]; simp only [specLeaf]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
      simp only [Rv.E.eval, cw]
      congr 1; unfold FCtx.lo0 h3Word; simp only; rw [Nat.div_eq_of_lt (by omega : L.tau < 2 ^ 32)]
      omega
    · rw [wf 0x1C8 (by omega) (by omega), hmem]; simp only [specLeaf, layFC]
      rw [memEval_cons_eq _ _ _ _ _ rfl]
      simp only [stW0, ldE, cw, Rv.E.eval, BinOp.eval]
      rw [merge_w0_toNat, h30, BitVec.toNat_ofNat]
      simp only [LCtx.cctx]
      norm_num
    · simp only [layFC, hbit]
      rw [writeHash_at0 _ ans _ h12 (by omega)]; exact (vw0_answer ans).symm
    · simp only [layFC, hbit]
      rw [show 0x1E8 + 16 * (L.e % 2) = 0x1E0 + 16 * (L.e % 2) + 8 by omega,
        writeHash_at8 _ ans _ h12 (by omega)]; exact (vw1_answer ans).symm
    · rw [writeHash_pc, hu.pc rfl, pcOf_add4]
      simp only [specLeaf, layFC, hbit, lvlPc, ← hdv, Nat.add_zero]
    · rw [writeHash_getReg]; exact hK2.2 (.x26, BitVec.ofNat 64 (h3Word L.lay)) (by simp)
    · rw [writeHash_getReg]; exact hK2.2 (.x27, BitVec.ofNat 64 (hWord L.lay)) (by simp)
    · rw [writeHash_getReg]; exact hK2.2 (.x15, BitVec.ofNat 64 (bVal L.lay 41)) (by simp)
    · rw [writeHash_getReg, hu.keep .x30 (by simp [leafKeep])]; exact h30
    · exact ⟨by rw [wf 0xE0 (by omega) (by omega), mfr 0xE0 (by omega) (by omega) (by omega) (by omega)
          (by omega)]; exact hZ.1,
        by rw [wf 0xE8 (by omega) (by omega), mfr 0xE8 (by omega) (by omega) (by omega) (by omega)
          (by omega)]; exact hZ.2⟩

end SigGolfCandidate.Verify
