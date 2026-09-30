import SigGolfCandidate.Verify.FoldRuns
import SigGolfCandidate.Verify.ChainSem
import Mathlib.Data.Nat.Bitwise

/-! # Merkle fold levels: semantics -/

set_option linter.unusedSimpArgs false

macro "bvne" : tactic => `(tactic| (intro h; have h' := congrArg BitVec.toNat h; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at h'; omega))

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Node format `tw(t, f2, tau, lam, j) | P | l | r` (`nodeInput`, `ftsNodeInput`). -/
def nodeF (t f2 tau : Nat) : NodeFmt := fun lam j l r => thInput (tweak t f2 tau lam j) (l ++ r)

theorem nodeInput_eq (lay tau : Nat) : nodeInput lay tau = nodeF 3 lay tau := rfl
theorem ftsNodeInput_eq (k idx : Nat) : ftsNodeInput k idx = nodeF 10 k idx := rfl

theorem pad64_nodeF (t f2 tau lam j : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) :
    pad64 (nodeF t f2 tau lam j l r) = queryOfWords 0
      [BitVec.ofNat 64 (twLo t f2 tau lam), BitVec.ofNat 64 (twHi tau j), 0, 0,
        vw0 l, vw1 l, vw0 r, vw1 r] := by
  unfold nodeF
  rw [pad64_thInput _ _ (by simp) 0 (by simp [hl, hr]) (by simp [hl, hr]), wordsOfN_tweak]
  simp only [List.length_append, hl, hr]
  rw [show 8 * 0 + 4 = 2 + (2 + 0) by rfl, List.append_assoc l r, wordsOfN_val_append l hl,
    wordsOfN_val_append r hr]
  rfl

structure FCtx where
  wl : List Byte
  pk : List Byte
  E : Nat
  h : Nat
  base : Nat
  t : Nat
  f2 : Nat
  tau : Nat
  sibOff : Nat
  dst : Nat

def FCtx.ok (fc : FCtx) : Prop :=
  1 ≤ fc.h ∧ fc.h ≤ 10 ∧ fc.E < 2 ^ fc.h ∧ fc.t < 256 ∧ fc.f2 < 256 ∧ fc.wl.length = 7756 ∧
  fc.sibOff % 8 = 0 ∧ fc.sibOff + 16 * fc.h ≤ 7756 ∧ safeDest fc.dst = true ∧
  (fc.dst + 32 ≤ 0x1C0 ∨ 0x210 ≤ fc.dst) ∧ fc.base < 2 ^ 40

def FCtx.lo0 (fc : FCtx) : Nat := 1 + 256 * fc.t + 65536 * fc.f2 + 2 ^ 24 * (fc.tau / 2 ^ 32 % 256)

def FCtx.path (fc : FCtx) : List Val := (List.range fc.h).map fun l => slice fc.wl (fc.sibOff + 16 * l) 16

def FCtx.node (fc : FCtx) : NodeFmt := nodeF fc.t fc.f2 fc.tau

def bitOf (E lam : Nat) : Nat := E / 2 ^ lam % 2

def FrameOK (s0 s : MachineState) : Prop :=
  (∀ r ∈ keepRegs, s.getReg r = s0.getReg r) ∧
  (∀ A, A < 2 ^ 64 → (A < 0x1C0 ∨ 0x210 ≤ A) → s.getMem (BitVec.ofNat 64 A) = s0.getMem (BitVec.ofNat 64 A))

def FoldInv (fc : FCtx) (s0 : MachineState) (lam : Nat) (v : Val) (s : MachineState) : Prop :=
  Glob fc.wl fc.pk s ∧ KnownOK (foldK (0x1E0 + 16 * bitOf fc.E lam)) s ∧
  s.getReg .x23 = BitVec.ofNat 64 fc.E ∧ s.getReg .x24 = BitVec.ofNat 64 (16 * fc.E) ∧
  (s.getMem (BitVec.ofNat 64 0x1C0)).toNat % 2 ^ 32 = fc.lo0 ∧
  (s.getMem (BitVec.ofNat 64 0x1C8)).toNat % 2 ^ 32 = fc.tau % 2 ^ 32 ∧
  s.getMem (BitVec.ofNat 64 (0x1E0 + 16 * bitOf fc.E lam)) = vw0 v ∧
  s.getMem (BitVec.ofNat 64 (0x1E8 + 16 * bitOf fc.E lam)) = vw1 v ∧ v.length = 16 ∧
  FrameOK s0 s ∧ s.pc = pcOf (foldPc fc.base lam)

def FoldEnd (fc : FCtx) (s0 : MachineState) (u : MachineState) : Prop :=
  Glob fc.wl fc.pk u ∧ KnownOK (globK ++ [(.x10, 0x1C0), (.x11, 64), (.x12, BitVec.ofNat 64 fc.dst)]) u ∧
  FrameOK s0 u ∧ u.pc = pcOf (foldPc fc.base (fc.h - 1) + 9) ∧
  fetch image u = some (.base .ECALL) ∧
  (u.getMem (BitVec.ofNat 64 0x1C8)).toNat % 2 ^ 32 = fc.tau % 2 ^ 32

/-! ## Bit extraction -/

theorem land16 (n : Nat) : n &&& 16 = 16 * (n / 16 % 2) := by
  rw [show (16 : Nat) = 2 ^ 4 from rfl, Nat.and_two_pow, Nat.toNat_testBit, Nat.mul_comm]

theorem gpE_eval (u b : Nat) (hE : u < 2 ^ 10) (hb : b ≤ 9) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 u) (h24 : s.getReg .x24 = BitVec.ofNat 64 (16 * u)) :
    (gpE b).eval s = BitVec.ofNat 64 (16 * bitOf u b) := by
  apply BitVec.eq_of_toNat_eq
  unfold gpE bitOf
  split
  · rename_i hb4; subst hb4
    simp only [Rv.E.eval, BinOp.eval, cwf, h23, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show u < 2 ^ 64 by omega), show (16 : Nat) % 2 ^ 64 = 16 from rfl, land16]
    omega
  · simp only [Rv.E.eval, BinOp.eval, cwf, h24, BitVec.toNat_and, BitVec.toNat_ofNat,
      BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show 16 * u < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show b < 64 by omega), show (16 : Nat) % 2 ^ 64 = 16 from rfl, land16,
      Nat.mod_eq_of_lt (show 16 * (u / 2 ^ b % 2) < 2 ^ 64 by omega)]
    congr 2
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm (2 ^ b) 16, ← Nat.div_div_eq_div_mul,
      Nat.mul_div_cancel_left _ (by decide)]

theorem srl_eval (u b : Nat) (hE : u < 2 ^ 10) (hb : b ≤ 10) (s : MachineState)
    (h23 : s.getReg .x23 = BitVec.ofNat 64 u) :
    (Rv.E.bin .srl (.reg .x23) (cwf b)).eval s = BitVec.ofNat 64 (u / 2 ^ b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [Rv.E.eval, BinOp.eval, cwf, h23, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  have : u / 2 ^ b ≤ u := Nat.div_le_self _ _
  rw [Nat.mod_eq_of_lt (show u < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt (show b < 64 by omega), Nat.mod_eq_of_lt (show u / 2 ^ b < 2 ^ 64 by omega)]

theorem stW_eval (a : Nat) (v : Rv.E) (s : MachineState) :
    (stW a v).eval s = StoreKind.merge .w (s.getMem (BitVec.ofNat 64 a)) 4 (v.eval s) := rfl

/-! ## Family facts -/

theorem okFold_spec {o : Option PRes} {e : PRes} {post : List (Reg × Word)}
    (h : okFold o e post = true) :
    o = some e ∧ resOK e = true ∧ knownB post e = true ∧ keepB keepRegs e = true := by
  simp only [okFold, Bool.and_eq_true] at h
  exact ⟨optBeq_eq h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem foldCheck_at {base h wa0 dst : Nat} (hc : foldCheck base h wa0 dst = true) (lam b : Nat)
    (hlam : lam < h) (hb : b < 2) :
    okFold (runAt (foldK (0x1E0 + 16 * b)) [] (foldPc base lam) [])
      (foldExp base h lam b (wa0 + 16 * lam) dst) (foldPost h lam dst b) = true := by
  simp only [foldCheck, List.all_eq_true, List.mem_range] at hc
  exact hc lam hlam b hb

theorem bitOf_lt (u lam : Nat) : bitOf u lam < 2 := Nat.mod_lt _ (by decide)

theorem FrameOK.trans {s0 s t : MachineState} (h1 : FrameOK s0 s)
    (hr : ∀ r ∈ keepRegs, t.getReg r = s.getReg r)
    (hm : ∀ A, A < 2 ^ 64 → (A < 0x1C0 ∨ 0x210 ≤ A) →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : FrameOK s0 t :=
  ⟨fun r hr' => (hr r hr').trans (h1.1 r hr'), fun A hA hA' => (hm A hA hA').trans (h1.2 A hA hA')⟩

theorem sib_words (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam < fc.h) (s : MachineState)
    (hG : Glob fc.wl fc.pk s) :
    s.getMem (BitVec.ofNat 64 (0x800 + fc.sibOff + 16 * lam)) =
      vw0 (slice fc.wl (fc.sibOff + 16 * lam) 16) ∧
    s.getMem (BitVec.ofNat 64 (0x800 + fc.sibOff + 16 * lam + 8)) =
      vw1 (slice fc.wl (fc.sibOff + 16 * lam) 16) := by
  obtain ⟨-, h10, -, -, -, hwl, h8, hsz, -⟩ := hfc
  rw [vw0_slice, vw1_slice, show 0x800 + fc.sibOff + 16 * lam = 0x800 + (fc.sibOff + 16 * lam) by omega,
    show 0x800 + (fc.sibOff + 16 * lam) + 8 = 0x800 + (fc.sibOff + 16 * lam + 8) by omega]
  exact ⟨wit_word hG.2.1 _ (by omega) (by omega), wit_word hG.2.1 _ (by omega) (by omega)⟩

def FCtx.sib (fc : FCtx) (lam : Nat) : Val := slice fc.wl (fc.sibOff + 16 * lam) 16

/-- The spec's input of fold level `lam` with current value `v`. -/
def FCtx.input (fc : FCtx) (lam : Nat) (v : Val) : List Byte :=
  if fc.E / 2 ^ lam % 2 = 1 then fc.node (lam + 1) (fc.E / 2 ^ (lam + 1)) (fc.sib lam) v
  else fc.node (lam + 1) (fc.E / 2 ^ (lam + 1)) v (fc.sib lam)

theorem length_sib (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam < fc.h) :
    (fc.sib lam).length = 16 := by
  obtain ⟨-, h10, -, -, -, hwl, h8, hsz, -⟩ := hfc
  unfold FCtx.sib; apply length_slice16; omega

theorem pad64_input (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam < fc.h) (v : Val)
    (hv : v.length = 16) :
    pad64 (fc.input lam v) = queryOfWords 0
      [BitVec.ofNat 64 (twLo fc.t fc.f2 fc.tau (lam + 1)),
        BitVec.ofNat 64 (twHi fc.tau (fc.E / 2 ^ (lam + 1))), 0, 0,
        if bitOf fc.E lam = 1 then vw0 (fc.sib lam) else vw0 v,
        if bitOf fc.E lam = 1 then vw1 (fc.sib lam) else vw1 v,
        if bitOf fc.E lam = 1 then vw0 v else vw0 (fc.sib lam),
        if bitOf fc.E lam = 1 then vw1 v else vw1 (fc.sib lam)] := by
  unfold FCtx.input bitOf
  split
  · rw [FCtx.node, pad64_nodeF _ _ _ _ _ _ _ (length_sib fc hfc lam hlam) hv]; try simp_all
  · rw [FCtx.node, pad64_nodeF _ _ _ _ _ _ _ hv (length_sib fc hfc lam hlam)]; try simp_all

theorem level_lt (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam + 1 < fc.h)
    (hchk : foldCheck fc.base fc.h (0x800 + fc.sibOff) fc.dst = true) (s0 : MachineState)
    (v : Val) (s : MachineState) (hs : FoldInv fc s0 lam v s) :
    ∃ t, Steps image s (if lam = 3 then 11 else 12) (if lam = 3 then 11 else 12) t ∧
      fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = pad64 (fc.input lam v) ∧
      ∀ a, FoldInv fc s0 (lam + 1) (answerBytes 16 a) (writeHash t a) := by
  have hb2 := bitOf_lt fc.E lam
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okFold_spec (foldCheck_at hchk lam (bitOf fc.E lam) (by omega) hb2)
  simp only [foldPost, if_neg (show ¬ (lam + 1 = fc.h) by omega)] at hkn
  obtain ⟨hG, hK, h23, h24, hN0, hN8, hv0, hv1, hvl, hF, hpc⟩ := hs
  obtain ⟨hh1, hh10, hE, ht, hf2, hwl, hs8, hsz, hsafe, hdst, hbase⟩ := hfc
  set b := bitOf fc.E lam with hbdef
  set r := foldExp fc.base fc.h lam b (0x800 + fc.sibOff + 16 * lam) fc.dst with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, foldExp, show ¬ (lam + 1 = fc.h) by omega])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have hE10 : fc.E < 2 ^ 10 := lt_of_lt_of_le hE (Nat.pow_le_pow_right (by decide) hh10)
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0x1C0 := hK' (.x10, 0x1C0) (by simp)
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, 64) (by simp)
  have h23' : (r.toState s).getReg .x23 = BitVec.ofNat 64 fc.E := (hkeep' _ (by simp [keepRegs])).trans h23
  have h24' : (r.toState s).getReg .x24 = BitVec.ofNat 64 (16 * fc.E) :=
    (hkeep' _ (by simp [keepRegs])).trans h24
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * bitOf fc.E (lam + 1)) := by
    rw [PRes.toState_getReg]
    simp only [hr, foldExp, if_neg (show ¬ (lam + 1 = fc.h) by omega)]
    rw [RegFile.get_set_self _ _ (by decide)]
    simp only [Rv.E.eval, BinOp.eval, cwf]
    rw [gpE_eval fc.E (lam + 1) hE10 (by omega) s h23 h24, BitVec.ofNat_add_ofNat]
    congr 1; omega
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0x1C8⟩, stW 0x1C8 (.bin .srl (.reg .x23) (cwf (lam + 1)))),
       (⟨none, BitVec.ofNat 64 0x1C0⟩, stW 0x1C0 (cwf (lam + 1))),
       (⟨none, BitVec.ofNat 64 (0x1F0 - 16 * b + 8)⟩, .ld (cwf (0x800 + fc.sibOff + 16 * lam + 8))),
       (⟨none, BitVec.ofNat 64 (0x1F0 - 16 * b)⟩, .ld (cwf (0x800 + fc.sibOff + 16 * lam)))] := by
    simp [hr, foldExp, show ¬ (lam + 1 = fc.h) by omega]
  have hsib := sib_words fc ⟨hh1, hh10, hE, ht, hf2, hwl, hs8, hsz, hsafe, hdst, hbase⟩ lam (by omega) s hG
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  -- memory of the final state
  have m1C0 : (r.toState s).getMem (BitVec.ofNat 64 0x1C0) =
      BitVec.ofNat 64 (fc.lo0 + 2 ^ 32 * (lam + 1)) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_eq _ _ _ _ _ rfl]
    simp only [stW, Rv.E.eval, BinOp.eval, cwf]
    rw [stMerge_eval _ _ _ (by omega) hN0]
  have m1C8 : (r.toState s).getMem (BitVec.ofNat 64 0x1C8) =
      BitVec.ofNat 64 (fc.tau % 2 ^ 32 + 2 ^ 32 * (fc.E / 2 ^ (lam + 1))) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl, stW_eval,
      srl_eval fc.E (lam + 1) hE10 (by omega) s h23]
    rw [stMerge_eval _ _ _ (by
      have : fc.E / 2 ^ (lam + 1) ≤ fc.E := Nat.div_le_self _ _
      omega) hN8]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0x1C8 → A ≠ 0x1C0 → A ≠ 0x1F0 - 16 * b + 8 →
      A ≠ 0x1F0 - 16 * b → (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by
      rw [hmem]; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp <;> omega)]
  have msib0 : (r.toState s).getMem (BitVec.ofNat 64 (0x1F0 - 16 * b)) = vw0 (fc.sib lam) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_eq _ _ _ _ _ rfl]
    simp only [Rv.E.eval, cwf]; exact hsib.1
  have msib1 : (r.toState s).getMem (BitVec.ofNat 64 (0x1F0 - 16 * b + 8)) = vw1 (fc.sib lam) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
    simp only [Rv.E.eval, cwf]; exact hsib.2
  have mv0 : (r.toState s).getMem (BitVec.ofNat 64 (0x1E0 + 16 * b)) = vw0 v := by
    rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv0
  have mv1 : (r.toState s).getMem (BitVec.ofNat 64 (0x1E8 + 16 * b)) = vw1 v := by
    rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv1
  refine ⟨r.toState s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : r.steps = if lam = 3 then 11 else 12 := by
      simp only [hr, foldExp, if_neg (show ¬ (lam + 1 = fc.h) by omega)]
    have e2 : r.cycles = if lam = 3 then 11 else 12 := by
      simp only [hr, foldExp, if_neg (show ¬ (lam + 1 = fc.h) by omega)]
    rw [e1, e2] at hst; exact hst
  · exact hec (by simp [hr, foldExp, show ¬ (lam + 1 = fc.h) by omega])
  · exact hK' (.x5, 0) (by simp [globK])
  · have hb' := bitOf_lt fc.E (lam + 1)
    exact hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega)
  · rw [hashInput_ofNat _ 0x1C0 0 h10 h11 (by decide) (by decide),
      pad64_input fc ⟨hh1, hh10, hE, ht, hf2, hwl, hs8, hsz, hsafe, hdst, hbase⟩ lam (by omega) v hvl]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero]
    have hlo : twLo fc.t fc.f2 fc.tau (lam + 1) = fc.lo0 + 2 ^ 32 * (lam + 1) := by
      unfold twLo FCtx.lo0; omega
    have hhi : twHi fc.tau (fc.E / 2 ^ (lam + 1)) = fc.tau % 2 ^ 32 + 2 ^ 32 * (fc.E / 2 ^ (lam + 1)) := by
      unfold twHi
      have : fc.E / 2 ^ (lam + 1) ≤ fc.E := Nat.div_le_self _ _
      omega
    rw [hlo, hhi, m1C0, m1C8, mfr 0x1D0 (by omega) (by omega) (by omega) (by omega) (by omega),
      mfr 0x1D8 (by omega) (by omega) (by omega) (by omega) (by omega), hP 0x1D0 (by decide),
      hP 0x1D8 (by decide)]
    rcases (show b = 0 ∨ b = 1 by omega) with h0 | h1
    · rw [h0] at mv0 mv1 msib0 msib1
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceSub] at mv0 mv1 msib0 msib1
      rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h0]
    · rw [h1] at mv0 mv1 msib0 msib1
      simp only [Nat.mul_one, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] at mv0 mv1 msib0 msib1
      rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h1]
  · intro a
    have hb' := bitOf_lt fc.E (lam + 1)
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x1E0 + 16 * bitOf fc.E (lam + 1) ∨
        0x1E0 + 16 * bitOf fc.E (lam + 1) + 32 ≤ A) =>
      writeHash_frame _ a _ A h12 hA (by omega) h
    refine ⟨Glob_writeHash (hglob _ _ hG) a _ h12 (by
        rcases (show bitOf fc.E (lam + 1) = 0 ∨ bitOf fc.E (lam + 1) = 1 by omega) with h | h <;> rw [h] <;> decide),
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, by simp, ?_, ?_⟩
    · intro p hp
      rw [writeHash_getReg]
      simp only [foldK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with hp | hp | hp | hp
      · exact hK' p (by simp [hp])
      · subst hp; exact h10
      · subst hp; exact h11
      · subst hp; exact h12
    · rw [writeHash_getReg]; exact h23'
    · rw [writeHash_getReg]; exact h24'
    · rw [wf 0x1C0 (by omega) (by omega), m1C0, BitVec.toNat_ofNat]; unfold FCtx.lo0; omega
    · rw [wf 0x1C8 (by omega) (by omega), m1C8, BitVec.toNat_ofNat]
      have : fc.E / 2 ^ (lam + 1) ≤ fc.E := Nat.div_le_self _ _
      omega
    · rw [writeHash_at0 _ a _ h12 (by omega)]; simp [vw0_answer]
    · rw [show 0x1E8 + 16 * bitOf fc.E (lam + 1) = 0x1E0 + 16 * bitOf fc.E (lam + 1) + 8 by omega,
        writeHash_at8 _ a _ h12 (by omega)]; simp [vw1_answer]
    · refine FrameOK.trans (FrameOK.trans hF (fun r hr => hkeep' r hr) (fun A hA hA' => ?_))
        (fun r _ => writeHash_getReg _ _ _) (fun A hA hA' => wf A hA (by omega))
      exact mfr A hA (by omega) (by omega) (by omega) (by omega)
    · rw [writeHash_pc, PRes.toState_pc]
      simp only [hr, foldExp, if_neg (show ¬ (lam + 1 = fc.h) by omega)]
      rw [pcOf_add4]
      exact congrArg pcOf (by simp only [foldPc]; split_ifs <;> omega)

theorem level_last (fc : FCtx) (hfc : fc.ok) (lam : Nat) (hlam : lam + 1 = fc.h)
    (hchk : foldCheck fc.base fc.h (0x800 + fc.sibOff) fc.dst = true) (s0 : MachineState)
    (v : Val) (s : MachineState) (hs : FoldInv fc s0 lam v s) :
    ∃ t, Steps image s 9 9 t ∧ t.getReg .x5 = 0 ∧ hashArgumentsValid t = true ∧
      hashInput t = pad64 (fc.input lam v) ∧ FoldEnd fc s0 t := by
  have hb2 := bitOf_lt fc.E lam
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okFold_spec (foldCheck_at hchk lam (bitOf fc.E lam) (by omega) hb2)
  simp only [foldPost, if_pos hlam] at hkn
  obtain ⟨hG, hK, h23, h24, hN0, hN8, hv0, hv1, hvl, hF, hpc⟩ := hs
  obtain ⟨hh1, hh10, hE, ht, hf2, hwl, hs8, hsz, hsafe, hdst, hbase⟩ := hfc
  set b := bitOf fc.E lam with hbdef
  set r := foldExp fc.base fc.h lam b (0x800 + fc.sibOff + 16 * lam) fc.dst with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, foldExp, hlam])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0x1C0 := hK' (.x10, 0x1C0) (by simp)
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, 64) (by simp)
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 fc.dst :=
    hK' (.x12, _) (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))))
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0x1C8⟩, stW 0x1C8 (cwf 0)),
       (⟨none, BitVec.ofNat 64 0x1C0⟩, stW 0x1C0 (cwf (lam + 1))),
       (⟨none, BitVec.ofNat 64 (0x1F0 - 16 * b + 8)⟩, .ld (cwf (0x800 + fc.sibOff + 16 * lam + 8))),
       (⟨none, BitVec.ofNat 64 (0x1F0 - 16 * b)⟩, .ld (cwf (0x800 + fc.sibOff + 16 * lam)))] := by
    simp [hr, foldExp, hlam]
  have hsib := sib_words fc ⟨hh1, hh10, hE, ht, hf2, hwl, hs8, hsz, hsafe, hdst, hbase⟩ lam (by omega) s hG
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have m1C0 : (r.toState s).getMem (BitVec.ofNat 64 0x1C0) =
      BitVec.ofNat 64 (fc.lo0 + 2 ^ 32 * (lam + 1)) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_eq _ _ _ _ _ rfl, stW_eval]
    simp only [Rv.E.eval, cwf]
    rw [stMerge_eval _ _ _ (by omega) hN0]
  have m1C8 : (r.toState s).getMem (BitVec.ofNat 64 0x1C8) = BitVec.ofNat 64 (fc.tau % 2 ^ 32) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl, stW_eval]
    simp only [Rv.E.eval, cwf]
    rw [stMerge_eval _ _ _ (by omega) hN8, Nat.mul_zero, Nat.add_zero]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0x1C8 → A ≠ 0x1C0 → A ≠ 0x1F0 - 16 * b + 8 →
      A ≠ 0x1F0 - 16 * b → (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by
      rw [hmem]; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp <;> omega)]
  have msib0 : (r.toState s).getMem (BitVec.ofNat 64 (0x1F0 - 16 * b)) = vw0 (fc.sib lam) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_eq _ _ _ _ _ rfl]
    simp only [Rv.E.eval, cwf]; exact hsib.1
  have msib1 : (r.toState s).getMem (BitVec.ofNat 64 (0x1F0 - 16 * b + 8)) = vw1 (fc.sib lam) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by bvne),
      memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
    simp only [Rv.E.eval, cwf]; exact hsib.2
  have mv0 : (r.toState s).getMem (BitVec.ofNat 64 (0x1E0 + 16 * b)) = vw0 v := by
    rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv0
  have mv1 : (r.toState s).getMem (BitVec.ofNat 64 (0x1E8 + 16 * b)) = vw1 v := by
    rw [mfr _ (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hv1
  refine ⟨r.toState s, ?_, ?_, ?_, ?_, ?_⟩
  · have e1 : r.steps = 9 := by simp only [hr, foldExp, if_pos hlam]
    have e2 : r.cycles = 9 := by simp only [hr, foldExp, if_pos hlam]
    rw [e1, e2] at hst; exact hst
  · exact hK' (.x5, 0) (by simp [globK])
  · have hs' := hsafe
    simp only [safeDest, Bool.and_eq_true, decide_eq_true_eq] at hs'
    exact hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega)
  · rw [hashInput_ofNat _ 0x1C0 0 h10 h11 (by decide) (by decide),
      pad64_input fc ⟨hh1, hh10, hE, ht, hf2, hwl, hs8, hsz, hsafe, hdst, hbase⟩ lam (by omega) v hvl]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero]
    have hlo : twLo fc.t fc.f2 fc.tau (lam + 1) = fc.lo0 + 2 ^ 32 * (lam + 1) := by
      unfold twLo FCtx.lo0; omega
    have hj : fc.E / 2 ^ (lam + 1) = 0 := Nat.div_eq_of_lt (by rw [hlam]; exact hE)
    have hhi : twHi fc.tau (fc.E / 2 ^ (lam + 1)) = fc.tau % 2 ^ 32 := by
      unfold twHi; rw [hj]; omega
    rw [hlo, hhi, m1C0, m1C8, mfr 0x1D0 (by omega) (by omega) (by omega) (by omega) (by omega),
      mfr 0x1D8 (by omega) (by omega) (by omega) (by omega) (by omega), hP 0x1D0 (by decide),
      hP 0x1D8 (by decide)]
    rcases (show b = 0 ∨ b = 1 by omega) with h0 | h1
    · rw [h0] at mv0 mv1 msib0 msib1
      simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero, Nat.reduceAdd, Nat.reduceMul,
        Nat.reduceSub] at mv0 mv1 msib0 msib1
      rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h0]
    · rw [h1] at mv0 mv1 msib0 msib1
      simp only [Nat.mul_one, Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub] at mv0 mv1 msib0 msib1
      rw [mv0, mv1, msib0, msib1]; simp [← hbdef, h1]
  · refine ⟨hglob _ _ hG, hK', FrameOK.trans hF (fun r hr => hkeep' r hr) (fun A hA hA' => ?_), ?_,
      hec (by simp [hr, foldExp, hlam]), by rw [m1C8, BitVec.toNat_ofNat]; omega⟩
    · exact mfr A hA (by omega) (by omega) (by omega) (by omega)
    · rw [PRes.toState_pc]
      simp only [hr, foldExp, if_pos hlam]
      rw [show fc.h - 1 = lam by omega]

/-! ## The whole fold -/

def FCtx.stepFn (fc : FCtx) : Val → Nat → OracleComp HashSpec Val := fun v lam =>
  let sib := fc.path.getD lam []
  let j := fc.E / 2 ^ (lam + 1)
  if fc.E / 2 ^ lam % 2 = 1 then hash16 (fc.node (lam + 1) j sib v)
  else hash16 (fc.node (lam + 1) j v sib)

theorem stepFn_eq (fc : FCtx) (lam : Nat) (hlam : lam < fc.h) (v : Val) :
    fc.stepFn v lam = hash16 (fc.input lam v) := by
  have : fc.path.getD lam [] = fc.sib lam := by
    simp [FCtx.path, FCtx.sib, List.getD_eq_getElem?_getD, List.getElem?_map, hlam]
  unfold FCtx.stepFn FCtx.input
  rw [this]
  split <;> rfl

theorem foldPath_eq (fc : FCtx) (v : Val) :
    foldPath fc.node fc.E v fc.path = (List.range' 0 fc.h).foldlM fc.stepFn v := by
  unfold foldPath
  rw [show fc.path.length = fc.h by simp [FCtx.path], List.range_eq_range']
  rfl

def levelCost (h lam : Nat) : Nat := if lam + 1 = h then 17 else if lam = 3 then 19 else 20

def foldCost (h lam k : Nat) : Nat := ((List.range' lam k).map (levelCost h)).sum

theorem fold_good (fc : FCtx) (hfc : fc.ok)
    (hchk : foldCheck fc.base fc.h (0x800 + fc.sibOff) fc.dst = true) (s0 : MachineState)
    (K : Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ a u, FoldEnd fc s0 u → Good (writeHash u a) N C (K (answerBytes 16 a))) :
    ∀ k lam, lam + k = fc.h → 0 < k → ∀ v s, FoldInv fc s0 lam v s →
      Good s (N + 14 * k) (C + foldCost fc.h lam k)
        (cc ((List.range' lam k).foldlM fc.stepFn v) K) := by
  intro k
  induction k with
  | zero => intro lam _ h; omega
  | succ k ih =>
    intro lam hk _ v s hs
    have hvl : v.length = 16 := hs.2.2.2.2.2.2.2.2.1
    have hblk : (pad64 (fc.input lam v)).blocks = 1 := by
      rw [pad64_input fc hfc lam (by omega) v hvl]; rfl
    rw [List.range'_succ, List.foldlM_cons, stepFn_eq fc lam (by omega), cc_bind]
    by_cases hlast : lam + 1 = fc.h
    · obtain rfl : k = 0 := by omega
      obtain ⟨t, hst, h5, hv, hin, hend⟩ := level_last fc hfc lam hlast hchk s0 v s hs
      simp only [List.range'_zero, List.foldlM_nil, cc_pure]
      have h3 := Good.hash (K := K) hend.2.2.2.2.1 h5 hv hin (fun a => hK a t hend)
      rw [hblk] at h3
      refine Good.steps' hst h3 (by omega) ?_
      simp [foldCost, levelCost, hlast]
    · obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := level_lt fc hfc lam (by omega) hchk s0 v s hs
      have h3 := Good.hash (K := fun v => cc ((List.range' (lam + 1) k).foldlM fc.stepFn v) K)
        hf h5 hv hin (fun a => ih (lam + 1) (by omega) (by omega) _ _ (hpost a))
      rw [hblk] at h3
      refine Good.steps' hst h3 (by split <;> omega) ?_
      simp only [foldCost, List.range'_succ, List.map_cons, List.sum_cons, levelCost, if_neg hlast]
      split <;> omega

end SigGolfCandidate.Verify
