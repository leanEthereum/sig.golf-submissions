import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.Common

/-! # Chains: semantics of the chain blocks (heads, table entries, steps) -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

structure CCtx where
  wl : List Byte
  pk : List Byte
  lay : Nat
  tau : Nat
  e : Nat
  d0 : Word
  d1 : Word

def CCtx.x31 (c : CCtx) : Word := BitVec.ofNat 64 (c.tau + 2 ^ 32 * c.e)

def CCtx.Regs (c : CCtx) (s : MachineState) : Prop :=
  s.getReg .x16 = c.d0 ∧ s.getReg .x17 = c.d1 ∧
  s.getReg .x23 = BitVec.ofNat 64 c.e ∧ s.getReg .x30 = BitVec.ofNat 64 c.tau ∧
  s.getReg .x31 = c.x31

def CCtx.ok (c : CCtx) : Prop :=
  c.lay < 7 ∧ c.tau < 2 ^ 32 ∧ c.e < 2 ^ 32 ∧ c.wl.length = 7756 ∧ c.d0.toNat < 2 ^ 63 ∧
    c.d1.toNat < 2 ^ 63

def CBOk (c : CCtx) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 0xC0)).toNat % 2 ^ 32 = 0x101 + 65536 * c.lay ∧
  s.getMem (BitVec.ofNat 64 0xC8) = c.x31

/-- Digit `i` of the current layer. -/
def dig (c : CCtx) (i : Nat) : Nat := (if i < 21 then c.d0 else c.d1).toNat / 8 ^ (i % 21) % 8

/-- First chain of the pair of chain `i`. -/
def pf (i : Nat) : Nat := if isFirst i then i else i - 1

/-- Table entry index of chain `i`. -/
def entIdx (c : CCtx) (i : Nat) : Nat :=
  if isSingle i then dig c i else dig c (pf i) + 8 * dig c (pf i + 1)

/-- The dispatch register of chain `i`. -/
def rOf (c : CCtx) (i : Nat) : Nat := bVal c.lay i + 16 * entIdx c i

def headPc (lay i t : Nat) : Nat := if i = 0 then tget c0Tab lay t else nextPc' lay (i - 1)

def HeadInv (c : CCtx) (i : Nat) (acc : List Val) (s : MachineState) : Prop :=
  Glob gkL c.wl c.pk s ∧ KnownOK (headK c.lay i) s ∧ c.Regs s ∧ CBOk c s ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧ LBOk acc s ∧
  acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ (∃ t, t < 2 ∧ s.pc = pcOf (headPc c.lay i t)) ∧
  (i < 42 → hasPrep i = false → s.getReg .x14 = BitVec.ofNat 64 (rOf c i))

def RB (c : CCtx) (i : Nat) (s : MachineState) : Prop :=
  s.getReg .x15 = BitVec.ofNat 64 (bVal c.lay i) ∧ s.getReg .x14 = BitVec.ofNat 64 (rOf c i)

/-- At the table entry of chain `i`, with the chain value loaded. -/
def EntInv (c : CCtx) (i : Nat) (acc : List Val) (s : MachineState) : Prop :=
  Glob gkL c.wl c.pk s ∧ KnownOK (chK c.lay 0xE0) s ∧ c.Regs s ∧ CBOk c s ∧ RB c i s ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧ LBOk acc s ∧
  acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧
  s.getReg .x1 = vw0 (witChain c.wl c.lay i) ∧ s.getReg .x2 = vw1 (witChain c.wl c.lay i) ∧
  s.pc = pcOf (entryIdx c.lay i (entIdx c i))

/-- At step label `s_mu` with value `v` in CB+32. -/
def StepInv (c : CCtx) (i : Nat) (acc : List Val) (mu : Nat) (v : Val) (s : MachineState) : Prop :=
  Glob gkL c.wl c.pk s ∧ KnownOK (chK c.lay 0xE0) s ∧ c.Regs s ∧ CBOk c s ∧ RB c i s ∧
  s.getMem (BitVec.ofNat 64 0xE0) = vw0 v ∧ s.getMem (BitVec.ofNat 64 0xE8) = vw1 v ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧ LBOk acc s ∧
  acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ v.length = 16 ∧
  s.pc = pcOf (s1Pc c.lay i + 5 * (mu - 1))

/-- After the ecall of step `mu < 7` (pad not yet zeroed). -/
def PostInv (c : CCtx) (i : Nat) (acc : List Val) (mu : Nat) (v : Val) (s : MachineState) : Prop :=
  Glob gkL c.wl c.pk s ∧ KnownOK (chK c.lay 0xE0) s ∧ c.Regs s ∧ CBOk c s ∧ RB c i s ∧
  s.getMem (BitVec.ofNat 64 0xE0) = vw0 v ∧ s.getMem (BitVec.ofNat 64 0xE8) = vw1 v ∧ LBOk acc s ∧
  acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ v.length = 16 ∧
  s.pc = pcOf (s1Pc c.lay i + 5 * (mu - 1) + 3)

/-- After the ecall of step 7. -/
def EndInv (c : CCtx) (i : Nat) (acc : List Val) (v : Val) (s : MachineState) : Prop :=
  Glob gkL c.wl c.pk s ∧ KnownOK (chK c.lay (0x360 + 16 * i)) s ∧ c.Regs s ∧ CBOk c s ∧ RB c i s ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧
  LBOk (acc ++ [v]) s ∧ acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ v.length = 16 ∧
  s.pc = pcOf (s1Pc c.lay i + 34)

theorem length_witChain (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) :
    (witChain c.wl c.lay i).length = 16 := by
  obtain ⟨h1, -, -, h4, -⟩ := hc
  unfold witChain witLayerOff
  apply length_slice16; omega

/-! ## Family facts -/


theorem okC_spec {o : Option PRes} {e : PRes} {post : List (Reg × Word)} {keep : List Reg}
    (h : okC o e post keep = true) :
    o = some e ∧ resOK gkL e = true ∧ knownB post e = true ∧ keepB keep e = true := by
  simp only [okC, Bool.and_eq_true] at h
  exact ⟨optBeq_eq h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem check_step {lay i : Nat} (h : chainCheck lay i = true) (mu : Nat) (h1 : 1 ≤ mu) (h2 : mu ≤ 7) :
    okC (runAt (chK lay 0xE0) [] (s1Pc lay i + 5 * (mu - 1)) []) (stepExp lay i mu)
      (chK lay (if mu = 7 then 0x360 + 16 * i else 0xE0)) ckeep = true := by
  simp only [chainCheck, stepsCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.2.1.1 (mu - 1) (by omega)
  rw [show mu - 1 + 1 = mu by omega] at this
  by_cases h7 : mu = 7
  · subst h7; simpa using this
  · simpa [h7, show mu - 1 ≠ 6 by omega] using this

theorem check_tail {lay i : Nat} (h : chainCheck lay i = true) (mu : Nat) (h1 : 1 ≤ mu) (h2 : mu ≤ 6) :
    okC (runAt (chK lay 0xE0) [s1Pc lay i + 5 * mu] (s1Pc lay i + 5 * (mu - 1) + 3) [])
      (tailExp lay i mu) (chK lay 0xE0) ckeep = true := by
  simp only [chainCheck, stepsCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.2.1.2 (mu - 1) (by omega)
  rwa [show mu - 1 + 1 = mu by omega] at this

theorem check_end {lay i : Nat} (h : chainCheck lay i = true) :
    okC (runAt (chK lay (0x360 + 16 * i)) [nextPc' lay i] (s1Pc lay i + 34) []) (endExp lay i)
      (chK lay 0xE0) ckeep = true := by
  simp only [chainCheck, stepsCheck, Bool.and_eq_true] at h
  exact h.1.2.2

theorem check_head {lay i : Nat} (h : chainCheck lay i = true) (hi : i ≠ 0) :
    okC (runAt (headK lay i) [] (nextPc' lay (i - 1)) [.jmp]) (headExp lay i)
      (chK lay 0xE0 ++ [(.x15, BitVec.ofNat 64 (bVal lay i))]) (headKeep i) = true := by
  simp only [chainCheck, headCheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h.1.1.resolve_left hi

theorem entChk_spec (lay i : Nat) : ∀ (n e : Nat),
    entChk lay i (Images.verifyCode.drop (entryIdx lay i e)) e n = true →
    ∀ f, e ≤ f → f < e + n →
      symRun cfg0 (Images.verifyCode.drop (entryIdx lay i f)) (pcOf (entryIdx lay i f)) 3 =
        some (entryRes lay i (entDigit i f)) := by
  intro n
  induction n with
  | zero => intro e _ f h1 h2; omega
  | succ n ih =>
    intro e h f h1 h2
    simp only [entChk, Bool.and_eq_true] at h
    by_cases hf : f = e
    · subst hf
      obtain ⟨h1, -⟩ := h
      split at h1
      · rename_i r hr; rw [hr, resBeq_eq h1]
      · cases h1
    · apply ih (e + 1) _ f (by omega) (by omega)
      have := h.2
      rwa [List.drop_drop, show entryIdx lay i e + 4 = entryIdx lay i (e + 1) by
        unfold entryIdx; omega] at this

/-! ## Steps -/

theorem Regs_keep {c : CCtx} {r : PRes} {s : MachineState} (hR : c.Regs s)
    (hkeep : ∀ x ∈ ckeep, (r.toState s).getReg x = s.getReg x) : c.Regs (r.toState s) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hR
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [hkeep _ (by simp [ckeep])]; assumption)

theorem RB_keep {c : CCtx} {i : Nat} {r : PRes} {s : MachineState} (hB : RB c i s)
    (hkeep : ∀ x ∈ ckeep, (r.toState s).getReg x = s.getReg x) : RB c i (r.toState s) := by
  obtain ⟨h1, h2⟩ := hB
  refine ⟨?_, ?_⟩ <;> (rw [hkeep _ (by simp [ckeep])]; assumption)

theorem Regs_wh {c : CCtx} {s : MachineState} (hR : c.Regs s) (a : BitVec 256) :
    c.Regs (writeHash s a) := by
  simp only [CCtx.Regs, writeHash_getReg]; exact hR

theorem RB_wh {c : CCtx} {i : Nat} {s : MachineState} (hB : RB c i s) (a : BitVec 256) :
    RB c i (writeHash s a) := by
  simp only [RB, writeHash_getReg]; exact hB

theorem chK_x10 (lay a2 : Nat) : ((.x10 : Reg), (0xC0 : Word)) ∈ chK lay a2 := by simp [chK]
theorem chK_x11 (lay a2 : Nat) : ((.x11 : Reg), (64 : Word)) ∈ chK lay a2 := by simp [chK]
theorem chK_x12 (lay a2 : Nat) : ((.x12 : Reg), BitVec.ofNat 64 a2) ∈ chK lay a2 :=
  List.mem_append_right _ (by simp)
theorem chK_x5 (lay a2 : Nat) : ((.x5 : Reg), (0 : Word)) ∈ chK lay a2 := by simp [chK, gkL, baseK]

theorem step_head (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val) (mu : Nat)
    (hmu1 : 1 ≤ mu) (hmu6 : mu ≤ 6) (hchk : chainCheck c.lay i = true) (v : Val) (s : MachineState)
    (hs : StepInv c i acc mu v s) :
    ∃ t, Steps image s 2 2 t ∧ fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = pad64 (chainInput c.lay c.tau c.e i mu v) ∧
      ∀ a, PostInv c i acc mu (answerBytes 16 a) (writeHash t a) := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okC_spec (check_step hchk mu hmu1 (by omega))
  rw [if_neg (by omega)] at hkn
  obtain ⟨hG, hK, hR, hCB, hB, hE0, hE8, hF0, hF8, hLB, hlen, hvs, hv, hpc⟩ := hs
  set r := stepExp c.lay i mu with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, stepExp, show mu ≠ 7 by omega])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0xC0 := hK' _ (chK_x10 _ _)
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' _ (chK_x11 _ _)
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 0xE0 := hK' _ (chK_x12 _ _)
  obtain ⟨hlay, htau, he, hwl, -⟩ := hc
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0xC0⟩, stW 0xC0 (cw (8 * i + mu - 1)))] := by
    simp [hr, stepExp, show mu ≠ 7 by omega]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0xC0 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by rw [hmem]; simp; omega)]
  have m0 : (r.toState s).getMem (BitVec.ofNat 64 0xC0) =
      BitVec.ofNat 64 (0x101 + 65536 * c.lay + 2 ^ 32 * (8 * i + mu - 1)) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
    simp only [stW, ldE, cw, Rv.E.eval, BinOp.eval]
    rw [stMerge_eval _ _ _ (by omega) hCB.1]
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  refine ⟨r.toState s, ?_, hec (by simp [hr, stepExp, show mu ≠ 7 by omega]),
    hK' _ (chK_x5 _ _), hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide),
    ?_, ?_⟩
  · simpa [hr, stepExp, show mu ≠ 7 by omega] using hst
  · rw [hashInput_ofNat _ 0xC0 0 h10 h11 (by decide) (by decide), pad64_chainInput _ _ _ _ _ _ hv]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero, List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [m0]; congr 1; unfold twLo; rw [Nat.div_eq_of_lt htau]; omega
    · rw [mfr 0xC8 (by omega) (by omega), hCB.2]; unfold CCtx.x31 twHi; congr 1; omega
    · rw [mfr 0xD0 (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0xD8 (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0xE0 (by omega) (by omega)]; exact hE0
    · rw [mfr 0xE8 (by omega) (by omega)]; exact hE8
    · rw [mfr 0xF0 (by omega) (by omega)]; exact hF0
    · rw [mfr 0xF8 (by omega) (by omega)]; exact hF8
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0xE0 ∨ 0xE0 + 32 ≤ A) =>
      writeHash_frame _ a 0xE0 A h12 hA (by omega) h
    refine ⟨Glob_writeHash (hglob _ _ hG) a 0xE0 h12 (by decide), Known_writeHash hK' a,
      Regs_wh (Regs_keep hR hkeep') a, ⟨?_, ?_⟩, RB_wh (RB_keep hB hkeep') a, ?_, ?_, ?_, hlen, hvs,
      by simp, ?_⟩
    · rw [wf 0xC0 (by omega) (by omega), m0, BitVec.toNat_ofNat]; omega
    · rw [wf 0xC8 (by omega) (by omega), mfr 0xC8 (by omega) (by omega)]; exact hCB.2
    · rw [writeHash_at0 _ a 0xE0 h12 (by omega)]; simp [vw0_answer]
    · rw [writeHash_at8 _ a 0xE0 h12 (by omega)]; simp [vw1_answer]
    · refine LBOk_frame hLB (fun j hj => ?_)
      rw [hlen] at hj
      rw [wf _ (by omega) (by omega), wf _ (by omega) (by omega), mfr _ (by omega) (by omega),
        mfr _ (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [writeHash_pc, PRes.toState_pc _ _ (by simp [hr, stepExp, show mu ≠ 7 by omega])]
      simp only [hr, stepExp, show mu ≠ 7 by omega, if_false]
      rw [pcOf_add4]

theorem step_tail (c : CCtx) (i : Nat) (hi : i < 42) (acc : List Val) (mu : Nat)
    (hmu1 : 1 ≤ mu) (hmu6 : mu ≤ 6) (hchk : chainCheck c.lay i = true) (v : Val) (s : MachineState)
    (hs : PostInv c i acc mu v s) :
    ∃ t, Steps image s 2 2 t ∧ StepInv c i acc (mu + 1) v t := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okC_spec (check_tail hchk mu hmu1 hmu6)
  obtain ⟨hG, hK, hR, hCB, hB, hE0, hE8, hLB, hlen, hvs, hv, hpc⟩ := hs
  set r := tailExp c.lay i mu with hr
  obtain ⟨hst, -, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, tailExp])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0xF8⟩, .c 0), (⟨none, BitVec.ofNat 64 0xF0⟩, .c 0)] := by
    simp [hr, tailExp]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0xF0 → A ≠ 0xF8 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by
      rw [hmem]; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl) <;> simp <;> omega)]
  refine ⟨r.toState s, by simpa [hr, tailExp] using hst, hglob _ _ hG, hK', Regs_keep hR hkeep',
    ⟨?_, ?_⟩, RB_keep hB hkeep', ?_, ?_, ?_, ?_, ?_, hlen, hvs, hv, ?_⟩
  · rw [mfr 0xC0 (by omega) (by omega) (by omega)]; exact hCB.1
  · rw [mfr 0xC8 (by omega) (by omega) (by omega)]; exact hCB.2
  · rw [mfr 0xE0 (by omega) (by omega) (by omega)]; exact hE0
  · rw [mfr 0xE8 (by omega) (by omega) (by omega)]; exact hE8
  · rw [PRes.toState_getMem, hmem, memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]; rfl
  · rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]; rfl
  · exact LBOk_frame hLB (fun j hj => by
      rw [hlen] at hj
      exact ⟨mfr _ (by omega) (by omega) (by omega), mfr _ (by omega) (by omega) (by omega)⟩)
  · rw [PRes.toState_pc _ _ (by simp [hr, tailExp])]; simp only [hr, tailExp, Nat.add_sub_cancel]

set_option maxRecDepth 8000 in
theorem step_7 (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (v : Val) (s : MachineState)
    (hs : StepInv c i acc 7 v s) :
    ∃ t, Steps image s 3 3 t ∧ fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = pad64 (chainInput c.lay c.tau c.e i 7 v) ∧
      ∀ a, EndInv c i acc (answerBytes 16 a) (writeHash t a) := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okC_spec (check_step hchk 7 (by omega) (by omega))
  rw [if_pos rfl] at hkn
  obtain ⟨hG, hK, hR, hCB, hB, hE0, hE8, hF0, hF8, hLB, hlen, hvs, hv, hpc⟩ := hs
  set r := stepExp c.lay i 7 with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, stepExp])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0xC0 := hK' _ (chK_x10 _ _)
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' _ (chK_x11 _ _)
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 (0x360 + 16 * i) := hK' _ (chK_x12 _ _)
  obtain ⟨hlay, htau, he, hwl, -⟩ := hc
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0xC0⟩, stW 0xC0 (cw (8 * i + 7 - 1)))] := by
    simp [hr, stepExp]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0xC0 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by rw [hmem]; simp; omega)]
  have m0 : (r.toState s).getMem (BitVec.ofNat 64 0xC0) =
      BitVec.ofNat 64 (0x101 + 65536 * c.lay + 2 ^ 32 * (8 * i + 7 - 1)) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
    simp only [stW, ldE, cw, Rv.E.eval, BinOp.eval]
    rw [stMerge_eval _ _ _ (by omega) hCB.1]
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  refine ⟨r.toState s, ?_, hec (by simp [hr, stepExp]),
    hK' _ (chK_x5 _ _), hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega), ?_, ?_⟩
  · simpa [hr, stepExp] using hst
  · rw [hashInput_ofNat _ 0xC0 0 h10 h11 (by decide) (by decide), pad64_chainInput _ _ _ _ _ _ hv]
    apply congrArg (queryOfWords 0)
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero, List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [m0]; apply congrArg (BitVec.ofNat 64); unfold twLo; rw [Nat.div_eq_of_lt htau]; omega
    · rw [mfr 0xC8 (by omega) (by omega), hCB.2]; unfold CCtx.x31 twHi; apply congrArg (BitVec.ofNat 64); omega
    · rw [mfr 0xD0 (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0xD8 (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0xE0 (by omega) (by omega)]; exact hE0
    · rw [mfr 0xE8 (by omega) (by omega)]; exact hE8
    · rw [mfr 0xF0 (by omega) (by omega)]; exact hF0
    · rw [mfr 0xF8 (by omega) (by omega)]; exact hF8
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x360 + 16 * i ∨ 0x360 + 16 * i + 32 ≤ A) =>
      writeHash_frame _ a (0x360 + 16 * i) A h12 hA (by omega) h
    refine ⟨Glob_writeHash (hglob _ _ hG) a _ h12 (by simp only [safeDest, pSlots]; simp; omega),
      Known_writeHash hK' a, Regs_wh (Regs_keep hR hkeep') a, ⟨?_, ?_⟩, RB_wh (RB_keep hB hkeep') a,
      ?_, ?_, ?_, hlen, hvs, by simp, ?_⟩
    · rw [wf 0xC0 (by omega) (by omega), m0, BitVec.toNat_ofNat]; omega
    · rw [wf 0xC8 (by omega) (by omega), mfr 0xC8 (by omega) (by omega)]; exact hCB.2
    · rw [wf 0xF0 (by omega) (by omega), mfr 0xF0 (by omega) (by omega)]; exact hF0
    · rw [wf 0xF8 (by omega) (by omega), mfr 0xF8 (by omega) (by omega)]; exact hF8
    · refine LBOk_append (LBOk_frame hLB (fun j hj => ?_)) _ ?_ ?_
      · rw [hlen] at hj
        rw [wf _ (by omega) (by omega), wf _ (by omega) (by omega), mfr _ (by omega) (by omega),
          mfr _ (by omega) (by omega)]
        exact ⟨rfl, rfl⟩
      · rw [hlen, writeHash_at0 _ a _ h12 (by omega)]; simp [vw0_answer]
      · rw [hlen, show 0x368 + 16 * i = 0x360 + 16 * i + 8 by omega,
          writeHash_at8 _ a _ h12 (by omega)]; simp [vw1_answer]
    · rw [writeHash_pc, PRes.toState_pc _ _ (by simp [hr, stepExp])]
      simp only [hr, stepExp, if_true]
      rw [pcOf_add4]

end SigGolfCandidate.Verify
