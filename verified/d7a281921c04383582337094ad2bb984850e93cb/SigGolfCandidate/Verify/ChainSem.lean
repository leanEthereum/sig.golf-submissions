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

/-- CB+32..48 (between the P slot and the value) is zero. -/
def CBZ (s : MachineState) : Prop :=
  s.getMem (BitVec.ofNat 64 0xE0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xE8) = 0

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
  Glob gkL c.wl c.pk s ∧ KnownOK (headK c.lay i) s ∧ c.Regs s ∧ CBOk c s ∧ CBZ s ∧ LBOk acc s ∧
  acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ (∃ t, t < 2 ∧ s.pc = pcOf (headPc c.lay i t)) ∧
  (i < 42 → hasPrep i = false → s.getReg .x14 = BitVec.ofNat 64 (rOf c i))

def RB (c : CCtx) (i : Nat) (s : MachineState) : Prop :=
  s.getReg .x15 = BitVec.ofNat 64 (bVal c.lay i) ∧ s.getReg .x14 = BitVec.ofNat 64 (rOf c i)

/-- At the table entry of chain `i`, with the chain value loaded. -/
def EntInv (c : CCtx) (i : Nat) (acc : List Val) (s : MachineState) : Prop :=
  Glob gkL c.wl c.pk s ∧ KnownOK (chKa c.lay) s ∧ c.Regs s ∧ CBOk c s ∧ RB c i s ∧ CBZ s ∧
  LBOk acc s ∧ acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧
  s.getReg .x1 = vw0 (witChain c.wl c.lay i) ∧ s.getReg .x2 = vw1 (witChain c.wl c.lay i) ∧
  s.pc = pcOf (entryIdx c.lay i (entIdx c i))

/-- At step label `s_mu` with value `v` in CB+48. -/
def StepInv (c : CCtx) (i : Nat) (acc : List Val) (mu : Nat) (v : Val) (s : MachineState) : Prop :=
  Glob gkL c.wl c.pk s ∧ KnownOK (chKa c.lay) s ∧ c.Regs s ∧ CBOk c s ∧ RB c i s ∧ CBZ s ∧
  s.getMem (BitVec.ofNat 64 0xF0) = vw0 v ∧ s.getMem (BitVec.ofNat 64 0xF8) = vw1 v ∧ LBOk acc s ∧
  acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ v.length = 16 ∧
  s.pc = pcOf (s1Pc c.lay i + 3 * (mu - 1))

/-- After the ecall of step 7 (the end value is in leaf slot `i`). -/
def EndInv (c : CCtx) (i : Nat) (acc : List Val) (v : Val) (s : MachineState) : Prop :=
  Glob gkL c.wl c.pk s ∧ KnownOK (chK c.lay) s ∧ c.Regs s ∧ CBOk c s ∧ RB c i s ∧ CBZ s ∧
  LBOk (acc ++ [v]) s ∧ acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ v.length = 16 ∧
  s.pc = pcOf (s1Pc c.lay i + 22)

theorem length_witChain (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) :
    (witChain c.wl c.lay i).length = 16 := by
  obtain ⟨h1, -, -, h4, -⟩ := hc
  unfold witChain witLayerOff
  apply length_slice16; omega

/-- The chain block `tw || 0^32 || v` (the oracle input format of a chain step). -/
theorem fmt_chainInput_words (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16) :
    fmt (chainInput lay tau e i mu v) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 1 lay tau (8 * i + mu - 1)), BitVec.ofNat 64 (twHi tau e), 0, 0, 0, 0,
        vw0 v, vw1 v] := by
  rw [fmt_chainInput _ _ _ _ _ _ hv]
  have hl : (tweak 1 lay tau (8 * i + mu - 1) e ++ zeros 32 ++ v).length ≤ 8 * 8 := by
    simp [length_tweak, hv]
  have h8 : wordsOfN 8 (tweak 1 lay tau (8 * i + mu - 1) e ++ (zeros 32 ++ v)) =
      wordsOfN 2 (tweak 1 lay tau (8 * i + mu - 1) e) ++ wordsOfN 6 (zeros 32 ++ v) :=
    wordsOfN_append 2 6 _ _ (by simp [length_tweak])
  have h6 : wordsOfN 6 (zeros 32 ++ v) = wordsOfN 4 (zeros (8 * 4)) ++ wordsOfN 2 v :=
    wordsOfN_append 4 2 _ _ (by simp [length_zeros])
  have h2 : wordsOfN 2 v = [vw0 v, vw1 v] := by
    have := wordsOfN_val_append v hv 0 []
    simpa [wordsOfN] using this
  have hw : wordsOfN 8 (tweak 1 lay tau (8 * i + mu - 1) e ++ zeros 32 ++ v) =
      [BitVec.ofNat 64 (twLo 1 lay tau (8 * i + mu - 1)), BitVec.ofNat 64 (twHi tau e), 0, 0, 0, 0,
        vw0 v, vw1 v] := by
    rw [List.append_assoc, h8, h6, wordsOfN_tweak, wordsOfN_zeros, h2]; rfl
  unfold queryOfWords ofList
  rw [← hw, wordsToNat_wordsOfN 8 _ hl]

/-! ## Family facts -/


theorem okC_spec {o : Option PRes} {e : PRes} {post : List (Reg × Word)} {keep : List Reg}
    (h : okC o e post keep = true) :
    o = some e ∧ resOK gkL e = true ∧ knownB post e = true ∧ keepB keep e = true := by
  simp only [okC, Bool.and_eq_true] at h
  exact ⟨optBeq_eq h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem check_step {lay i : Nat} (h : chainCheck lay i = true) (mu : Nat) (h1 : 1 ≤ mu) (h2 : mu ≤ 7) :
    okC (runAt (chKa lay) [] (s1Pc lay i + 3 * (mu - 1)) []) (stepExp lay i mu)
      (chK lay ++ [(.x12, BitVec.ofNat 64 (if mu = 7 then 0x360 + 16 * i else 0xF0))]) ckeep = true := by
  simp only [chainCheck, stepsCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.2 (mu - 1) (by omega)
  rw [show mu - 1 + 1 = mu by omega] at this
  by_cases h7 : mu = 7
  · subst h7; simpa using this
  · simpa [h7, show mu - 1 ≠ 6 by omega] using this

theorem check_head {lay i : Nat} (h : chainCheck lay i = true) (hi : i ≠ 0) :
    okC (runAt (headK lay i) [] (nextPc' lay (i - 1)) [.jmp]) (headExp lay i)
      (chKa lay ++ [(.x15, BitVec.ofNat 64 (bVal lay i))]) (headKeep i) = true := by
  simp only [chainCheck, headCheck, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact h.1.1.resolve_left hi

theorem entChk_spec (lay i : Nat) : ∀ (n e : Nat),
    entChk lay i (Images.verifyCode.drop (entryIdx lay i e)) e n = true →
    ∀ f, e ≤ f → f < e + n →
      symRun cfg0 (Images.verifyCode.drop (entryIdx lay i f)) (pcOf (entryIdx lay i f)) 4 =
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

theorem chK_x10 (lay : Nat) : ((.x10 : Reg), (0xC0 : Word)) ∈ chK lay := by simp [chK]
theorem chK_x11 (lay : Nat) : ((.x11 : Reg), (64 : Word)) ∈ chK lay := by simp [chK]
theorem chK_x5 (lay : Nat) : ((.x5 : Reg), (0 : Word)) ∈ chK lay := by simp [chK, gkL, baseK]

theorem KnownOK_chK {lay : Nat} {l : List (Reg × Word)} {s : MachineState} (h : KnownOK (chK lay ++ l) s) :
    KnownOK (chK lay) s := (KnownOK_append.mp h).1

/-- The hash input of a chain step: the block `tw || 0^32 || v` at CB. -/
theorem chain_hashInput (c : CCtx) (hc : c.ok) (i mu : Nat) (v : Val) (hv : v.length = 16)
    (t : MachineState) (h10 : t.getReg .x10 = BitVec.ofNat 64 0xC0)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (m0 : t.getMem (BitVec.ofNat 64 0xC0) = BitVec.ofNat 64 (0x101 + 65536 * c.lay + 2 ^ 32 * (8 * i + mu - 1)))
    (hp : 8 * i + mu - 1 < 2 ^ 32)
    (m1 : t.getMem (BitVec.ofNat 64 0xC8) = c.x31) (hP : ∀ a ∈ pSlots, t.getMem (BitVec.ofNat 64 a) = 0)
    (hZ : CBZ t) (m6 : t.getMem (BitVec.ofNat 64 0xF0) = vw0 v)
    (m7 : t.getMem (BitVec.ofNat 64 0xF8) = vw1 v) :
    hashInput t = fmt (chainInput c.lay c.tau c.e i mu v) := by
  obtain ⟨hlay, htau, he, hwl, -⟩ := hc
  rw [hashInput_ofNat _ 0xC0 0 h10 h11 (by decide) (by decide), fmt_chainInput_words _ _ _ _ _ _ hv]
  apply congrArg (queryOfWords 0)
  simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
    Nat.mul_zero, List.cons.injEq]
  refine ⟨?_, ?_, hP _ (by decide), hP _ (by decide), hZ.1, hZ.2, m6, m7, trivial⟩
  · rw [m0]; apply congrArg (BitVec.ofNat 64); unfold twLo; rw [Nat.div_eq_of_lt htau]; omega
  · rw [m1]; unfold CCtx.x31 twHi; apply congrArg (BitVec.ofNat 64); omega

theorem cb0_step (c : CCtx) (s : MachineState) (hCB : CBOk c s) (p : Nat) (hp : p < 2 ^ 32) :
    (stW 0xC0 (cw p)).eval s = BitVec.ofNat 64 (0x101 + 65536 * c.lay + 2 ^ 32 * p) := by
  simp only [stW, ldE, cw, Rv.E.eval, BinOp.eval]
  rw [stMerge_eval _ _ _ hp hCB.1]

/-- Steps `mu = 1 .. 6`: the answer lands at CB+48 as the next value. -/
theorem step_mid (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val) (mu : Nat)
    (hmu1 : 1 ≤ mu) (hmu6 : mu ≤ 6) (hchk : chainCheck c.lay i = true) (v : Val) (s : MachineState)
    (hs : StepInv c i acc mu v s) :
    ∃ t, Steps image s 2 2 t ∧ fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = fmt (chainInput c.lay c.tau c.e i mu v) ∧
      ∀ a, StepInv c i acc (mu + 1) (answerBytes 16 a) (writeHash t a) := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okC_spec (check_step hchk mu hmu1 (by omega))
  rw [if_neg (by omega)] at hkn
  obtain ⟨hG, hK, hR, hCB, hB, hZ, hF0, hF8, hLB, hlen, hvs, hv, hpc⟩ := hs
  set r := stepExp c.lay i mu with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, stepExp, show mu ≠ 7 by omega])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0xC0 := hK' _ (List.mem_append_left _ (chK_x10 _))
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) :=
    hK' _ (List.mem_append_left _ (chK_x11 _))
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 0xF0 :=
    hK' (.x12, BitVec.ofNat 64 0xF0) (List.mem_append_right _ (List.mem_singleton_self _))
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0xC0⟩, stW 0xC0 (cw (8 * i + mu - 1)))] := by
    simp [hr, stepExp, show mu ≠ 7 by omega]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0xC0 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by rw [hmem]; simp; omega)]
  have m0 : (r.toState s).getMem (BitVec.ofNat 64 0xC0) =
      BitVec.ofNat 64 (0x101 + 65536 * c.lay + 2 ^ 32 * (8 * i + mu - 1)) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
    exact cb0_step c s hCB _ (by omega)
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have hglob' := hglob _ _ hG
  have hlay := hc.1
  refine ⟨r.toState s, ?_, hec (by simp [hr, stepExp, show mu ≠ 7 by omega]),
    hK' _ (List.mem_append_left _ (chK_x5 _)),
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide), ?_, ?_⟩
  · simpa [hr, stepExp, show mu ≠ 7 by omega] using hst
  · exact chain_hashInput c hc i mu v hv _ h10 h11 m0 (by omega)
      ((mfr 0xC8 (by omega) (by omega)).trans hCB.2) hglob'.2.2.2
      ⟨(mfr 0xE0 (by omega) (by omega)).trans hZ.1, (mfr 0xE8 (by omega) (by omega)).trans hZ.2⟩
      ((mfr 0xF0 (by omega) (by omega)).trans hF0) ((mfr 0xF8 (by omega) (by omega)).trans hF8)
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0xF0 ∨ 0xF0 + 32 ≤ A) =>
      writeHash_frame _ a 0xF0 A h12 hA (by omega) h
    refine ⟨Glob_writeHash hglob' a 0xF0 h12 (by decide), ?_, Regs_wh (Regs_keep hR hkeep') a,
      ⟨?_, ?_⟩, RB_wh (RB_keep hB hkeep') a, ⟨?_, ?_⟩, ?_, ?_, ?_, hlen, hvs, by simp, ?_⟩
    · intro p hp
      rw [writeHash_getReg]
      simp only [chKa, List.mem_append, List.mem_singleton] at hp
      rcases hp with hp | hp
      · exact hK' p (List.mem_append_left _ hp)
      · subst hp; exact h12
    · rw [wf 0xC0 (by omega) (by omega), m0, BitVec.toNat_ofNat]; omega
    · rw [wf 0xC8 (by omega) (by omega), mfr 0xC8 (by omega) (by omega)]; exact hCB.2
    · rw [wf 0xE0 (by omega) (by omega), mfr 0xE0 (by omega) (by omega)]; exact hZ.1
    · rw [wf 0xE8 (by omega) (by omega), mfr 0xE8 (by omega) (by omega)]; exact hZ.2
    · rw [writeHash_at0 _ a 0xF0 h12 (by omega)]; simp [vw0_answer]
    · rw [show (0xF8 : Nat) = 0xF0 + 8 from rfl, writeHash_at8 _ a 0xF0 h12 (by omega)]; simp [vw1_answer]
    · refine LBOk_frame hLB (fun j hj => ?_)
      rw [hlen] at hj
      rw [wf _ (by omega) (by omega), wf _ (by omega) (by omega), mfr _ (by omega) (by omega),
        mfr _ (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [writeHash_pc, PRes.toState_pc _ _ (by simp [hr, stepExp, show mu ≠ 7 by omega])]
      simp only [hr, stepExp, show mu ≠ 7 by omega, if_false]
      rw [pcOf_add4]; congr 1; omega

/-- Step 7: the answer goes to leaf slot `i`. -/
theorem step_7 (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (v : Val) (s : MachineState)
    (hs : StepInv c i acc 7 v s) :
    ∃ t, Steps image s 3 3 t ∧ fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = fmt (chainInput c.lay c.tau c.e i 7 v) ∧
      ∀ a, EndInv c i acc (answerBytes 16 a) (writeHash t a) := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okC_spec (check_step hchk 7 (by omega) (by omega))
  rw [if_pos rfl] at hkn
  obtain ⟨hG, hK, hR, hCB, hB, hZ, hF0, hF8, hLB, hlen, hvs, hv, hpc⟩ := hs
  set r := stepExp c.lay i 7 with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, stepExp])
  have hK' := knownB_ok hkn s
  have hkeep' := keepB_ok hkeep s
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0xC0 := hK' _ (List.mem_append_left _ (chK_x10 _))
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) :=
    hK' _ (List.mem_append_left _ (chK_x11 _))
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 (0x360 + 16 * i) :=
    hK' (.x12, BitVec.ofNat 64 (0x360 + 16 * i)) (List.mem_append_right _ (List.mem_singleton_self _))
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0xC0⟩, stW 0xC0 (cw (8 * i + 7 - 1)))] := by
    simp [hr, stepExp]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0xC0 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by rw [hmem]; simp; omega)]
  have m0 : (r.toState s).getMem (BitVec.ofNat 64 0xC0) =
      BitVec.ofNat 64 (0x101 + 65536 * c.lay + 2 ^ 32 * (8 * i + 7 - 1)) := by
    rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
    exact cb0_step c s hCB _ (by omega)
  have hglob' := hglob _ _ hG
  have hlay := hc.1
  refine ⟨r.toState s, ?_, hec (by simp [hr, stepExp]),
    hK' _ (List.mem_append_left _ (chK_x5 _)), hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega)
      (by omega) (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega), ?_, ?_⟩
  · simpa [hr, stepExp] using hst
  · exact chain_hashInput c hc i 7 v hv _ h10 h11 m0 (by omega)
      ((mfr 0xC8 (by omega) (by omega)).trans hCB.2) hglob'.2.2.2
      ⟨(mfr 0xE0 (by omega) (by omega)).trans hZ.1, (mfr 0xE8 (by omega) (by omega)).trans hZ.2⟩
      ((mfr 0xF0 (by omega) (by omega)).trans hF0) ((mfr 0xF8 (by omega) (by omega)).trans hF8)
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x360 + 16 * i ∨ 0x360 + 16 * i + 32 ≤ A) =>
      writeHash_frame _ a (0x360 + 16 * i) A h12 hA (by omega) h
    refine ⟨Glob_writeHash hglob' a _ h12 (by simp only [safeDest, pSlots]; simp; omega),
      Known_writeHash (KnownOK_chK hK') a, Regs_wh (Regs_keep hR hkeep') a, ⟨?_, ?_⟩,
      RB_wh (RB_keep hB hkeep') a, ⟨?_, ?_⟩, ?_, hlen, hvs, by simp, ?_⟩
    · rw [wf 0xC0 (by omega) (by omega), m0, BitVec.toNat_ofNat]; omega
    · rw [wf 0xC8 (by omega) (by omega), mfr 0xC8 (by omega) (by omega)]; exact hCB.2
    · rw [wf 0xE0 (by omega) (by omega), mfr 0xE0 (by omega) (by omega)]; exact hZ.1
    · rw [wf 0xE8 (by omega) (by omega), mfr 0xE8 (by omega) (by omega)]; exact hZ.2
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
