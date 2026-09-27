import SigGolfCandidate.Verify.ChainRuns
import SigGolfCandidate.Verify.Arith

/-! # Chains: semantics of the chain blocks -/

set_option linter.unusedSimpArgs false

macro "bvne" : tactic => `(tactic| (intro h; have h' := congrArg BitVec.toNat h; simp only [BitVec.toNat_ofNat] at h'; omega))

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

structure CCtx where
  wl : List Byte
  pk : List Byte
  lay : Nat
  tau : Nat
  e : Nat
  idx : Nat
  d0 : Word
  d1 : Word

def CCtx.x31 (c : CCtx) : Word := BitVec.ofNat 64 (c.tau + 2 ^ 32 * c.e)

def CCtx.Regs (c : CCtx) (s : MachineState) : Prop :=
  s.getReg .x16 = c.d0 ∧ s.getReg .x17 = c.d1 ∧ s.getReg .x22 = BitVec.ofNat 64 c.idx ∧
  s.getReg .x23 = BitVec.ofNat 64 c.e ∧ s.getReg .x30 = BitVec.ofNat 64 c.tau ∧
  s.getReg .x31 = c.x31

def CCtx.ok (c : CCtx) : Prop := c.lay < 7 ∧ c.tau < 2 ^ 32 ∧ c.e < 2 ^ 32 ∧ c.wl.length = 7756

def LBOk (acc : List Val) (s : MachineState) : Prop :=
  ∀ j, j < acc.length → s.getMem (BitVec.ofNat 64 (0x360 + 16 * j)) = vw0 (acc.getD j []) ∧
    s.getMem (BitVec.ofNat 64 (0x368 + 16 * j)) = vw1 (acc.getD j [])

def CBOk (c : CCtx) (s : MachineState) : Prop :=
  (s.getMem (BitVec.ofNat 64 0xC0)).toNat % 2 ^ 32 = 0x101 + 65536 * c.lay ∧
  s.getMem (BitVec.ofNat 64 0xC8) = c.x31

def headOrLeaf (lay i : Nat) : Nat := if i < 42 then head lay i else leafTab.getD lay 0

def HeadInv (c : CCtx) (i : Nat) (acc : List Val) (s : MachineState) : Prop :=
  Glob c.wl c.pk s ∧ KnownOK (chainK 0xE0) s ∧ c.Regs s ∧ CBOk c s ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧ LBOk acc s ∧
  acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ s.pc = pcOf (headOrLeaf c.lay i)

/-- Digit `i` of the current layer. -/
def dig (c : CCtx) (i : Nat) : Nat := (if i < 21 then c.d0 else c.d1).toNat / 8 ^ (i % 21) % 8

theorem regfile_eval_known {known : List (Reg × Word)} {s : MachineState} (hk : KnownOK known s)
    (r : Reg) : ((RegFile.withKnown known).get r).eval s = s.getReg r :=
  RegFile.withKnown_eval s known hk r

def StepInv (c : CCtx) (i : Nat) (acc : List Val) (mu : Nat) (v : Val) (s : MachineState) : Prop :=
  Glob c.wl c.pk s ∧ KnownOK (chainK 0xE0) s ∧ c.Regs s ∧ CBOk c s ∧
  s.getMem (BitVec.ofNat 64 0xE0) = vw0 v ∧ s.getMem (BitVec.ofNat 64 0xE8) = vw1 v ∧ LBOk acc s ∧
  acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ v.length = 16 ∧
  s.pc = pcOf (stepStart (head c.lay i) mu)

def EndInv (c : CCtx) (i : Nat) (acc : List Val) (v : Val) (s : MachineState) : Prop :=
  Glob c.wl c.pk s ∧ KnownOK (chainK (0x360 + 16 * i)) s ∧ c.Regs s ∧ CBOk c s ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧
  LBOk (acc ++ [v]) s ∧ acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ v.length = 16 ∧
  s.pc = pcOf (head c.lay i + 44)

/-! ## Witness words -/

theorem vw0_slice (l : List Byte) (off : Nat) : vw0 (slice l off 16) = w64 (slice l off 8) := by
  simp [vw0, slice, List.take_take]

theorem vw1_slice (l : List Byte) (off : Nat) :
    vw1 (slice l off 16) = w64 (slice l (off + 8) 8) := by
  simp only [vw1, slice, List.drop_take, List.drop_drop]


theorem wit_word {wl : List Byte} {s : MachineState} (hW : WitOK wl s) (off : Nat)
    (h8 : off % 8 = 0) (hoff : off < 7760) :
    s.getMem (BitVec.ofNat 64 (0x800 + off)) = w64 (slice wl off 8) := by
  have := hW (off / 8) (by omega)
  rwa [show 8 * (off / 8) = off by omega] at this

theorem length_slice16 (l : List Byte) (off : Nat) (h : off + 16 ≤ l.length) :
    (slice l off 16).length = 16 := by
  simp [slice]; omega

theorem length_witChain (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) :
    (witChain c.wl c.lay i).length = 16 := by
  obtain ⟨h1, -, -, h4⟩ := hc
  unfold witChain witLayerOff
  apply length_slice16; omega

/-! ## Family facts -/

theorem okRun_spec {o : Option PRes} {e : PRes} {post : List (Reg × Word)}
    (h : okRun o e post = true) :
    o = some e ∧ resOK e = true ∧ knownB post e = true ∧ keepB layRegs e = true := by
  simp only [okRun, Bool.and_eq_true] at h
  exact ⟨optBeq_eq h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem chainCheck_disp {lay i : Nat} (h : chainCheck lay i = true) (x : Nat) (hx : x < 8) :
    okRun (runAt (chainK 0xE0) [nextHead lay i] (head lay i) (dirsOf x))
      (dispExp lay i (head lay i) (nextHead lay i) x)
      (chainK (if x = 6 then 0x360 + 16 * i else 0xE0)) = true := by
  simp only [chainCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  exact h.2 x hx

theorem chainCheck_step {lay i : Nat} (h : chainCheck lay i = true) (mu : Nat) (h1 : 2 ≤ mu)
    (h2 : mu ≤ 7) :
    okRun (runAt (chainK 0xE0) [] (stepStart (head lay i) mu) []) (stepExp i (head lay i) mu)
      (chainK (if mu = 7 then 0x360 + 16 * i else 0xE0)) = true := by
  simp only [chainCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1.1 (mu - 2) (by omega)
  rwa [show mu - 2 + 2 = mu by omega] at this

theorem chainCheck_end {lay i : Nat} (h : chainCheck lay i = true) :
    okRun (runAt (chainK (0x360 + 16 * i)) [nextHead lay i] (head lay i + 44) [])
      (endExp i (head lay i) (nextHead lay i)) (chainK 0xE0) = true := by
  simp only [chainCheck, Bool.and_eq_true] at h
  exact h.1.2

/-! ## Simp sets for final states -/

theorem kRegs_eval {a2 : Nat} {s : MachineState} (hk : KnownOK (chainK a2) s) (r : Reg) :
    ((kRegs a2).get r).eval s = s.getReg r := RegFile.withKnown_eval s _ hk r

theorem pcOf_add4 (n : Nat) : pcOf n + 4 = pcOf (n + 1) := by
  unfold pcOf
  rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat]
  congr 1

/-! ## Branch conditions -/

theorem brsOf_spec (i x : Nat) (hx : x < 8) :
    ∀ b ∈ brsOf i x, ∃ k, 1 ≤ k ∧ k < 8 ∧ b = brK i k (decide (k ≤ x)) := by
  intro b hb
  interval_cases x <;> simp only [brsOf, List.mem_cons, List.not_mem_nil, or_false] at hb <;>
    rcases hb with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, by decide, by decide, rfl⟩

theorem brK_holds (c : CCtx) (i k : Nat) (d : Bool) (hi : i < 42) (hk : k < 8) (s : MachineState)
    (hR : c.Regs s) : (brK i k d).holds s ↔ decide (k ≤ dig c i) = d := by
  obtain ⟨h16, h17, -⟩ := hR
  have key : CmpOp.geu.eval ((tExp i).eval s) (BitVec.ofNat 64 k <<< 61) = decide (k ≤ dig c i) := by
    simp only [tExp, E.eval, BinOp.eval, cw, digReg, dig]
    split
    · rw [h16]; exact geu_digit c.d0 (i % 21) k (by omega) hk
    · rw [h17]; exact geu_digit c.d1 (i % 21) k (by omega) hk
  simp only [Br.holds, brK, E.eval]
  rw [key]

theorem disp_brs (c : CCtx) (i x : Nat) (hi : i < 42) (hx : x < 8) (hdig : dig c i = x)
    (s : MachineState) (hR : c.Regs s) : ∀ b ∈ brsOf i x, b.holds s := by
  intro b hb
  obtain ⟨k, hk1, hk2, rfl⟩ := brsOf_spec i x hx b hb
  rw [brK_holds c i k _ hi hk2 s hR, hdig]

theorem nextHead_eq (lay i : Nat) : nextHead lay i = headOrLeaf lay (i + 1) := by
  unfold nextHead headOrLeaf
  by_cases h : i < 41
  · rw [if_pos h, if_pos (by omega)]
  · rw [if_neg h, if_neg (by omega)]

theorem memEval_cons_ne (s : MachineState) (k : Word) (v : E) (ws : SymMem) (A : Word)
    (h : A ≠ k) : memEval s ((⟨none, k⟩, v) :: ws) A = memEval s ws A := by
  rw [memEval_cons, if_neg (by simpa [Addr.eval] using h)]

theorem memEval_cons_eq (s : MachineState) (k : Word) (v : E) (ws : SymMem) (A : Word)
    (h : A = k) : memEval s ((⟨none, k⟩, v) :: ws) A = v.eval s := by
  rw [memEval_cons, if_pos (by simpa [Addr.eval] using h)]

/-! ## LB slots -/

theorem LBOk_append {acc : List Val} {s : MachineState} (h : LBOk acc s) (v : Val)
    (h0 : s.getMem (BitVec.ofNat 64 (0x360 + 16 * acc.length)) = vw0 v)
    (h1 : s.getMem (BitVec.ofNat 64 (0x368 + 16 * acc.length)) = vw1 v) : LBOk (acc ++ [v]) s := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hjl : j < acc.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
    exact h j hjl
  · have : j = acc.length := by omega
    subst this
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
    exact ⟨h0, h1⟩

theorem LBOk_frame {acc : List Val} {s t : MachineState} (h : LBOk acc s)
    (hf : ∀ j, j < acc.length → t.getMem (BitVec.ofNat 64 (0x360 + 16 * j)) =
      s.getMem (BitVec.ofNat 64 (0x360 + 16 * j)) ∧ t.getMem (BitVec.ofNat 64 (0x368 + 16 * j)) =
      s.getMem (BitVec.ofNat 64 (0x368 + 16 * j))) : LBOk acc t := by
  intro j hj
  rw [(hf j hj).1, (hf j hj).2]; exact h j hj

theorem Regs_keep {c : CCtx} {r : PRes} {s : MachineState} (hR : c.Regs s)
    (hkeep : keepB layRegs r = true) : c.Regs (r.toState s) := by
  have h := keepB_ok hkeep s
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> (rw [h _ (by simp [layRegs])]; assumption)

theorem Regs_writeHash {c : CCtx} {s : MachineState} (hR : c.Regs s) (a : BitVec 256) :
    c.Regs (writeHash s a) := by
  simp only [CCtx.Regs, writeHash_getReg]; exact hR

theorem Known_writeHash {known : List (Reg × Word)} {s : MachineState} (h : KnownOK known s)
    (a : BitVec 256) : KnownOK known (writeHash s a) := by
  intro p hp; rw [writeHash_getReg]; exact h p hp

theorem disp_lt6 (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val) (x : Nat)
    (hx : x < 6) (hdig : dig c i = x) (hchk : chainCheck c.lay i = true) (s : MachineState)
    (hs : HeadInv c i acc s) :
    ∃ t, Steps image s 12 12 t ∧ fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = pad64 (chainInput c.lay c.tau c.e i (x + 1) (witChain c.wl c.lay i)) ∧
      ∀ a, StepInv c i acc (x + 2) (answerBytes 16 a) (writeHash t a) := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okRun_spec (chainCheck_disp hchk x (by omega))
  rw [if_neg (by omega)] at hkn
  obtain ⟨hG, hK, hR, hCB, hF0, hF8, hLB, hlen, hvs, hpc⟩ := hs
  have hpc' : s.pc = pcOf (head c.lay i) := by rw [hpc, headOrLeaf, if_pos hi]
  have hbr : ∀ b ∈ (dispExp c.lay i (head c.lay i) (nextHead c.lay i) x).brs, b.holds s := by
    simp only [dispExp, if_neg (show x ≠ 7 by omega), if_neg (show x ≠ 6 by omega)]
    exact disp_brs c i x hi (by omega) hdig s hR
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc' hK hbr
  set r := dispExp c.lay i (head c.lay i) (nextHead c.lay i) x with hr
  have hK' := knownB_ok hkn s
  refine ⟨r.toState s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hr, dispExp, show x ≠ 7 by omega, show x ≠ 6 by omega] using hst
  · exact hec (by simp [hr, dispExp, show x ≠ 7 by omega, show x ≠ 6 by omega])
  · exact hK' (.x5, 0) (by simp [chainK, globK])
  · have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0xC0 := hK' (.x10, 0xC0) (by simp [chainK])
    have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 64 := hK' (.x11, 64) (by simp [chainK])
    have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 0xE0 := hK' (.x12, _) (by simp [chainK])
    exact hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide)
  · have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0xC0 := hK' (.x10, 0xC0) (by simp [chainK])
    have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, 64) (by simp [chainK])
    rw [hashInput_ofNat _ 0xC0 0 h10 h11 (by decide) (by decide),
      pad64_chainInput _ _ _ _ _ _ (length_witChain c hc i hi)]
    congr 1
    simp only [hr, dispExp, show x ≠ 7 by omega, show x ≠ 6 by omega, if_false]
    simp only [PRes.toState_getMem, memEval_cons, memEval_nil, Addr.eval, List.range, List.range.loop,
      List.map, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd, Nat.reduceMul]
    simp only [BitVec.reduceEq, ↓reduceIte, E.eval, cw, stMerge, BinOp.eval]
    obtain ⟨hlay, htau, he, hwl⟩ := hc
    have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
    have hoff : chainAddr c.lay i = 0x800 + (2480 + 752 * c.lay + 16 * i) := by unfold chainAddr; omega
    have hoff8 : chainAddr c.lay i + 8 = 0x800 + (2480 + 752 * c.lay + 16 * i + 8) := by
      unfold chainAddr; omega
    simp only [List.cons.injEq]
    refine ⟨?_, hCB.2.trans ?_, hP 0xD0 (by decide), hP 0xD8 (by decide), ?_, ?_, hF0, hF8, trivial⟩
    · rw [stMerge_eval _ _ _ (by omega) hCB.1]
      congr 1; unfold twLo; rw [Nat.div_eq_of_lt htau]; omega
    · unfold CCtx.x31 twHi; congr 1; omega
    · rw [hoff, wit_word hG.2.1 _ (by omega) (by omega), witChain, vw0_slice]; rfl
    · rw [hoff8, wit_word hG.2.1 _ (by omega) (by omega), witChain, vw1_slice]; rfl
  · intro a
    have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 0xE0 := hK' (.x12, _) (by simp [chainK])
    obtain ⟨hlay, htau, he, hwl⟩ := hc
    have hkeep' := keepB_ok hkeep s
    have wh := fun A (hA : A < 2 ^ 64) => writeHash_getMem_ofNat _ a 0xE0 A h12 hA (by omega)
    refine ⟨Glob_writeHash (hglob _ _ hG) a 0xE0 h12 (by decide), ?_, ?_, ?_, ?_, ?_, ?_, hlen, hvs,
      by simp, ?_⟩
    · intro p hp; rw [writeHash_getReg]; exact hK' p hp
    · obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hR
      simp only [CCtx.Regs, writeHash_getReg]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (rw [hkeep' _ (by simp [layRegs])]; assumption)
    · refine ⟨?_, ?_⟩
      · rw [wh 0xC0 (by omega)]
        simp only [hr, dispExp, show x ≠ 7 by omega, show x ≠ 6 by omega, if_false]
        simp only [PRes.toState_getMem, memEval_cons, memEval_nil, Addr.eval,
          BitVec.ofNat_eq_ofNat, BitVec.reduceEq, ↓reduceIte, E.eval, cw, stMerge, BinOp.eval,
          Nat.reduceAdd, Nat.reduceEqDiff]
        rw [stMerge_low _ _ (by omega)]; exact hCB.1
      · rw [wh 0xC8 (by omega)]
        simp only [hr, dispExp, show x ≠ 7 by omega, show x ≠ 6 by omega, if_false]
        simp only [PRes.toState_getMem, memEval_cons, memEval_nil, Addr.eval,
          BitVec.ofNat_eq_ofNat, BitVec.reduceEq, ↓reduceIte, Nat.reduceAdd, Nat.reduceEqDiff]
        exact hCB.2
    · rw [wh 0xE0 (by omega)]; simp [vw0_answer]
    · rw [wh 0xE8 (by omega)]; simp [vw1_answer]
    · intro j hj
      rw [hlen] at hj
      rw [writeHash_frame _ a 0xE0 _ h12 (by omega) (by omega) (by omega),
        writeHash_frame _ a 0xE0 _ h12 (by omega) (by omega) (by omega),
        PRes.toState_getMem, PRes.toState_getMem,
        memEval_frame_ofNat _ _ _ (by omega) (by
          simp only [hr, dispExp, show x ≠ 7 by omega, show x ≠ 6 by omega, if_false]
          simp; omega),
        memEval_frame_ofNat _ _ _ (by omega) (by
          simp only [hr, dispExp, show x ≠ 7 by omega, show x ≠ 6 by omega, if_false]
          simp; omega)]
      exact hLB j (by omega)
    · rw [writeHash_pc, PRes.toState_pc]
      simp only [hr, dispExp, show x ≠ 7 by omega, show x ≠ 6 by omega, if_false]
      rw [pcOf_add4]
      exact congrArg pcOf (by unfold stepStart; omega)

theorem step_lt7 (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val) (mu : Nat)
    (hmu2 : 2 ≤ mu) (hmu6 : mu ≤ 6) (hchk : chainCheck c.lay i = true) (v : Val) (s : MachineState)
    (hs : StepInv c i acc mu v s) :
    ∃ t, Steps image s 4 4 t ∧ fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = pad64 (chainInput c.lay c.tau c.e i mu v) ∧
      ∀ a, StepInv c i acc (mu + 1) (answerBytes 16 a) (writeHash t a) := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okRun_spec (chainCheck_step hchk mu hmu2 (by omega))
  rw [if_neg (by omega)] at hkn
  obtain ⟨hG, hK, hR, hCB, hE0, hE8, hLB, hlen, hvs, hv, hpc⟩ := hs
  set r := stepExp i (head c.lay i) mu with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, stepExp, show mu ≠ 7 by omega])
  have hK' := knownB_ok hkn s
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0xC0 := hK' (.x10, 0xC0) (by simp [chainK])
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) :=
    hK' (.x11, 64) (by simp [chainK])
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 0xE0 := hK' (.x12, _) (by simp [chainK])
  obtain ⟨hlay, htau, he, hwl⟩ := hc
  have hmem : r.st.mem = [(⟨none, 0xC0⟩, stMerge (8 * i + mu - 1)), (⟨none, 0xF8⟩, .c 0),
      (⟨none, 0xF0⟩, .c 0)] := by simp [hr, stepExp, show mu ≠ 7 by omega]
  refine ⟨r.toState s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hr, stepExp, show mu ≠ 7 by omega] using hst
  · exact hec (by simp [hr, stepExp, show mu ≠ 7 by omega])
  · exact hK' (.x5, 0) (by simp [chainK, globK])
  · exact hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide)
  · rw [hashInput_ofNat _ 0xC0 0 h10 h11 (by decide) (by decide), pad64_chainInput _ _ _ _ _ _ hv]
    congr 1
    simp only [PRes.toState_getMem, hmem, memEval_cons, memEval_nil, Addr.eval, List.range,
      List.range.loop, List.map, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
      Nat.reduceMul]
    simp only [BitVec.reduceEq, ↓reduceIte, E.eval, cw, stMerge, BinOp.eval]
    have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
    simp only [List.cons.injEq]
    refine ⟨?_, hCB.2.trans ?_, hP 0xD0 (by decide), hP 0xD8 (by decide), hE0, hE8, ?_⟩
    rotate_left 2
    · simp
    · rw [stMerge_eval _ _ _ (by omega) hCB.1]
      congr 1; unfold twLo; rw [Nat.div_eq_of_lt htau]; omega
    · unfold CCtx.x31 twHi; congr 1; omega
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0xE0 ∨ 0xE0 + 32 ≤ A) =>
      writeHash_frame _ a 0xE0 A h12 hA (by omega) h
    refine ⟨Glob_writeHash (hglob _ _ hG) a 0xE0 h12 (by decide), Known_writeHash hK' a,
      Regs_writeHash (Regs_keep hR hkeep) a, ?_, ?_, ?_, ?_, hlen, hvs, by simp, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [wf 0xC0 (by omega) (by omega), PRes.toState_getMem, hmem]
        simp only [memEval_cons, memEval_nil, Addr.eval, BitVec.ofNat_eq_ofNat, BitVec.reduceEq,
          ↓reduceIte, E.eval, cw, stMerge, BinOp.eval]
        rw [stMerge_low _ _ (by omega)]; exact hCB.1
      · rw [wf 0xC8 (by omega) (by omega), PRes.toState_getMem,
          memEval_frame_ofNat _ _ _ (by omega) (by rw [hmem]; simp)]
        exact hCB.2
    · rw [writeHash_at0 _ a 0xE0 h12 (by omega)]; simp [vw0_answer]
    · rw [writeHash_at8 _ a 0xE0 h12 (by omega)]; simp [vw1_answer]
    · refine LBOk_frame hLB (fun j hj => ?_)
      rw [hlen] at hj
      rw [wf _ (by omega) (by omega), wf _ (by omega) (by omega), PRes.toState_getMem,
        PRes.toState_getMem, memEval_frame_ofNat _ _ _ (by omega) (by rw [hmem]; simp; omega),
        memEval_frame_ofNat _ _ _ (by omega) (by rw [hmem]; simp; omega)]
      exact ⟨rfl, rfl⟩
    · rw [writeHash_pc, PRes.toState_pc]
      simp only [hr, stepExp, show mu ≠ 7 by omega, if_false]
      rw [pcOf_add4]
      exact congrArg pcOf (by unfold stepStart; omega)

theorem step_7 (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (v : Val) (s : MachineState)
    (hs : StepInv c i acc 7 v s) :
    ∃ t, Steps image s 5 5 t ∧ fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = pad64 (chainInput c.lay c.tau c.e i 7 v) ∧
      ∀ a, EndInv c i acc (answerBytes 16 a) (writeHash t a) := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okRun_spec (chainCheck_step hchk 7 (by omega) (by omega))
  rw [if_pos rfl] at hkn
  obtain ⟨hG, hK, hR, hCB, hE0, hE8, hLB, hlen, hvs, hv, hpc⟩ := hs
  set r := stepExp i (head c.lay i) 7 with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, stepExp])
  have hK' := knownB_ok hkn s
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0xC0 := hK' (.x10, 0xC0) (by simp [chainK])
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) :=
    hK' (.x11, 64) (by simp [chainK])
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 (0x360 + 16 * i) :=
    hK' (.x12, _) (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))))
  obtain ⟨hlay, htau, he, hwl⟩ := hc
  have hmem : r.st.mem = [(⟨none, 0xC0⟩, stMerge (8 * i + 6)), (⟨none, 0xF8⟩, .c 0),
      (⟨none, 0xF0⟩, .c 0)] := by simp [hr, stepExp]
  refine ⟨r.toState s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hr, stepExp] using hst
  · exact hec (by simp [hr, stepExp])
  · exact hK' (.x5, 0) (by simp [chainK, globK])
  · exact hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega)
  · rw [hashInput_ofNat _ 0xC0 0 h10 h11 (by decide) (by decide), pad64_chainInput _ _ _ _ _ _ hv]
    congr 1
    simp only [PRes.toState_getMem, hmem, memEval_cons, memEval_nil, Addr.eval, List.range,
      List.range.loop, List.map, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
      Nat.reduceMul]
    simp only [BitVec.reduceEq, ↓reduceIte, E.eval, cw, stMerge, BinOp.eval]
    have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
    simp only [List.cons.injEq]
    refine ⟨?_, hCB.2.trans ?_, hP 0xD0 (by decide), hP 0xD8 (by decide), hE0, hE8, ?_⟩
    rotate_left 2
    · simp
    · rw [stMerge_eval _ _ _ (by omega) hCB.1]
      congr 1; unfold twLo; rw [Nat.div_eq_of_lt htau]; omega
    · unfold CCtx.x31 twHi; congr 1; omega
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x360 + 16 * i ∨ 0x360 + 16 * i + 32 ≤ A) =>
      writeHash_frame _ a (0x360 + 16 * i) A h12 hA (by omega) h
    refine ⟨Glob_writeHash (hglob _ _ hG) a _ h12 (by simp only [safeDest, pSlots]; simp; omega),
      Known_writeHash hK' a, Regs_writeHash (Regs_keep hR hkeep) a, ?_, ?_, ?_, ?_, hlen, hvs,
      by simp, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [wf 0xC0 (by omega) (by omega), PRes.toState_getMem, hmem]
        simp only [memEval_cons, memEval_nil, Addr.eval, BitVec.ofNat_eq_ofNat, BitVec.reduceEq,
          ↓reduceIte, E.eval, cw, stMerge, BinOp.eval]
        rw [stMerge_low _ _ (by omega)]; exact hCB.1
      · rw [wf 0xC8 (by omega) (by omega), PRes.toState_getMem,
          memEval_frame_ofNat _ _ _ (by omega) (by rw [hmem]; simp)]
        exact hCB.2
    · rw [wf 0xF0 (by omega) (by omega), PRes.toState_getMem, hmem]
      simp only [memEval_cons, memEval_nil, Addr.eval, BitVec.ofNat_eq_ofNat, BitVec.reduceEq,
          ↓reduceIte, E.eval]
    · rw [wf 0xF8 (by omega) (by omega), PRes.toState_getMem, hmem]
      simp only [memEval_cons, memEval_nil, Addr.eval, BitVec.ofNat_eq_ofNat, BitVec.reduceEq,
          ↓reduceIte, E.eval]
    · refine LBOk_append (LBOk_frame hLB (fun j hj => ?_)) _ ?_ ?_
      · rw [hlen] at hj
        rw [wf _ (by omega) (by omega), wf _ (by omega) (by omega), PRes.toState_getMem,
          PRes.toState_getMem, memEval_frame_ofNat _ _ _ (by omega) (by rw [hmem]; simp; omega),
          memEval_frame_ofNat _ _ _ (by omega) (by rw [hmem]; simp; omega)]
        exact ⟨rfl, rfl⟩
      · rw [hlen, writeHash_at0 _ a _ h12 (by omega)]; simp [vw0_answer]
      · rw [hlen, show 0x368 + 16 * i = 0x360 + 16 * i + 8 by omega,
          writeHash_at8 _ a _ h12 (by omega)]; simp [vw1_answer]
    · rw [writeHash_pc, PRes.toState_pc]
      simp only [hr, stepExp, if_true]
      rw [pcOf_add4]

theorem disp_6 (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hdig : dig c i = 6) (hchk : chainCheck c.lay i = true) (s : MachineState)
    (hs : HeadInv c i acc s) :
    ∃ t, Steps image s 13 13 t ∧ fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 0 ∧
      hashArgumentsValid t = true ∧
      hashInput t = pad64 (chainInput c.lay c.tau c.e i 7 (witChain c.wl c.lay i)) ∧
      ∀ a, EndInv c i acc (answerBytes 16 a) (writeHash t a) := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okRun_spec (chainCheck_disp hchk 6 (by omega))
  rw [if_pos rfl] at hkn
  obtain ⟨hG, hK, hR, hCB, hF0, hF8, hLB, hlen, hvs, hpc⟩ := hs
  have hpc' : s.pc = pcOf (head c.lay i) := by rw [hpc, headOrLeaf, if_pos hi]
  set r := dispExp c.lay i (head c.lay i) (nextHead c.lay i) 6 with hr
  have hbr : ∀ b ∈ r.brs, b.holds s := by
    simp only [hr, dispExp, if_neg (show (6 : Nat) ≠ 7 by omega), if_pos rfl]
    exact disp_brs c i 6 hi (by omega) hdig s hR
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc' hK hbr
  have hK' := knownB_ok hkn s
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0xC0 := hK' (.x10, 0xC0) (by simp [chainK])
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) :=
    hK' (.x11, 64) (by simp [chainK])
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 (0x360 + 16 * i) :=
    hK' (.x12, _) (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))))
  have hmem : r.st.mem = [(⟨none, 0xC0⟩, stMerge (8 * i + 6)), (⟨none, 0xE8⟩, .ld (cw (chainAddr c.lay i + 8))),
      (⟨none, 0xE0⟩, .ld (cw (chainAddr c.lay i)))] := by simp [hr, dispExp]
  obtain ⟨hlay, htau, he, hwl⟩ := hc
  refine ⟨r.toState s, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [hr, dispExp] using hst
  · exact hec (by simp [hr, dispExp])
  · exact hK' (.x5, 0) (by simp [chainK, globK])
  · exact hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega)
  · rw [hashInput_ofNat _ 0xC0 0 h10 h11 (by decide) (by decide),
      pad64_chainInput _ _ _ _ _ _ (length_witChain c ⟨hlay, htau, he, hwl⟩ i hi)]
    congr 1
    simp only [PRes.toState_getMem, hmem, memEval_cons, memEval_nil, Addr.eval, List.range,
      List.range.loop, List.map, BitVec.ofNat_eq_ofNat, BitVec.ofNat_add_ofNat, Nat.reduceAdd,
      Nat.reduceMul]
    simp only [BitVec.reduceEq, ↓reduceIte, E.eval, cw, stMerge, BinOp.eval]
    have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
    have hoff : chainAddr c.lay i = 0x800 + (2480 + 752 * c.lay + 16 * i) := by unfold chainAddr; omega
    have hoff8 : chainAddr c.lay i + 8 = 0x800 + (2480 + 752 * c.lay + 16 * i + 8) := by
      unfold chainAddr; omega
    simp only [List.cons.injEq]
    refine ⟨?_, hCB.2.trans ?_, hP 0xD0 (by decide), hP 0xD8 (by decide), ?_, ?_, hF0, hF8, trivial⟩
    · rw [stMerge_eval _ _ _ (by omega) hCB.1]
      congr 1; unfold twLo; rw [Nat.div_eq_of_lt htau]; omega
    · unfold CCtx.x31 twHi; congr 1; omega
    · rw [hoff, wit_word hG.2.1 _ (by omega) (by omega), witChain, vw0_slice]; rfl
    · rw [hoff8, wit_word hG.2.1 _ (by omega) (by omega), witChain, vw1_slice]; rfl
  · intro a
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x360 + 16 * i ∨ 0x360 + 16 * i + 32 ≤ A) =>
      writeHash_frame _ a (0x360 + 16 * i) A h12 hA (by omega) h
    refine ⟨Glob_writeHash (hglob _ _ hG) a _ h12 (by simp only [safeDest, pSlots]; simp; omega),
      Known_writeHash hK' a, Regs_writeHash (Regs_keep hR hkeep) a, ?_, ?_, ?_, ?_, hlen, hvs,
      by simp, ?_⟩
    · refine ⟨?_, ?_⟩
      · rw [wf 0xC0 (by omega) (by omega), PRes.toState_getMem, hmem]
        simp only [memEval_cons, memEval_nil, Addr.eval, BitVec.ofNat_eq_ofNat, BitVec.reduceEq,
          ↓reduceIte, E.eval, cw, stMerge, BinOp.eval]
        rw [stMerge_low _ _ (by omega)]; exact hCB.1
      · rw [wf 0xC8 (by omega) (by omega), PRes.toState_getMem,
          memEval_frame_ofNat _ _ _ (by omega) (by rw [hmem]; simp)]
        exact hCB.2
    · rw [wf 0xF0 (by omega) (by omega), PRes.toState_getMem,
        memEval_frame_ofNat _ _ _ (by omega) (by rw [hmem]; simp)]; exact hF0
    · rw [wf 0xF8 (by omega) (by omega), PRes.toState_getMem,
        memEval_frame_ofNat _ _ _ (by omega) (by rw [hmem]; simp)]; exact hF8
    · refine LBOk_append (LBOk_frame hLB (fun j hj => ?_)) _ ?_ ?_
      · rw [hlen] at hj
        rw [wf _ (by omega) (by omega), wf _ (by omega) (by omega), PRes.toState_getMem,
          PRes.toState_getMem, memEval_frame_ofNat _ _ _ (by omega) (by rw [hmem]; simp; omega),
          memEval_frame_ofNat _ _ _ (by omega) (by rw [hmem]; simp; omega)]
        exact ⟨rfl, rfl⟩
      · rw [hlen, writeHash_at0 _ a _ h12 (by omega)]; simp [vw0_answer]
      · rw [hlen, show 0x368 + 16 * i = 0x360 + 16 * i + 8 by omega,
          writeHash_at8 _ a _ h12 (by omega)]; simp [vw1_answer]
    · rw [writeHash_pc, PRes.toState_pc]
      simp only [hr, dispExp, if_neg (show (6 : Nat) ≠ 7 by omega), if_true]
      rw [pcOf_add4]

theorem disp_7 (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hdig : dig c i = 7) (hchk : chainCheck c.lay i = true) (s : MachineState)
    (hs : HeadInv c i acc s) :
    ∃ t, Steps image s (10 + grp i) (10 + grp i) t ∧
      HeadInv c (i + 1) (acc ++ [witChain c.wl c.lay i]) t := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okRun_spec (chainCheck_disp hchk 7 (by omega))
  rw [if_neg (by omega)] at hkn
  obtain ⟨hG, hK, hR, hCB, hF0, hF8, hLB, hlen, hvs, hpc⟩ := hs
  have hpc' : s.pc = pcOf (head c.lay i) := by rw [hpc, headOrLeaf, if_pos hi]
  set r := dispExp c.lay i (head c.lay i) (nextHead c.lay i) 7 with hr
  have hbr : ∀ b ∈ r.brs, b.holds s := by
    simp only [hr, dispExp, if_pos rfl]
    exact disp_brs c i 7 hi (by omega) hdig s hR
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc' hK hbr
  have hK' := knownB_ok hkn s
  have hmem : r.st.mem =
      [(⟨none, BitVec.ofNat 64 (0x368 + 16 * i)⟩, .ld (cw (chainAddr c.lay i + 8))),
       (⟨none, BitVec.ofNat 64 (0x360 + 16 * i)⟩, .ld (cw (chainAddr c.lay i))),
       (⟨none, 0xE8⟩, .ld (cw (chainAddr c.lay i + 8))), (⟨none, 0xE0⟩, .ld (cw (chainAddr c.lay i)))] := by
    simp [hr, dispExp]
  obtain ⟨hlay, htau, he, hwl⟩ := hc
  have hoff : chainAddr c.lay i = 0x800 + (2480 + 752 * c.lay + 16 * i) := by unfold chainAddr; omega
  have hoff8 : chainAddr c.lay i + 8 = 0x800 + (2480 + 752 * c.lay + 16 * i + 8) := by
    unfold chainAddr; omega
  have fr : ∀ A, A < 2 ^ 64 → A ≠ 0x368 + 16 * i → A ≠ 0x360 + 16 * i → A ≠ 0xE8 → A ≠ 0xE0 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by
      rw [hmem]; simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp <;> omega)]
  refine ⟨r.toState s, ?_, ?_⟩
  · simpa [hr, dispExp] using hst
  refine ⟨hglob _ _ hG, hK', Regs_keep hR hkeep, ⟨?_, ?_⟩, ?_, ?_, ?_, by simp [hlen], ?_, ?_⟩
  · rw [fr 0xC0 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hCB.1
  · rw [fr 0xC8 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hCB.2
  · rw [fr 0xF0 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF0
  · rw [fr 0xF8 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF8
  · refine LBOk_append (LBOk_frame hLB (fun j hj => ?_)) _ ?_ ?_
    · rw [hlen] at hj
      rw [fr _ (by omega) (by omega) (by omega) (by omega) (by omega),
        fr _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact ⟨rfl, rfl⟩
    · rw [hlen, PRes.toState_getMem, hmem]
      rw [memEval_cons_ne _ _ _ _ _ (by bvne), memEval_cons_eq _ _ _ _ _ rfl]
      simp only [E.eval, cw]
      rw [hoff, wit_word hG.2.1 _ (by omega) (by omega), witChain, vw0_slice]; rfl
    · rw [hlen, PRes.toState_getMem, hmem]
      rw [memEval_cons_eq _ _ _ _ _ rfl]
      simp only [E.eval, cw]
      rw [hoff8, wit_word hG.2.1 _ (by omega) (by omega), witChain, vw1_slice]; rfl
  · intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact hvs v h
    · rw [List.mem_singleton.mp h]; exact length_witChain c ⟨hlay, htau, he, hwl⟩ i hi
  · rw [PRes.toState_pc]
    simp only [hr, dispExp, ↓reduceIte, nextHead_eq]

theorem chain_end (c : CCtx) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (v : Val) (s : MachineState) (hs : EndInv c i acc v s) :
    ∃ t, Steps image s (1 + grp i) (1 + grp i) t ∧ HeadInv c (i + 1) (acc ++ [v]) t := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okRun_spec (chainCheck_end hchk)
  obtain ⟨hG, hK, hR, hCB, hF0, hF8, hLB, hlen, hvs, hv, hpc⟩ := hs
  set r := endExp i (head c.lay i) (nextHead c.lay i) with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc hK (by simp [hr, endExp])
  have hK' := knownB_ok hkn s
  have hmem : r.st.mem = [] := by simp [hr, endExp]
  have fr : ∀ A, (r.toState s).getMem A = s.getMem A := by
    intro A; rw [PRes.toState_getMem, hmem]; rfl
  refine ⟨r.toState s, ?_, ?_⟩
  · simpa [hr, endExp] using hst
  refine ⟨hglob _ _ hG, hK', Regs_keep hR hkeep, ⟨?_, ?_⟩, ?_, ?_, ?_, by simp [hlen], ?_, ?_⟩
  · rw [fr]; exact hCB.1
  · rw [fr]; exact hCB.2
  · rw [fr]; exact hF0
  · rw [fr]; exact hF8
  · exact LBOk_frame hLB (fun j _ => ⟨fr _, fr _⟩)
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact hvs w h
    · rw [List.mem_singleton.mp h]; exact hv
  · rw [PRes.toState_pc]
    simp only [hr, endExp, nextHead_eq]

end SigGolfCandidate.Verify
