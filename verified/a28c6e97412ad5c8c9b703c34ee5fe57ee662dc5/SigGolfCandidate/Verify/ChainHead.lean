import SigGolfCandidate.Verify.ChainSem

/-! # Chains: dispatch heads, table entries and chain ends -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem land1008 (n : Nat) : n &&& 1008 = 16 * (n / 16 % 64) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and]
  rw [show 16 * (n / 16 % 64) = (n >>> 4 % 2 ^ 6) <<< 4 by
    simp only [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega]
  rw [Nat.testBit_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  by_cases hj : j < 10
  · interval_cases j <;> simp <;> intro _ <;> decide
  · rw [Nat.testBit_lt_two_pow (show 1008 < 2 ^ j from
      lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (show 10 ≤ j by omega)))]
    simp; omega

theorem even_andNot1 (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0; simp; rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]; simp [h]
  · simp [h0, hj]


def maskV (i D : Nat) : Nat := if isSingle i then D / 8 ^ 20 else D / 8 ^ (i % 21) % 64

theorem maskE_eval (i : Nat) (hi : i < 42) (hf : isFirst i = true ∨ isSingle i = true)
    (s : MachineState) (D : Word) (hD : s.getReg (dReg i) = D) (hD63 : D.toNat < 2 ^ 63) :
    (maskE i).eval s = BitVec.ofNat 64 (16 * maskV i D.toNat) := by
  unfold maskE maskV
  by_cases hs : isSingle i = true
  · simp only [hs, if_true, mkBin_eval, E.eval, BinOp.eval, cw, hD]
    have hr : i % 21 = 20 := by simp [isSingle] at hs; omega
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have : D.toNat / 2 ^ 60 < 8 := by omega
    rw [show 8 ^ 20 = 2 ^ 60 by norm_num]
    simp only [Nat.reducePow, Nat.reduceMod]
    omega
  · have hf' : isFirst i = true := by simpa [hs] using hf
    simp only [isFirst, hs, Bool.not_false, Bool.true_and, decide_eq_true_eq] at hf'
    simp only [hs, if_false, Bool.false_eq_true]
    by_cases h0 : i % 21 = 0
    · simp only [h0, if_true, mkBin_eval, E.eval, BinOp.eval, cw, hD]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
      rw [show (1008 : Nat) % 2 ^ 64 = 1008 from rfl, land1008]
      simp only [Nat.reducePow, Nat.reduceMod, Nat.pow_zero, Nat.div_one]
      omega
    · have hr2 : 2 ≤ i % 21 := by omega
      have hr18 : i % 21 ≤ 18 := by simp [isSingle] at hs; omega
      simp only [h0, if_false, mkBin_eval, E.eval, BinOp.eval, cw, hD]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
      rw [show (1008 : Nat) % 2 ^ 64 = 1008 from rfl, land1008]
      rw [Nat.mod_eq_of_lt (show 3 * (i % 21) - 4 < 2 ^ 64 by omega),
        Nat.mod_eq_of_lt (show 3 * (i % 21) - 4 < 64 by omega), Nat.div_div_eq_div_mul,
        show (16 : Nat) = 2 ^ 4 from rfl, ← Nat.pow_add, show 3 * (i % 21) - 4 + 4 = 3 * (i % 21) by omega,
        show (8 : Nat) = 2 ^ 3 from rfl, ← Nat.pow_mul]
      omega


/-! ## Digits and table indices -/

theorem dig_lt (c : CCtx) (i : Nat) : dig c i < 8 := by unfold dig; omega

theorem entIdx_mask (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42)
    (hf : isFirst i = true ∨ isSingle i = true) :
    entIdx c i = maskV i (if i < 21 then c.d0 else c.d1).toNat := by
  obtain ⟨-, -, -, -, h0, h1⟩ := hc
  unfold entIdx maskV
  by_cases hs : isSingle i = true
  · simp only [hs, if_true]
    have hr : i % 21 = 20 := by simp [isSingle] at hs; omega
    unfold dig; rw [hr]
    have : (if i < 21 then c.d0 else c.d1).toNat < 2 ^ 63 := by split <;> assumption
    rw [show 8 ^ 20 = 2 ^ 60 by norm_num]; omega
  · have hf' : isFirst i = true := by simpa [hs] using hf
    have hr : i % 21 % 2 = 0 := by simpa [isFirst, hs] using hf'
    have hr18 : i % 21 ≤ 18 := by simp [isSingle] at hs; omega
    simp only [hs, if_false, Bool.false_eq_true, pf, hf', ↓reduceIte]
    unfold dig
    have e1 : (i + 1) % 21 = i % 21 + 1 := by omega
    have e2 : (if i + 1 < 21 then c.d0 else c.d1) = (if i < 21 then c.d0 else c.d1) := by
      split_ifs <;> first | rfl | omega
    rw [e1, e2, Nat.pow_succ, ← Nat.div_div_eq_div_mul]
    generalize (if i < 21 then c.d0 else c.d1).toNat / 8 ^ (i % 21) = q
    omega

def entDigitOk : Bool :=
  (List.range 42).all fun i => isSingle i || isFirst i || (decide (1 ≤ i) && isFirst (i - 1) && !isSingle (i - 1))

theorem entDigitOk_eq : entDigitOk = true := by decide

theorem entIdx_spec (c : CCtx) (i : Nat) (hi : i < 42) :
    entIdx c i < nEnt i ∧ entDigit i (entIdx c i) = dig c i := by
  have := List.all_eq_true.mp entDigitOk_eq i (List.mem_range.mpr hi)
  have d0 := dig_lt c i
  unfold entIdx nEnt entDigit
  by_cases hs : isSingle i = true
  · simp only [hs, ↓reduceIte]; exact ⟨d0, trivial⟩
  · by_cases hf : isFirst i = true
    · simp only [hs, hf, pf, if_true, if_false, Bool.false_eq_true]
      have := dig_lt c (i + 1); omega
    · simp only [hs, hf, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at this
      simp only [hs, hf, pf, if_false, Bool.false_eq_true]
      have := dig_lt c (i - 1)
      rw [show i - 1 + 1 = i by omega]; omega

/-! ## Table facts -/

def tabOk (lay i : Nat) : Bool :=
  decide (tabAddr lay i % 4 = 0) && decide (0x1000 ≤ tabAddr lay i) &&
    decide (tabAddr lay i + 1024 ≤ 0x1000 + 4 * (256 * 275)) && decide (bVal lay i < 2 ^ 32) &&
    decide (nextPc' lay i = s1Pc lay i + 15) &&
    (!(decide (i + 1 < 42) && !hasPrep (i + 1)) || bVal lay (i + 1) == bVal lay i)

def tabOkAll : Bool := (List.range 5).all fun lay => (List.range 42).all fun i => tabOk lay i

theorem tabOkAll_eq : tabOkAll = true := by decide +kernel

theorem tabOk_at (lay i : Nat) (hl : lay < 5) (hi : i < 42) : tabOk lay i = true :=
  List.all_eq_true.mp (List.all_eq_true.mp tabOkAll_eq lay (List.mem_range.mpr hl)) i
    (List.mem_range.mpr hi)

theorem tabOk_spec {lay i : Nat} (h : tabOk lay i = true) :
    tabAddr lay i % 4 = 0 ∧ 0x1000 ≤ tabAddr lay i ∧ tabAddr lay i + 1024 ≤ 0x1000 + 4 * (256 * 275) ∧
      bVal lay i < 2 ^ 32 ∧ (i + 1 < 42 → hasPrep (i + 1) = false → bVal lay (i + 1) = bVal lay i) ∧
      nextPc' lay i = s1Pc lay i + 15 := by
  simp only [tabOk, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_imp, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h6⟩, h5⟩ := h
  refine ⟨h1, h2, h3, h4, fun ha hb => ?_, h6⟩
  rcases h5 with h5 | h5
  · have := h5 (by simpa using ha); rw [hb] at this; simp at this
  · exact h5

def pairOk : Bool := (List.range 41).all fun i => hasPrep (i + 1) || (isFirst i && !isSingle i)

theorem pairOk_eq : pairOk = true := by decide

/-- A chain without dispatch prep reuses the dispatch register of its predecessor. -/
theorem rOf_next (c : CCtx) (i : Nat) (hl : c.lay < 5) (hi : i + 1 < 42)
    (hp : hasPrep (i + 1) = false) : rOf c (i + 1) = rOf c i := by
  have := List.all_eq_true.mp pairOk_eq i (List.mem_range.mpr (by omega))
  simp only [hp, Bool.false_or, Bool.and_eq_true, Bool.not_eq_true'] at this
  obtain ⟨hf, hs⟩ := this
  have hp2 : isFirst (i + 1) = false ∧ isSingle (i + 1) = false := by
    unfold hasPrep at hp
    cases h1 : isFirst (i + 1) <;> cases h2 : isSingle (i + 1) <;> simp [h1, h2] at hp ⊢
  obtain ⟨hf1, hs1⟩ := hp2
  unfold rOf entIdx
  rw [(tabOk_spec (tabOk_at c.lay i hl (by omega))).2.2.2.2.1 hi hp]
  simp only [hs, hs1, pf, hf, hf1, if_true, if_false, Bool.false_eq_true, Nat.add_sub_cancel]

/-! ## Word arithmetic -/

theorem add_sub_ofNat (B e T : Nat) (_hB : B < 2 ^ 32) (_hT : T < 2 ^ 32) (_he : e < 2 ^ 32) :
    BitVec.ofNat 64 (B + e) + (BitVec.ofNat 64 T - BitVec.ofNat 64 B) = BitVec.ofNat 64 (T + e) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  omega

theorem pcOf_entry (lay i e : Nat) (h1 : tabAddr lay i % 4 = 0) (h2 : 0x1000 ≤ tabAddr lay i) :
    pcOf (entryIdx lay i e) = BitVec.ofNat 64 (tabAddr lay i + 16 * e) := by
  unfold pcOf entryIdx; congr 1; omega

/-! ## Frames -/

theorem Glob_frame {gk : List (Reg × Word)} {wl pk : List Byte} {s t : MachineState}
    (hG : Glob gk wl pk s) (hr : ∀ x, t.getReg x = s.getReg x)
    (hm : ∀ A, A < 2 ^ 64 → (0x800 ≤ A ∨ A ∈ pSlots ∨ A = 0xA0 ∨ A = 0xA8) →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) : Glob gk wl pk t := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  refine ⟨fun p hp => (hr _).trans (h1 p hp), fun j hj => ?_, ?_, fun a ha => ?_⟩
  · rw [hm _ (by omega) (Or.inl (by omega))]; exact h2 j hj
  · exact ⟨(hm 0xA0 (by omega) (by simp)).trans h3.1, (hm 0xA8 (by omega) (by simp)).trans h3.2⟩
  · have : a < 2 ^ 64 := by simp [pSlots] at ha; omega
    rw [hm a this (Or.inr (Or.inl ha))]; exact h4 a ha

/-! ## Heads -/

def headCost (lay i : Nat) : Nat :=
  6 + (if hasPrep i then 3 else 0) + (if hasPrep i && hasLui lay i then 1 else 0)

theorem PRes.toState_pc_some (r : PRes) (s : MachineState) (e : E) (h : r.spc = some e) :
    (r.toState s).pc = e.eval s := by
  simp [PRes.toState, PRes.finalPc, h]

theorem headExp_x1 (lay i : Nat) : (headExp lay i).st.regs.get .x1 = ldE (chainAddr lay i) := by
  simp only [headExp]
  rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide),
    RegFile.get_set_ne _ _ (by decide), RegFile.get_set_self _ _ (by decide)]

theorem headExp_x2 (lay i : Nat) : (headExp lay i).st.regs.get .x2 = ldE (chainAddr lay i + 8) := by
  simp only [headExp]
  rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide),
    RegFile.get_set_self _ _ (by decide)]

theorem headExp_x14 (lay i : Nat) (h : hasPrep i = true) : (headExp lay i).st.regs.get .x14 = rE lay i := by
  simp only [headExp, h, if_true]
  rw [RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide),
    RegFile.get_set_ne _ _ (by decide), RegFile.get_set_ne _ _ (by decide),
    RegFile.get_set_self _ _ (by decide)]

theorem head_step (c : CCtx) (hc : c.ok) (i : Nat) (hi1 : 1 ≤ i) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (s : MachineState) (hs : HeadInv c i acc s) :
    ∃ t, Steps image s (headCost c.lay i) (headCost c.lay i) t ∧ EntInv c i acc t := by
  obtain ⟨hrun, hok, hkn, hkeep⟩ := okC_spec (check_head hchk (by omega))
  obtain ⟨hG, hK, hR, hCB, hZ, hLB, hlen, hvs, ⟨tt, -, hpc⟩, hx14⟩ := hs
  rw [headPc, if_neg (by omega)] at hpc
  obtain ⟨hst, -, hglob⟩ := run_post hrun hok s hpc hK (by simp [headExp])
  set r := headExp c.lay i with hr
  have hK' := knownB_ok hkn s
  rw [KnownOK_append] at hK'
  have hkeep' := keepB_ok hkeep s
  have hl := hc.1
  obtain ⟨ht4, ht1, htb, hB, -, -⟩ := tabOk_spec (tabOk_at c.lay i hl hi)
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 0xC0⟩, stB 5 (cw i))] := by simp [hr, headExp]
  have fr : ∀ A, A < 2 ^ 64 → A ≠ 0xC0 → (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by rw [hmem]; simp; omega)]
  have m0 : ((r.toState s).getMem (BitVec.ofNat 64 0xC0)).toNat =
      (s.getMem (BitVec.ofNat 64 0xC0)).toNat % 2 ^ 40 + 2 ^ 40 * i := by
    rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl, stB_toNat _ _ _ (by omega)]
    have := hCB.2.2
    generalize (s.getMem (BitVec.ofNat 64 0xC0)).toNat = w at *
    norm_num at this ⊢
    omega
  have hx15 : (r.toState s).getReg .x15 = BitVec.ofNat 64 (bVal c.lay i) := hK'.2 (.x15, _) (List.mem_singleton_self _)
  have he := entIdx_spec c i hi
  have hsn : nEnt i ≤ 64 := by unfold nEnt; split <;> omega
  -- the dispatch register
  have hR14 : (r.toState s).getReg .x14 = BitVec.ofNat 64 (rOf c i) ∧
      (if hasPrep i then rE c.lay i else .reg .x14).eval s = BitVec.ofNat 64 (rOf c i) := by
    by_cases hp : hasPrep i = true
    · have hf : isFirst i = true ∨ isSingle i = true := by
        simp only [hasPrep, Bool.and_eq_true, Bool.or_eq_true] at hp; exact hp.2
      have hD : s.getReg (dReg i) = (if i < 21 then c.d0 else c.d1) := by
        unfold dReg; split
        · exact hR.1
        · exact hR.2.1
      have hD63 : (if i < 21 then c.d0 else c.d1).toNat < 2 ^ 63 := by
        split
        · exact hc.2.2.2.2.1
        · exact hc.2.2.2.2.2
      have hv : (rE c.lay i).eval s = BitVec.ofNat 64 (rOf c i) := by
        simp only [rE, mkBin_eval, BinOp.eval, cw, E.eval]
        rw [maskE_eval i hi hf s _ hD hD63, BitVec.ofNat_add_ofNat, rOf,
          entIdx_mask c hc i hi hf, Nat.add_comm]
      simp only [hp, if_true]
      rw [PRes.toState_getReg, hr, headExp_x14 _ _ hp]
      exact ⟨hv, hv⟩
    · have hp' : hasPrep i = false := by simpa using hp
      have h14 : (r.toState s).getReg .x14 = s.getReg .x14 :=
        hkeep' _ (by simp [headKeep, hp'])
      simp only [hp', if_false, Bool.false_eq_true, E.eval]
      rw [h14]
      exact ⟨hx14 hi hp', hx14 hi hp'⟩
  have hoff : chainAddr c.lay i = 0x800 + (witLayerOff c.lay + 16 * i) := by
    unfold chainAddr; rw [witLayerOff_eq _ hc.1]; omega
  have hlb := layBody_le _ hc.1
  have hwl := hc.2.2.2.1
  refine ⟨r.toState s, by simpa [hr, headExp, headCost] using hst, hglob _ _ hG, hK'.1, ?_, ⟨?_, ?_, ?_⟩,
    ?_, ⟨hx15, hR14.1⟩, ⟨by rw [fr _ (by omega) (by omega)]; exact hZ.1, by rw [fr _ (by omega) (by omega)]; exact hZ.2⟩,
    LBOk_frame hLB (fun j hj => ⟨fr _ (by omega) (by omega), fr _ (by omega) (by omega)⟩), hlen, hvs, ?_, ?_, ?_⟩
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hR
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (rw [hkeep' _ (by simp [headKeep])]; assumption)
  · rw [m0]; have := hCB.1; omega
  · rw [fr _ (by omega) (by omega)]; exact hCB.2.1
  · rw [m0]; omega
  · unfold CBi; rw [m0]; omega
  · rw [PRes.toState_getReg, hr, headExp_x1]
    simp only [ldE, cw, E.eval]
    rw [hoff, wit_word hG.2.1 _ (by have := witLayerOff_eq _ hc.1; omega) (by have := witLayerOff_eq _ hc.1; omega),
      witChain, vw0_slice]
  · rw [PRes.toState_getReg, hr, headExp_x2]
    simp only [ldE, cw, E.eval]
    rw [hoff, show 0x800 + (witLayerOff c.lay + 16 * i) + 8 = 0x800 + (witLayerOff c.lay + 16 * i + 8)
      by omega, wit_word hG.2.1 _ (by have := witLayerOff_eq _ hc.1; omega) (by have := witLayerOff_eq _ hc.1; omega),
      witChain, vw1_slice]
  · rw [PRes.toState_pc_some _ _ _ (by simp only [hr, headExp]; rfl)]
    simp only [mkBin_eval, mkAdd_eval, BinOp.eval, E.eval]
    rw [hR14.2, rOf, add_sub_ofNat _ _ _ hB (by omega) (by omega),
      even_andNot1 _ (by omega), pcOf_entry _ _ _ ht4 ht1]


/-! ## The checkpoint of the next chain -/

theorem headInv_next (c : CCtx) (i : Nat) (hl : c.lay < 5) (hi : i < 42) (acc : List Val)
    (t : MachineState) (hG : Glob gkL c.wl c.pk t) (hK : KnownOK (chK c.lay) t) (hR : c.Regs t)
    (hCB : CBOk c t) (hZ : CBZ t) (hLB : LBOk acc t) (hlen : acc.length = i + 1)
    (hvs : ∀ v ∈ acc, v.length = 16) (hB : RB c i t) (hpc : t.pc = pcOf (nextPc' c.lay i)) :
    HeadInv c (i + 1) acc t := by
  refine ⟨hG, KnownOK_append.mpr ⟨hK, fun p hp => ?_⟩, hR, hCB, hZ, hLB, hlen, hvs,
    ⟨0, by omega, by rw [headPc, if_neg (by omega), Nat.add_sub_cancel]; exact hpc⟩,
    fun h1 h2 => by rw [rOf_next c i hl h1 h2]; exact hB.2⟩
  rw [List.mem_singleton.mp hp]
  simp only [bIn, if_neg (show i + 1 ≠ 0 by omega), Nat.add_sub_cancel]
  exact hB.1

/-! ## Table entries -/

theorem entry_mem (s : MachineState) (dst A : Nat) (hd : dst + 16 < 2 ^ 64) (hA : A < 2 ^ 64) :
    memEval s [(⟨none, BitVec.ofNat 64 (dst + 8)⟩, .reg .x2), (⟨none, BitVec.ofNat 64 dst⟩, .reg .x1)]
      (BitVec.ofNat 64 A) =
      if A = dst + 8 then s.getReg .x2 else if A = dst then s.getReg .x1 else
        s.getMem (BitVec.ofNat 64 A) := by
  have ne : ∀ B, B < 2 ^ 64 → A ≠ B → BitVec.ofNat 64 A ≠ BitVec.ofNat 64 B := by
    intro B hB h e; apply h
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this; omega
  split_ifs with h1 h2
  · subst h1; rw [memEval_cons_eq _ _ _ _ _ rfl]; rfl
  · subst h2; rw [memEval_cons_ne _ _ _ _ _ (ne _ (by omega) h1), memEval_cons_eq _ _ _ _ _ rfl]; rfl
  · rw [memEval_cons_ne _ _ _ _ _ (ne _ (by omega) h1), memEval_cons_ne _ _ _ _ _ (ne _ (by omega) h2)]
    rfl

theorem entry_run (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (hchk : chainCheck c.lay i = true)
    (s : MachineState) (hpc : s.pc = pcOf (entryIdx c.lay i (entIdx c i))) :
    Steps image s (if dig c i < 7 then 3 else 4) (if dig c i < 7 then 3 else 4)
      ((entryRes c.lay i (dig c i)).toState s) := by
  obtain ⟨ht4, ht1, htb, -, -, -⟩ := tabOk_spec (tabOk_at c.lay i hc.1 hi)
  obtain ⟨he, hd⟩ := entIdx_spec c i hi
  have hsn : nEnt i ≤ 64 := by unfold nEnt; split <;> omega
  have hent : entriesCheck c.lay i = true := by
    simp only [chainCheck, Bool.and_eq_true] at hchk; exact hchk.2
  unfold entriesCheck at hent
  rw [codeFrom_eq _ (by unfold entryIdx; omega)] at hent
  have hsym := entChk_spec c.lay i (nEnt i) 0 hent (entIdx c i) (by omega) (by omega)
  rw [hd] at hsym
  have hcode := codeAt_from (entryIdx c.lay i (entIdx c i)) (by unfold entryIdx; omega)
  exact symRun_sound hsym hcode s hpc (by simp [Result.obligs, entryRes, Oblig.all])

theorem entry_lt7 (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (s : MachineState) (hs : EntInv c i acc s) (hd : dig c i < 7) :
    ∃ t, Steps image s 3 3 t ∧ StepInv c i acc (dig c i + 1) (witChain c.wl c.lay i) t := by
  obtain ⟨hG, hK, hR, hCB, hCi, hB, hZ, hLB, hlen, hvs, hx1, hx2, hpc⟩ := hs
  have hst := entry_run c hc i hi hchk s hpc
  rw [if_pos hd] at hst
  set t := (entryRes c.lay i (dig c i)).toState s with ht
  have hreg : ∀ x, t.getReg x = s.getReg x := fun x => by
    rw [ht, Result.toState_getReg]; exact RegFile.init_get_eval s x
  have hmem : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = 0xF8 then s.getReg .x2 else if A = 0xF0 then s.getReg .x1 else
        s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [ht, Result.toState_getMem]; simp only [entryRes, if_pos hd]
    exact entry_mem s 0xF0 A (by omega) hA
  have fr : ∀ A, A < 2 ^ 64 → A ≠ 0xF0 → A ≠ 0xF8 → t.getMem (BitVec.ofNat 64 A) =
      s.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 => by
    rw [hmem A hA, if_neg h2, if_neg h1]
  refine ⟨t, hst, Glob_frame hG hreg (fun A hA hp => fr A hA ?_ ?_),
    fun p hp => (hreg _).trans (hK p hp), ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, hlen, hvs,
    length_witChain c hc i hi, ?_⟩
  · rcases hp with h | h | h | h <;> simp_all [pSlots] <;> omega
  · rcases hp with h | h | h | h <;> simp_all [pSlots] <;> omega
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hR
    exact ⟨(hreg _).trans h1, (hreg _).trans h2, (hreg _).trans h3, (hreg _).trans h4, (hreg _).trans h5⟩
  · exact ⟨by rw [fr _ (by omega) (by omega) (by omega)]; exact hCB.1,
      by rw [fr _ (by omega) (by omega) (by omega)]; exact hCB.2.1,
      by rw [fr _ (by omega) (by omega) (by omega)]; exact hCB.2.2⟩
  · unfold CBi; rw [fr _ (by omega) (by omega) (by omega)]; exact hCi
  · exact ⟨(hreg _).trans hB.1, (hreg _).trans hB.2⟩
  · rw [fr _ (by omega) (by omega) (by omega)]; exact hZ.1
  · rw [fr _ (by omega) (by omega) (by omega)]; exact hZ.2
  · rw [hmem _ (by omega)]; simpa using hx1
  · rw [hmem _ (by omega)]; simpa using hx2
  · exact LBOk_frame hLB (fun j hj => by
      rw [hlen] at hj
      exact ⟨fr _ (by omega) (by omega) (by omega), fr _ (by omega) (by omega) (by omega)⟩)
  · rw [ht, Result.toState_pc]; simp only [entryRes, if_pos hd, E.eval]
    congr 2

theorem entry_7 (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (s : MachineState) (hs : EntInv c i acc s) (hd : dig c i = 7) :
    ∃ t, Steps image s 4 4 t ∧ HeadInv c (i + 1) (acc ++ [witChain c.wl c.lay i]) t := by
  obtain ⟨hG, hK, hR, hCB, -, hB, hZ, hLB, hlen, hvs, hx1, hx2, hpc⟩ := hs
  have hst := entry_run c hc i hi hchk s hpc
  rw [if_neg (by omega)] at hst
  set t := (entryRes c.lay i (dig c i)).toState s with ht
  have hreg : ∀ x, t.getReg x = s.getReg x := fun x => by
    rw [ht, Result.toState_getReg]; exact RegFile.init_get_eval s x
  have hmem : ∀ A, A < 2 ^ 64 → t.getMem (BitVec.ofNat 64 A) =
      if A = 0x360 + 16 * i + 8 then s.getReg .x2 else if A = 0x360 + 16 * i then s.getReg .x1 else
        s.getMem (BitVec.ofNat 64 A) := fun A hA => by
    rw [ht, Result.toState_getMem]; simp only [entryRes, hd, show ¬ (7 < 7) by omega, if_false]
    exact entry_mem s _ A (by omega) hA
  have fr : ∀ A, A < 2 ^ 64 → A ≠ 0x360 + 16 * i → A ≠ 0x360 + 16 * i + 8 →
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := fun A hA h1 h2 => by
    rw [hmem A hA, if_neg h2, if_neg h1]
  have hw := length_witChain c hc i hi
  refine ⟨t, hst, headInv_next c i hc.1 hi _ t
    (Glob_frame hG hreg (fun A hA hp => fr A hA ?_ ?_))
    (fun p hp => (hreg _).trans (hK p (List.mem_append_left _ hp)))
    ?_ ?_ ⟨?_, ?_⟩ ?_ (by simp [hlen]) ?_ ⟨(hreg _).trans hB.1, (hreg _).trans hB.2⟩ ?_⟩
  · rcases hp with h | h | h | h <;> simp_all [pSlots] <;> omega
  · rcases hp with h | h | h | h <;> simp_all [pSlots] <;> omega
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hR
    exact ⟨(hreg _).trans h1, (hreg _).trans h2, (hreg _).trans h3, (hreg _).trans h4, (hreg _).trans h5⟩
  · exact ⟨by rw [fr _ (by omega) (by omega) (by omega)]; exact hCB.1,
      by rw [fr _ (by omega) (by omega) (by omega)]; exact hCB.2.1,
      by rw [fr _ (by omega) (by omega) (by omega)]; exact hCB.2.2⟩
  · rw [fr _ (by omega) (by omega) (by omega)]; exact hZ.1
  · rw [fr _ (by omega) (by omega) (by omega)]; exact hZ.2
  · refine LBOk_append (LBOk_frame hLB (fun j hj => ?_)) _ ?_ ?_
    · rw [hlen] at hj
      exact ⟨fr _ (by omega) (by omega) (by omega), fr _ (by omega) (by omega) (by omega)⟩
    · rw [hmem _ (by omega), hlen, if_neg (by omega), if_pos rfl]; exact hx1
    · rw [hmem _ (by omega), hlen, if_pos (by omega)]; exact hx2
  · intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact hvs v h
    · rw [List.mem_singleton.mp h]; exact hw
  · rw [ht, Result.toState_pc]; simp only [entryRes, hd, show ¬ (7 < 7) by omega, if_false, E.eval]

/-! ## Chain end -/

theorem chain_end (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (v : Val) (s : MachineState) (hs : EndInv c i acc v s) :
    HeadInv c (i + 1) (acc ++ [v]) s := by
  obtain ⟨hG, hK, hR, hCB, hB, hZ, hLB, hlen, hvs, hv, hpc⟩ := hs
  have hn := (tabOk_spec (tabOk_at c.lay i hc.1 hi)).2.2.2.2.2
  refine headInv_next c i hc.1 hi _ s hG hK hR hCB hZ hLB (by simp [hlen]) ?_ hB (by rw [hpc, hn])
  intro w hw
  rcases List.mem_append.mp hw with h | h
  · exact hvs w h
  · rw [List.mem_singleton.mp h]; exact hv

end SigGolfCandidate.Verify
