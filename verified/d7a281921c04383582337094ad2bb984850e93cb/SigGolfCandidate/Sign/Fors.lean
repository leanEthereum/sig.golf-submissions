import SigGolfCandidate.Sign.ForsLevel

/-!
# `sign`, the FORS trees (`fors_loop`, instructions 112 .. 190)

`fors_sim` : from `fors_loop` with `KAP = 0`, the machine refines `signFors S N`: opening `k`
(`s_k`, path) at `SIG + 16 + 176 k`, root `k` at `RB2 + 32 + 16 k`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- `FW` register value. -/
def fwVal (idx : Nat) : Nat := 0x801 + 2 ^ 24 * (idx / 2 ^ 32)

/-- Facts at the start of the FORS loop. -/
structure ForsCtx (S : List Byte) (idx N : Nat) (tF : MachineState) : Prop where
  x5 : tF.getReg .x5 = 0
  x14 : tF.getReg .x14 = BitVec.ofNat 64 (fwVal idx)
  x19 : tF.getReg .x19 = BitVec.ofNat 64 0x30000
  us : ∀ k < 14, tF.getMem (BitVec.ofNat 64 (0x710 + 8 * k)) = BitVec.ofNat 64 (uOf N k)
  pb0 : hi32 (tF.getMem (BitVec.ofNat 64 0x6A0)) = 0
  cb0 : hi32 (tF.getMem (BitVec.ofNat 64 0xC0)) = 0
  pb8 : lo32 (tF.getMem (BitVec.ofNat 64 0x6A8)) = BitVec.ofNat 32 idx
  cb8 : lo32 (tF.getMem (BitVec.ofNat 64 0xC8)) = BitVec.ofNat 32 idx
  nb8 : lo32 (tF.getMem (BitVec.ofNat 64 0x1C8)) = BitVec.ofNat 32 idx
  pbP : tF.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : tF.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cbP : tF.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]
  nbP : tF.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0]

def forsW (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ (0xE0 ≤ a ∧ a < 0x100) ∨ a = 0x1C0 ∨ a = 0x1C8 ∨
    (0x1E0 ≤ a ∧ a < 0x200) ∨ (0x30000 ≤ a ∧ a < 0x30000 + 16 * 1025) ∨
    (0x2650 + 16 ≤ a ∧ a < 0x2650 + 2480) ∨ (0x240 ≤ a ∧ a < 0x320)

def forsRegs : List Reg :=
  [.x1, .x2, .x3, .x8, .x9, .x10, .x11, .x12, .x13, .x15, .x16, .x17, .x18, .x29]

/-- An opening `(s, path)` stored at `B` (`s`, then the 10 path nodes). -/
def OpenAt (t : MachineState) (B : Nat) (o : Val × List Val) : Prop :=
  o.1.length = 16 ∧ o.2.length = 10 ∧ (∀ v ∈ o.2, v.length = 16) ∧ Slots t B (o.1 :: o.2)

/-- Invariant after `k` trees. -/
def ForsInv (tF : MachineState) (k : Nat) (st : List (Val × List Val) × List Val) (t : MachineState) :
    Prop :=
  k ≤ 14 ∧ st.1.length = k ∧ st.2.length = k ∧
  (∀ i (hi : i < st.1.length), OpenAt t (0x2650 + 16 + 176 * i) st.1[i]) ∧
  (∀ v ∈ st.2, v.length = 16) ∧ Slots t 0x240 st.2 ∧
  t.pc = (if k < 14 then pcOf 112 else pcOf 191) ∧ t.getReg .x8 = BitVec.ofNat 64 k ∧
  t.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) ∧
  RegsEq tF t forsRegs ∧ Frame tF t forsW ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (tF.getMem (BitVec.ofNat 64 0x6A8)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (tF.getMem (BitVec.ofNat 64 0xC8)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x1C8)) = lo32 (tF.getMem (BitVec.ofNat 64 0x1C8)) ∧
  hi32 (t.getMem (BitVec.ofNat 64 0x6A0)) = hi32 (tF.getMem (BitVec.ofNat 64 0x6A0)) ∧
  hi32 (t.getMem (BitVec.ofNat 64 0xC0)) = hi32 (tF.getMem (BitVec.ofNat 64 0xC0))

theorem buildFtsTree_bind {β : Type} (S : List Byte) (k idx u : Nat)
    (g : Val × List Val × Val → OracleComp HashSpec β) :
    buildFtsTree S k idx 10 u >>= g =
      buildFtsLeaves S k idx 10 u >>= fun p =>
        (List.range' 1 10).foldlM (levelStep (ftsNodeInput k idx) u) (p.1, []) >>= fun st =>
          g (p.2, st.2, st.1.getD 0 []) := by
  simp only [buildFtsTree, buildLevels, bind_assoc, pure_bind]

theorem fors_body (S : List Byte) (hS : S.length = 32) (idx N : Nat) (hidx : idx < 2 ^ 34)
    (hu : ∀ k, uOf N k < 1024) (tF : MachineState) (ctx : ForsCtx S idx N tF) (k : Nat) (hk : k < 14)
    (st : List (Val × List Val) × List Val) (t : MachineState) (hinv : ForsInv tF k st t) :
    Sim image t (8 + (1024 * 34 + (2 + (10 * 12822 + 9))))
      (do
        let (s, path, root) ← buildFtsTree S k idx 10 (uOf N k)
        pure (st.1 ++ [(s, path)], st.2 ++ [root]))
      (ForsInv tF (k + 1)) := by
  obtain ⟨-, hl1, hl2, hopen, hrv, hroots, tpc, t8, t18, tregs, tframe, lo1, lo2, lo3, hi1, hi2⟩ := hinv
  have tpc' : t.pc = pcOf 112 := by rw [tpc, if_pos hk]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by decide), ctx.x5]
  have tx14 : t.getReg .x14 = BitVec.ofNat 64 (fwVal idx) := by rw [tregs.get .x14 (by decide), ctx.x14]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x30000 := by rw [tregs.get .x19 (by decide), ctx.x19]
  have hu' := hu k
  have hi4 : idx / 2 ^ 32 < 4 := by omega
  -- block 112: tree setup
  have hs1 := symRun_sound blk112 codeAt_112 t tpc' (by
    simp only [blk112.res, rv_simp]; bvsimp [t8, accessValid_ofNat]; omega)
  have hc1 : blk112.res.cycles = 8 := rfl
  rw [hc1] at hs1
  set t1 := blk112.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x6A0 ∨ x = 0xC0) := by
    apply frame_toState; intro x hx hW
    simp only [blk112.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x3, .x9, .x13, .x29] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have y13 : t1.getReg .x13 = BitVec.ofNat 64 (uOf N k) := by
    simp only [ht1, blk112.res, rv_simp]; bvsimp [t8]
    rw [show k * 8 + 1808 = 0x710 + 8 * k by ring, tframe.getMem (by omega) (by simp only [forsW]; omega),
      ctx.us k hk]
  have y9 : t1.getReg .x9 = BitVec.ofNat 64 0 := by simp only [ht1, blk112.res, rv_simp]
  have pc1 : t1.pc = pcOf 120 := by simp only [ht1, blk112.res, rv_simp]
  have hfw : fwVal idx + k * 65536 < 2 ^ 32 := by unfold fwVal; omega
  have pb0 : t1.getMem (BitVec.ofNat 64 0x6A0) = twWord0 8 k idx 0 := by
    simp only [ht1, blk112.res, rv_simp]; bvsimp [t8, tx14, ofNat_eq_iff]
    refine (word_of_halves _ (fwVal idx + k * 65536) 0 (by rw [lo32_replace0]) (by
      rw [hi32_replace0, hi1, ctx.pb0]; rfl)).trans ?_
    unfold twWord0 fwVal; congr 1; omega
  have cb0 : t1.getMem (BitVec.ofNat 64 0xC0) = twWord0 9 k idx 0 := by
    simp only [ht1, blk112.res, rv_simp]; bvsimp [t8, tx14, ofNat_eq_iff]
    refine (word_of_halves _ (fwVal idx + k * 65536 + 256) 0 (by rw [lo32_replace0]) (by
      rw [hi32_replace0, hi2, ctx.cb0]; rfl)).trans ?_
    unfold twWord0 fwVal; congr 1; omega
  have hWt : ∀ x, ¬ forsW x → x ≠ 0x6A0 → x ≠ 0xC0 → ¬ (x = 0x6A0 ∨ x = 0xC0) := by
    intro x _ h1 h2 h; omega
  have lctx : LeafCtx S k idx (uOf N k) t1 := by
    refine ⟨pb0, ?_, ?_, ?_, cb0, ?_, ?_, ?_, y13, ?_, ?_⟩
    · rw [f1.getMem (by norm_num) (by omega), lo1, ctx.pb8]
    · rw [f1.readWords _ _ (by norm_num) (by intro i hi; omega),
        tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega), ctx.pbP]
    · rw [f1.readWords _ _ (by norm_num) (by intro i hi; omega),
        tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega), ctx.pbS]
    · rw [f1.getMem (by norm_num) (by omega), lo2, ctx.cb8]
    · rw [f1.readWords _ _ (by norm_num) (by intro i hi; omega),
        tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega), ctx.cbP]
    · rw [r1.get .x5, tx5]
    · rw [r1.get .x18, t18]
    · rw [r1.get .x19, tx19]
  rw [buildFtsTree_bind]
  refine Sim.steps hs1 (Sim.bind (forsLeaves_sim S hS k idx (uOf N k) hk hidx hu' t1 lctx pc1 y9)
    (fun p t2 h2 => ?_))
  obtain ⟨-, hlv, hlvv, hlvs, hsec, pc2, -, lregs, lframe, llo1, llo2⟩ := h2
  have pc2' : t2.pc = pcOf 140 := by rw [pc2]; rfl
  obtain ⟨hsl, hsw⟩ := hsec hu'
  -- block 140
  have hs3 := symRun_sound blk140 codeAt_140 t2 pc2' (by simp only [blk140.res, rv_simp])
  have hc3 : blk140.res.cycles = 2 := rfl
  rw [hc3] at hs3
  set t3 := blk140.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk140.res]
  have r3 : RegsEq t2 t3 [.x15, .x17] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft13 : Frame t t3 (fun x => (x = 0x6A0 ∨ x = 0xC0) ∨ leafW k x) :=
    (f1.trans (lframe.trans f3)).mono (by
      intro x hx; rcases hx with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact h.elim)
  have rt13 : RegsEq t t3 ([.x3, .x9, .x13, .x29] ++ leafRegs ++ [.x15, .x17]) :=
    (r1.trans lregs).trans r3
  have vctx : LevCtx k idx (uOf N k) t3 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [rt13.get .x5, tx5]
    · rw [rt13.get .x8, t8]
    · rw [r3.get .x13, lregs.get .x13 (by decide), y13]
    · rw [rt13.get .x14, tx14]; rfl
    · rw [rt13.get .x18, t18]
    · rw [rt13.get .x19, tx19]
    · rw [ft13.getMem (by norm_num) (by simp only [leafW]; omega), lo3, ctx.nb8]
    · rw [ft13.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega),
        tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega), ctx.nbP]
  refine Sim.steps hs3 (Sim.bind (forsLevels_sim k idx (uOf N k) hk hidx hu' t3 vctx p.1 hlv hlvv
    (hlvs.frame f3 (by omega) (by simp)) (by simp only [ht3, blk140.res, rv_simp])
    (by simp only [ht3, blk140.res, rv_simp]) (by simp only [ht3, blk140.res, rv_simp]))
    (fun st' t4 h4 => ?_))
  obtain ⟨-, hl4, hv4, hs4, hp4, hpv4, hps4, pc4, -, -, vregs, vframe, vlo⟩ := h4
  have pc4' : t4.pc = pcOf 182 := by rw [pc4]; rfl
  have rt4 : RegsEq t t4 ([.x3, .x9, .x13, .x29] ++ leafRegs ++ [.x15, .x17] ++ levRegs) :=
    rt13.trans vregs
  have x48 : t4.getReg .x8 = BitVec.ofNat 64 k := by rw [rt4.get .x8, t8]
  have x418 : t4.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) := by rw [rt4.get .x18, t18]
  have x419 : t4.getReg .x19 = BitVec.ofNat 64 0x30000 := by rw [rt4.get .x19, tx19]
  -- block 182: root, next tree
  have hs5 := symRun_sound blk182 codeAt_182 t4 pc4' (by
    simp only [blk182.res, rv_simp]; bvsimp [x48, x419, accessValid_ofNat]; omega)
  have hc5 : blk182.res.cycles = 9 := rfl
  rw [hc5] at hs5
  set t5 := blk182.res.toState t4 with ht5
  have f5 : Frame t4 t5 (fun x => x = 0x240 + 16 * k ∨ x = 0x240 + 16 * k + 8) := by
    apply frame_toState; intro x hx hW
    simp only [blk182.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [x48, ofNat_eq_iff]
    omega
  have r5 : RegsEq t4 t5 [.x1, .x2, .x3, .x8, .x18] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have root5 : t5.readWords (BitVec.ofNat 64 (0x240 + 16 * k)) 2 = wordsOf (st'.1.getD 0 []) := by
    rw [← hs4.getD 0 (by rw [hl4]; norm_num), readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht5, blk182.res, rv_simp]
    bvsimp [x48, x419, ofNat_eq_iff]
    simp (disch := bvomega) only [if_pos, if_neg]
  -- the frame from `t` to `t5`
  have ft5 : Frame t t5 (fun x => ((x = 0x6A0 ∨ x = 0xC0) ∨ leafW k x) ∨ levW k x ∨
      (x = 0x240 + 16 * k ∨ x = 0x240 + 16 * k + 8)) := ft13.trans (vframe.trans f5)
  have hsec5 : t5.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf p.2 := by
    rw [f5.readWords _ _ (by omega) (by intro i hi; omega),
      vframe.readWords _ _ (by omega) (by intro i hi; simp only [levW]; omega),
      f3.readWords _ _ (by omega) (by simp), hsw]
  have hpath5 : Slots t5 (0x2650 + 176 * k + 32) st'.2 :=
    hps4.frame f5 (by omega) (by intro i hi; rw [hp4] at hi; constructor <;> omega)
  refine Sim.pure_steps hs5 ⟨by omega, by simp [hl1], by simp [hl2], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hik : i < st.1.length
    · rw [List.getElem_append_left hik]
      obtain ⟨o1, o2, o3, o4⟩ := hopen i hik
      refine ⟨o1, o2, o3, o4.frame ft5 (by simp [o2]; omega) ?_⟩
      intro j hj
      simp only [List.length_cons, o2] at hj
      simp only [leafW, levW]
      constructor <;> omega
    · have : i = st.1.length := by omega
      subst this
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton]
      refine ⟨hsl, hp4, hpv4, Slots.cons ?_ ?_⟩
      · rw [hl1, show 0x2650 + 16 + 176 * k = 0x2650 + 176 * k + 16 by ring]; exact hsec5
      · rw [hl1, show 0x2650 + 16 + 176 * k + 16 = 0x2650 + 176 * k + 32 by ring]; exact hpath5
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hrv v hv
    · simp at hv; subst hv
      simp only [List.getElem?_eq_getElem (show 0 < st'.1.length by rw [hl4]; norm_num),
        Option.getD_some]
      exact hv4 _ (List.getElem_mem _)
  · apply Slots.snoc
    · exact hroots.frame ft5 (by omega) (by
        intro i hi; simp only [leafW, levW]; constructor <;> omega)
    · rw [hl2]; exact root5
  · simp only [ht5, blk182.res, rv_simp]
    bvsimp [x48, ofNat_bne_ofNat]
    by_cases h : k + 1 < 14
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · simp only [ht5, blk182.res, rv_simp]; bvsimp [x48]
  · simp only [ht5, blk182.res, rv_simp]; bvsimp [x418]
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_ofNat]; omega
  · exact ((tregs.trans rt4).trans r5).mono (by decide)
  · exact (tframe.trans ft5).mono (by intro x hx; simp only [forsW, leafW, levW] at hx ⊢; omega)
  · rw [f5.getMem (by norm_num) (by omega), vframe.getMem (by norm_num) (by simp only [levW]; omega),
      f3.getMem (by norm_num) (by simp), llo1, f1.getMem (by norm_num) (by omega), lo1]
  · rw [f5.getMem (by norm_num) (by omega), vframe.getMem (by norm_num) (by simp only [levW]; omega),
      f3.getMem (by norm_num) (by simp), llo2, f1.getMem (by norm_num) (by omega), lo2]
  · rw [f5.getMem (by norm_num) (by omega), vlo, ft13.getMem (by norm_num) (by simp only [leafW]; omega),
      lo3]
  · rw [f5.getMem (by norm_num) (by omega), vframe.getMem (by norm_num) (by simp only [levW]; omega),
      f3.getMem (by norm_num) (by simp), lframe.getMem (by norm_num) (by simp only [leafW]; omega), pb0,
      ctx.pb0, twWord0, hi32_ofNat]
    rw [Nat.div_eq_of_lt (by omega)]; rfl
  · rw [f5.getMem (by norm_num) (by omega), vframe.getMem (by norm_num) (by simp only [levW]; omega),
      f3.getMem (by norm_num) (by simp), lframe.getMem (by norm_num) (by simp only [leafW]; omega), cb0,
      ctx.cb0, twWord0, hi32_ofNat]
    rw [Nat.div_eq_of_lt (by omega)]; rfl

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Cycle bound of one FORS tree. -/
abbrev forsTreeW : Nat := 8 + (1024 * 34 + (2 + (10 * 12822 + 9)))

/-- **FORS**: the 14 trees. -/
theorem fors_sim (S : List Byte) (hS : S.length = 32) (N : Nat) (tF : MachineState)
    (ctx : ForsCtx S (idxOf N) N tF) (hpc : tF.pc = pcOf 112)
    (h8 : tF.getReg .x8 = BitVec.ofNat 64 0) (h18 : tF.getReg .x18 = BitVec.ofNat 64 0x2650) :
    Sim image tF (14 * forsTreeW) (signFors S N) (ForsInv tF 14) := by
  have hidx : idxOf N < 2 ^ 34 := Nat.mod_lt _ (by norm_num)
  have hu : ∀ k, uOf N k < 1024 := fun k => Nat.mod_lt _ (by norm_num)
  unfold signFors ftsTrees ftsA
  apply Sim.foldlM_range 14 _ ([], []) (ForsInv tF) forsTreeW
  · intro k hk st t h
    exact fors_body S hS (idxOf N) N hidx hu tF ctx k hk st t h
  · exact ⟨by norm_num, rfl, rfl, fun i hi => absurd hi (by simp), by simp, Slots.nil _ _,
      by simpa using hpc, h8, by simpa using h18, RegsEq.refl _ _, Frame.refl _ _, rfl, rfl, rfl,
      rfl, rfl⟩

end SigGolfCandidate.Sign
