import SigGolfCandidate.Keygen.Inv
import SigGolfCandidate.Keygen.XSim

/-!
# `keygen`: the chain step loop, the chains, the leaves
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

/-- `pc` of instruction `k`. -/
abbrev pcOf (k : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * k)

/-- Leaf-loop context: leaves `0 .. e-1` are in the tree array. -/
structure LCtx (W : List Word) (e : Nat) (leaves : List Val) (t : MachineState) : Prop where
  base : Base W t
  t1 : (t.getMem (BitVec.ofNat 64 1696)).toNat % 2 ^ 32 = 1
  t2 : (t.getMem (BitVec.ofNat 64 192)).toNat % 2 ^ 32 = 257
  r17 : t.getReg .x17 = BitVec.ofNat 64 32
  r20 : t.getReg .x20 = BitVec.ofNat 64 e
  len : leaves.length = e
  lv : Vals t TA leaves

/-- Chain-loop context of leaf `e`: chain ends `0 .. j-1` are in the leaf buffer. -/
structure CCtx (W : List Word) (e : Nat) (leaves : List Val) (j : Nat) (ends : List Val)
    (t : MachineState) : Prop extends LCtx W e leaves t where
  w1704 : t.getMem (BitVec.ofNat 64 1704) = BitVec.ofNat 64 (2 ^ 32 * e)
  w200 : t.getMem (BitVec.ofNat 64 200) = BitVec.ofNat 64 (2 ^ 32 * e)
  w840 : t.getMem (BitVec.ofNat 64 840) = BitVec.ofNat 64 (2 ^ 32 * e)
  r21 : t.getReg .x21 = BitVec.ofNat 64 j
  elen : ends.length = j
  ev : Vals t 864 ends

/-- A key that does not touch the chain-loop context (except possibly `1696`, `192`). -/
def CSafe (e j k : Nat) : Prop :=
  BaseSafe k ∧ k ∉ [1704, 200, 840] ∧ (k + 8 ≤ TA ∨ TA + 16 * e ≤ k) ∧ (k + 8 ≤ 864 ∨ 864 + 16 * j ≤ k)

theorem CCtx.frame {W : List Word} {e j : Nat} {leaves ends : List Val} {s t : MachineState}
    {keys : List Nat} (h : CCtx W e leaves j ends s) (he : e ≤ 32) (hj : j ≤ 42)
    (hr : ∀ r, r = .x5 ∨ r = .x8 ∨ r = .x30 ∨ r = .x9 ∨ r = .x19 ∨ r = .x17 ∨ r = .x20 ∨ r = .x21 →
      t.getReg r = s.getReg r)
    (hf : Frame s t keys) (hk : ∀ k ∈ keys, CSafe e j k)
    (ht1 : (t.getMem (BitVec.ofNat 64 1696)).toNat % 2 ^ 32 = 1)
    (ht2 : (t.getMem (BitVec.ofNat 64 192)).toNat % 2 ^ 32 = 257) :
    CCtx W e leaves j ends t := by
  have fr : ∀ A < 2 ^ 64, (∀ k ∈ keys, A ≠ k) → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
    fun A hA hne => hf A hA (fun hm => hne A hm rfl)
  refine ⟨⟨h.base.frame (fun r hr' => hr r (by rcases hr' with h | h | h | h | h <;> simp [h]))
      hf (fun k hk' => (hk k hk').1), ht1, ht2, ?_, ?_, h.len, ?_⟩, ?_, ?_, ?_, ?_, h.elen, ?_⟩
  · rw [hr _ (by simp)]; exact h.r17
  · rw [hr _ (by simp)]; exact h.r20
  · exact h.lv.frame hf (by rw [h.len]; unfold TA; omega) (fun k hk' => by
      have := (hk k hk').2.2.1; rw [h.len]; unfold TA at *; omega)
  · rw [fr _ (by omega) (fun k hk' heq => (hk k hk').2.1 (by simp [← heq]))]; exact h.w1704
  · rw [fr _ (by omega) (fun k hk' heq => (hk k hk').2.1 (by simp [← heq]))]; exact h.w200
  · rw [fr _ (by omega) (fun k hk' heq => (hk k hk').2.1 (by simp [← heq]))]; exact h.w840
  · rw [hr _ (by simp)]; exact h.r21
  · exact h.ev.frame hf (by rw [h.elen]; omega) (fun k hk' => by
      have := (hk k hk').2.2.2; rw [h.elen]; omega)

theorem readWords8 (t : MachineState) (B : Nat) :
    t.readWords (BitVec.ofNat 64 B) 8 = [t.getMem (BitVec.ofNat 64 B), t.getMem (BitVec.ofNat 64 (B + 8)),
      t.getMem (BitVec.ofNat 64 (B + 16)), t.getMem (BitVec.ofNat 64 (B + 24)),
      t.getMem (BitVec.ofNat 64 (B + 32)), t.getMem (BitVec.ofNat 64 (B + 40)),
      t.getMem (BitVec.ofNat 64 (B + 48)), t.getMem (BitVec.ofNat 64 (B + 56))] := by
  simp only [MachineState.readWords, ofNat_add8]

/-- Chain-step context: step `m` of chain `j` (value `v` in the chain buffer). -/
structure SCtx (W : List Word) (e : Nat) (leaves : List Val) (j : Nat) (ends : List Val)
    (m : Nat) (v : Val) (t : MachineState) : Prop extends CCtx W e leaves j ends t where
  r24 : t.getReg .x24 = BitVec.ofNat 64 (8 * j + m)
  r23 : t.getReg .x23 = BitVec.ofNat 64 m
  r11 : t.getReg .x11 = BitVec.ofNat 64 64
  vv : ValAt t 224 v
  vl : v.length = 16
  z240 : t.getMem (BitVec.ofNat 64 240) = 0
  z248 : t.getMem (BitVec.ofNat 64 248) = 0

theorem hashArgs_const (t : MachineState) (a b c : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 b) (h12 : t.getReg .x12 = BitVec.ofNat 64 c)
    (ha : a % 8 = 0) (hb : 0 < b ∧ b % 64 = 0) (hab : a + b ≤ 2 ^ 24) (hc : c % 8 = 0)
    (hc' : c + 32 ≤ 2 ^ 24) : hashArgumentsValid t = true := by
  simp only [hashArgumentsValid, h10, h11, h12, rangeValid, accessValid, MEMORY_BYTES,
    Bool.and_eq_true, decide_eq_true_eq, toNat_ofNat_lt (by omega : a < 2 ^ 64),
    toNat_ofNat_lt (by omega : b < 2 ^ 64), toNat_ofNat_lt (by omega : c < 2 ^ 64)]
  omega

/-- One chain step (`mu = m + 1`). -/
theorem step_xsim (W : List Word) (e : Nat) (leaves : List Val) (j : Nat) (ends : List Val)
    (m : Nat) (hm : m < 7) (he : e < 32) (hj : j < 42) (st : Val × Val) (t : MachineState)
    (h : SCtx W e leaves j ends m st.1 t) (hpc : t.pc = pcOf 38) :
    XSim image t 10 17 1 1
      (do let v ← Ref.hash16 (chainInput 0 0 e j (1 + m) st.1)
          pure (v, if 1 + m = 0 then v else st.2))
      (fun st' u => SCtx W e leaves j ends (m + 1) st'.1 u ∧
        u.pc = if m + 1 < 7 then pcOf 38 else pcOf 48) := by
  obtain ⟨u, hst, upc, u23, u10, u12, uun, u192, ufr⟩ :=
    spec_38 t hpc m (8 * j + m) (by omega) h.r23 h.r24 h.t2
  have ux : ∀ r, r ≠ .x23 ∧ r ≠ .x10 ∧ r ≠ .x12 → u.getReg r = t.getReg r :=
    fun r hr => uun r hr.1 hr.2.1 hr.2.2
  have hq : hashInput u = pad64 (chainInput 0 0 e j (1 + m) st.1) := by
    have hx : (chainInput 0 0 e j (1 + m) st.1).length = 48 := by
      simp [chainInput, thInput, h.vl]
    refine hashInput_eq_pad64 u 0 192 _ (by rw [ux _ (by simp), h.r11]) (by norm_num) u10
      (by norm_num) (by norm_num) (by omega) (by omega) ?_
    rw [readWords8, u192]
    simp only [wordsToNat]
    have g : ∀ A ∈ [200, 208, 216, 224, 232, 240, 248],
        u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
      intro A hA; simp at hA
      exact getMem_frame ufr (by omega) (by simp; omega)
    simp only [Nat.reduceAdd]
    rw [g 200 (by simp), g 208 (by simp), g 216 (by simp), g 224 (by simp), g 232 (by simp),
      g 240 (by simp), g 248 (by simp), h.w200, h.base.zero 208 (by simp [zeroKeys]),
      h.base.zero 216 (by simp [zeroKeys]), h.vv.1, h.z240, h.z248]
    have hv2 := h.vv.2
    simp only [Nat.reduceAdd] at hv2
    rw [hv2]
    simp only [chainInput, thInput, leNat_append, List.length_append, length_tweak, length_P,
      P, leNat_zeros, length_zeros, leNat_tweak0 1 0 _ _ (by norm_num) (by norm_num), leNat_val st.1 h.vl]
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.reducePow, Nat.reduceMul,
      Nat.reduceAdd]
    omega
  have hblk : (pad64 (chainInput 0 0 e j (1 + m) st.1)).blocks = 1 := by
    simp [Query.blocks, pad64, padBlocks, chainInput, thInput, h.vl]
  refine (XSim.steps hst (XSim.hash16_bind (k := 5) (c := 5) (n := 0) (b := 0)
    (f := fun v => pure (v, if 1 + m = 0 then v else st.2))
    ((codeAt_42.fetch u upc).trans rfl) (by rw [ux _ (by simp)]; exact h.base.r5)
    (hashArgs_const u 192 64 224 u10 (by rw [ux _ (by simp)]; exact h.r11) u12 (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hq (fun a => ?_))).of_eq rfl
    (by rfl) (by rw [hblk]) (by rfl) (by rw [hblk])
  have wpc : (writeHash u a).pc = pcOf 43 := by rw [pc_writeHash, upc]; rfl
  obtain ⟨v, vst, vpc, v24, vun, v240, v248, vfr⟩ := spec_43 (writeHash u a) wpc (m + 1) (8 * j + m)
    (by omega) (by rw [getReg_writeHash, u23]) (by rw [getReg_writeHash, ux _ (by simp), h.r24])
  refine XSim.pure_steps vst ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · have fr := (ufr.trans (Frame.writeHash u a 224 u12 (by norm_num) (by norm_num))).trans vfr
    refine h.toCCtx.frame (by omega) (by omega) (fun r hr => ?_) fr (fun k hk => ?_) ?_ ?_
    · rw [vun r (by rcases hr with h | h | h | h | h | h | h | h <;> simp [h])
        (by rcases hr with h | h | h | h | h | h | h | h <;> simp [h]), getReg_writeHash,
        ux r (by rcases hr with h | h | h | h | h | h | h | h <;> simp [h])]
    · simp at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [CSafe, BaseSafe, zeroKeys, TA] <;> omega
    · rw [getMem_frame fr (by norm_num) (by simp)]; exact h.t1
    · rw [getMem_frame vfr (by norm_num) (by simp),
        getMem_frame (Frame.writeHash u a 224 u12 (by norm_num) (by norm_num)) (by norm_num) (by simp),
        u192, BitVec.toNat_ofNat]
      omega
  · rw [v24]; congr 1
  · rw [vun _ (by simp) (by simp), getReg_writeHash, u23]
  · rw [vun _ (by simp) (by simp), getReg_writeHash, ux _ (by simp), h.r11]
  · exact (valAt_writeHash u a 224 u12 (by norm_num)).frame vfr (by norm_num) (by simp)
  · simp
  · exact v240
  · exact v248
  · rw [vpc]
    by_cases hm7 : m + 1 = 7
    · rw [if_pos hm7, if_neg (by omega)]
    · rw [if_neg hm7, if_pos (by omega)]

/-- The secret-key words `W` encode `S`. -/
def SkOk (W : List Word) (S : List Byte) : Prop :=
  S.length = 32 ∧ (W.getD 0 0).toNat + 2 ^ 64 * ((W.getD 1 0).toNat + 2 ^ 64 * ((W.getD 2 0).toNat +
    2 ^ 64 * (W.getD 3 0).toNat)) = leNat S

theorem sumTo_const' (c n : Nat) : sumTo (fun _ => c) n = n * c := sumTo_const c n

/-- A whole chain (`prf`, 7 steps) of leaf `e`, ending with the copy of its end. -/
theorem chain_xsim (W : List Word) (S : List Byte) (hS : SkOk W S) (e : Nat) (leaves : List Val)
    (j : Nat) (he : e < 32) (hj : j < 42) (st : List Val × List Val) (t : MachineState)
    (h : CCtx W e leaves j st.1 t) (h24 : t.getReg .x24 = BitVec.ofNat 64 (8 * j))
    (hpc : t.pc = pcOf 30) :
    XSim image t 87 143 8 8
      (do let (v, c) ← buildChain S 0 0 e j (([] : List Nat).getD j 0)
          pure (st.1 ++ [v], st.2 ++ [c]))
      (fun st' u => CCtx W e leaves (j + 1) st'.1 u ∧ u.getReg .x24 = BitVec.ofNat 64 (8 * (j + 1)) ∧
        u.pc = if j + 1 < 42 then pcOf 30 else pcOf 57) := by
  obtain ⟨u, hst, upc, u10, u11, u12, uun, u1696, ufr⟩ :=
    spec_30 t hpc j (by omega) h.r21 h.t1
  have ux : ∀ r, r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 → u.getReg r = t.getReg r :=
    fun r hr => uun r hr.1 hr.2.1 hr.2.2
  have hq : hashInput u = pad64 (prfInput S 0 0 e j) := by
    have hx : (prfInput S 0 0 e j).length = 64 := by simp [prfInput, thInput, hS.1]
    refine hashInput_eq_pad64 u 0 1696 _ (by rw [u11]) (by norm_num) u10
      (by norm_num) (by norm_num) (by omega) (by omega) ?_
    rw [readWords8, u1696]
    simp only [wordsToNat]
    have g : ∀ A ∈ [1704, 1712, 1720, 1728, 1736, 1744, 1752],
        u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
      intro A hA; simp at hA
      exact getMem_frame ufr (by omega) (by simp; omega)
    simp only [Nat.reduceAdd]
    rw [g 1704 (by simp), g 1712 (by simp), g 1720 (by simp), g 1728 (by simp), g 1736 (by simp),
      g 1744 (by simp), g 1752 (by simp), h.w1704, h.base.zero 1712 (by simp [zeroKeys]),
      h.base.zero 1720 (by simp [zeroKeys]), h.base.sk 0 (by norm_num), h.base.sk 1 (by norm_num),
      h.base.sk 2 (by norm_num), h.base.sk 3 (by norm_num)]
    have hW := hS.2
    simp only [prfInput, thInput, leNat_append, List.length_append, length_tweak,
      P, leNat_zeros, length_zeros, leNat_tweak0 0 0 _ _ (by norm_num) (by norm_num)]
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.reducePow, Nat.reduceMul,
      Nat.reduceAdd] at hW ⊢
    omega
  have hblk : (pad64 (prfInput S 0 0 e j)).blocks = 1 := by
    simp [Query.blocks, pad64, padBlocks, prfInput, thInput, hS.1]
  -- the chain itself
  have hchain : XSim image t 78 134 8 8 (buildChain S 0 0 e j 0)
      (fun p w => SCtx W e leaves j st.1 7 p.1 w ∧ w.pc = pcOf 48) := by
    unfold buildChain
    refine (XSim.steps hst (XSim.hash16_bind (k := 73) (c := 122) (n := 7) (b := 7)
      ((codeAt_34.fetch u upc).trans rfl) (by rw [ux _ (by simp)]; exact h.base.r5)
      (hashArgs_const u 1696 64 224 u10 u11 u12 (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)) hq (fun a => ?_))).of_eq rfl
      (by rfl) (by rw [hblk]) (by rfl) (by rw [hblk])
    have wpc : (writeHash u a).pc = pcOf 35 := by rw [pc_writeHash, upc]; rfl
    obtain ⟨v, vst, vpc, v23, vun, v240, v248, vfr⟩ := spec_35 (writeHash u a) wpc
    have fr := (ufr.trans (Frame.writeHash u a 224 u12 (by norm_num) (by norm_num))).trans vfr
    have hv0 : SCtx W e leaves j st.1 0 (answerBytes 16 a) v := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, v240, v248⟩
      · refine h.frame (by omega) (by omega) (fun r hr => ?_) fr (fun k hk => ?_) ?_ ?_
        · rw [vun r (by rcases hr with h | h | h | h | h | h | h | h <;> simp [h]), getReg_writeHash,
            ux r (by rcases hr with h | h | h | h | h | h | h | h <;> simp [h])]
        · simp at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            simp [CSafe, BaseSafe, zeroKeys, TA] <;> omega
        · rw [getMem_frame vfr (by norm_num) (by simp),
            getMem_frame (Frame.writeHash u a 224 u12 (by norm_num) (by norm_num)) (by norm_num) (by simp),
            u1696, BitVec.toNat_ofNat]
          omega
        · rw [getMem_frame fr (by norm_num) (by simp)]; exact h.t2
      · rw [vun _ (by simp), getReg_writeHash, ux _ (by simp), h24]; rfl
      · rw [v23]
      · rw [vun _ (by simp), getReg_writeHash, u11]
      · exact (valAt_writeHash u a 224 u12 (by norm_num)).frame vfr (by norm_num) (by simp)
      · simp
    have := XSim.foldlM_range' (image := image) 1 7
      (fun (st : Val × Val) mu => do
        let v ← Ref.hash16 (chainInput 0 0 e j mu st.1)
        pure (v, if mu = 0 then v else st.2))
      (answerBytes 16 a, answerBytes 16 a)
      (fun m st' w => SCtx W e leaves j st.1 m st'.1 w ∧ w.pc = if m < 7 then pcOf 38 else pcOf 48)
      (fun _ => 10) (fun _ => 17) (fun _ => 1) (fun _ => 1)
      (fun m hm st' w hw => step_xsim W e leaves j st.1 m hm he hj st' w hw.1
        (by rw [hw.2, if_pos hm]))
      ⟨hv0, by rw [vpc]; rfl⟩
    refine (XSim.steps vst this).of_eq rfl (by rfl) (by rfl) (by rfl) (by rfl) |>.mono ?_
    intro p w hw; exact ⟨hw.1, by rw [hw.2]; rfl⟩
  refine (XSim.bind (k₂ := 9) (c₂ := 9) (n₂ := 0) (b₂ := 0) hchain (fun p w hw => ?_)).of_eq rfl
    (by rfl) (by rfl) (by rfl) (by rfl)
  obtain ⟨v, c⟩ := p
  obtain ⟨x, xst, xpc, x21, x24, xun, x864, x872, xfr⟩ :=
    spec_48 w hw.2 j (8 * j + 7) hj hw.1.r21 hw.1.r24
  refine XSim.pure_steps xst ⟨?_, by rw [x24]; congr 1 <;> omega, ?_⟩
  · have hs := hw.1
    refine CCtx.mk (LCtx.mk ?_ ?_ ?_ ?_ ?_ hs.len ?_) ?_ ?_ ?_ x21 ?_ ?_
    · refine hs.base.frame (fun r hr => xun r ?_ ?_ ?_ ?_ ?_) xfr (fun k hk => ?_) <;>
        try (rcases hr with h | h | h | h | h <;> simp [h])
      simp at hk; rcases hk with rfl | rfl <;> simp [BaseSafe, zeroKeys] <;> omega
    · rw [getMem_frame xfr (by norm_num) (by simp; omega)]; exact hs.t1
    · rw [getMem_frame xfr (by norm_num) (by simp; omega)]; exact hs.t2
    · rw [xun _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hs.r17
    · rw [xun _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hs.r20
    · exact hs.lv.frame xfr (by rw [hs.len]; unfold TA; omega)
        (fun k hk => by simp at hk; rw [hs.len]; unfold TA; omega)
    · rw [getMem_frame xfr (by norm_num) (by simp; omega)]; exact hs.w1704
    · rw [getMem_frame xfr (by norm_num) (by simp; omega)]; exact hs.w200
    · rw [getMem_frame xfr (by norm_num) (by simp; omega)]; exact hs.w840
    · simp [hs.elen]
    · have hv := hs.vv
      refine (hs.ev.frame xfr (by rw [hs.elen]; omega) (fun k hk => by
        simp at hk; rw [hs.elen]; omega)).snoc ?_ hs.vl
      rw [hs.elen]
      exact ⟨by rw [x864]; exact hv.1, by rw [x872]; exact hv.2⟩
  · rw [xpc]
    by_cases hj' : j + 1 = 42
    · rw [if_pos hj', if_neg (by omega)]
    · rw [if_neg hj', if_pos (by omega)]

theorem Vals.nil (t : MachineState) (A : Nat) : Vals t A [] := ⟨by simp, by simp⟩

/-- A whole leaf `e`: 42 chains, the leaf hash into the tree array. -/
theorem leaf_xsim (W : List Word) (S : List Byte) (hS : SkOk W S) (e : Nat) (he : e < 32)
    (acc : List Val × List Val) (t : MachineState) (h : LCtx W e acc.1 t) (hpc : t.pc = pcOf 23) :
    XSim image t 3668 6107 337 347
      (do let (leaf, c) ← buildLeaf S 0 0 e []
          pure (acc.1 ++ [leaf], if e = 0 then c else acc.2))
      (fun acc' u => LCtx W (e + 1) acc'.1 u ∧ u.pc = if e + 1 < 32 then pcOf 23 else pcOf 64) := by
  obtain ⟨u, hst, upc, u21, u24, uun, u1704, u200, u840, ufr⟩ :=
    spec_23 t hpc e (by omega) h.r20 h.base.r30
  have h0 : CCtx W e acc.1 0 [] u := by
    refine CCtx.mk (LCtx.mk ?_ ?_ ?_ ?_ ?_ h.len ?_) u1704 u200 u840 u21 rfl (Vals.nil u 864)
    · refine h.base.frame (fun r hr => uun r ?_ ?_ ?_) ufr (fun k hk => ?_) <;>
        try (rcases hr with h | h | h | h | h <;> simp [h])
      simp at hk; rcases hk with rfl | rfl | rfl <;> simp [BaseSafe, zeroKeys]
    · rw [getMem_frame ufr (by norm_num) (by simp)]; exact h.t1
    · rw [getMem_frame ufr (by norm_num) (by simp)]; exact h.t2
    · rw [uun _ (by simp) (by simp) (by simp)]; exact h.r17
    · rw [uun _ (by simp) (by simp) (by simp)]; exact h.r20
    · exact h.lv.frame ufr (by rw [h.len]; unfold TA; omega)
        (fun k hk => by simp at hk; rw [h.len]; unfold TA; omega)
  have hchains := XSim.foldlM_range (image := image) 42
    (fun (st : List Val × List Val) i => do
      let (v, c) ← buildChain S 0 0 e i (([] : List Nat).getD i 0)
      pure (st.1 ++ [v], st.2 ++ [c]))
    ([], [])
    (fun j st w => CCtx W e acc.1 j st.1 w ∧ w.getReg .x24 = BitVec.ofNat 64 (8 * j) ∧
      w.pc = if j < 42 then pcOf 30 else pcOf 57)
    (fun _ => 87) (fun _ => 143) (fun _ => 8) (fun _ => 8)
    (fun j hj st w hw => chain_xsim W S hS e acc.1 j he hj st w hw.1 hw.2.1
      (by rw [hw.2.2, if_pos hj]))
    ⟨h0, u24, by rw [upc]; rfl⟩
  unfold buildLeaf
  simp only [bind_assoc]
  refine (XSim.steps hst (XSim.bind (k₂ := 7) (c₂ := 94) (n₂ := 1) (b₂ := 11) hchains
    (fun st w hw => ?_))).of_eq rfl (by rfl) (by rfl) (by rfl) (by rfl)
  obtain ⟨hc, _, hpc57⟩ := hw
  have hl42 : st.1.length = 42 := hc.elen
  obtain ⟨x, xst, xpc, x10, x11, x12, xun, xfr⟩ :=
    spec_57 w (by rw [hpc57]; rfl) e he hc.r20 hc.base.r19
  have xm : ∀ A < 2 ^ 64, x.getMem (BitVec.ofNat 64 A) = w.getMem (BitVec.ofNat 64 A) :=
    fun A hA => xfr A hA (by simp)
  have hx : (leafInput 0 0 e st.1).length = 704 := by
    simp [leafInput, thInput, length_flatten16 _ hc.ev.1, hl42]
  have hq : hashInput x = pad64 (leafInput 0 0 e st.1) := by
    refine hashInput_eq_pad64 x 10 832 _ (by rw [x11]) (by norm_num) x10
      (by norm_num) (by norm_num) (by omega) (by omega) ?_
    rw [show 8 * (10 + 1) = 4 + 2 * st.1.length by omega, readWords_add, wordsToNat_append,
      readWords_length, show 832 + 8 * 4 = 864 by norm_num]
    have hv := wordsToNat_vals x 864 st.1 hc.ev.1 (fun i hi => by
      have := hc.ev.2 i hi
      exact ⟨by rw [xm _ (by omega)]; exact this.1, by rw [xm _ (by omega)]; exact this.2⟩)
    rw [hv]
    simp only [MachineState.readWords, ofNat_add8, Nat.reduceAdd, wordsToNat]
    rw [xm 832 (by norm_num), xm 840 (by norm_num), xm 848 (by norm_num), xm 856 (by norm_num),
      hc.base.w832, hc.w840, hc.base.zero 848 (by simp [zeroKeys]),
      hc.base.zero 856 (by simp [zeroKeys])]
    simp only [leafInput, thInput, leNat_append, List.length_append, length_tweak,
      P, leNat_zeros, length_zeros, leNat_tweak0 2 0 _ _ (by norm_num) (by norm_num)]
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.reducePow, Nat.reduceMul,
      Nat.reduceAdd]
    omega
  have hblk : (pad64 (leafInput 0 0 e st.1)).blocks = 11 := by
    simp only [Query.blocks, pad64, padBlocks, hx]
  refine (XSim.steps xst (XSim.hash16_bind (k := 2) (c := 2) (n := 0) (b := 0)
    ((codeAt_61.fetch x xpc).trans rfl)
    (by rw [xun _ (by simp) (by simp) (by simp) (by simp)]; exact hc.base.r5)
    (hashArgs_const x 832 704 (TA + 16 * e) x10 x11 x12 (by norm_num) (by norm_num) (by norm_num)
      (by unfold TA; omega) (by unfold TA; omega)) hq (fun a => ?_))).of_eq rfl (by rfl) (by rw [hblk])
      (by rfl) (by rw [hblk])
  have wpc : (writeHash x a).pc = pcOf 62 := by rw [pc_writeHash, xpc]; rfl
  obtain ⟨y, yst, ypc, y20, yun, yfr⟩ := spec_62 (writeHash x a) wpc e he
    (by rw [getReg_writeHash, xun _ (by simp) (by simp) (by simp) (by simp)]; exact hc.r20)
    (by rw [getReg_writeHash, xun _ (by simp) (by simp) (by simp) (by simp)]; exact hc.r17)
  have hwf := Frame.writeHash x a (TA + 16 * e) x12 (by unfold TA; omega) (by unfold TA; omega)
  have ym : ∀ A < 2 ^ 64, y.getMem (BitVec.ofNat 64 A) = (writeHash x a).getMem (BitVec.ofNat 64 A) :=
    fun A hA => yfr A hA (by simp)
  have yr : ∀ r, r ≠ .x20 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → y.getReg r = w.getReg r :=
    fun r h1 h2 h3 h4 h5 => by rw [yun r h1, getReg_writeHash, xun r h2 h3 h4 h5]
  refine XSim.pure_steps yst ⟨LCtx.mk ?_ ?_ ?_ ?_ y20 (by simp [h.len]) ?_, ?_⟩
  · have fr := (xfr.trans hwf).trans yfr
    refine hc.base.frame (fun r hr => ?_) fr (fun k hk => ?_)
    · rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact yr _ (by simp) (by simp) (by simp) (by simp) (by simp)
    · simp at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simp [BaseSafe, zeroKeys, TA] <;> omega
  · rw [ym _ (by norm_num), getMem_frame hwf (by norm_num) (by simp; unfold TA; omega), xm _ (by norm_num)]
    exact hc.t1
  · rw [ym _ (by norm_num), getMem_frame hwf (by norm_num) (by simp; unfold TA; omega), xm _ (by norm_num)]
    exact hc.t2
  · rw [yr _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact hc.r17
  · have hlv' : Vals y TA acc.1 := (hc.lv.frame (xfr.trans hwf) (by rw [hc.len]; unfold TA; omega)
      (fun k hk => by simp at hk; rw [hc.len]; unfold TA at *; omega)).frame yfr
      (by rw [hc.len]; unfold TA; omega) (by simp)
    refine hlv'.snoc ?_ (length_answer16 a)
    rw [hc.len]
    exact (valAt_writeHash x a (TA + 16 * e) x12 (by unfold TA; omega)).frame yfr
      (by unfold TA; omega) (by simp)
  · rw [ypc]
    by_cases he' : e + 1 = 32
    · rw [if_pos he', if_neg (by omega)]
    · rw [if_neg he', if_pos (by omega)]

end SigGolfCandidate.Keygen
