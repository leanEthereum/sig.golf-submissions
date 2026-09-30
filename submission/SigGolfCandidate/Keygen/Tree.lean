import SigGolfCandidate.Keygen.Chain

/-!
# `keygen`: the tree levels (in place in the tree array)
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

/-- Node-loop context of level `lam = k + 1` (`n` nodes): nodes `0 .. j-1` done, inputs
`L[2j ..]` still in place. -/
structure NCtx (W : List Word) (k n : Nat) (L : List Val) (j : Nat) (acc : List Val)
    (t : MachineState) : Prop where
  base : Base W t
  r15 : t.getReg .x15 = BitVec.ofNat 64 (k + 1)
  r17 : t.getReg .x17 = BitVec.ofNat 64 n
  r16 : t.getReg .x16 = BitVec.ofNat 64 j
  w448 : t.getMem (BitVec.ofNat 64 448) = BitVec.ofNat 64 (769 + 2 ^ 32 * (k + 1))
  w456 : (t.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = 0
  alen : acc.length = j
  av : Vals t TA acc
  llen : L.length = 2 * n
  l16 : ∀ v ∈ L, v.length = 16
  lv : ∀ i, 2 * j ≤ i → i < 2 * n → ValAt t (TA + 16 * i) (L.getD i [])

theorem getD_len {L : List Val} (h : ∀ v ∈ L, v.length = 16) (i : Nat) (hi : i < L.length) :
    (L.getD i []).length = 16 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact h _ (List.getElem_mem hi)

/-- One node. -/
theorem node_xsim (W : List Word) (k n : Nat) (hk : k < 5) (hn : n ≤ 16) (L : List Val) (j : Nat)
    (hj : j < n) (acc : List Val) (t : MachineState) (h : NCtx W k n L j acc t)
    (hpc : t.pc = pcOf 73) :
    XSim image t 18 25 1 1
      (do let v ← Ref.hash16 (nodeInput 0 0 (k + 1) j (L.getD (2 * j) []) (L.getD (2 * j + 1) []))
          pure (acc ++ [v]))
      (fun acc' u => NCtx W k n L (j + 1) acc' u ∧ u.pc = if j + 1 < n then pcOf 73 else pcOf 91) := by
  obtain ⟨u, hst, upc, u10, u11, u12, uun, u456, u480, u488, u496, u504, ufr⟩ :=
    spec_73 t hpc j (by omega) h.r16 h.base.r19 h.w456
  have ux : ∀ r, r ≠ .x1 ∧ r ≠ .x3 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 → u.getReg r = t.getReg r :=
    fun r hr => uun r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2
  have hl := h.lv (2 * j) (by omega) (by omega)
  have hr := h.lv (2 * j + 1) (by omega) (by omega)
  have hll := getD_len h.l16 (2 * j) (by rw [h.llen]; omega)
  have hrl := getD_len h.l16 (2 * j + 1) (by rw [h.llen]; omega)
  have hq : hashInput u = pad64 (nodeInput 0 0 (k + 1) j (L.getD (2 * j) []) (L.getD (2 * j + 1) [])) := by
    have hx : (nodeInput 0 0 (k + 1) j (L.getD (2 * j) []) (L.getD (2 * j + 1) [])).length = 64 := by
      simp only [nodeInput, thInput, List.length_append, length_tweak, length_P, hll, hrl]
    refine hashInput_eq_pad64 u 0 448 _ (by rw [u11]) (by norm_num) u10
      (by norm_num) (by norm_num) (by omega) (by omega) ?_
    rw [readWords8]
    simp only [Nat.reduceAdd, wordsToNat]
    rw [getMem_frame (A := 448) ufr (by norm_num) (by simp),
      getMem_frame (A := 464) ufr (by norm_num) (by simp),
      getMem_frame (A := 472) ufr (by norm_num) (by simp), u456, u480, u488, u496, u504, h.w448,
      h.base.zero 464 (by simp [zeroKeys]), h.base.zero 472 (by simp [zeroKeys])]
    obtain ⟨hl1, hl2⟩ := hl
    obtain ⟨hr1, hr2⟩ := hr
    simp only [TA] at hl1 hl2 hr1 hr2
    rw [show 213248 + 32 * j = 213248 + 16 * (2 * j) by ring, hl1,
      show 213248 + 16 * (2 * j) + 8 = 213248 + 16 * (2 * j) + 8 from rfl, hl2,
      show 213248 + 16 * (2 * j) + 16 = 213248 + 16 * (2 * j + 1) by ring, hr1,
      show 213248 + 16 * (2 * j) + 24 = 213248 + 16 * (2 * j + 1) + 8 by ring, hr2]
    simp only [nodeInput, thInput, leNat_append, List.length_append, length_tweak,
      P, leNat_zeros, length_zeros, leNat_tweak0 3 0 _ _ (by norm_num) (by norm_num), hll,
      leNat_val _ hll, leNat_val _ hrl]
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.reducePow, Nat.reduceMul,
      Nat.reduceAdd]
    rw [Nat.mod_eq_of_lt (a := 769 + 4294967296 * (k + 1)) (by omega),
      Nat.mod_eq_of_lt (a := 4294967296 * j) (by omega), Nat.mod_eq_of_lt (a := k + 1) (by omega),
      Nat.mod_eq_of_lt (a := j) (by omega)]
    ring
  have hblk : (pad64 (nodeInput 0 0 (k + 1) j (L.getD (2 * j) []) (L.getD (2 * j + 1) []))).blocks = 1 := by
    simp only [Query.blocks, pad64, padBlocks, nodeInput, thInput, List.length_append, length_tweak,
      length_P, hll, hrl]
  refine (XSim.steps hst (XSim.hash16_bind (k := 2) (c := 2) (n := 0) (b := 0)
    (f := fun v => pure (acc ++ [v]))
    ((codeAt_88.fetch u upc).trans rfl) (by rw [ux _ (by simp)]; exact h.base.r5)
    (hashArgs_const u 448 64 (TA + 16 * j) u10 u11 u12 (by norm_num) (by norm_num) (by norm_num)
      (by unfold TA; omega) (by unfold TA; omega)) hq (fun a => ?_))).of_eq rfl (by rfl) (by rw [hblk])
      (by rfl) (by rw [hblk])
  have wpc : (writeHash u a).pc = pcOf 89 := by rw [pc_writeHash, upc]; rfl
  obtain ⟨v, vst, vpc, v16, vun, vfr⟩ := spec_89 (writeHash u a) wpc j n (by omega) (by omega)
    (by rw [getReg_writeHash, ux _ (by simp), h.r16]) (by rw [getReg_writeHash, ux _ (by simp), h.r17])
  have hwf := Frame.writeHash u a (TA + 16 * j) u12 (by unfold TA; omega) (by unfold TA; omega)
  have fr := (ufr.trans hwf).trans vfr
  have vr : ∀ r, r ≠ .x16 → r ≠ .x1 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 →
      v.getReg r = t.getReg r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [vun r h1, getReg_writeHash, ux r ⟨h2, h3, h4, h5, h6⟩]
  have vm : ∀ A < 2 ^ 64, v.getMem (BitVec.ofNat 64 A) = (writeHash u a).getMem (BitVec.ofNat 64 A) :=
    fun A hA => vfr A hA (by simp)
  refine XSim.pure_steps vst ⟨NCtx.mk ?_ ?_ ?_ v16 ?_ ?_ (by simp [h.alen]) ?_ h.llen h.l16 ?_, ?_⟩
  · refine h.base.frame (fun r hr => ?_) fr (fun k hk => ?_)
    · rcases hr with rfl | rfl | rfl | rfl | rfl <;> exact vr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · simp at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [BaseSafe, zeroKeys, TA] <;> omega
  · rw [vr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r15
  · rw [vr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r17
  · rw [vm _ (by norm_num), getMem_frame hwf (by norm_num) (by simp; unfold TA; omega),
      getMem_frame (A := 448) ufr (by norm_num) (by simp)]
    exact h.w448
  · rw [vm _ (by norm_num), getMem_frame hwf (by norm_num) (by simp; unfold TA; omega), u456,
      BitVec.toNat_ofNat]
    omega
  · have hav : Vals v TA acc := h.av.frame fr (by rw [h.alen]; unfold TA; omega)
      (fun k hk => by simp at hk; rw [h.alen]; unfold TA at *; omega)
    refine hav.snoc ?_ (length_answer16 a)
    rw [h.alen]
    exact (valAt_writeHash u a (TA + 16 * j) u12 (by unfold TA; omega)).frame vfr
      (by unfold TA; omega) (by simp)
  · intro i hi1 hi2
    exact (h.lv i (by omega) hi2).frame fr (by unfold TA; omega)
      (fun k hk => by simp at hk; unfold TA at *; omega)
  · rw [vpc]
    by_cases hjn : j + 1 = n
    · rw [if_pos hjn, if_neg (by omega)]
    · rw [if_neg hjn, if_pos (by omega)]

/-- Level-loop context: `k` levels built, the current level `lvl` (`2^(5-k)` nodes) in the array. -/
structure VCtx (W : List Word) (k : Nat) (lvl : List Val) (t : MachineState) : Prop where
  base : Base W t
  r15 : t.getReg .x15 = BitVec.ofNat 64 (k + 1)
  r17 : t.getReg .x17 = BitVec.ofNat 64 (2 ^ (5 - k))
  len : lvl.length = 2 ^ (5 - k)
  lv : Vals t TA lvl

/-- One tree level `lam = k + 1`. -/
theorem level_xsim (W : List Word) (k : Nat) (hk : k < 5) (st : List Val × List Val)
    (t : MachineState) (h : VCtx W k st.1 t) (hpc : t.pc = pcOf 65) :
    XSim image t (10 + 2 ^ (4 - k) * 18) (10 + 2 ^ (4 - k) * 25) (2 ^ (4 - k)) (2 ^ (4 - k))
      (levelStep (nodeInput 0 0) 0 st (1 + k))
      (fun st' u => VCtx W (k + 1) st'.1 u ∧ u.pc = if k + 1 < 5 then pcOf 65 else pcOf 93) := by
  have hn : 2 ^ (5 - k) = 2 * 2 ^ (4 - k) := by
    rw [show 5 - k = (4 - k) + 1 by omega, Nat.pow_succ]; ring
  have hn16 : 2 ^ (4 - k) ≤ 16 := by
    calc 2 ^ (4 - k) ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 16 := by norm_num
  have hn1 : 1 ≤ 2 ^ (4 - k) := Nat.one_le_two_pow
  obtain ⟨u, hst, upc, u17, u16, uun, u448, u456, ufr⟩ :=
    spec_65 t hpc (k + 1) (2 ^ (5 - k)) (by omega) (by omega) h.r15 h.base.r8 h.base.r30 h.r17
  have h0 : NCtx W k (2 ^ (4 - k)) st.1 0 [] u := by
    refine NCtx.mk ?_ ?_ ?_ u16 u448 u456 rfl (Vals.nil u TA) (by rw [h.len, hn]) h.lv.1 ?_
    · refine h.base.frame (fun r hr => uun r ?_ ?_ ?_ ?_) ufr (fun k hk => ?_) <;>
        try (rcases hr with h | h | h | h | h <;> simp [h])
      simp at hk; rcases hk with rfl | rfl <;> simp [BaseSafe, zeroKeys]
    · rw [uun _ (by simp) (by simp) (by simp) (by simp)]; exact h.r15
    · rw [u17, hn]; congr 1; omega
    · intro i _ hi2
      have := h.lv.2 i (by rw [h.len, hn]; exact hi2)
      exact this.frame ufr (by unfold TA; omega) (fun k hk => by simp at hk; unfold TA; omega)
  have hloop := XSim.foldlM_range (image := image) (2 ^ (4 - k))
    (fun (acc : List Val) j => do
      let v ← Ref.hash16 (nodeInput 0 0 (1 + k) j (st.1.getD (2 * j) []) (st.1.getD (2 * j + 1) []))
      pure (acc ++ [v]))
    []
    (fun j acc w => NCtx W k (2 ^ (4 - k)) st.1 j acc w ∧
      w.pc = if j < 2 ^ (4 - k) then pcOf 73 else pcOf 91)
    (fun _ => 18) (fun _ => 25) (fun _ => 1) (fun _ => 1)
    (fun j hj acc w hw => by
      rw [Nat.add_comm 1 k]
      exact node_xsim W k (2 ^ (4 - k)) hk hn16 st.1 j hj acc w hw.1 (by rw [hw.2, if_pos hj]))
    ⟨h0, by rw [upc, if_pos (by omega)]⟩
  have hlen : st.1.length / 2 = 2 ^ (4 - k) := by rw [h.len, hn]; omega
  unfold levelStep buildLevel
  simp only []
  rw [hlen]
  refine (XSim.steps hst (XSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0) hloop
    (fun acc w hw => ?_))).of_eq rfl
    (by simp only [sumTo_const] <;> ring) (by simp only [sumTo_const] <;> ring)
    (by simp only [sumTo_const] <;> ring) (by simp only [sumTo_const] <;> ring)
  obtain ⟨hc, hpc91⟩ := hw
  obtain ⟨x, xst, xpc, x15, xun, xfr⟩ := spec_91 w (by rw [hpc91, if_neg (by omega)]) (k + 1)
    (by omega) hc.r15 hc.base.r9
  refine XSim.pure_steps xst ⟨VCtx.mk ?_ x15 ?_ ?_ ?_, ?_⟩
  · exact hc.base.frame (fun r hr => xun r (by rcases hr with h | h | h | h | h <;> simp [h])) xfr
      (by simp)
  · rw [xun _ (by simp), hc.r17]; congr 2; omega
  · rw [hc.alen]; congr 1; omega
  · have := hc.av
    exact ⟨this.1, fun i hi => (this.2 i hi).frame xfr (by rw [hc.alen] at hi; unfold TA; omega) (by simp)⟩
  · rw [xpc]
    by_cases hk' : k + 1 + 1 ≤ 5
    · rw [if_pos hk', if_pos (by omega)]
    · rw [if_neg hk', if_neg (by omega)]

end SigGolfCandidate.Keygen
