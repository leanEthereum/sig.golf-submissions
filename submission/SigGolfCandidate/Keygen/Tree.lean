import SigGolfCandidate.Keygen.Chain

/-!
# `keygen`: the tree levels, in the cache region

Level `l` of the top tree (level 0 = the 2048 leaves) is stored right after level `l - 1`:
node `(l, j)` at `REGION + 16 (lvOff l + j)`, `lvOff l = Σ_{i<l} 2^(11-i)` (the region layout
of the cache). The node loop reads the children from the previous level (`s3 + 32 j`) and
writes the node at `s9 + 16 j` (the next free slot). Invariant: the whole list of levels built
so far, flattened, is stored from `REGION` on.
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

/-- Index of the first node of level `k` in the region. -/
def lvOff (k : Nat) : Nat := ((List.range k).map fun i => 2 ^ (11 - i)).sum

theorem lvOff_succ (k : Nat) : lvOff (k + 1) = lvOff k + 2 ^ (11 - k) := by
  simp [lvOff, List.range_succ]

theorem lvOff_le (k : Nat) (hk : k ≤ 12) : lvOff k ≤ 4095 := by
  interval_cases k <;> decide

theorem lvOff_11 : lvOff 11 = 4094 := by decide

theorem lvOff_eq_topN (k : Nat) : lvOff k = topN k := rfl

/-- Shape of the list of levels `0 .. k`. -/
structure Shape (k : Nat) (levels : List (List Val)) : Prop where
  len : levels.length = k + 1
  lens : ∀ i < k + 1, (levels.getD i []).length = 2 ^ (11 - i)
  vals : ∀ L ∈ levels, ∀ v ∈ L, v.length = 16

theorem getD_lt {α : Type} (l : List α) (i : Nat) (d : α) (h : i < l.length) : l.getD i d = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem h]

theorem flatten_take_length (levels : List (List Val)) :
    ∀ k, k ≤ levels.length → (∀ i < k, (levels.getD i []).length = 2 ^ (11 - i)) →
      (levels.take k).flatten.length = lvOff k := by
  intro k
  induction k with
  | zero => intro _ _; simp [lvOff]
  | succ k ih =>
    intro hk hl
    rw [List.take_succ, List.flatten_append, List.length_append, ih (by omega) (fun i hi => hl i (by omega)),
      lvOff_succ, List.getElem?_eq_getElem (by omega)]
    simp only [Option.toList_some, List.flatten_singleton]
    rw [← getD_lt levels k [] (by omega), hl k (by omega)]

theorem flatten_length (k : Nat) (levels : List (List Val)) (hs : Shape k levels) :
    levels.flatten.length = lvOff (k + 1) := by
  have := flatten_take_length levels (k + 1) (by rw [hs.len]) hs.lens
  rwa [List.take_of_length_le (by rw [hs.len])] at this

/-- Node `(l, i)` in the flattened levels. -/
theorem flatten_getD (k : Nat) (levels : List (List Val)) (hs : Shape k levels) (l i : Nat)
    (hl : l ≤ k) (hi : i < 2 ^ (11 - l)) :
    levels.flatten.getD (lvOff l + i) [] = (levels.getD l []).getD i [] := by
  have hlen : l < levels.length := by rw [hs.len]; omega
  have e : levels = levels.take l ++ (levels[l] :: levels.drop (l + 1)) := by
    conv_lhs => rw [← List.take_append_drop l levels]
    rw [List.drop_eq_getElem_cons hlen]
  have ht := flatten_take_length levels l (by omega) (fun j hj => hs.lens j (by omega))
  have hL : levels[l].length = 2 ^ (11 - l) := by
    rw [← getD_lt levels l [] hlen]; exact hs.lens l (by omega)
  conv_lhs => rw [e]
  rw [List.flatten_append, List.flatten_cons, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega), ht, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by omega), getD_lt levels l [] hlen, List.getD_eq_getElem?_getD]

theorem Shape.getD_len {k : Nat} {levels : List (List Val)} (hs : Shape k levels) (l i : Nat)
    (hl : l ≤ k) (hi : i < 2 ^ (11 - l)) : ((levels.getD l []).getD i []).length = 16 := by
  have hlen : l < levels.length := by rw [hs.len]; omega
  have hL := hs.lens l (by omega)
  rw [getD_lt _ _ _ hlen] at hL ⊢
  rw [getD_lt _ _ _ (by omega)]
  exact hs.vals _ (List.getElem_mem hlen) _ (List.getElem_mem _)

theorem Vals.getD_append_left {t : MachineState} {A : Nat} {L M : List Val} (h : Vals t A (L ++ M))
    (i : Nat) (hi : i < L.length) : ValAt t (A + 16 * i) (L.getD i []) := by
  have := h.2 i (by simp; omega)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD] at this

/-- Node-loop context of level `lam = k + 1` (`n = 2^(10-k)` nodes): nodes `0 .. j-1` done. -/
structure NCtx (W : List Word) (k : Nat) (levels : List (List Val)) (j : Nat) (acc : List Val)
    (t : MachineState) : Prop where
  base : Base W t
  r15 : t.getReg .x15 = BitVec.ofNat 64 (k + 1)
  r17 : t.getReg .x17 = BitVec.ofNat 64 (2 ^ (10 - k))
  r16 : t.getReg .x16 = BitVec.ofNat 64 j
  r19 : t.getReg .x19 = BitVec.ofNat 64 (REGION + 16 * lvOff k)
  r25 : t.getReg .x25 = BitVec.ofNat 64 (REGION + 16 * lvOff (k + 1))
  w448 : t.getMem (BitVec.ofNat 64 448) = BitVec.ofNat 64 (769 + 2 ^ 32 * (k + 1))
  w456 : (t.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = 0
  shape : Shape k levels
  alen : acc.length = j
  lv : Vals t REGION (levels.flatten ++ acc)

/-- One node. -/
theorem node_xsim (W : List Word) (k : Nat) (hk : k < 11) (levels : List (List Val)) (j : Nat)
    (hj : j < 2 ^ (10 - k)) (acc : List Val) (t : MachineState) (h : NCtx W k levels j acc t)
    (hpc : t.pc = pcOf 83) :
    XSim image t 18 25 1 1
      (do let v ← Ref.hash16 (nodeInput 0 0 (k + 1) j ((levels.getD k []).getD (2 * j) [])
            ((levels.getD k []).getD (2 * j + 1) []))
          pure (acc ++ [v]))
      (fun acc' u => NCtx W k levels (j + 1) acc' u ∧
        u.pc = if j + 1 < 2 ^ (10 - k) then pcOf 83 else pcOf 101) := by
  have hs := h.shape
  have hfl := flatten_length k levels hs
  have hoff := lvOff_succ k
  have hoff2 := lvOff_succ (k + 1)
  have hle := lvOff_le (k + 1 + 1) (by omega)
  have hn : 2 ^ (11 - k) = 2 * 2 ^ (10 - k) := by
    rw [show 11 - k = (10 - k) + 1 by omega, Nat.pow_succ]; ring
  have hn' : 2 ^ (11 - (k + 1)) = 2 ^ (10 - k) := by rw [show 11 - (k + 1) = 10 - k by omega]
  have hj11 : 2 ^ (10 - k) ≤ 1024 := by
    calc 2 ^ (10 - k) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 1024 := by norm_num
  obtain ⟨u, hst, upc, u10, u11, u12, uun, u456, u480, u488, u496, u504, ufr⟩ :=
    spec_83 t hpc j (REGION + 16 * lvOff k) (REGION + 16 * lvOff (k + 1)) (by omega)
      (by unfold REGION; omega) (by unfold REGION; omega) (by unfold REGION; omega)
      (by unfold REGION; omega) h.r16 h.r19 h.r25 h.w456
  have ux : ∀ r, r ≠ .x1 ∧ r ≠ .x3 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 → u.getReg r = t.getReg r :=
    fun r hr => uun r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2
  have hL := h.lv.getD_append_left (lvOff k + 2 * j) (by rw [hfl]; omega)
  have hR := h.lv.getD_append_left (lvOff k + (2 * j + 1)) (by rw [hfl]; omega)
  rw [flatten_getD k levels hs k (2 * j) le_rfl (by omega)] at hL
  rw [flatten_getD k levels hs k (2 * j + 1) le_rfl (by omega)] at hR
  have hll := hs.getD_len k (2 * j) le_rfl (by omega)
  have hrl := hs.getD_len k (2 * j + 1) le_rfl (by omega)
  have hq : hashInput u = pad64 (nodeInput 0 0 (k + 1) j ((levels.getD k []).getD (2 * j) []) ((levels.getD k []).getD (2 * j + 1) [])) := by
    refine hashInput_eq_pad64 u 0 448 _ (by rw [u11]) (by norm_num) u10
      (by norm_num) (by norm_num)
      (by simp only [nodeInput, thInput, List.length_append, length_tweak, length_P, hll, hrl]; norm_num)
      (by simp only [nodeInput, thInput, List.length_append, length_tweak, length_P, hll, hrl]; norm_num) ?_
    rw [readWords8]
    simp only [Nat.reduceAdd, wordsToNat]
    rw [getMem_frame (A := 448) ufr (by norm_num) (by simp),
      getMem_frame (A := 464) ufr (by norm_num) (by simp),
      getMem_frame (A := 472) ufr (by norm_num) (by simp), u456, u480, u488, u496, u504, h.w448,
      h.base.zero 464 (by simp [zeroKeys]), h.base.zero 472 (by simp [zeroKeys])]
    obtain ⟨hl1, hl2⟩ := hL
    obtain ⟨hr1, hr2⟩ := hR
    rw [show REGION + 16 * lvOff k + 32 * j = REGION + 16 * (lvOff k + 2 * j) by ring, hl1,
      show REGION + 16 * (lvOff k + 2 * j) + 8 = REGION + 16 * (lvOff k + 2 * j) + 8 from rfl, hl2,
      show REGION + 16 * (lvOff k + 2 * j) + 16 = REGION + 16 * (lvOff k + (2 * j + 1)) by ring, hr1,
      show REGION + 16 * (lvOff k + 2 * j) + 24 = REGION + 16 * (lvOff k + (2 * j + 1)) + 8 by ring, hr2]
    simp only [nodeInput, thInput, leNat_append, List.length_append, length_tweak,
      P, leNat_zeros, length_zeros, leNat_tweak0 3 0 _ _ (by norm_num) (by norm_num), hll,
      leNat_val _ hll, leNat_val _ hrl]
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.reducePow, Nat.reduceMul,
      Nat.reduceAdd]
    rw [Nat.mod_eq_of_lt (a := 769 + 4294967296 * (k + 1)) (by omega),
      Nat.mod_eq_of_lt (a := 4294967296 * j) (by omega), Nat.mod_eq_of_lt (a := k + 1) (by omega),
      Nat.mod_eq_of_lt (a := j) (by omega)]
    ring
  have hblk : (pad64 (nodeInput 0 0 (k + 1) j ((levels.getD k []).getD (2 * j) []) ((levels.getD k []).getD (2 * j + 1) []))).blocks = 1 := by
    simp only [Query.blocks, pad64, padBlocks, nodeInput, thInput, List.length_append, length_tweak,
      length_P, hll, hrl]
  have D16 : REGION + 16 * lvOff (k + 1) + 16 * j + 32 < 0x144C0 + 8 := by unfold REGION; omega
  refine (XSim.steps hst (XSim.hash16_bind
    (x := nodeInput 0 0 (k + 1) j ((levels.getD k []).getD (2 * j) []) ((levels.getD k []).getD (2 * j + 1) []))
    (k := 2) (c := 2) (n := 0) (b := 0)
    (f := fun v => pure (acc ++ [v]))
    ((codeAt_98.fetch u upc).trans rfl) (by rw [ux _ (by simp)]; exact h.base.r5)
    (hashArgs_const u 448 64 (REGION + 16 * lvOff (k + 1) + 16 * j) u10 u11 u12 (by norm_num)
      (by norm_num) (by norm_num) (by unfold REGION; omega) (by unfold REGION; omega))
    (hq.trans (fmt_thInput 3 0 0 _ _ _ (by decide)).symm) (fun a => ?_))).of_eq rfl (by rfl)
      (by rw [hblk]) (by rfl) (by rw [hblk])
  have wpc : (writeHash u a).pc = pcOf 99 := by rw [pc_writeHash, upc]; rfl
  obtain ⟨v, vst, vpc, v16, vun, vfr⟩ := spec_99 (writeHash u a) wpc j (2 ^ (10 - k)) (by omega)
    (by omega) (by rw [getReg_writeHash, ux _ (by simp), h.r16])
    (by rw [getReg_writeHash, ux _ (by simp), h.r17])
  have hwf := Frame.writeHash u a (REGION + 16 * lvOff (k + 1) + 16 * j) u12
    (by unfold REGION; omega) (by unfold REGION; omega)
  have fr := (ufr.trans hwf).trans vfr
  have vr : ∀ r, r ≠ .x16 → r ≠ .x1 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 →
      v.getReg r = t.getReg r :=
    fun r h1 h2 h3 h4 h5 h6 => by rw [vun r h1, getReg_writeHash, ux r ⟨h2, h3, h4, h5, h6⟩]
  have vm : ∀ A < 2 ^ 64, v.getMem (BitVec.ofNat 64 A) = (writeHash u a).getMem (BitVec.ofNat 64 A) :=
    fun A hA => vfr A hA (by simp)
  refine XSim.pure_steps vst ⟨NCtx.mk ?_ ?_ ?_ v16 ?_ ?_ ?_ ?_ hs (by simp [h.alen]) ?_, ?_⟩
  · refine h.base.frame (fun r hr => ?_) fr (fun k' hk' => ?_)
    · rcases hr with rfl | rfl | rfl | rfl <;> exact vr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · simp at hk'
      rcases hk' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [BaseSafe, zeroKeys, REGION] <;> omega
  · rw [vr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r15
  · rw [vr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r17
  · rw [vr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r19
  · rw [vr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r25
  · rw [vm _ (by norm_num), getMem_frame hwf (by norm_num) (by simp; unfold REGION; omega),
      getMem_frame (A := 448) ufr (by norm_num) (by simp)]
    exact h.w448
  · rw [vm _ (by norm_num), getMem_frame hwf (by norm_num) (by simp; unfold REGION; omega), u456,
      BitVec.toNat_ofNat]
    omega
  · have hav : Vals v REGION (levels.flatten ++ acc) := h.lv.frame fr
      (by simp [h.alen, hfl]; unfold REGION; omega)
      (fun k' hk' => by simp at hk'; simp only [List.length_append, h.alen, hfl]; unfold REGION at *; omega)
    rw [← List.append_assoc]
    refine hav.snoc ?_ (length_answer16 a)
    rw [List.length_append, h.alen, hfl, show REGION + 16 * (lvOff (k + 1) + j) =
      REGION + 16 * lvOff (k + 1) + 16 * j by ring]
    exact (valAt_writeHash u a _ u12 (by unfold REGION; omega)).frame vfr
      (by unfold REGION; omega) (by simp)
  · rw [vpc]
    by_cases hjn : j + 1 = 2 ^ (10 - k)
    · rw [if_pos hjn, if_neg (by omega)]
    · rw [if_neg hjn, if_pos (by omega)]

/-- Level-loop context: levels `0 .. k` built and stored. -/
structure VCtx (W : List Word) (k : Nat) (levels : List (List Val)) (t : MachineState) : Prop where
  base : Base W t
  r15 : t.getReg .x15 = BitVec.ofNat 64 (k + 1)
  r17 : t.getReg .x17 = BitVec.ofNat 64 (2 ^ (11 - k))
  r19 : t.getReg .x19 = BitVec.ofNat 64 (REGION + 16 * lvOff k)
  shape : Shape k levels
  lv : Vals t REGION levels.flatten

/-- One tree level `lam = k + 1`. -/
theorem level_xsim (W : List Word) (k : Nat) (hk : k < 11) (levels : List (List Val))
    (t : MachineState) (h : VCtx W k levels t) (hpc : t.pc = pcOf 73) :
    XSim image t (13 + 2 ^ (10 - k) * 18) (13 + 2 ^ (10 - k) * 25) (2 ^ (10 - k)) (2 ^ (10 - k))
      (do let level ← buildLevel (nodeInput 0 0) (1 + k) (levels.getD (1 + k - 1) [])
          pure (levels ++ [level]))
      (fun levels' u => VCtx W (k + 1) levels' u ∧ u.pc = if k + 1 < 11 then pcOf 73 else pcOf 104) := by
  have hs := h.shape
  have hn : 2 ^ (11 - k) = 2 * 2 ^ (10 - k) := by
    rw [show 11 - k = (10 - k) + 1 by omega, Nat.pow_succ]; ring
  have hj11 : 2 ^ (10 - k) ≤ 1024 := by
    calc 2 ^ (10 - k) ≤ 2 ^ 10 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 1024 := by norm_num
  have hn1 : 1 ≤ 2 ^ (10 - k) := Nat.one_le_two_pow
  have hle := lvOff_le (k + 1) (by omega)
  have hle0 := lvOff_le k (by omega)
  obtain ⟨u, hst, upc, u17, u16, u25, uun, u448, u456, ufr⟩ :=
    spec_73 t hpc (k + 1) (2 ^ (11 - k)) (REGION + 16 * lvOff k) (by omega) (by omega)
      (by unfold REGION; omega) h.r15 h.base.r8 h.base.r30 h.r17 h.r19
  have h0 : NCtx W k levels 0 [] u := by
    refine NCtx.mk ?_ ?_ ?_ u16 ?_ ?_ u448 u456 hs rfl ?_
    · refine h.base.frame (fun r hr => uun r ?_ ?_ ?_ ?_ ?_) ufr (fun k hk => ?_) <;>
        try (rcases hr with h | h | h | h <;> simp [h])
      simp at hk; rcases hk with rfl | rfl <;> simp [BaseSafe, zeroKeys]
    · rw [uun _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r15
    · rw [u17, hn]; congr 1; omega
    · rw [uun _ (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r19
    · rw [u25, lvOff_succ]; congr 1; ring
    · have hfl := flatten_length k levels hs
      rw [List.append_nil]
      exact h.lv.frame ufr (by rw [hfl]; unfold REGION; omega)
        (fun k' hk' => by simp at hk'; unfold REGION; omega)
  have hlen : (levels.getD k []).length / 2 = 2 ^ (10 - k) := by
    rw [hs.lens k (by omega), hn]; omega
  have hloop := XSim.foldlM_range (image := image) (2 ^ (10 - k))
    (fun (acc : List Val) j => do
      let v ← Ref.hash16 (nodeInput 0 0 (1 + k) j ((levels.getD k []).getD (2 * j) [])
        ((levels.getD k []).getD (2 * j + 1) []))
      pure (acc ++ [v]))
    []
    (fun j acc w => NCtx W k levels j acc w ∧
      w.pc = if j < 2 ^ (10 - k) then pcOf 83 else pcOf 101)
    (fun _ => 18) (fun _ => 25) (fun _ => 1) (fun _ => 1)
    (fun j hj acc w hw => by
      rw [Nat.add_comm 1 k]
      exact node_xsim W k hk levels j hj acc w hw.1 (by rw [hw.2, if_pos hj]))
    ⟨h0, by rw [upc, if_pos (by omega)]⟩
  unfold buildLevel
  rw [show 1 + k - 1 = k by omega, hlen]
  refine (XSim.steps hst (XSim.bind (k₂ := 3) (c₂ := 3) (n₂ := 0) (b₂ := 0) hloop
    (fun acc w hw => ?_))).of_eq rfl
    (by simp only [sumTo_const] <;> ring) (by simp only [sumTo_const] <;> ring)
    (by simp only [sumTo_const] <;> ring) (by simp only [sumTo_const] <;> ring)
  obtain ⟨hc, hpc90⟩ := hw
  obtain ⟨x, xst, xpc, x15, x19, xun, xfr⟩ := spec_101 w (by rw [hpc90, if_neg (by omega)]) (k + 1)
    (by omega) hc.r15 hc.base.r9
  have hfl := flatten_length k levels hs
  refine XSim.pure_steps xst ⟨VCtx.mk ?_ x15 ?_ ?_ ?_ ?_, ?_⟩
  · exact hc.base.frame (fun r hr => xun r (by rcases hr with h | h | h | h <;> simp [h])
      (by rcases hr with h | h | h | h <;> simp [h])) xfr (by simp)
  · rw [xun _ (by simp) (by simp), hc.r17]; congr 2; omega
  · rw [x19, hc.r25]
  · refine ⟨by simp [hs.len], fun i hi => ?_, fun L hL v hv => ?_⟩
    · by_cases hik : i < k + 1
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hs.len]; omega),
          ← List.getD_eq_getElem?_getD]
        exact hs.lens i hik
      · rw [show i = k + 1 by omega, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (by rw [hs.len]), hs.len, Nat.sub_self]
        simp [hc.alen]
    · rcases List.mem_append.mp hL with hL | hL
      · exact hs.vals L hL v hv
      · simp at hL; subst hL
        have := hc.lv.1 v (List.mem_append_right _ hv)
        exact this
  · rw [List.flatten_append, List.flatten_singleton]
    exact ⟨hc.lv.1, fun i hi => (hc.lv.2 i hi).frame xfr (by
      simp [hc.alen, hfl] at hi; unfold REGION; omega) (by simp)⟩
  · rw [xpc]
    by_cases hk' : k + 1 + 1 ≤ 11
    · rw [if_pos hk', if_pos (by omega)]
    · rw [if_neg hk', if_neg (by omega)]

end SigGolfCandidate.Keygen
