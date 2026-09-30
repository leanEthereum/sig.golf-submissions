import SigGolfCandidate.Keygen.Tree

/-!
# `keygen`: masking the region in place

After the tree, the region holds levels `0 .. 10` of the top tree (`levels.flatten`, first 4094
nodes). The mask loop walks the region in order: node `(l, j)` (index `lvOff l + j`) is replaced by
`X_{l,j} xor mask(l, j)`, `mask(l, j) = Th(tw(13, 0, 0, l, j), S)` (answer at `EO = 320`).
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

/-! ## Bytewise XOR of 16-byte values -/

theorem xor_byte_add (x y A B : Nat) (hx : x < 256) (hy : y < 256) :
    (x + 256 * A) ^^^ (y + 256 * B) = (x ^^^ y) + 256 * (A ^^^ B) := by
  have hxy : x ^^^ y < 2 ^ 8 := Nat.xor_lt_two_pow (by omega) (by omega)
  rw [show x + 256 * A = 2 ^ 8 * A + x by ring, show y + 256 * B = 2 ^ 8 * B + y by ring,
    show (x ^^^ y) + 256 * (A ^^^ B) = 2 ^ 8 * (A ^^^ B) + (x ^^^ y) by ring]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ (by omega : x < 2 ^ 8),
    Nat.testBit_two_pow_mul_add _ (by omega : y < 2 ^ 8), Nat.testBit_two_pow_mul_add _ hxy]
  split <;> simp [Nat.testBit_xor]

theorem leNat_xorBytes : ∀ (a b : List Byte), a.length = b.length →
    leNat (xorBytes a b) = leNat a ^^^ leNat b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: as, y :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := leNat_xorBytes as bs h
    simp only [xorBytes, List.zipWith_cons_cons, leNat] at ih ⊢
    rw [ih, BitVec.toNat_xor, xor_byte_add _ _ _ _ x.isLt y.isLt]

theorem length_xorBytes (a b : Val) (ha : a.length = 16) (hb : b.length = 16) :
    (xorBytes a b).length = 16 := by
  simp [xorBytes, ha, hb]

theorem lo_xor (a b : Val) (h : a.length = b.length) : lo (xorBytes a b) = lo a ^^^ lo b := by
  simp only [lo]; rw [leNat_xorBytes a b h, BitVec.ofNat_xor]

theorem hi_xor (a b : Val) (h : a.length = b.length) : hi (xorBytes a b) = hi a ^^^ hi b := by
  simp only [hi]; rw [leNat_xorBytes a b h, Nat.xor_div_two_pow, BitVec.ofNat_xor]

/-! ## Updating one value of an array -/

theorem Vals.update {s t : MachineState} {A : Nat} {L R : List Val} {x y : Val}
    (h : Vals s A (L ++ x :: R)) {keys : List Nat} (hf : Frame s t keys)
    (hk : ∀ k ∈ keys, k = A + 16 * L.length ∨ k = A + 16 * L.length + 8 ∨ k + 8 ≤ A ∨
      A + 16 * (L.length + 1 + R.length) ≤ k)
    (hA : A + 16 * (L.length + 1 + R.length) < 2 ^ 64)
    (hy : ValAt t (A + 16 * L.length) y) (hyl : y.length = 16) : Vals t A (L ++ y :: R) := by
  refine ⟨fun v hv => ?_, fun i hi => ?_⟩
  · rcases List.mem_append.mp hv with hv | hv
    · exact h.1 v (List.mem_append_left _ hv)
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact hyl
      · exact h.1 v (List.mem_append_right _ (List.mem_cons_of_mem _ hv))
  · simp only [List.length_append, List.length_cons] at hi
    by_cases hiL : i = L.length
    · subst hiL
      simpa [List.getD_eq_getElem?_getD] using hy
    · have := h.2 i (by simp; omega)
      have e : (L ++ y :: R).getD i [] = (L ++ x :: R).getD i [] := by
        simp only [List.getD_eq_getElem?_getD]
        by_cases hlt : i < L.length
        · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
        · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
          rw [show i - L.length = (i - L.length - 1) + 1 by omega]
          rfl
      rw [e]
      exact this.frame hf (by omega) (fun k hk' => by
        rcases hk k hk' with h1 | h1 | h1 | h1
        · by_cases hlt : i < L.length
          · right; omega
          · left; omega
        · by_cases hlt : i < L.length
          · right; omega
          · left; omega
        · left; omega
        · right; omega)

/-! ## Contexts -/

/-- Facts kept after the root copy: the public key at `160`, the zeroed 32 bytes after the region. -/
structure Out (root : Val) (t : MachineState) : Prop where
  pk : ValAt t 160 root
  z : ∀ A ∈ [0x144A0, 0x144A8, 0x144B0, 0x144B8], t.getMem (BitVec.ofNat 64 A) = 0

theorem Out.frame {root : Val} {s t : MachineState} {keys : List Nat} (h : Out root s)
    (hf : Frame s t keys)
    (hk : ∀ k ∈ keys, (k + 8 ≤ 160 ∨ 176 ≤ k) ∧ (k + 8 ≤ 0x144A0 ∨ 0x144C0 ≤ k) ∧ k < 2 ^ 64) :
    Out root t := by
  refine ⟨h.pk.frame hf (by norm_num) (fun k hk' => by have := hk k hk'; omega), fun A hA => ?_⟩
  rw [getMem_frame hf (by simp at hA; omega) (fun k hk' heq => by
    have := hk k hk'; subst heq; simp at hA; omega)]
  exact h.z A hA

/-- The region before masking: the first 4094 tree nodes. -/
abbrev nodes (levels : List (List Val)) : List Val := levels.flatten.take 4094

/-- Mask-loop context of level `l` (outer loop): levels `0 .. l-1` masked. -/
structure OCtx (W : List Word) (levels : List (List Val)) (root : Val) (l : Nat) (macc : List Val)
    (t : MachineState) : Prop where
  base : Base W t
  r15 : t.getReg .x15 = BitVec.ofNat 64 l
  r20 : t.getReg .x20 = BitVec.ofNat 64 (REGION + 16 * lvOff l)
  shape : Shape 11 levels
  mlen : macc.length = lvOff l
  lv : Vals t REGION (macc ++ (nodes levels).drop (lvOff l))
  out : Out root t

/-- Inner mask loop: node `j` of level `l`. -/
structure ICtx (W : List Word) (levels : List (List Val)) (root : Val) (l j : Nat) (macc inner : List Val)
    (t : MachineState) : Prop where
  base : Base W t
  r15 : t.getReg .x15 = BitVec.ofNat 64 l
  r16 : t.getReg .x16 = BitVec.ofNat 64 j
  r17 : t.getReg .x17 = BitVec.ofNat 64 (2 ^ (11 - l))
  r20 : t.getReg .x20 = BitVec.ofNat 64 (REGION + 16 * (lvOff l + j))
  shape : Shape 11 levels
  mlen : macc.length = lvOff l
  ilen : inner.length = j
  lv : Vals t REGION (macc ++ inner ++ (nodes levels).drop (lvOff l + j))
  out : Out root t

theorem nodes_length (levels : List (List Val)) (hs : Shape 11 levels) : (nodes levels).length = 4094 := by
  have := flatten_length 11 levels hs
  simp only [nodes, List.length_take, this]
  decide

theorem lvOff_add_lt (l j : Nat) (hl : l < 11) (hj : j < 2 ^ (11 - l)) : lvOff l + j < 4094 := by
  have h1 := lvOff_succ l
  have h2 : lvOff (l + 1) ≤ 4094 := by interval_cases l <;> decide
  omega

theorem nodes_getD (levels : List (List Val)) (hs : Shape 11 levels) (l j : Nat) (hl : l < 11)
    (hj : j < 2 ^ (11 - l)) : (nodes levels).getD (lvOff l + j) [] = (levels.getD l []).getD j [] := by
  have hlt := lvOff_add_lt l j hl hj
  rw [nodes, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hlt, ← List.getD_eq_getElem?_getD,
    flatten_getD 11 levels hs l j (by omega) hj]

/-- One mask step: `mask(l, j)`, node `(l, j)` ^= mask. -/
theorem mask_node_xsim (W : List Word) (S : List Byte) (hS : SkOk W S) (levels : List (List Val))
    (root : Val) (l j : Nat) (hl : l < 11) (hj : j < 2 ^ (11 - l)) (macc inner : List Val)
    (t : MachineState) (h : ICtx W levels root l j macc inner t) (hpc : t.pc = pcOf 123) :
    XSim image t 21 28 1 1
      (do let mk ← Ref.hash16 (maskInput S l j)
          pure (inner ++ [xorBytes ((levels.getD l []).getD j []) mk]))
      (fun inner' u => ICtx W levels root l (j + 1) macc inner' u ∧
        u.pc = if j + 1 < 2 ^ (11 - l) then pcOf 123 else pcOf 144) := by
  have hs := h.shape
  have hlt := lvOff_add_lt l j hl hj
  have hj11 : 2 ^ (11 - l) ≤ 2048 := by
    calc 2 ^ (11 - l) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2048 := by norm_num
  obtain ⟨u, hst, upc, u10, u11, u12, uun, u1696, u1704, ufr⟩ :=
    spec_123 t hpc l j hl (by omega) h.r15 h.r16
  have ux : ∀ r, r ≠ .x3 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 → u.getReg r = t.getReg r :=
    fun r hr => uun r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  have hq : hashInput u = pad64 (maskInput S l j) := by
    have hx : (maskInput S l j).length = 64 := by simp [maskInput, thInput, hS.1]
    refine hashInput_eq_pad64 u 0 1696 _ (by rw [u11]) (by norm_num) u10
      (by norm_num) (by norm_num) (by omega) (by omega) ?_
    rw [readWords8, u1696]
    simp only [wordsToNat]
    have g : ∀ A ∈ [1712, 1720, 1728, 1736, 1744, 1752],
        u.getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
      intro A hA; simp at hA
      exact getMem_frame ufr (by omega) (by simp; omega)
    simp only [Nat.reduceAdd]
    rw [u1704, g 1712 (by simp), g 1720 (by simp), g 1728 (by simp), g 1736 (by simp),
      g 1744 (by simp), g 1752 (by simp), h.base.zero 1712 (by simp [zeroKeys]),
      h.base.zero 1720 (by simp [zeroKeys]), h.base.sk 0 (by norm_num), h.base.sk 1 (by norm_num),
      h.base.sk 2 (by norm_num), h.base.sk 3 (by norm_num)]
    have hW := hS.2
    simp only [maskInput, thInput, leNat_append, List.length_append, length_tweak,
      P, leNat_zeros, length_zeros, leNat_tweak0 13 0 _ _ (by norm_num) (by norm_num)]
    simp only [BitVec.toNat_ofNat, show (0 : Word).toNat = 0 from rfl, Nat.reducePow, Nat.reduceMul,
      Nat.reduceAdd] at hW ⊢
    omega
  have hblk : (pad64 (maskInput S l j)).blocks = 1 := by
    simp [Query.blocks, pad64, padBlocks, maskInput, thInput, hS.1]
  set A := REGION + 16 * (lvOff l + j) with hAdef
  set lv := (levels.getD l []).getD j [] with hlv
  have hlvl : lv.length = 16 := hs.getD_len l j (by omega) hj
  -- the node before masking
  have hdrop : (nodes levels).drop (lvOff l + j) =
      lv :: (nodes levels).drop (lvOff l + j + 1) := by
    rw [List.drop_eq_getElem_cons (by rw [nodes_length levels hs]; exact hlt), hlv,
      ← nodes_getD levels hs l j hl hj, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by rw [nodes_length levels hs]; exact hlt), Option.getD_some]
  have hlv0 := h.lv
  rw [hdrop] at hlv0
  have hv0 : ValAt t A lv := by
    have := hlv0.2 (macc.length + inner.length) (by simp)
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp),
      show macc.length + inner.length - (macc ++ inner).length = 0 by simp,
      List.getElem?_cons_zero, Option.getD_some, h.mlen, h.ilen] at this
    exact this
  refine (XSim.steps hst (XSim.hash16_bind (x := maskInput S l j) (k := 11) (c := 11) (n := 0) (b := 0)
    (f := fun mk => pure (inner ++ [xorBytes lv mk]))
    ((codeAt_132.fetch u upc).trans rfl) (by rw [ux _ (by simp)]; exact h.base.r5)
    (hashArgs_const u 1696 64 320 u10 u11 u12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num))
    (hq.trans (fmt_thInput 13 0 0 l j S (by decide)).symm)
    (not_digest_thInput 13 0 0 l j S (by decide)) (fun a => ?_))).of_eq rfl (by rfl)
      (by rw [hblk]) (by rfl) (by rw [hblk])
  have wpc : (writeHash u a).pc = pcOf 133 := by rw [pc_writeHash, upc]; rfl
  have hwf := Frame.writeHash u a 320 u12 (by norm_num) (by norm_num)
  have hA0 : A + 16 < 2 ^ 24 := by rw [hAdef]; unfold REGION; omega
  obtain ⟨v, vst, vpc, v20, v16, vun, vA, vA8, vfr⟩ := spec_133 (writeHash u a) wpc A j (2 ^ (11 - l))
    hA0 (by rw [hAdef]; unfold REGION; omega) (by rw [hAdef]; unfold REGION; omega) (by omega) (by omega)
    (by rw [getReg_writeHash, ux _ (by simp), h.r20])
    (by rw [getReg_writeHash, ux _ (by simp), h.r16])
    (by rw [getReg_writeHash, ux _ (by simp), h.r17])
  have fr := (ufr.trans hwf).trans vfr
  have hmk := valAt_writeHash u a 320 u12 (by norm_num)
  have mA : (writeHash u a).getMem (BitVec.ofNat 64 A) = lo lv := by
    rw [getMem_frame hwf (by omega) (by simp; rw [hAdef]; unfold REGION; omega),
      getMem_frame ufr (by omega) (by simp; rw [hAdef]; unfold REGION; omega)]
    exact hv0.1
  have mA8 : (writeHash u a).getMem (BitVec.ofNat 64 (A + 8)) = hi lv := by
    rw [getMem_frame hwf (by omega) (by simp; rw [hAdef]; unfold REGION; omega),
      getMem_frame ufr (by omega) (by simp; rw [hAdef]; unfold REGION; omega)]
    exact hv0.2
  have hnew : ValAt v A (xorBytes lv (answerBytes 16 a)) := by
    constructor
    · rw [vA, mA, hmk.1, lo_xor _ _ (by rw [hlvl, length_answer16])]
    · rw [vA8, mA8, hmk.2, hi_xor _ _ (by rw [hlvl, length_answer16])]
  have vr : ∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x20 → r ≠ .x16 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 →
      r ≠ .x12 → v.getReg r = t.getReg r :=
    fun r h1 h2 h3 h4 h5 h6 h7 h8 => by
      rw [vun r h1 h2 h3 h4, getReg_writeHash, ux r ⟨h5, h6, h7, h8⟩]
  have hkeys : ∀ k ∈ [1696, 1704] ++ [320, 320 + 8, 320 + 16, 320 + 24] ++ [A, A + 8],
      (k + 8 ≤ 160 ∨ 176 ≤ k) ∧ (k + 8 ≤ 0x144A0 ∨ 0x144C0 ≤ k) ∧ k < 2 ^ 64 := by
    intro k hk; simp at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      (try rw [hAdef]) <;> (try unfold REGION) <;> omega
  refine XSim.pure_steps vst ⟨⟨?_, ?_, v16, ?_, ?_, hs, h.mlen, by simp [h.ilen], ?_, ?_⟩, ?_⟩
  · refine h.base.frame (fun r hr => ?_) fr (fun k hk => ?_)
    · rcases hr with rfl | rfl | rfl | rfl <;>
        exact vr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    · simp at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [BaseSafe, zeroKeys, REGION, hAdef] <;> omega
  · rw [vr _ (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)]; exact h.r15
  · rw [vun _ (by simp) (by simp) (by simp) (by simp), getReg_writeHash, ux _ (by simp)]; exact h.r17
  · rw [v20, hAdef]; congr 1
  · have hlen : (macc ++ inner).length = lvOff l + j := by simp [h.mlen, h.ilen]
    have hrl : ((nodes levels).drop (lvOff l + j + 1)).length = 4094 - (lvOff l + j + 1) := by
      simp [nodes_length levels hs]
    have hup := hlv0.update (L := macc ++ inner) (y := xorBytes lv (answerBytes 16 a)) fr
      (fun k hk => by
        rw [hlen, hrl]; simp at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first
          | (left; rw [hAdef]; done)
          | (right; left; rw [hAdef]; done)
          | (right; right; left; unfold REGION; omega))
      (by rw [hlen, hrl]; unfold REGION; omega) (by rw [hlen]; exact hnew)
      (length_xorBytes _ _ hlvl (length_answer16 a))
    rw [show lvOff l + (j + 1) = lvOff l + j + 1 by ring]
    simpa [List.append_assoc] using hup
  · exact h.out.frame fr hkeys
  · rw [vpc]
    by_cases hjn : j + 1 = 2 ^ (11 - l)
    · rw [if_pos hjn, if_neg (by omega)]
    · rw [if_neg hjn, if_pos (by omega)]

/-- One mask level `l` (all its nodes, left to right). -/
theorem mask_level_xsim (W : List Word) (S : List Byte) (hS : SkOk W S) (levels : List (List Val))
    (root : Val) (l : Nat) (hl : l < 11) (macc : List Val) (t : MachineState)
    (h : OCtx W levels root l macc t) (hpc : t.pc = pcOf 118) :
    XSim image t (8 + 2 ^ (11 - l) * 21) (8 + 2 ^ (11 - l) * 28) (2 ^ (11 - l)) (2 ^ (11 - l))
      (do let ml ← maskLevel S l (levels.getD l []); pure (macc ++ ml))
      (fun macc' u => OCtx W levels root (l + 1) macc' u ∧
        u.pc = if l + 1 < 11 then pcOf 118 else pcOf 147) := by
  have hs := h.shape
  have hn1 : 1 ≤ 2 ^ (11 - l) := Nat.one_le_two_pow
  obtain ⟨u, hst, upc, u17, u16, uun, ufr⟩ := spec_118 t hpc l hl h.r15
  have h0 : ICtx W levels root l 0 macc [] u := by
    refine ⟨h.base.frame (fun r hr => uun r ?_ ?_ ?_ ?_) ufr (by simp), ?_, u16, u17, ?_, hs, h.mlen, rfl,
      ?_, h.out.frame ufr (by simp)⟩ <;> try (rcases hr with h | h | h | h <;> simp [h])
    · rw [uun _ (by simp) (by simp) (by simp) (by simp)]; exact h.r15
    · rw [uun _ (by simp) (by simp) (by simp) (by simp), h.r20, Nat.add_zero]
    · have hL : (macc ++ (nodes levels).drop (lvOff l)).length ≤ 4094 := by
        have := lvOff_add_lt l 0 hl (by positivity)
        simp [h.mlen, nodes_length levels hs]; omega
      simpa using (show Vals u REGION (macc ++ (nodes levels).drop (lvOff l)) from
        ⟨h.lv.1, fun i hi => (h.lv.2 i hi).frame ufr (by unfold REGION; omega) (by simp)⟩)
  have hlen : (levels.getD l []).length = 2 ^ (11 - l) := hs.lens l (by omega)
  have hloop := XSim.foldlM_range (image := image) (2 ^ (11 - l))
    (fun (acc : List Val) j => do
      let mk ← Ref.hash16 (maskInput S l j)
      pure (acc ++ [xorBytes ((levels.getD l []).getD j []) mk]))
    []
    (fun j inner w => ICtx W levels root l j macc inner w ∧
      w.pc = if j < 2 ^ (11 - l) then pcOf 123 else pcOf 144)
    (fun _ => 21) (fun _ => 28) (fun _ => 1) (fun _ => 1)
    (fun j hj inner w hw => mask_node_xsim W S hS levels root l j hl hj macc inner w hw.1
      (by rw [hw.2, if_pos hj]))
    ⟨h0, by rw [upc, if_pos (by omega)]⟩
  unfold maskLevel
  rw [hlen]
  refine (XSim.steps hst (XSim.bind (k₂ := 3) (c₂ := 3) (n₂ := 0) (b₂ := 0) hloop
    (fun inner w hw => ?_))).of_eq rfl
    (by simp only [sumTo_const] <;> ring) (by simp only [sumTo_const] <;> ring)
    (by simp only [sumTo_const] <;> ring) (by simp only [sumTo_const] <;> ring)
  obtain ⟨hc, hpc130⟩ := hw
  obtain ⟨x, xst, xpc, x15, xun, xfr⟩ := spec_144 w (by rw [hpc130, if_neg (by omega)]) l hl hc.r15
  have hoff := lvOff_succ l
  refine XSim.pure_steps xst ⟨⟨?_, x15, ?_, hs, by simp [h.mlen, hc.ilen, hoff], ?_, ?_⟩, ?_⟩
  · exact hc.base.frame (fun r hr => xun r (by rcases hr with h | h | h | h <;> simp [h])
      (by rcases hr with h | h | h | h <;> simp [h])) xfr (by simp)
  · rw [xun _ (by simp) (by simp), hc.r20, hoff]
  · have := hc.lv
    rw [← hoff] at this
    have h2 := lvOff_add_lt l (2 ^ (11 - l) - 1) hl (by omega)
    have hL : (macc ++ inner ++ (nodes levels).drop (lvOff (l + 1))).length ≤ 4094 := by
      simp [h.mlen, hc.ilen, nodes_length levels hs]; omega
    exact ⟨this.1, fun i hi => (this.2 i hi).frame xfr (by unfold REGION; omega) (by simp)⟩
  · exact hc.out.frame xfr (by simp)
  · rw [xpc]
    by_cases hl' : l + 1 = 11
    · rw [if_pos hl', if_neg (by omega)]
    · rw [if_neg hl', if_pos (by omega)]

/-- All masks: levels `l = 0 .. 10`, from instruction 101. -/
theorem masks_xsim (W : List Word) (S : List Byte) (hS : SkOk W S) (levels : List (List Val))
    (root : Val) (t : MachineState) (hb : Base W t) (hs : Shape 11 levels)
    (hv : Vals t REGION (nodes levels)) (hout : Out root t) (hpc : t.pc = pcOf 115) :
    XSim image t (3 + sumTo (fun l => 8 + 2 ^ (11 - l) * 21) 11)
      (3 + sumTo (fun l => 8 + 2 ^ (11 - l) * 28) 11) (sumTo (fun l => 2 ^ (11 - l)) 11)
      (sumTo (fun l => 2 ^ (11 - l)) 11)
      ((List.range 11).foldlM (fun (acc : List Val) l => do
        let ml ← maskLevel S l (levels.getD l [])
        pure (acc ++ ml)) [])
      (fun masked u => OCtx W levels root 11 masked u ∧ u.pc = pcOf 147) := by
  obtain ⟨u, hst, upc, u20, u15, uun, ufr⟩ := spec_115 t hpc
  have h0 : OCtx W levels root 0 [] u := by
    refine ⟨hb.frame (fun r hr => uun r (by rcases hr with h | h | h | h <;> simp [h])
      (by rcases hr with h | h | h | h <;> simp [h])) ufr (by simp), u15, ?_, hs, rfl, ?_,
      hout.frame ufr (by simp)⟩
    · rw [u20]; rfl
    · simpa [lvOff] using (show Vals u REGION (nodes levels) from
        ⟨hv.1, fun i hi => (hv.2 i hi).frame ufr (by
          simp [nodes_length levels hs] at hi; unfold REGION; omega) (by simp)⟩)
  refine (XSim.steps hst (XSim.foldlM_range 11 _ [] (fun l macc w => OCtx W levels root l macc w ∧
    w.pc = if l < 11 then pcOf 118 else pcOf 147)
    (fun l => 8 + 2 ^ (11 - l) * 21) (fun l => 8 + 2 ^ (11 - l) * 28) (fun l => 2 ^ (11 - l))
    (fun l => 2 ^ (11 - l))
    (fun l hl macc w hw => mask_level_xsim W S hS levels root l hl macc w hw.1 (by rw [hw.2, if_pos hl]))
    ⟨h0, by rw [upc]; rfl⟩)).mono (fun m w hw => ⟨hw.1, by rw [hw.2]; rfl⟩)

end SigGolfCandidate.Keygen
