import SigGolfCandidate.Keygen.Mask
import SigGolfCandidate.Keygen.Output

/-!
# `keygen` refines `keygenRef`

`keygen_run` : for every secret key `sk`,
`submission.run .keygen sk = (fun o => ⟨some o, true, 13500615, 653310, 674814⟩) <$> keygenRef sk`:
the machine makes exactly the oracle queries of `keygenRef sk` (in order), outputs its public key
and cache, and always takes 13500615 cycles, 653310 calls and 674814 compressions.
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref
  SigGolfCandidate.Mem OracleComp

/-- The initial state of `keygen`. -/
def kInit (sk : SecretKey) : MachineState :=
  let blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  ((blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase image)) image.data).writeBytesAsWords
    (BitVec.ofNat 64 0x80) (bytes sk)).setReg .x2 (BitVec.ofNat 64 (dataBase image))

theorem kInit_eq (sk : SecretKey) : initialState submission .keygen sk = some (kInit sk) := by
  unfold initialState
  rw [if_pos (submission_admissible.2 .keygen)]
  rfl

theorem kInit_pc (sk : SecretKey) : (kInit sk).pc = pcOf 0 := by
  rw [initialState_pc _ _ _ _ (kInit_eq sk)]; rfl

theorem kInit_x5 (sk : SecretKey) : (kInit sk).getReg .x5 = 0 := by
  simp only [kInit, getReg_setReg', MachineState.getReg_writeBytesAsWords]
  rfl

theorem kInit_mem (sk : SecretKey) (A : Nat) (hA : A < 2 ^ 64) :
    (kInit sk).getMem (BitVec.ofNat 64 A) =
      if 128 ≤ A ∧ A < 160 ∧ (A - 128) % 8 = 0 then
        BitVec.ofNat 64 (leNat (((bytes sk).drop (A - 128)).take 8))
      else 0 := by
  have hl : (bytes sk).length = 32 := by simp [SigGolf.bytes]
  unfold kInit
  simp only [MachineState.getMem_setReg]
  rw [getMem_writeBytesAsWords _ _ _ _ (by rw [hl]; norm_num) hA, hl, bytesToWordLE_eq]
  simp only [show image.data = [] from rfl, MachineState.writeBytesAsWords_nil]
  rfl

/-- The secret-key doublewords of the initial state. -/
def kW (sk : SecretKey) : List Word :=
  [(kInit sk).getMem (BitVec.ofNat 64 128), (kInit sk).getMem (BitVec.ofNat 64 136),
    (kInit sk).getMem (BitVec.ofNat 64 144), (kInit sk).getMem (BitVec.ofNat 64 152)]

theorem leNat_take_drop8 (l : List Byte) (h : 8 ≤ l.length) :
    leNat l = leNat (l.take 8) + 2 ^ 64 * leNat (l.drop 8) := by
  conv_lhs => rw [← List.take_append_drop 8 l]
  rw [leNat_append, List.length_take, Nat.min_eq_left h]

theorem leNat_take8_lt (l : List Byte) : leNat (l.take 8) < 2 ^ 64 := by
  have := leNat_lt (l.take 8)
  have h2 : (l.take 8).length ≤ 8 := by simp
  calc leNat (l.take 8) < 256 ^ (l.take 8).length := this
    _ ≤ 256 ^ 8 := Nat.pow_le_pow_right (by norm_num) h2
    _ = 2 ^ 64 := by norm_num

theorem kW_skOk (sk : SecretKey) : SkOk (kW sk) (toList sk) := by
  have hl : (toList sk).length = 32 := length_toList sk
  refine ⟨hl, ?_⟩
  simp only [kW, List.getD_cons_zero, List.getD_cons_succ]
  rw [kInit_mem sk 128 (by norm_num), if_pos (by decide), kInit_mem sk 136 (by norm_num),
    if_pos (by decide), kInit_mem sk 144 (by norm_num), if_pos (by decide),
    kInit_mem sk 152 (by norm_num), if_pos (by decide)]
  simp only [Nat.reduceSub]
  have e := fun (k : Nat) => toNat_ofNat_lt (leNat_take8_lt ((bytes sk).drop k))
  rw [e, e, e, e]
  simp only [List.drop_zero]
  have s1 := leNat_take_drop8 (toList sk) (by omega)
  have s2 := leNat_take_drop8 ((toList sk).drop 8) (by simp [hl])
  have s3 := leNat_take_drop8 ((toList sk).drop 16) (by simp [hl])
  have s4 : ((toList sk).drop 24).take 8 = (toList sk).drop 24 := List.take_of_length_le (by simp [hl])
  simp only [List.drop_drop, Nat.reduceAdd] at s2 s3
  rw [s1, s2, s3, ← s4]
  rfl

theorem leaves_xsim (sk : SecretKey) :
    XSim image (kInit sk) (25 + sumTo (fun _ => 4214) (2 ^ 11)) (25 + sumTo (fun _ => 6506) (2 ^ 11))
      (sumTo (fun _ => 316) (2 ^ 11)) (sumTo (fun _ => 326) (2 ^ 11))
      (buildLeaves (toList sk) 0 0 11 0 [])
      (fun p u => LCtx (kW sk) (2 ^ 11) p.1 u ∧ u.pc = if 2 ^ 11 < 2048 then pcOf 25 else pcOf 76) := by
  obtain ⟨t, hst, tpc, t8, t30, t9, t19, t17, t20, t5, t1728, t1736, t1744, t1752, t1696, t192,
    t832, t224, t232, tfr⟩ := spec_0 (kInit sk) (kInit_pc sk) (by rw [kInit_mem sk 1696 (by norm_num)]; rfl)
      (by rw [kInit_mem sk 192 (by norm_num)]; rfl)
  have zi : ∀ A < 2 ^ 64, (A < 128 ∨ 160 ≤ A) → (kInit sk).getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA h; rw [kInit_mem sk A hA, if_neg (by omega)]
  have hb : Base (kW sk) t := by
    refine ⟨by rw [t5, kInit_x5], t8, t30, t9, ?_, ?_, ?_, t832, ?_⟩
    · intro k hk
      interval_cases k
      · exact t1728
      · exact t1736
      · exact t1744
      · exact t1752
    · intro k hk
      rw [tfr _ (by omega) (by simp; omega)]
      interval_cases k <;> rfl
    · intro A hA
      simp [zeroKeys] at hA
      by_cases h224 : A = 224
      · subst h224; exact t224
      by_cases h232 : A = 232
      · subst h232; exact t232
      rw [tfr A (by omega) (by simp; omega), zi A (by omega) (by omega)]
    · intro A h1 h2
      rw [tfr A (by omega) (by simp; omega), zi A (by omega) (by omega)]
  have h0 : LCtx (kW sk) 0 [] t := ⟨hb, t1696, t192, t17, t19, t20, rfl, Vals.nil t REGION⟩
  unfold buildLeaves
  refine XSim.steps hst (XSim.foldlM_range (2 ^ 11) _ ([], [])
    (fun e acc u => LCtx (kW sk) e acc.1 u ∧ u.pc = if e < 2048 then pcOf 25 else pcOf 76)
    (fun _ => 4214) (fun _ => 6506) (fun _ => 316) (fun _ => 326)
    (fun e he acc u hu => leaf_xsim (kW sk) (toList sk) (kW_skOk sk) e (by norm_num at he; omega)
      acc u hu.1 (by rw [hu.2, if_pos (by norm_num at he; omega)])) ⟨h0, by rw [tpc]; rfl⟩)

/-- The tree levels `1 .. 11`, from the leaves in the region. -/
theorem levels_xsim (W : List Word) (leaves : List Val) (u : MachineState)
    (h : LCtx W 2048 leaves u) (hpc : u.pc = pcOf 76) :
    XSim image u (1 + sumTo (fun k => 11 + 2 ^ (10 - k) * 19) 11)
      (1 + sumTo (fun k => 11 + 2 ^ (10 - k) * 26) 11) (sumTo (fun k => 2 ^ (10 - k)) 11)
      (sumTo (fun k => 2 ^ (10 - k)) 11)
      (buildAllLevels (nodeInput 0 0) 11 leaves)
      (fun levels w => VCtx W 11 levels w ∧ w.pc = pcOf 107) := by
  obtain ⟨v, vst, vpc, v15, vun, vfr⟩ := spec_76 u hpc
  have h0 : VCtx W 0 [leaves] v := by
    refine ⟨h.base.frame (fun r hr => vun r (by rcases hr with h | h | h | h <;> simp [h])) vfr
      (by simp), v15, ?_, ?_, ⟨rfl, fun i hi => ?_, fun L hL x hx => ?_⟩, ?_⟩
    · rw [vun _ (by simp), h.r17]; rfl
    · rw [vun _ (by simp), h.r19]; rfl
    · rw [show i = 0 by omega]; simp [h.len]
    · simp at hL; subst hL; exact h.lv.1 x hx
    · rw [List.flatten_singleton]
      exact ⟨h.lv.1, fun i hi => (h.lv.2 i hi).frame vfr (by rw [h.len] at hi; unfold REGION; omega)
        (by simp)⟩
  unfold buildAllLevels
  refine (XSim.steps vst (XSim.foldlM_range' 1 11 _ [leaves]
      (fun k levels w => VCtx W k levels w ∧ w.pc = if k < 11 then pcOf 77 else pcOf 107)
      (fun k => 11 + 2 ^ (10 - k) * 19) (fun k => 11 + 2 ^ (10 - k) * 26) (fun k => 2 ^ (10 - k))
      (fun k => 2 ^ (10 - k))
      (fun k hk levels w hw => level_xsim W k hk levels w hw.1 (by rw [hw.2, if_pos hk]))
      ⟨h0, by rw [vpc]; rfl⟩)).mono (fun levels w hw => ⟨hw.1, by rw [hw.2]; rfl⟩)

/-- The MAC and the final HALT, from instruction 133. -/
theorem mac_xsim (W : List Word) (S : List Byte) (hS : SkOk W S) (levels : List (List Val))
    (root : Val) (masked : List Val) (t : MachineState) (h : OCtx W levels root 11 masked t)
    (hpc : t.pc = pcOf 147) :
    XSim image t 27 8226 1 1025 (H (macInput S masked.flatten))
      (fun a w => fetch image w = some (.base .ECALL) ∧ w.getReg .x5 = 1 ∧ w.getReg .x10 = 0 ∧
        ValAt w 160 root ∧ Vals w REGION masked ∧
        (∀ k < 4, w.getMem (BitVec.ofNat 64 (0x4B00 + 8 * k)) = a.extractLsb' (64 * k) 64) ∧
        ∀ A, 0x14B00 ≤ A → A < 0x24B00 → A % 8 = 0 → w.getMem (BitVec.ofNat 64 A) = 0) := by
  have hml : masked.length = 4094 := by rw [h.mlen, lvOff_11]
  have hs := h.shape
  have hvm : Vals t REGION masked := by
    have := h.lv
    rw [lvOff_11, List.drop_eq_nil_of_le (by rw [nodes_length levels hs]), List.append_nil] at this
    exact this
  obtain ⟨u, hst, upc, u10, u11, u12, uun, u4AE0, u4B00, u4B08, u4B10, u4B18, uz0, uz1, uz2, uz3, ufr⟩ :=
    spec_147 t hpc
  have ux : ∀ r, r ≠ .x1 ∧ r ≠ .x3 ∧ r ≠ .x10 ∧ r ≠ .x11 ∧ r ≠ .x12 ∧ r ≠ .x29 → u.getReg r = t.getReg r :=
    fun r hr => uun r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2
  have hvu : Vals u REGION masked := ⟨hvm.1, fun i hi => (hvm.2 i hi).frame ufr
    (by rw [hml] at hi; unfold REGION; omega) (fun k hk => by simp at hk; rw [hml] at hi; unfold REGION; omega)⟩
  have hfl : masked.flatten.length = 65504 := by rw [length_flatten16 _ hvm.1, hml]
  have hxl : (macInput S masked.flatten).length = 65568 := by
    simp [macInput, thInput, hS.1, hfl]
  have hq : hashInput u = pad64 (macInput S masked.flatten) := by
    refine hashInput_eq_pad64 u 1024 0x4AE0 _ (by rw [u11]) (by norm_num) u10
      (by norm_num) (by norm_num) (by omega) (by omega) ?_
    rw [show 8 * (1024 + 1) = 2 + (2 + (4 + (2 * masked.length + 4))) by rw [hml],
      readWords_add, readWords_add, readWords_add, readWords_add, wordsToNat_append, wordsToNat_append,
      wordsToNat_append, wordsToNat_append, readWords_length, readWords_length, readWords_length,
      readWords_length]
    have hg : ∀ A ∈ [0x4AE8, 0x4AF0, 0x4AF8],
        u.getMem (BitVec.ofNat 64 A) = 0 := by
      intro A hA
      rw [getMem_frame ufr (by simp at hA; omega) (by simp at hA ⊢; omega)]
      exact h.base.zero A (by simp [zeroKeys] at hA ⊢; omega)
    have p1 : wordsToNat (u.readWords (BitVec.ofNat 64 0x4AE0) 2) = 3585 := by
      rw [readWords_two, u4AE0, hg 0x4AE8 (by simp)]; rfl
    have p2 : wordsToNat (u.readWords (BitVec.ofNat 64 (0x4AE0 + 8 * 2)) 2) = 0 := by
      rw [readWords_two, hg 0x4AF0 (by simp), hg 0x4AF8 (by simp)]; rfl
    have p3 : wordsToNat (u.readWords (BitVec.ofNat 64 (0x4AE0 + 8 * 2 + 8 * 2)) 4) = leNat S := by
      rw [← hS.2]
      simp only [MachineState.readWords, ofNat_add8, Nat.reduceAdd, Nat.reduceMul, wordsToNat]
      rw [u4B00, u4B08, u4B10, u4B18, h.base.skIn 0 (by norm_num), h.base.skIn 1 (by norm_num),
        h.base.skIn 2 (by norm_num), h.base.skIn 3 (by norm_num)]
      ring
    have p4 : wordsToNat (u.readWords (BitVec.ofNat 64 (0x4AE0 + 8 * 2 + 8 * 2 + 8 * 4))
        (2 * masked.length)) = leNat masked.flatten := wordsToNat_vals u _ masked hvu.1 hvu.2
    have p5 : wordsToNat (u.readWords (BitVec.ofNat 64 (0x4AE0 + 8 * 2 + 8 * 2 + 8 * 4 +
        8 * (2 * masked.length))) 4) = 0 := by
      rw [hml]
      simp only [MachineState.readWords, ofNat_add8, Nat.reduceAdd, Nat.reduceMul, wordsToNat]
      rw [uz0, uz1, uz2, uz3]; rfl
    rw [p1, p2, p3, p4, p5, Nat.mul_zero, Nat.add_zero]
    simp only [macInput, thInput, leNat_append, List.length_append, length_tweak, length_P, hS.1,
      P, leNat_zeros, leNat_tweak0 14 0 _ _ (by norm_num) (by norm_num)]
    generalize leNat masked.flatten = R
    generalize leNat S = X
    norm_num
    ring
  have hblk : (fmt (macInput S masked.flatten)).blocks = 1025 := by
    rw [blocks_fmt (macInput S masked.flatten) (not_digest_thInput 14 0 0 0 0 _ (by decide))]; simp [Query.blocks, pad64, padBlocks, hxl]
  have hq' : hashInput u = fmt (macInput S masked.flatten) :=
    hq.trans (fmt_thInput 14 0 0 0 0 _ (by decide)).symm
  have hv : hashArgumentsValid u = true :=
    hashArgs_const u 0x4AE0 65600 0x4B00 u10 u11 u12 (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  refine (XSim.steps hst (XSim.bind (k₂ := 2) (c₂ := 2) (n₂ := 0) (b₂ := 0)
    (XSim.query ((codeAt_171.fetch u upc).trans rfl) (by rw [ux _ (by simp)]; exact h.base.r5) hv hq')
    (fun a w hw => ?_))).of_eq (by simp only [H, bind_pure]; rfl) (by rfl) (by rw [hblk]) (by rfl)
    (by rw [hblk])
  subst hw
  have wpc : (writeHash u a).pc = pcOf 172 := by rw [pc_writeHash, upc]; rfl
  obtain ⟨x, xst, xpc, x5, x10, xfr⟩ := spec_172 (writeHash u a) wpc
  have hwf := Frame.writeHash u a 0x4B00 u12 (by norm_num) (by norm_num)
  have xm : ∀ A < 2 ^ 64, x.getMem (BitVec.ofNat 64 A) = (writeHash u a).getMem (BitVec.ofNat 64 A) :=
    fun A hA => xfr A hA (by simp)
  refine XSim.pure_steps xst ⟨(codeAt_174.fetch x xpc).trans rfl, x5, x10, ?_, ?_, ?_, ?_⟩
  · exact (h.out.pk.frame (ufr.trans hwf) (by norm_num) (fun k hk => by simp at hk; omega)).frame xfr
      (by norm_num) (by simp)
  · exact ⟨hvu.1, fun i hi => ((hvu.2 i hi).frame hwf (by rw [hml] at hi; unfold REGION; omega)
      (fun k hk => by simp at hk; unfold REGION; omega)).frame xfr
      (by rw [hml] at hi; unfold REGION; omega) (by simp)⟩
  · intro k hk
    rw [xm _ (by omega), getMem_writeHash u a 0x4B00 _ u12 (by norm_num) (by omega)]
    interval_cases k <;> simp
  · intro A h1 h2 h8
    rw [xm _ (by omega), getMem_writeHash u a 0x4B00 _ u12 (by norm_num) (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    by_cases hA : A < 0x14B20
    · have : A = 0x14B00 ∨ A = 0x14B08 ∨ A = 0x14B10 ∨ A = 0x14B18 := by omega
      rcases this with rfl | rfl | rfl | rfl
      · exact uz0
      · exact uz1
      · exact uz2
      · exact uz3
    · rw [getMem_frame ufr (by omega) (by simp; omega)]
      exact h.base.tail A (by omega) h2

/-- The whole of `keygenList`, from the initial state to the final HALT. -/
theorem keygenList_xsim (sk : SecretKey) :
    XSim image (kInit sk) 8755412 13500614 653310 674814 (keygenList (toList sk))
      (fun r t => fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
        ValAt t 160 r.1 ∧ r.1.length = 16 ∧ readBuffer t 0x4B00 CACHE_BYTES = ofList CACHE_BYTES r.2) := by
  have hS := kW_skOk sk
  unfold keygenList
  refine (XSim.bind (k₂ := 39015 + (8 + (86065 + 27))) (c₂ := 53344 + (8 + (114723 + 8226)))
    (n₂ := 2047 + (4094 + 1)) (b₂ := 2047 + (4094 + 1025)) (leaves_xsim sk)
    (fun p u hu => ?_)).of_eq rfl (by simp only [sumTo_const]; norm_num)
    (by simp only [sumTo_const]; norm_num) (by simp only [sumTo_const]; norm_num)
    (by simp only [sumTo_const]; norm_num)
  obtain ⟨leaves, c⟩ := p
  obtain ⟨hl, hpc⟩ := hu
  refine (XSim.bind (k₂ := 8 + (86065 + 27)) (c₂ := 8 + (114723 + 8226))
    (n₂ := 4094 + 1) (b₂ := 4094 + 1025)
    (levels_xsim (kW sk) leaves u hl (by rw [hpc]; rfl)) (fun levels v hv => ?_)).of_eq rfl
      (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hvc, vpc⟩ := hv
  have hs := hvc.shape
  have hfl := flatten_length 11 levels hs
  have h19 : v.getReg .x19 = BitVec.ofNat 64 0x14B00 := by rw [hvc.r19, lvOff_11]
  obtain ⟨w, wst, wpc, wun, w160, w168, wz0, wz1, wz2, wz3, wfr⟩ := spec_107 v vpc h19
  set root := (levels.getD 11 []).getD 0 [] with hroot
  have hrv : ValAt v (REGION + 16 * lvOff 11) root := by
    have := hvc.lv.2 (lvOff 11 + 0) (by rw [hfl]; decide)
    rwa [flatten_getD 11 levels hs 11 0 le_rfl (by norm_num)] at this
  have hrl : root.length = 16 := hs.getD_len 11 0 le_rfl (by norm_num)
  have hout : Out root w := by
    refine ⟨⟨?_, ?_⟩, fun A hA => ?_⟩
    · rw [w160, show (0x14B00 : Nat) = REGION + 16 * lvOff 11 by rw [lvOff_11]]; exact hrv.1
    · rw [w168, show (0x14B08 : Nat) = REGION + 16 * lvOff 11 + 8 by rw [lvOff_11]]; exact hrv.2
    · simp at hA; rcases hA with rfl | rfl | rfl | rfl
      · exact wz0
      · exact wz1
      · exact wz2
      · exact wz3
  have hbw : Base (kW sk) w := hvc.base.frame (fun r hr => wun r (by rcases hr with h | h | h | h <;> simp [h])
    (by rcases hr with h | h | h | h <;> simp [h])) wfr (fun k hk => by
      simp at hk; rcases hk with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [BaseSafe, zeroKeys])
  have hnv : Vals w REGION (nodes levels) := by
    have hn := nodes_length levels hs
    refine ⟨fun x hx => hvc.lv.1 x (List.mem_of_mem_take hx), fun i hi => ?_⟩
    have h12 : lvOff (11 + 1) = 4095 := by rw [lvOff_succ, lvOff_11]; rfl
    rw [hn] at hi
    have := hvc.lv.2 i (by rw [hfl, h12]; omega)
    have e : (nodes levels).getD i [] = levels.flatten.getD i [] := by
      simp only [nodes, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]
    rw [e]
    exact this.frame wfr (by unfold REGION; omega) (fun k hk => by simp at hk; unfold REGION; omega)
  refine XSim.steps wst ((XSim.bind (k₂ := 27) (c₂ := 8226) (n₂ := 1) (b₂ := 1025)
    (masks_xsim (kW sk) (toList sk) hS levels root w hbw hs hnv hout (by rw [wpc]))
    (fun masked x hx => ?_)).of_eq rfl (by decide) (by decide) (by decide) (by decide))
  obtain ⟨hoc, xpc⟩ := hx
  refine (XSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0)
    (mac_xsim (kW sk) (toList sk) hS levels root masked x hoc xpc)
    (fun a y hy => XSim.pure ?_)).of_eq rfl rfl rfl rfl rfl
  obtain ⟨y1, y5, y10, ypk, yreg, ytag, yz⟩ := hy
  have hml : masked.length = 4094 := by rw [hoc.mlen, lvOff_11]
  exact ⟨y1, y5, y10, ypk, hrl, (readBuffer_cache_eq y a masked hml ytag yreg yz).symm ▸ rfl⟩

/-- The whole of `keygen`. -/
theorem keygen_xsim (sk : SecretKey) :
    XSim image (kInit sk) 8755412 13500614 653310 674814 (keygenRef sk)
      (fun o t => fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
        readOutput submission.sizes submission.layout .keygen t = o) := by
  unfold keygenRef
  refine (XSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) (keygenList_xsim sk)
    (fun r t ht => ?_)).of_eq rfl rfl rfl rfl rfl
  obtain ⟨root, cache⟩ := r
  obtain ⟨t1, t5, t10, tpk, trl, tc⟩ := ht
  refine XSim.pure ⟨t1, t5, t10, ?_⟩
  show (readBuffer t 160 16, readBuffer t 0x4B00 CACHE_BYTES) = (ofList 16 root, ofList CACHE_BYTES cache)
  rw [readBuffer_val t 160 root trl (by norm_num) (by norm_num) tpk, tc]

/-- **keygen**: for every secret key, one run makes exactly the oracle queries of
`keygenRef sk`, outputs its public key and cache, and always takes 13500615 cycles, 653310 calls
and 674814 compressions. -/
theorem keygen_run (sk : SecretKey) :
    submission.run .keygen sk =
      (fun o => ⟨some o, true, 13500615, 653310, 674814⟩) <$> keygenRef sk :=
  XSim.run_eq submission .keygen sk (kInit_eq sk) (keygen_xsim sk) (by decide) id
    (fun _ _ h => h)

/-- The reference makes exactly 653310 calls and 674814 compressions. -/
theorem keygenRef_counts (sk : SecretKey) :
    countCalls (keygenRef sk) = (fun a => (a, 653310)) <$> keygenRef sk ∧
      countBlocks (keygenRef sk) = (fun a => (a, 674814)) <$> keygenRef sk :=
  (keygen_xsim sk).count_eq

/-- The joint call / compression count of the reference is constant. -/
theorem keygenRef_countBoth (sk : SecretKey) :
    Sign.countBoth (keygenRef sk) = (fun a => (a, 653310, 674814)) <$> keygenRef sk :=
  (keygen_xsim sk).countBoth_eq

/-- Value, calls and compressions of the run = the reference's value with its joint
call / compression count. -/
theorem keygen_run_counts (sk : SecretKey) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .keygen sk =
      (fun p => (some p.1, p.2.1, p.2.2)) <$> Sign.countBoth (keygenRef sk) := by
  rw [keygen_run, keygenRef_countBoth, Functor.map_map, Functor.map_map]; rfl

/-- Fixed-oracle form: finished, exactly 13500615 cycles (`< 2^32`), for every oracle. -/
theorem keygen_runWith (hash : Hash) (sk : SecretKey) :
    submission.runWith hash .keygen sk =
      ⟨some (evalWithAnswerFn hash (keygenRef sk)), true, 13500615, 653310, 674814⟩ := by
  unfold Submission.runWith
  rw [keygen_run, evalWithAnswerFn_map]
  rfl

end SigGolfCandidate.Keygen
