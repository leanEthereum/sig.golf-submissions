import SigGolfCandidate.Keygen.Tree
import SigGolfCandidate.Keygen.Output

/-!
# `keygen` refines `keygenRef`

`keygen_run` : for every secret key `sk`,
`submission.run .keygen sk = (fun pk => ⟨some (pk, 0), true, 196282, 10815, 11135⟩) <$> keygenRef sk`:
the machine makes exactly the oracle queries of `keygenRef sk` (in order), outputs its public key
and an all-zero cache, and always takes 196282 cycles, 10815 calls and 11135 compressions.
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
    XSim image (kInit sk) (23 + sumTo (fun _ => 3668) (2 ^ 5)) (23 + sumTo (fun _ => 6107) (2 ^ 5))
      (sumTo (fun _ => 337) (2 ^ 5)) (sumTo (fun _ => 347) (2 ^ 5))
      (buildLeaves (toList sk) 0 0 5 0 [])
      (fun p u => LCtx (kW sk) (2 ^ 5) p.1 u ∧ u.pc = if 2 ^ 5 < 32 then pcOf 23 else pcOf 64) := by
  obtain ⟨t, hst, tpc, t8, t30, t9, t19, t17, t20, t5, t1728, t1736, t1744, t1752, t1696, t192,
    t832, tfr⟩ := spec_0 (kInit sk) (kInit_pc sk) (by rw [kInit_mem sk 1696 (by norm_num)]; rfl)
      (by rw [kInit_mem sk 192 (by norm_num)]; rfl)
  have zi : ∀ A < 2 ^ 64, (A < 128 ∨ 160 ≤ A) → (kInit sk).getMem (BitVec.ofNat 64 A) = 0 := by
    intro A hA h; rw [kInit_mem sk A hA, if_neg (by omega)]
  have hb : Base (kW sk) t := by
    refine ⟨by rw [t5, kInit_x5], t8, t30, t9, t19, ?_, ?_, t832, ?_⟩
    · intro k hk
      interval_cases k
      · exact t1728
      · exact t1736
      · exact t1744
      · exact t1752
    · intro A hA
      simp [zeroKeys] at hA
      rw [tfr A (by omega) (by simp; omega), zi A (by omega) (by omega)]
    · intro A h1 h2
      rw [tfr A (by omega) (by simp; omega), zi A (by omega) (by omega)]
  have h0 : LCtx (kW sk) 0 [] t := ⟨hb, t1696, t192, t17, t20, rfl, Vals.nil t TA⟩
  unfold buildLeaves
  refine XSim.steps hst (XSim.foldlM_range (2 ^ 5) _ ([], [])
    (fun e acc u => LCtx (kW sk) e acc.1 u ∧ u.pc = if e < 32 then pcOf 23 else pcOf 64)
    (fun _ => 3668) (fun _ => 6107) (fun _ => 337) (fun _ => 347)
    (fun e he acc u hu => leaf_xsim (kW sk) (toList sk) (kW_skOk sk) e (by norm_num at he; omega)
      acc u hu.1 (by rw [hu.2, if_pos (by norm_num at he; omega)])) ⟨h0, by rw [tpc]; rfl⟩)

/-- The tree levels, from the leaves in the tree array. -/
theorem levels_xsim (W : List Word) (leaves : List Val) (u : MachineState)
    (h : LCtx W 32 leaves u) (hpc : u.pc = pcOf 64) :
    XSim image u (1 + sumTo (fun k => 10 + 2 ^ (4 - k) * 18) 5)
      (1 + sumTo (fun k => 10 + 2 ^ (4 - k) * 25) 5) (sumTo (fun k => 2 ^ (4 - k)) 5)
      (sumTo (fun k => 2 ^ (4 - k)) 5)
      (buildLevels (nodeInput 0 0) 0 5 leaves)
      (fun r w => Base W w ∧ ValAt w TA r.1 ∧ r.1.length = 16 ∧ w.pc = pcOf 93) := by
  obtain ⟨v, vst, vpc, v15, vun, vfr⟩ := spec_64 u hpc
  have h0 : VCtx W 0 leaves v := by
    refine ⟨h.base.frame (fun r hr => vun r (by rcases hr with h | h | h | h | h <;> simp [h])) vfr
      (by simp), v15, ?_, by rw [h.len]; rfl, ?_⟩
    · rw [vun _ (by simp), h.r17]; rfl
    · exact ⟨h.lv.1, fun i hi => (h.lv.2 i hi).frame vfr (by rw [h.len] at hi; unfold TA; omega)
        (by simp)⟩
  unfold buildLevels
  refine (XSim.steps vst (XSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0)
    (XSim.foldlM_range' 1 5 _ (leaves, [])
      (fun k st w => VCtx W k st.1 w ∧ w.pc = if k < 5 then pcOf 65 else pcOf 93)
      (fun k => 10 + 2 ^ (4 - k) * 18) (fun k => 10 + 2 ^ (4 - k) * 25) (fun k => 2 ^ (4 - k))
      (fun k => 2 ^ (4 - k))
      (fun k hk st w hw => level_xsim W k hk st w hw.1 (by rw [hw.2, if_pos hk]))
      ⟨h0, by rw [vpc]; rfl⟩)
    (fun st w hw => XSim.pure ?_))).of_eq rfl rfl rfl rfl rfl
  obtain ⟨hc, hpc93⟩ := hw
  have hl1 : st.1.length = 1 := by rw [hc.len]; rfl
  have hv := hc.lv.2 0 (by omega)
  refine ⟨hc.base, by simpa using hv, hc.lv.1 _ ?_, by rw [hpc93]; rfl⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
  exact List.getElem_mem _

/-- The whole of `keygen`. -/
theorem keygen_xsim (sk : SecretKey) :
    XSim image (kInit sk) 118016 196281 10815 11135 (keygenRef sk)
      (fun pk t => fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
        readOutput submission.sizes submission.layout .keygen t = (pk, 0)) := by
  unfold keygenRef keygenList buildTree
  simp only [show height 0 = 5 from rfl]
  have htree : XSim image (kInit sk) 118008 196273 10815 11135
      (do
        let x ← buildLeaves (toList sk) 0 0 5 0 []
        let y ← buildLevels (nodeInput 0 0) 0 5 x.1
        pure (y.1, x.2, y.2))
      (fun r w => Base (kW sk) w ∧ ValAt w TA r.1 ∧ r.1.length = 16 ∧ w.pc = pcOf 93) := by
    refine (XSim.bind (k₂ := 1 + sumTo (fun k => 10 + 2 ^ (4 - k) * 18) 5)
      (c₂ := 1 + sumTo (fun k => 10 + 2 ^ (4 - k) * 25) 5) (n₂ := sumTo (fun k => 2 ^ (4 - k)) 5)
      (b₂ := sumTo (fun k => 2 ^ (4 - k)) 5) (leaves_xsim sk) (fun p u hu => ?_)).of_eq rfl
      (by decide) (by decide) (by decide) (by decide)
    refine (XSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0)
      (levels_xsim (kW sk) p.1 u hu.1 (by rw [hu.2]; rfl))
      (fun y w hw => XSim.pure (Q := fun (r : Val × List Val × List Val) w => Base (kW sk) w ∧
        ValAt w TA r.1 ∧ r.1.length = 16 ∧
        w.pc = pcOf 93) hw)).of_eq rfl (by simp) (by simp) (by simp) (by simp)
  refine (XSim.bind (k₂ := 8) (c₂ := 8) (n₂ := 0) (b₂ := 0)
    (XSim.bind (k₂ := 0) (c₂ := 0) (n₂ := 0) (b₂ := 0) htree
      (fun x w hw => XSim.pure (Q := fun r w => Base (kW sk) w ∧ ValAt w TA r ∧ r.length = 16 ∧
        w.pc = pcOf 93) hw))
    (fun root w hw => ?_)).of_eq rfl (by decide) (by decide) (by decide) (by decide)
  obtain ⟨hb, hv, hl, hpc⟩ := hw
  obtain ⟨t, tst, tpc, t5, t10, t160, t168, tfr⟩ := spec_93 w hpc
  refine XSim.pure_steps tst ⟨(codeAt_101.fetch t tpc).trans rfl, t5, t10, ?_⟩
  show (readBuffer t 160 16, readBuffer t 0x44A0 CACHE_BYTES) = (ofList 16 root, 0)
  rw [readBuffer_val t 160 root hl (by norm_num) (by norm_num) ⟨by rw [t160]; exact hv.1,
    by rw [t168]; exact hv.2⟩, readBuffer_cache t (fun A h1 h2 => by
      rw [tfr A (by omega) (by simp; omega)]; exact hb.cache A h1 h2)]

/-- **keygen**: for every secret key, one run makes exactly the oracle queries of
`keygenRef sk`, outputs its public key and an all-zero cache, and always takes 196282 cycles,
10815 calls and 11135 compressions. -/
theorem keygen_run (sk : SecretKey) :
    submission.run .keygen sk =
      (fun pk => ⟨some (pk, 0), true, 196282, 10815, 11135⟩) <$> keygenRef sk :=
  XSim.run_eq submission .keygen sk (kInit_eq sk) (keygen_xsim sk) (by decide) (fun pk => (pk, 0))
    (fun _ _ h => h)

/-- The reference makes exactly 10815 calls and 11135 compressions. -/
theorem keygenRef_counts (sk : SecretKey) :
    countCalls (keygenRef sk) = (fun a => (a, 10815)) <$> keygenRef sk ∧
      countBlocks (keygenRef sk) = (fun a => (a, 11135)) <$> keygenRef sk :=
  (keygen_xsim sk).count_eq

/-- The joint call / compression count of the reference is constant. -/
theorem keygenRef_countBoth (sk : SecretKey) :
    Sign.countBoth (keygenRef sk) = (fun a => (a, 10815, 11135)) <$> keygenRef sk :=
  (keygen_xsim sk).countBoth_eq

/-- Value, calls and compressions of the run = the reference's value with its joint
call / compression count. -/
theorem keygen_run_counts (sk : SecretKey) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .keygen sk =
      (fun p => (some (p.1, 0), p.2.1, p.2.2)) <$> Sign.countBoth (keygenRef sk) := by
  rw [keygen_run, keygenRef_countBoth, Functor.map_map, Functor.map_map]; rfl

/-- Fixed-oracle form: finished, exactly 196282 cycles (`< 2^32`), for every oracle. -/
theorem keygen_runWith (hash : Hash) (sk : SecretKey) :
    submission.runWith hash .keygen sk =
      ⟨some (evalWithAnswerFn hash (keygenRef sk), 0), true, 196282, 10815, 11135⟩ := by
  unfold Submission.runWith
  rw [keygen_run, evalWithAnswerFn_map]

end SigGolfCandidate.Keygen
