import SigGolfCandidate.Sign.Setup
import SigGolfCandidate.Sign.PorsTreeSim
import SigGolfCandidate.Sign.Entry

/-!
# `sign` refines `signRef` (main theorems)
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem decode_ecall : decodeInstruction 0x00000073#32 = some (.base .ECALL) := rfl

theorem fetch_ecall (t : MachineState) (i : Nat) (hi : image.code[i]? = some 0x00000073#32)
    (hlt : 0x1000 + 4 * i < 2 ^ 64) (hpc : t.pc = pcOf i) : fetch image t = some (.base .ECALL) := by
  unfold fetch
  rw [hpc]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [if_neg (by simp <;> omega), show (0x1000 + 4 * i - 0x1000) / 4 = i by omega, hi]
  exact decode_ecall

theorem code141 : image.code[141]? = some 0x00000073#32 := by decide +kernel
theorem code144 : image.code[144]? = some 0x00000073#32 := by decide +kernel
theorem code381 : image.code[381]? = some 0x00000073#32 := by decide +kernel
theorem code2843 : image.code[2843]? = some 0x00000073#32 := by decide +kernel

/-- `signList` after the MAC check. -/
def signRest (S cache m : List Byte) : OracleComp HashSpec (Option (List Byte)) :=
  searchDigest S m 0 (2 ^ 20 - 1 + 1) >>= fun r =>
    match r with
    | none => pure none
    | some (rho, N) =>
      buildPorsTree S (idxOf N) >>= fun p =>
        signLayers S cache (idxOf N) 4 ((p.1.getD porsH []).getD 0 []) >>= fun r2 =>
          match r2 with
          | none => pure none
          | some lays => pure (some (serialize rho (porsOpening (sortLeaves (leavesOf N)) p.1 p.2) lays))

theorem signList_eq (S cache m : List Byte) :
    signList S cache m = (H (macInput S (cacheRegion cache)) >>= fun tag =>
      if toList (n := 32) tag = cacheTag cache then signRest S cache m else pure none) := by
  simp only [signList, signRest]
  rfl

/-- Result of `signList`: at a HALT, `a0 = 1` (failure) or `a0 = 0` and the signature. -/
def ListPost (r : Option (List Byte)) (t : MachineState) : Prop :=
  fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
  match r with
  | none => t.getReg .x10 = 1
  | some l => t.getReg .x10 = 0 ∧ readBuffer t 0x3300 6100 = ofList 6100 l

/-- The zero buffers used as P slots / padding, never written by `sign` after the setup. -/
def ZA (a : Nat) : Prop :=
  (0x110 ≤ a ∧ a < 0x120) ∨ (0x6B0 ≤ a ∧ a < 0x6C0) ∨ (0xD0 ≤ a ∧ a < 0xE0) ∨
    (0x350 ≤ a ∧ a < 0x360) ∨ (0x1D0 ≤ a ∧ a < 0x1E0) ∨ (0xF0 ≤ a ∧ a < 0x100)

/-- The sorted keys give the sorted leaf indices, strictly increasing and `< 2^14`. -/
theorem keys_facts (N : Nat) (hadm : admissible N = true) :
    (sortKeys (keys0 N)).length = 15 ∧ ((sortKeys (keys0 N)).map keyV).Pairwise (· < ·) ∧
      (∀ v ∈ (sortKeys (keys0 N)).map keyV, v < 2 ^ 14) ∧ KeysBound (sortKeys (keys0 N)) ∧
      (sortKeys (keys0 N)).map keyV = sortLeaves (leavesOf N) := by
  have hl : (keys0 N).length = 15 := by simp [keys0]
  have hb : KeysBound (sortKeys (keys0 N)) :=
    keysBound_perm (keysBound_keys0 N) (sortKeys_perm _ hl (keys0_nodup N))
  have hvs := (sortLeaves_eq N).symm
  refine ⟨length_sortKeys _ hl, ?_, fun v hv => ?_, hb, hvs⟩
  · have hle : ((sortKeys (keys0 N)).map keyV).Pairwise (· ≤ ·) := by
      rw [hvs]; exact List.pairwise_insertionSort _ _
    have hnd : ((sortKeys (keys0 N)).map keyV).Nodup := by
      rw [hvs, sortLeaves, (List.perm_insertionSort _ _).nodup_iff]
      unfold admissible at hadm
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hadm
      exact hadm.1
    exact (hle.and hnd).imp (fun h => Nat.lt_of_le_of_ne h.1 h.2)
  · simp only [List.mem_map] at hv
    obtain ⟨k, hk, rfl⟩ := hv
    have := hb k hk; unfold keyV; omega

theorem sched_le (N : Nat) (hadm : admissible N = true) :
    (schedule (sortLeaves (leavesOf N))).2.length ≤ 120 := by
  obtain ⟨hl, hs, hlt, -, hvs⟩ := keys_facts N hadm
  rw [← hvs]
  refine SchedMath.schedule_reads_le _ (by rw [List.length_map, hl]) hs hlt ?_
  rw [hvs]
  unfold admissible at hadm
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hadm
  exact hadm.2

/-- Cycle bound after the MAC check. -/
def restW : Nat :=
  (2 ^ 20 - 1 + 1) * digCyc + 2 + (34 + ((2 ^ 13 * 79 + (1 + 14 * (4 + (2 ^ 13 * 26 + 4)))) +
    (11 + 15 * 345 + (20 + (4 * layCyc + topCyc + (2123 + 2))))))

/-- Cycle bound of `signList`. -/
def signW : Nat := 54 + (8 * 1025 + (10 + restW))

theorem region_s0 (sk : SecretKey) (cache : Cache) (m : Message) :
    RegionOk (toList cache) (s0 sk cache m) := by
  intro l j hl hj
  have := cacheNodeOff_lt l j hl hj
  have h8 : cacheNodeOff l j % 8 = 0 := by unfold cacheNodeOff; omega
  rw [s0_readWords_cache sk cache m _ 2 h8 (by omega)]; rfl

set_option maxRecDepth 100000 in
theorem signRest_sim (sk : SecretKey) (cache : Cache) (m : Message) (u : MachineState)
    (hu : MacOk sk cache m u) :
    Sim image u restW (signRest (toList sk) (toList cache) (toList m)) ListPost := by
  have hS : (toList sk).length = 32 := length_toList sk
  have hcache : (toList cache).length = 131072 := by simp [toList, SigGolfCandidate.Legacy.bytes]; rfl
  have dmem := hu.mem
  have u5 := hu.x5
  have u7 := hu.x7
  have dinv := hu.inv
  have upbS := hu.pbS
  have fs0 := hu.frame
  unfold signRest restW
  refine Sim.bind (digLoop_sim sk m u dmem u5 u7 (2 ^ 20 - 1) 0 u (by norm_num) dinv)
    (fun r t h => ?_)
  rcases r with _ | ⟨rho, N⟩
  · obtain ⟨tpc, t5, t10⟩ := h
    exact (Sim.pure ⟨fetch_ecall t 141 code141 (by norm_num) tpc, t5, t10⟩).mono (by omega)
      (fun _ _ h => h)
  obtain ⟨tpc, tregs, tframe, hrl, hrw, ⟨ans, hN, hdo⟩, hadm, hkeys, hsent⟩ := h
  subst hN
  set N := ans.toNat with hNdef
  set idx := idxOf N with hidxdef
  have hidx : idx < 2 ^ 34 := Nat.mod_lt _ (by norm_num)
  obtain ⟨hL, hsort, hlt, hbound, hvs⟩ := keys_facts N hadm
  have hR := sched_le N hadm
  set L := sortKeys (keys0 N) with hLdef
  -- the frame from the initial state to `t`
  have fst : Frame (s0 sk cache m) t (fun a => macW a ∨ digW a) := fs0.trans tframe
  have t5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by decide), u5]
  have z0 : ∀ a, a % 8 = 0 → ZA a → (s0 sk cache m).getMem (BitVec.ofNat 64 a) = 0 := by
    intro a h8 hz; simp only [ZA] at hz; exact s0_zero sk cache m a h8 (by omega) (by omega)
  have zt : ∀ a, a % 8 = 0 → ZA a → t.getMem (BitVec.ofNat 64 a) = 0 := by
    intro a h8 hz
    rw [fst.getMem (by simp only [ZA] at hz; omega)
      (by simp only [ZA] at hz; simp only [macW, setupW, digW, anW]; omega), z0 a h8 hz]
  have zrw : ∀ a, a % 8 = 0 → ZA a → ZA (a + 8) → t.readWords (BitVec.ofNat 64 a) 2 = [0, 0] := by
    intro a h8 h1 h2
    rw [readWords_ofNat_two, zt a h8 h1, zt (a + 8) (by omega) h2]
  have tS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf (toList sk) := by
    rw [tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW, anW]; omega), upbS]
  obtain ⟨tF, hsF, lctx, plctx, pcF, x9F, capF, x22F, sigF, rF, fF⟩ :=
    digok_run (toList sk) rho ans L t tpc t5 hdo hL hsort hlt hbound hkeys hsent
      (zrw _ (by norm_num) (by simp [ZA]) (by simp [ZA])) tS
      (zrw _ (by norm_num) (by simp [ZA]) (by simp [ZA])) (zrw _ (by norm_num) (by simp [ZA]) (by simp [ZA]))
      (zrw _ (by norm_num) (by simp [ZA]) (by simp [ZA]))
  refine Sim.steps hsF (Sim.bind (porsTree_sim (toList sk) hS idx L tF lctx plctx pcF x9F capF)
    (fun p t2 h2 => ?_))
  obtain ⟨pc2, x19_2, hl1, hlv, hl2, hv2, hsec2, r2, f2⟩ := h2
  -- the schedule
  have f02 : Frame t t2 (fun a => digokW a ∨ porsW a) := fF.trans f2
  have sctx : SchCtx p.1 L t2 := by
    refine ⟨hL, hsort, hlt, hbound, fun i hi => ?_, ?_, fun l hl => (hlv l hl).1, fun l hl => (hlv l hl).2.1,
      fun l hl => (hlv l hl).2.2⟩
    · rw [f02.getMem (by omega) (by simp only [digokW, porsW]; omega)]; exact hkeys i hi
    · rw [f02.getMem (by norm_num) (by simp only [digokW, porsW]; omega)]; exact hsent
  obtain ⟨k3, c3, t3, hs3, hc3, pc3, heb3, rd3, r3, f3⟩ := sched_run p.1 L t2 sctx pc2 x19_2
  rw [hvs] at rd3 f3
  -- the layer entry
  set M := (p.1.getD porsH []).getD 0 [] with hMdef
  have hM : M.length = 16 := by
    obtain ⟨a1, a2, -⟩ := hlv 14 (by norm_num)
    rw [hMdef, show porsH = 14 from rfl, getD_of_lt (by rw [a1]; norm_num)]
    exact a2 _ (List.getElem_mem _)
  have f03 : Frame t t3 (fun a => (digokW a ∨ porsW a) ∨ ((0x120 ≤ a ∧ a < 0x130) ∨
      schW' (schedule (sortLeaves (leavesOf N))).2.length a)) := f02.trans f3
  have fs3 : Frame (s0 sk cache m) t3 (fun a => (macW a ∨ digW a) ∨ ((digokW a ∨ porsW a) ∨ ((0x120 ≤ a ∧ a < 0x130) ∨
      schW' (schedule (sortLeaves (leavesOf N))).2.length a))) := fst.trans f03
  have hW3 : ∀ a, ((macW a ∨ digW a) ∨ ((digokW a ∨ porsW a) ∨ ((0x120 ≤ a ∧ a < 0x130) ∨
      schW' (schedule (sortLeaves (leavesOf N))).2.length a))) →
      a < 0x900 ∨ (0x3300 ≤ a ∧ a < 0x3400 + 16 * 120) ∨ 0x30000 ≤ a ∨ (0x4AE0 ≤ a ∧ a < 0x4B20) ∨
        (0x14B00 ≤ a ∧ a < 0x14B20) := by
    intro a ha
    simp only [macW, setupW, digW, anW, digokW, porsW, schW'] at ha
    omega
  have z3 : ∀ a, a % 8 = 0 → ZA a → t3.getMem (BitVec.ofNat 64 a) = 0 := by
    intro a h8 hz
    have hnw : ¬ ((macW a ∨ digW a) ∨ ((digokW a ∨ porsW a) ∨ ((0x120 ≤ a ∧ a < 0x130) ∨
        schW' (schedule (sortLeaves (leavesOf N))).2.length a))) := by
      simp only [ZA] at hz
      simp only [macW, setupW, digW, anW, digokW, porsW, schW']
      omega
    rw [fs3.getMem (by simp only [ZA] at hz; omega) hnw, z0 a h8 hz]
  have z3rw : ∀ a, a % 8 = 0 → ZA a → ZA (a + 8) → t3.readWords (BitVec.ofNat 64 a) 2 = [0, 0] := by
    intro a h8 h1 h2
    rw [readWords_ofNat_two, z3 a h8 h1, z3 (a + 8) (by omega) h2]
  have st3 : Statics (toList sk) t3 := by
    refine ⟨z3rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]), z3rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]),
      ?_, z3rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]), z3rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]),
      z3rw _ (by norm_num) (by simp [ZA]) (by simp [ZA])⟩
    rw [f03.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW, porsW, schW']; omega), tS]
  have rgW : ∀ a, regionA a → ¬ ((macW a ∨ digW a) ∨ ((digokW a ∨ porsW a) ∨ ((0x120 ≤ a ∧ a < 0x130) ∨
      schW' (schedule (sortLeaves (leavesOf N))).2.length a))) := by
    intro a ha
    simp only [regionA] at ha
    simp only [macW, setupW, digW, anW, digokW, porsW, schW']
    omega
  have rg3 : RegionOk (toList cache) t3 := (region_s0 sk cache m).frame fs3 rgW
  have x5_3 : t3.getReg .x5 = 0 := by rw [r3.get .x5, r2.get .x5 (by decide), rF.get .x5 (by decide), t5]
  have x22_3 : t3.getReg .x22 = BitVec.ofNat 64 idx := by
    rw [r3.get .x22, r2.get .x22 (by decide), x22F]
  obtain ⟨t4, hs4, hhead, m4, r4⟩ := layer_entry (toList sk) (toList cache) idx hidx M hM t3 pc3 x5_3 x22_3
    (by rw [heb3]; rfl) st3 rg3
  have rhoB : rho.length = 16 := hrl
  set vs := sortLeaves (leavesOf N) with hvsdef
  have hvsl : vs.length = 15 := by rw [← hvs, List.length_map, hL]
  refine (Sim.steps hs3 (Sim.steps hs4 (Sim.bind (W₂ := 2123 + 2)
    (layers_sim (toList sk) (toList cache) hS hcache idx hidx 4 le_rfl M t4 hhead)
    (fun r2 t5 h5 => ?_)))).mono (by generalize layCyc = A; generalize topCyc = B; omega) (fun _ _ h => h)
  rcases r2 with _ | lays
  · obtain ⟨pc5, x55, x510⟩ := h5
    exact (Sim.pure ⟨fetch_ecall t5 381 code381 (by norm_num) pc5, x55, x510⟩).mono (by omega)
      (fun _ _ h => h)
  obtain ⟨hll, hst, pc5, x55, lframe⟩ := h5
  obtain ⟨t6, hs6, pc6, hw6, hf6⟩ := pack_run t5 pc5
  rw [pack_full] at hw6
  have hf6' : Frame t5 t6 (fun x => packD ≤ x ∧ x < packD + 8 * 491) :=
    hf6.mono (fun x hx => by simp only [packD] at hx ⊢; omega)
  have hs7 := symRun_sound blk2841 codeAt_2841 t6 pc6 (by simp only [blk2841.res, rv_simp])
  set t7 := blk2841.res.toState t6 with ht7
  have hc7 : 2123 + blk2841.res.cycles = 2123 + 2 := rfl
  have mem7 : ∀ a, t7.getMem a = t6.getMem a := by
    intro a; rw [ht7, Result.toState_getMem, show blk2841.res.st.mem = [] from rfl, memEval_nil]
  have by7 : bytesAt t7 0x3300 6100 = bytesAt t6 0x3300 6100 := by
    unfold bytesAt; apply List.map_congr_left; intro i _
    simp only [MachineState.getByte, mem7]
  -- the frame from `t3` to `t5`
  have f35 : Frame t3 t5 (layW 4) := fun a ha hW => by rw [lframe a ha hW, m4]
  have nlay : ∀ a, 0x3300 ≤ a → a < 0x3300 + 2176 → ¬ layW 4 a := by
    intro a h1 h2; simp only [layW]; omega
  -- the head facts at `t5`
  have hrho5 : t5.readWords (BitVec.ofNat 64 0x3300) 2 = wordsOf rho := by
    rw [f35.readWords _ _ (by norm_num) (fun i hi => nlay _ (by omega) (by omega)),
      f3.readWords _ _ (by norm_num) (by intro i hi; simp only [schW']; omega),
      f2.readWords _ _ (by norm_num) (by intro i hi; simp only [porsW]; omega), sigF, hrw]
  have hsec5 : ∀ s < 15, t5.readWords (BitVec.ofNat 64 (0x3310 + 16 * s)) 2 =
      wordsOf (p.2.getD (vs.getD s 0) []) := by
    intro s hs
    rw [f35.readWords _ _ (by omega) (fun i hi => nlay _ (by omega) (by omega)),
      f3.readWords _ _ (by omega) (by intro i hi; simp only [schW']; omega), hsec2 s hs, hvs]
  have hrd5 : ∀ r (hr : r < (schedule vs).2.length), t5.readWords (BitVec.ofNat 64 (0x3400 + 16 * r)) 2 =
      wordsOf (readVal p.1 (schedule vs).2[r]) := by
    intro r hr
    rw [f35.readWords _ _ (by omega) (fun i hi => nlay _ (by omega) (by omega))]
    exact rd3.2.2.1 r hr
  have hz5 : ∀ i, (schedule vs).2.length ≤ i → i < 120 →
      t5.readWords (BitVec.ofNat 64 (0x3400 + 16 * i)) 2 = [0, 0] := by
    intro i h1 h2
    have hnw : ∀ k < 2, ¬ ((macW (0x3400 + 16 * i + 8 * k) ∨ digW (0x3400 + 16 * i + 8 * k)) ∨
        ((digokW (0x3400 + 16 * i + 8 * k) ∨ porsW (0x3400 + 16 * i + 8 * k)) ∨
        ((0x120 ≤ 0x3400 + 16 * i + 8 * k ∧ 0x3400 + 16 * i + 8 * k < 0x130) ∨
        schW' (schedule vs).2.length (0x3400 + 16 * i + 8 * k)))) := by
      intro k hk
      simp only [macW, setupW, digW, anW, digokW, porsW, schW']
      omega
    rw [f35.readWords _ _ (by omega) (fun k hk => nlay _ (by omega) (by omega)),
      fs3.readWords _ _ (by omega) hnw, readWords_ofNat_two,
      s0_zero sk cache m _ (by omega) (by omega) (by omega), s0_zero sk cache m _ (by omega) (by omega) (by omega)]
  have hslots := head_slots t5 rho vs p.1 p.2 hvsl hR hrho5 hsec5 hrd5 hz5
  have hvals : ∀ v ∈ porsOpening vs p.1 p.2, v.length = 16 := by
    refine length_porsOpening_vals vs p.1 p.2 hv2 (fun x hx => ?_) (fun hj hhj => ?_)
    · rw [hl2]; rw [← hvs] at hx; exact hlt x hx
    · obtain ⟨r, hr, rfl⟩ := List.getElem_of_mem hhj
      exact rd3.2.2.2 r hr
  have hhead5 := head_bytes t5 rho rhoB vs p.1 p.2 hvsl hR hvals hslots
  refine (Sim.pure_steps (hs6.trans hs7) ⟨fetch_ecall t7 2843 code2843 (by norm_num) (by
      simp only [ht7, blk2841.res, rv_simp]),
    by simp only [ht7, blk2841.res, rv_simp] <;> rfl, by simp only [ht7, blk2841.res, rv_simp] <;> rfl, ?_⟩).mono
    (by rw [hc7]) (fun _ _ h => h)
  rw [readBuffer_bytesAt, by7, final_bytes t5 rho (porsOpening vs p.1 p.2) lays hhead5 hll hst t6 hw6 hf6']

theorem signList_sim (sk : SecretKey) (cache : Cache) (m : Message) :
    Sim image (s0 sk cache m) signW (signList (toList sk) (toList cache) (toList m)) ListPost := by
  rw [signList_eq]
  exact mac_sim sk cache m _ restW ListPost (fun u hu => signRest_sim sk cache m u hu)
    (fun t tpc t5 t10 => ⟨fetch_ecall t 144 code144 (by norm_num) tpc, t5, t10⟩)


/-- Final states: at a HALT whose output is `signRef`'s value. -/
def SignPost (a : Option (Bytes 6100)) (t : MachineState) : Prop :=
  fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
  a = if t.getReg .x10 = 0 then some (readBuffer t 0x3300 6100) else none
set_option maxRecDepth 100000 in

theorem signRef_sim (sk : SecretKey) (cache : Cache) (m : Message) :
    Sim image (s0 sk cache m) signW (signRef sk cache m) SignPost := by
  unfold signRef
  refine (Sim.bind (signList_sim sk cache m) (fun r t h => Sim.pure ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  rcases r with _ | l
  · simp only at h3; rw [h3]; simp
  · obtain ⟨h4, h5⟩ := h3
    rw [h4, if_pos rfl, h5]; rfl

theorem signW_lt : signW + 1 < CYCLE_LIMIT := by
  unfold signW restW digCyc anCyc layCyc topCyc treeCyc tleafCyc CYCLE_LIMIT; norm_num

set_option maxRecDepth 100000 in
/-- **Refinement** (value, #hash calls, #compressions) of the `sign` phase. -/
theorem sign_refines (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .sign (sk, cache, m) =
      countBoth (signRef sk cache m) :=
  (Sim.run_eq submission .sign (sk, cache, m) (initialState_eq sk cache m) (signRef_sim sk cache m)
    (by have := signW_lt; omega) id (fun a t h => ⟨h.1, h.2.1, h.2.2⟩)).trans (id_map _)

set_option maxRecDepth 100000 in
/-- **Refinement** including `finished = true`. -/
theorem sign_refines_finished (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => (r.value, r.finished, r.hashCalls, r.hashCompressions)) <$>
        submission.run .sign (sk, cache, m) =
      (fun p => (p.1, true, p.2.1, p.2.2)) <$> countBoth (signRef sk cache m) :=
  Sim.run_eq_fin submission .sign (sk, cache, m) (initialState_eq sk cache m) (signRef_sim sk cache m)
    (by have := signW_lt; omega) id (fun a t h => ⟨h.1, h.2.1, h.2.2⟩)

set_option maxRecDepth 100000 in
/-- **Termination** of `sign` for every fixed oracle and input. -/
theorem sign_terminates (hash : Hash) (sk : SecretKey) (cache : Cache) (m : Message) :
    (submission.runWith hash .sign (sk, cache, m)).finished = true ∧
      (submission.runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT := by
  obtain ⟨h1, h2⟩ := Sim.runWith submission .sign (sk, cache, m) (initialState_eq sk cache m)
    (signRef_sim sk cache m) signW_lt (fun a t h => ⟨h.1, h.2.1⟩) hash
  exact ⟨h1, by have := signW_lt; omega⟩

theorem proj_map {α β γ : Type} (x : OracleComp HashSpec α) (y : OracleComp HashSpec β) (g : α → β)
    (f : β → γ) (h : g <$> x = y) : (fun r => f (g r)) <$> x = f <$> y := by
  subst h; rw [Functor.map_map]

set_option maxRecDepth 100000 in
/-- Calls and compressions separately (`countCalls`, `countBlocks` of `Ref.Count`). -/
theorem sign_calls (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => (r.value, r.hashCalls)) <$> submission.run .sign (sk, cache, m) =
      countCalls (signRef sk cache m) := by
  rw [← countBoth_calls]; exact proj_map _ _ _ (fun p => (p.1, p.2.1)) (sign_refines sk cache m)

set_option maxRecDepth 100000 in
theorem sign_blocks (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => (r.value, r.hashCompressions)) <$> submission.run .sign (sk, cache, m) =
      countBlocks (signRef sk cache m) := by
  rw [← countBoth_blocks]; exact proj_map _ _ _ (fun p => (p.1, p.2.2)) (sign_refines sk cache m)

end SigGolfCandidate.Sign
