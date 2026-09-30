import SigGolfCandidate.Sign.Digest
import SigGolfCandidate.Sign.Mac

/-!
# `sign`: setup and the cache MAC check (instructions 0 .. 64)

* block 0 (0 .. 53): `S`, `m` into the buffers, the tag (cache bytes 0 .. 32) into `x13 .. x16`,
  the in-place MAC input `tw_mac | P | S | region | 0^32` at `CACHE - 32`; HASH at 54.
* 55 .. 62: compare the answer (`DO`) with the tag, dword by dword (`fail_mac` at 84 .. 86).
* 63 .. 64: `LIM = 2^20`, `CNT = 0`; the digest loop starts at 65.

`mac_sim` : the machine refines `H(macInput S region) >>= fun tag => if tag = cacheTag then rest
else pure none`, given a simulation of `rest` from the digest loop.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

-- Memory / register effect of the setup block (kernel-checked with a variable state).
kernel_theorem blk0_pbS : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x6C0) 4 = t.readWords (BitVec.ofNat 64 0x80) 4
kernel_theorem blk0_rbS : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x640) 4 = t.readWords (BitVec.ofNat 64 0x80) 4
kernel_theorem blk0_rbM : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x660) 4 = t.readWords (BitVec.ofNat 64 0x40) 4
kernel_theorem blk0_macS : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x44A0) 4 = t.readWords (BitVec.ofNat 64 0x80) 4
kernel_theorem blk0_db0 : ∀ t : MachineState,
    (blk0.res.toState t).getMem (BitVec.ofNat 64 0) = BitVec.ofNat 64 0xC01
kernel_theorem blk0_mac0 : ∀ t : MachineState,
    (blk0.res.toState t).getMem (BitVec.ofNat 64 0x4480) = BitVec.ofNat 64 0xE01
kernel_theorem blk0_macZ : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x144A0) 4 = [0, 0, 0, 0]
kernel_theorem blk0_tag : ∀ t : MachineState,
    [(blk0.res.toState t).getReg .x13, (blk0.res.toState t).getReg .x14,
      (blk0.res.toState t).getReg .x15, (blk0.res.toState t).getReg .x16] =
    t.readWords (BitVec.ofNat 64 0x44A0) 4
theorem blk0_rb0 (t : MachineState) :
    lo32 ((blk0.res.toState t).getMem (BitVec.ofNat 64 0x620)) = BitVec.ofNat 32 0x701 := by
  simp (config := { decide := true }) only [blk0.res, rv_simp, lo32_replace0, Nat.zero_div, ↓reduceIte]

/-- Addresses written by the setup block. -/
def setupW (a : Nat) : Prop :=
  a = 0 ∨ a = 0x620 ∨ (0x640 ≤ a ∧ a < 0x680) ∨ (0x6C0 ≤ a ∧ a < 0x6E0) ∨ a = 0x4480 ∨
    (0x44A0 ≤ a ∧ a < 0x44C0) ∨ (0x144A0 ≤ a ∧ a < 0x144C0)

/-- Addresses written up to the digest loop (setup, the MAC answer). -/
def macW (a : Nat) : Prop := setupW a ∨ (0x160 ≤ a ∧ a < 0x180)

/-- Facts at the start of the digest loop. -/
structure MacOk (sk : SecretKey) (cache : Cache) (m : Message) (u : MachineState) : Prop where
  pc : u.pc = pcOf 65
  mem : DigMem (toList sk) (toList m) u
  x5 : u.getReg .x5 = 0
  x6 : u.getReg .x6 = 0
  x7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20)
  pbS : u.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf (toList sk)
  frame : Frame (s0 sk cache m) u macW

theorem MacOk.inv {sk : SecretKey} {cache : Cache} {m : Message} {u : MachineState}
    (h : MacOk sk cache m u) : DigInv u 0 u :=
  ⟨h.pc, by rw [h.x6]; rfl, by norm_num, RegsEq.refl _ _, Frame.refl _ _, rfl⟩

theorem length_cacheRegion (cache : Cache) : (cacheRegion (toList cache)).length = 65504 := by
  have hlen : (toList cache).length = 131072 := by simp [toList, SigGolf.bytes]; rfl
  simp [cacheRegion, slice, hlen, regionBytes]; decide

theorem length_cacheTag (cache : Cache) : (cacheTag (toList cache)).length = 32 := by
  have hlen : (toList cache).length = 131072 := by simp [toList, SigGolf.bytes]; rfl
  simp [cacheTag, slice, hlen]

/-- A compare block `ld ra, D; bne ra, aK, fail`. -/
theorem cmp_block {r : Result} {code : List (BitVec 32)} {a b : Nat} (hrun : symRun { noAlias := true } code (pcOf a) 3 = some r)
    (hcode : CodeAt image (pcOf a) code) (hobl : r.st.obl = []) (hc : r.cycles = 2) (hk : r.steps = 2)
    (t : MachineState) (hpc : t.pc = pcOf a) (x y : Word)
    (hpc' : (r.toState t).pc = if x = y then pcOf (a + 2) else pcOf b)
    (hmem : r.st.mem = []) (hregs : RegsEq t (r.toState t) [.x1]) :
    Steps image t 2 2 (r.toState t) ∧ (r.toState t).pc = (if x = y then pcOf (a + 2) else pcOf b) ∧
      (∀ z, (r.toState t).getMem z = t.getMem z) ∧ RegsEq t (r.toState t) [.x1] := by
  have hs := symRun_sound hrun hcode t hpc (by simp only [Result.obligs, hobl, Oblig.all])
  rw [hc, hk] at hs
  refine ⟨hs, hpc', fun z => ?_, hregs⟩
  rw [Result.toState_getMem, hmem, memEval_nil]

kernel_theorem blk55_pc : ∀ t : MachineState, (blk55.res.toState t).pc =
    if (t.getMem (BitVec.ofNat 64 0x160) != t.getReg .x13) = true then pcOf 84 else pcOf 57
kernel_theorem blk57_pc : ∀ t : MachineState, (blk57.res.toState t).pc =
    if (t.getMem (BitVec.ofNat 64 0x168) != t.getReg .x14) = true then pcOf 84 else pcOf 59
kernel_theorem blk59_pc : ∀ t : MachineState, (blk59.res.toState t).pc =
    if (t.getMem (BitVec.ofNat 64 0x170) != t.getReg .x15) = true then pcOf 84 else pcOf 61
kernel_theorem blk61_pc : ∀ t : MachineState, (blk61.res.toState t).pc =
    if (t.getMem (BitVec.ofNat 64 0x178) != t.getReg .x16) = true then pcOf 84 else pcOf 63

/-- A compare block `ld ra, D(x0); bne ra, R, fail_mac`. -/
theorem blk_cmp {code : List (BitVec 32)} {a : Nat} {r : Result} {P : MachineState → Word}
    (hrun : symRun { noAlias := true } code (pcOf a) 3 = some r) (hcode : CodeAt image (pcOf a) code)
    (hobl : r.st.obl = []) (hc : r.cycles = 2) (hk : r.steps = 2) (hmem : r.st.mem = [])
    (hpc : ∀ t : MachineState, (r.toState t).pc = P t) (hregs : ∀ t : MachineState, RegsEq t (r.toState t) [.x1])
    (t : MachineState) (tpc : t.pc = pcOf a) :
    Steps image t 2 2 (r.toState t) ∧ (r.toState t).pc = P t ∧
      (∀ z, (r.toState t).getMem z = t.getMem z) ∧ RegsEq t (r.toState t) [.x1] := by
  have hs := symRun_sound hrun hcode t tpc (by simp only [Result.obligs, hobl, Oblig.all])
  rw [hc, hk] at hs
  exact ⟨hs, hpc t, fun z => by rw [Result.toState_getMem, hmem, memEval_nil], hregs t⟩

theorem setup_frame (t : MachineState) : Frame t (blk0.res.toState t) setupW := by
  apply frame_toState; intro x hx hW
  simp only [blk0.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true, ne_eq, ofNat_eq_iff]
  simp only [setupW] at hW
  omega

theorem setup_regs (t : MachineState) :
    RegsEq t (blk0.res.toState t) [.x1, .x3, .x10, .x11, .x12, .x13, .x14, .x15, .x16, .x29] := by
  intro r hr; rw [Result.toState_getReg]
  cases r <;> first | exact absurd (by decide) hr | rfl

/-- **The MAC check.** -/
theorem mac_sim (sk : SecretKey) (cache : Cache) (m : Message) {β : Type}
    (rest : OracleComp HashSpec (Option β)) (Wr : Nat) (Q : Option β → MachineState → Prop)
    (hrest : ∀ u, MacOk sk cache m u → Sim image u Wr rest Q)
    (hbad : ∀ t, t.pc = pcOf 86 → t.getReg .x5 = 1 → t.getReg .x10 = 1 → Q none t) :
    Sim image (s0 sk cache m) (54 + (8 * 1025 + (10 + Wr)))
      (H (macInput (toList sk) (cacheRegion (toList cache))) >>= fun tag =>
        if toList (n := 32) tag = cacheTag (toList cache) then rest else pure none) Q := by
  set s := s0 sk cache m with hs0
  have hS : (toList sk).length = 32 := length_toList sk
  have hs := symRun_sound blk0 codeAt_0 s (s0_pc sk cache m) (by simp only [blk0.res, rv_simp])
  have hk : blk0.res.cycles = 54 := rfl
  have hk' : blk0.res.steps = 54 := rfl
  rw [hk, hk'] at hs
  set u := blk0.res.toState s with hu
  have f := setup_frame s
  have rg := setup_regs s
  have e1 := symRun_ecall blk0 codeAt_0 s (by simp only [blk0.res, rv_simp]) rfl
  have x5 : u.getReg .x5 = 0 := by rw [rg.get .x5]; exact s0_getReg sk cache m .x5 (by decide)
  have x10 : u.getReg .x10 = BitVec.ofNat 64 0x4480 := by simp only [hu, blk0.res, rv_simp]
  have x11 : u.getReg .x11 = BitVec.ofNat 64 65600 := by simp only [hu, blk0.res, rv_simp]
  have x12 : u.getReg .x12 = BitVec.ofNat 64 0x160 := by simp only [hu, blk0.res, rv_simp]
  have pc1 : u.pc = pcOf 54 := by simp only [hu, blk0.res, rv_simp]
  have hR := length_cacheRegion cache
  obtain ⟨hn, hw⟩ := words_macInput (toList sk) (cacheRegion (toList cache)) hS hR
  have hq : hashInput u = pad64 (macInput (toList sk) (cacheRegion (toList cache))) := by
    refine hashInput_eq_pad64 u _ 1024 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (1024 + 1) = 1 + 1 + 2 + 4 + 8188 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add,
      readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, hu, blk0_mac0, ← hu,
      f.getMem (a := 0x4488) (by norm_num) (by simp only [setupW]; omega),
      s0_zero sk cache m 0x4488 (by norm_num) (by norm_num) (by omega),
      f.readWords _ _ (by norm_num) (by intro i hi; simp only [setupW]; omega),
      show (0x4490 : Nat) = 0x4490 from rfl, readWords_ofNat_two,
      s0_zero sk cache m 0x4490 (by norm_num) (by norm_num) (by omega),
      s0_zero sk cache m 0x4498 (by norm_num) (by norm_num) (by omega),
      hu, blk0_macS, blk0_macZ, ← hu,
      f.readWords _ _ (by norm_num) (by intro i hi; simp only [setupW]; omega),
      show (0x44C0 : Nat) = 0x44A0 + 32 from rfl, s0_readWords_cache sk cache m 32 8188 (by norm_num) (by norm_num),
      s0_readWords_sk]
    simp only [twWords_eq, twWord0, List.cons_append, List.nil_append, List.append_assoc]
    rfl
  have hb : (pad64 (macInput (toList sk) (cacheRegion (toList cache)))).blocks = 1025 := by
    simp [pad64, Query.blocks, hn]
  have hq' : hashInput u = fmt (macInput (toList sk) (cacheRegion (toList cache))) :=
    hq.trans (fmt_thInput _ _ _ _ _ _ (by decide)).symm
  refine (Sim.steps hs (Sim.query_bind (W := 10 + Wr) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq' (fun a => ?_))).mono (by rw [blocks_fmt, hb]) (fun _ _ h => h)
  set t2 := writeHash u a with ht2
  have pc2 : t2.pc = pcOf 55 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have f2 : Frame u t2 (fun x => 0x160 ≤ x ∧ x < 0x160 + 32) := frame_writeHash u a _ x12 (by norm_num)
  have wd : ∀ k, k < 4 → t2.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = a.extractLsb' (64 * k) 64 := by
    intro k hk
    rw [ht2, writeHash_getMem_ofNat u a 0x160 _ x12 (by norm_num) (by omega)]
    interval_cases k <;> simp
  have r2 : ∀ r, t2.getReg r = u.getReg r := fun r => by rw [ht2, writeHash_getReg]
  -- the tag words
  have htag := blk0_tag s
  rw [← hu, show (0x44A0 : Nat) = 0x44A0 + 0 from rfl, s0_readWords_cache sk cache m 0 4 (by norm_num)
    (by norm_num)] at htag
  have hct : slice (toList cache) 0 (8 * 4) = cacheTag (toList cache) := rfl
  rw [hct] at htag
  have heq := tag_eq_iff a _ (length_cacheTag cache) _ _ _ _ htag.symm
  -- the failure exit
  have fail : ∀ t, t.pc = pcOf 84 → Sim image t 2 (pure none) Q := by
    intro t tpc
    have hs84 := symRun_sound blk84 codeAt_84 t tpc (by simp only [blk84.res, rv_simp])
    have hc84 : blk84.res.cycles = 2 := rfl
    rw [hc84] at hs84
    exact Sim.pure_steps hs84 (hbad _ (by simp only [blk84.res, rv_simp]) (by simp only [blk84.res, rv_simp])
      (by simp only [blk84.res, rv_simp]))
  obtain ⟨e0, e1, e2, e3⟩ : t2.getMem (BitVec.ofNat 64 0x160) = a.extractLsb' 0 64 ∧
      t2.getMem (BitVec.ofNat 64 0x168) = a.extractLsb' 64 64 ∧
      t2.getMem (BitVec.ofNat 64 0x170) = a.extractLsb' 128 64 ∧
      t2.getMem (BitVec.ofNat 64 0x178) = a.extractLsb' 192 64 :=
    ⟨wd 0 (by norm_num), wd 1 (by norm_num), wd 2 (by norm_num), wd 3 (by norm_num)⟩
  -- the compare chain
  obtain ⟨hs3, pc3, m3, r3⟩ := blk_cmp blk55 codeAt_55 rfl rfl rfl rfl blk55_pc (fun t r hr => by
    rw [Result.toState_getReg]; cases r <;> first | exact absurd (by decide) hr | rfl) t2 pc2
  set t3 := blk55.res.toState t2
  rw [e0, r2] at pc3
  by_cases h0 : a.extractLsb' 0 64 = u.getReg .x13
  swap
  · rw [if_neg (fun h => h0 (heq.mp h).1)]
    exact (Sim.steps hs3 (fail t3 (by rw [pc3, if_pos (by simpa using h0)]))).mono (by omega) (fun _ _ h => h)
  obtain ⟨hs4, pc4, m4, r4⟩ := blk_cmp blk57 codeAt_57 rfl rfl rfl rfl blk57_pc (fun t r hr => by
    rw [Result.toState_getReg]; cases r <;> first | exact absurd (by decide) hr | rfl) t3
    (by rw [pc3, if_neg (by simp [h0])])
  set t4 := blk57.res.toState t3
  rw [m3, e1, r3.get .x14, r2] at pc4
  by_cases h1 : a.extractLsb' 64 64 = u.getReg .x14
  swap
  · rw [if_neg (fun h => h1 (heq.mp h).2.1)]
    exact (Sim.steps hs3 (Sim.steps hs4 (fail t4 (by rw [pc4, if_pos (by simpa using h1)])))).mono
      (by omega) (fun _ _ h => h)
  obtain ⟨hs5, pc5, m5, r5⟩ := blk_cmp blk59 codeAt_59 rfl rfl rfl rfl blk59_pc (fun t r hr => by
    rw [Result.toState_getReg]; cases r <;> first | exact absurd (by decide) hr | rfl) t4
    (by rw [pc4, if_neg (by simp [h1])])
  set t5 := blk59.res.toState t4
  rw [m4, m3, e2, r4.get .x15, r3.get .x15, r2] at pc5
  by_cases h2 : a.extractLsb' 128 64 = u.getReg .x15
  swap
  · rw [if_neg (fun h => h2 (heq.mp h).2.2.1)]
    exact (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 (fail t5 (by rw [pc5, if_pos (by simpa using h2)]))))).mono
      (by omega) (fun _ _ h => h)
  obtain ⟨hs6, pc6, m6, r6⟩ := blk_cmp blk61 codeAt_61 rfl rfl rfl rfl blk61_pc (fun t r hr => by
    rw [Result.toState_getReg]; cases r <;> first | exact absurd (by decide) hr | rfl) t5
    (by rw [pc5, if_neg (by simp [h2])])
  set t6 := blk61.res.toState t5
  rw [m5, m4, m3, e3, r5.get .x16, r4.get .x16, r3.get .x16, r2] at pc6
  by_cases h3 : a.extractLsb' 192 64 = u.getReg .x16
  swap
  · rw [if_neg (fun h => h3 (heq.mp h).2.2.2)]
    exact (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 (Sim.steps hs6 (fail t6
      (by rw [pc6, if_pos (by simpa using h3)])))))).mono (by omega) (fun _ _ h => h)
  rw [if_pos (heq.mpr ⟨h0, h1, h2, h3⟩)]
  have hs7 := symRun_sound blk63 codeAt_63 t6 (by rw [pc6, if_neg (by simp [h3])])
    (by simp only [blk63.res, rv_simp])
  have hc7 : blk63.res.cycles = 2 := rfl
  rw [hc7] at hs7
  set t7 := blk63.res.toState t6 with ht7
  have n7 : ∀ z, t7.getMem z = t2.getMem z := fun z => by
    rw [ht7, Result.toState_getMem, show blk63.res.st.mem = [] from rfl, memEval_nil, m6, m5, m4, m3]
  have r7 : RegsEq t6 t7 [.x6, .x7] := by
    intro r hr; rw [ht7, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have g7 : ∀ q, q ≠ .x1 → q ≠ .x6 → q ≠ .x7 → t7.getReg q = u.getReg q := by
    intro q h1 h6 h7
    rw [r7.get q (by simp [h6, h7]), r6.get q (by simp [h1]), r5.get q (by simp [h1]),
      r4.get q (by simp [h1]), r3.get q (by simp [h1]), r2]
  have fr : Frame s t7 macW := by
    intro x hx hW
    rw [n7, f2.getMem hx (by simp only [macW, setupW] at hW; omega),
      f.getMem hx (by simp only [macW, setupW] at hW ⊢; omega)]
  have fu : ∀ a n, a + 8 * n < 2 ^ 64 → (∀ i < n, ¬ macW (a + 8 * i)) →
      t7.readWords (BitVec.ofNat 64 a) n = s.readWords (BitVec.ofNat 64 a) n :=
    fun a n h1 h2 => fr.readWords a n h1 h2
  have fu7 : ∀ a n, a + 8 * n < 2 ^ 64 → (∀ i < n, ¬ (0x160 ≤ a + 8 * i ∧ a + 8 * i < 0x180)) →
      t7.readWords (BitVec.ofNat 64 a) n = u.readWords (BitVec.ofNat 64 a) n := by
    intro a n h1 h2
    exact readWords_congr _ _ a n (fun i hi => by rw [n7, f2.getMem (by omega) (by have := h2 i hi; omega)])
  have hz : ∀ a n, a % 8 = 0 → a + 8 * n + 8 < 2 ^ 64 →
      (∀ i < n, a + 8 * i + 8 ≤ 0x40 ∨ (0x60 ≤ a + 8 * i ∧ a + 8 * i + 8 ≤ 0x80) ∨
        (0xA0 ≤ a + 8 * i ∧ a + 8 * i + 8 ≤ 0x44A0) ∨ 0x244A0 ≤ a + 8 * i) →
      s.readWords (BitVec.ofNat 64 a) n = List.replicate n 0 := by
    intro a n h8 hb hout
    induction n generalizing a with
    | zero => rfl
    | succ n ih =>
      rw [readWords_ofNat_succ, s0_zero sk cache m a h8 (by omega) (by simpa using hout 0 (by omega)),
        ih (a + 8) (by omega) (by omega)
          (fun i hi => by rw [show a + 8 + 8 * i = a + 8 * (i + 1) by ring]; exact hout _ (by omega))]
      rfl
  have ok : MacOk sk cache m t7 := by
    refine ⟨by simp only [ht7, blk63.res, rv_simp], ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, fr⟩
    · rw [fu7 _ _ (by norm_num) (by intro i hi; omega), hu, blk0_rbS, s0_readWords_sk]
    · rw [fu7 _ _ (by norm_num) (by intro i hi; omega), hu, blk0_rbM, s0_readWords_msg]
    · rw [fu _ _ (by norm_num) (by intro i hi; simp only [macW, setupW]; omega),
        hz _ _ (by norm_num) (by norm_num) (by intro i hi; omega)]; rfl
    · rw [fu _ _ (by norm_num) (by intro i hi; simp only [macW, setupW]; omega),
        hz _ _ (by norm_num) (by norm_num) (by intro i hi; omega)]; rfl
    · rw [n7, f2.getMem (by norm_num) (by omega), hu, blk0_rb0]
    · rw [readWords_ofNat_succ, n7, f2.getMem (by norm_num) (by omega), hu, blk0_db0,
        fu _ _ (by norm_num) (by intro i hi; simp only [macW, setupW]; omega),
        hz _ _ (by norm_num) (by norm_num) (by intro i hi; omega)]; rfl
    · rw [fu _ _ (by norm_num) (by intro i hi; simp only [macW, setupW]; omega), s0_readWords_msg]
    · rw [fu _ _ (by norm_num) (by intro i hi; simp only [macW, setupW]; omega),
        hz _ _ (by norm_num) (by norm_num) (by intro i hi; omega)]; rfl
    · rw [g7 .x5 (by decide) (by decide) (by decide), x5]
    · simp only [ht7, blk63.res, rv_simp]
    · simp only [ht7, blk63.res, rv_simp]; rfl
    · rw [fu7 _ _ (by norm_num) (by intro i hi; omega), hu, blk0_pbS, s0_readWords_sk]
  exact (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 (Sim.steps hs6 (Sim.steps hs7
    (hrest t7 ok)))))).mono (by omega) (fun _ _ h => h)

end SigGolfCandidate.Sign
