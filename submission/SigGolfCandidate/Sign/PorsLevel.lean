import SigGolfCandidate.Sign.PorsLeaf
import SigGolfCandidate.Sign.TreeBuildNode

/-!
# `sign`, the PORS levels (`por_level_loop`, instructions 210 .. 237)

Level `l` (`2^(14 - l)` nodes) is stored at `lvBase l = FA_END - 16 * 2^(15 - l)`
(`FA_END = 0xB0000`), right after level `l - 1`. The node loop (`node_hash` with a separate
destination `DST = x25`) is `nodeD_spec` / `nodeLoopD_sim`; `porsLevels_sim` refines
`buildAllLevels (porsNodeFmt idx) 14 leaves`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- `node_hash` with the destination in `x25` (`add a2, s9, gp`). -/
def nodeSegD : List (BitVec 32) := [0x01180133#32, 0x1c202623#32, 0x00581193#32, 0x013181b3#32, 0x0001b083#32,
  0x1e103023#32, 0x0081b083#32, 0x1e103423#32, 0x0101b083#32, 0x1e103823#32, 0x0181b083#32,
  0x1e103c23#32, 0x1c000513#32, 0x04000593#32, 0x00481193#32, 0x003c8633#32, 0x00000073#32]

theorem seg215_eq : seg215 = nodeSegD := rfl
theorem seg232_eq : seg232 = nodeSegB := rfl
theorem codeAt_nodeD : CodeAt image (pcOf 215) nodeSegD := seg215_eq ▸ codeAt_215
theorem codeAt_nodeD2 : CodeAt image (pcOf (215 + 17)) nodeSegB := seg232_eq ▸ codeAt_232

theorem nodeD_spec (s : MachineState) (hpc : s.pc = pcOf 215) (j m B D : Nat)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 m) (hjm : j + m < 2 ^ 32)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 B) (h25 : s.getReg .x25 = BitVec.ofNat 64 D)
    (hB : 0x210 ≤ B) (hB8 : B % 8 = 0) (hjB : B + 32 * j + 32 ≤ 2 ^ 24) (hD8 : D % 8 = 0)
    (hjD : D + 16 * j + 32 ≤ 2 ^ 24) :
    ∃ t, Steps image s 16 16 t ∧ fetch image t = some (.base .ECALL) ∧ t.pc = pcOf 231 ∧
      t.getReg .x10 = BitVec.ofNat 64 448 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (D + 16 * j) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      ∀ a : Nat, a < 2 ^ 64 → t.getMem (BitVec.ofNat 64 a) =
        if a = 504 then s.getMem (BitVec.ofNat 64 (B + 32 * j + 24))
        else if a = 496 then s.getMem (BitVec.ofNat 64 (B + 32 * j + 16))
        else if a = 488 then s.getMem (BitVec.ofNat 64 (B + 32 * j + 8))
        else if a = 480 then s.getMem (BitVec.ofNat 64 (B + 32 * j))
        else if a = 456 then replaceWord32 (s.getMem (BitVec.ofNat 64 456)) 1 (BitVec.ofNat 32 (j + m))
        else s.getMem (BitVec.ofNat 64 a) := by
  have hobl : blk215.res.obligs s := by
    simp only [blk215.res, rv_simp, h16, h19, ofNat_shiftLeft, ofNat_add_ofNat,
      ne_eq, ofNat_eq_iff, accessValid_ofNat, BitVec.toNat_ofNat]
    norm_num
    omega
  refine ⟨_, symRun_sound blk215 codeAt_215 s hpc hobl, symRun_ecall blk215 codeAt_215 s hobl rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [blk215.res, rv_simp]
  · simp only [blk215.res, rv_simp]
  · simp only [blk215.res, rv_simp]
  · simp only [blk215.res, rv_simp, h16, h25, ofNat_shiftLeft, ofNat_add_ofNat,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    congr 1; ring
  · intro r h1 h2 h3 h10 h11 h12
    cases r <;> (try contradiction) <;> simp only [blk215.res, rv_simp] <;> rfl
  · intro a ha
    simp only [blk215.res, rv_simp, h16, h17, h19, ofNat_shiftLeft, ofNat_add_ofNat,
      ofNat_eq_iff, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, truncate32_ofNat]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega)

/-- Parameters of a node loop with a separate destination. -/
structure NodeCtxD where
  tt : Nat
  lay : Nat
  tau : Nat
  lam : Nat
  B : Nat
  D : Nat
  m : Nat

/-- Memory frame of the node loop: outside the destination `[D, D + 16 m + 16)` and the `NB`
dwords nothing changes. -/
def NodeFrameD (c : NodeCtxD) (s t : MachineState) : Prop :=
  (∀ a : Nat, a < 2 ^ 64 → (a < c.D ∨ c.D + 16 * c.m + 16 ≤ a) → a ≠ 456 → a ≠ 480 → a ≠ 488 → a ≠ 496 →
    a ≠ 504 → t.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 456)) = lo32 (s.getMem (BitVec.ofNat 64 456))

/-- Loop invariant after `j` nodes. -/
def NodeInvD (c : NodeCtxD) (lvl : List Val) (s : MachineState) (j : Nat) (acc : List Val)
    (t : MachineState) : Prop :=
  j ≤ c.m ∧ acc.length = j ∧ (∀ v ∈ acc, v.length = 16) ∧
  (∀ i (hi : i < acc.length), t.readWords (BitVec.ofNat 64 (c.D + 16 * i)) 2 = wordsOf acc[i]) ∧
  (∀ i (hi : i < lvl.length), t.readWords (BitVec.ofNat 64 (c.B + 16 * i)) 2 = wordsOf lvl[i]) ∧
  t.pc = (if j < c.m then pcOf 215 else pcOf 234) ∧
  t.getReg .x16 = BitVec.ofNat 64 j ∧ NodeRegs s t ∧ NodeFrameD c s t

/-- **Node loop** (separate destination): `m` nodes of level `lam` from the `2m` values `lvl` in
slots `B + 16 i`; the results land in slots `D + 16 j`; `26 m` cycles. -/
theorem nodeLoopD_sim (node : NodeFmt) (c : NodeCtxD) (lvl : List Val)
    (hlen : lvl.length = 2 * c.m) (hvals : ∀ v ∈ lvl, v.length = 16) (hm : 0 < c.m)
    (hB0 : 0x210 ≤ c.B) (hB8 : c.B % 8 = 0) (hBD : c.B + 32 * c.m ≤ c.D) (hD8 : c.D % 8 = 0)
    (hDm : c.D + 16 * c.m + 32 ≤ 2 ^ 24)
    (s : MachineState) (hpc : s.pc = pcOf 215) (h16 : s.getReg .x16 = 0)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c.m) (h19 : s.getReg .x19 = BitVec.ofNat 64 c.B)
    (h25 : s.getReg .x25 = BitVec.ofNat 64 c.D)
    (h5 : s.getReg .x5 = 0) (hm32 : 2 * c.m < 2 ^ 32)
    (hfmt : ∀ j l r, j < c.m → l.length = 16 → r.length = 16 →
      fmt (node c.lam j l r) = pad64 (nodeFmt c.tt c.lay c.tau 0 (c.m + j) l r))
    (hw0 : s.getMem (BitVec.ofNat 64 448) = twWord0 c.tt c.lay c.tau 0)
    (hw1 : lo32 (s.getMem (BitVec.ofNat 64 456)) = BitVec.ofNat 32 c.tau)
    (hz0 : s.getMem (BitVec.ofNat 64 464) = 0) (hz1 : s.getMem (BitVec.ofNat 64 472) = 0)
    (hslots : ∀ i (hi : i < lvl.length), s.readWords (BitVec.ofNat 64 (c.B + 16 * i)) 2 = wordsOf lvl[i]) :
    Sim image s (c.m * 26) (buildLevel node c.lam lvl) (NodeInvD c lvl s c.m) := by
  unfold buildLevel
  rw [hlen, show 2 * c.m / 2 = c.m by omega]
  apply Sim.foldlM_range c.m _ [] (NodeInvD c lvl s) 26
  · intro j hj acc t ⟨hjm, hacc, haccv, hslot, hlvl, tpc, t16, tregs, tframe⟩
    have t19 : t.getReg .x19 = BitVec.ofNat 64 c.B := by rw [tregs .x19 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), h19]
    have t25 : t.getReg .x25 = BitVec.ofNat 64 c.D := by rw [tregs .x25 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), h25]
    have t17 : t.getReg .x17 = BitVec.ofNat 64 c.m := by rw [tregs .x17 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), h17]
    have t5 : t.getReg .x5 = 0 := by rw [tregs .x5 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide), h5]
    obtain ⟨t1, st1, f1, pc1, a10, a11, a12, regs1, mem1⟩ :=
      nodeD_spec t (by rw [tpc, if_pos hj]) j c.m c.B c.D t16 t17 (by omega) t19 t25 hB0 hB8 (by omega)
        hD8 (by omega)
    have hl : (lvl.getD (2 * j) []).length = 16 := by
      rw [getD_of_lt (by omega)]; exact hvals _ (List.getElem_mem _)
    have hr : (lvl.getD (2 * j + 1) []).length = 16 := by
      rw [getD_of_lt (by omega)]; exact hvals _ (List.getElem_mem _)
    have hmemT : ∀ a : Nat, a < 2 ^ 64 → c.B ≤ a → t1.getMem (BitVec.ofNat 64 a) = t.getMem (BitVec.ofNat 64 a) := by
      intro a ha hBa
      rw [mem1 a ha, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    have hq : hashInput t1 = pad64 (nodeFmt c.tt c.lay c.tau 0 (c.m + j) (lvl.getD (2 * j) [])
        (lvl.getD (2 * j + 1) [])) := by
      apply node_hashInput t1 _ _ _ _ _ _ _ hl hr (by rw [a10]) (by rw [a11])
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
        rw [tframe.1 448 (by norm_num) (by omega) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), hw0]
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
          if_neg (by norm_num), if_pos rfl]
        exact word_of_halves _ c.tau (c.m + j) (by rw [lo32_replace1, tframe.2, hw1])
          (by rw [hi32_replace1, Nat.add_comm])
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
        rw [tframe.1 464 (by norm_num) (by omega) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), hz0]
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
        rw [tframe.1 472 (by norm_num) (by omega) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), hz1]
      · rw [readWords_ofNat_two, mem1 _ (by norm_num), mem1 _ (by norm_num), getD_of_lt (by omega),
          ← hlvl (2 * j) (by omega), readWords_ofNat_two]
        simp; constructor <;> congr 2 <;> omega
      · rw [readWords_ofNat_two, mem1 _ (by norm_num), mem1 _ (by norm_num), getD_of_lt (by omega),
          ← hlvl (2 * j + 1) (by omega), readWords_ofNat_two]
        simp; constructor <;> congr 2 <;> omega
    have := Sim.steps st1 (Sim.hash16_bindF (f := fun v => pure (acc ++ [v])) (W := 2) (Q := NodeInvD c lvl s (j + 1)) f1
      (by rw [regs1 .x5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t5])
      (hashArgs_of a10 a11 a12 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by omega))
      (hq.trans (hfmt j _ _ hj hl hr).symm) (fun a => by
        obtain ⟨t3, st3, pc3, x16', regs3, mem3⟩ := nodeB_spec (L := 215) codeAt_nodeD2 (writeHash t1 a)
          (by rw [writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp) j c.m
          (by rw [writeHash_getReg, regs1 .x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t16])
          (by rw [writeHash_getReg, regs1 .x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), t17])
          (by omega) (by omega)
        apply Sim.pure_steps st3
        have hwf : ∀ x : Nat, x < 2 ^ 64 → (x < c.D + 16 * j ∨ c.D + 16 * j + 32 ≤ x) →
            t3.getMem (BitVec.ofNat 64 x) = t1.getMem (BitVec.ofNat 64 x) := by
          intro x hx hout
          rw [mem3, writeHash_getMem_frame t1 a (c.D + 16 * j) x a12 (by omega) hx (by omega)]
        refine ⟨by omega, by simp [hacc], ?_, ?_, ?_, ?_, x16', ?_, ?_, ?_⟩
        · intro v hv; rcases List.mem_append.mp hv with hv | hv
          · exact haccv v hv
          · simp at hv; subst hv; simp
        · intro i hi
          simp only [List.length_append, List.length_singleton] at hi
          rw [readWords_ofNat_two]
          by_cases hij : i < acc.length
          · rw [List.getElem_append_left hij, ← hslot i hij, readWords_ofNat_two,
              hwf _ (by omega) (by omega), hwf _ (by omega) (by omega), hmemT _ (by omega) (by omega),
              hmemT _ (by omega) (by omega)]
          · have hij' : i = acc.length := by omega
            subst hij'
            rw [List.getElem_append_right (le_refl _)]
            simp only [Nat.sub_self, List.getElem_singleton]
            rw [← writeHash_readWords_val t1 a (c.D + 16 * acc.length) (by rw [a12, hacc]) (by omega),
              readWords_ofNat_two, mem3, mem3, hacc]
        · intro i hi
          rw [readWords_ofNat_two, hwf _ (by omega) (by omega), hwf _ (by omega) (by omega),
            hmemT _ (by omega) (by omega), hmemT _ (by omega) (by omega), ← readWords_ofNat_two]
          exact hlvl i hi
        · rw [pc3]; by_cases h : j + 1 = c.m
          · simp [h]
          · rw [if_neg h, if_pos (by omega)]
        · intro r h1 h2 h3 h10 h11 h12 h16'
          rw [regs3 r h16', writeHash_getReg, regs1 r h1 h2 h3 h10 h11 h12, tregs r h1 h2 h3 h10 h11 h12 h16']
        · intro x hx hout n1 n2 n3 n4 n5
          rw [hwf x hx (by omega), mem1 x hx, if_neg n5, if_neg n4, if_neg n3, if_neg n2, if_neg n1]
          exact tframe.1 x hx hout n1 n2 n3 n4 n5
        · rw [hwf 456 (by norm_num) (by omega), mem1 456 (by norm_num)]
          simp only [show ¬ ((456 : Nat) = 504) by norm_num, show ¬ ((456 : Nat) = 496) by norm_num,
            show ¬ ((456 : Nat) = 488) by norm_num, show ¬ ((456 : Nat) = 480) by norm_num, if_false,
            if_true, lo32_replace1]
          exact tframe.2))
    refine this.mono ?_ (fun _ _ h => h)
    rw [hfmt j _ _ hj hl hr, nodeFmt, pad64_blocks_one _ (words_th32 c.tt c.lay c.tau 0 (c.m + j) _ _ hl hr).1]
  · refine ⟨Nat.zero_le _, rfl, by simp, by simp, fun i hi => hslots i hi, by simp [hpc, hm],
      by simpa using h16, fun r _ _ _ _ _ _ _ => rfl, fun a _ _ _ _ _ _ _ => rfl, rfl⟩

/-! ## The level loop -/

/-- Base of PORS level `l`: `FA_END - 16 * 2^(15 - l)`. -/
def lvBase (l : Nat) : Nat := 0xB0000 - 16 * 2 ^ (15 - l)

theorem lvBase_succ (j : Nat) (hj : j < 15) : lvBase j + 16 * 2 ^ (14 - j) = lvBase (j + 1) := by
  unfold lvBase
  have h1 : 2 ^ (15 - j) = 2 * 2 ^ (14 - j) := by rw [← Nat.pow_succ']; congr 1; omega
  have h2 : 15 - (j + 1) = 14 - j := by omega
  rw [h1, h2]
  have : 2 ^ (14 - j) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem lvBase_ge (l : Nat) : 0x30000 ≤ lvBase l := by
  unfold lvBase
  have : 2 ^ (15 - l) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem lvBase_le (l : Nat) (hl : l ≤ 14) : lvBase l + 16 * 2 ^ (14 - l) + 16 ≤ 0xB0000 := by
  unfold lvBase
  have h1 : 2 ^ (15 - l) = 2 * 2 ^ (14 - l) := by rw [← Nat.pow_succ']; congr 1; omega
  have : 1 ≤ 2 ^ (14 - l) := Nat.one_le_two_pow
  have : 2 ^ (14 - l) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem lvBase_mono' {a b : Nat} (h : a ≤ b) (hb : b ≤ 15) : lvBase a ≤ lvBase b := by
  unfold lvBase
  have : 2 ^ (15 - b) ≤ 2 ^ (15 - a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ (15 - a) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

theorem lvBase_mono {a b : Nat} (h : a ≤ b) (hb : b ≤ 15) : lvBase a + 16 * 2 ^ (15 - b) ≤ lvBase b + 16 * 2 ^ (15 - a) := by
  unfold lvBase
  have : 2 ^ (15 - b) ≤ 2 ^ (15 - a) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 2 ^ (15 - a) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- Facts at the start of the level loop. -/
structure PLevCtx (idx : Nat) (t0 : MachineState) : Prop where
  x5 : t0.getReg .x5 = 0
  nb0 : t0.getMem (BitVec.ofNat 64 448) = twWord0 10 0 idx 0
  nb8 : lo32 (t0.getMem (BitVec.ofNat 64 456)) = BitVec.ofNat 32 idx
  nbP : t0.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0]

def plevW (a : Nat) : Prop :=
  a = 456 ∨ a = 480 ∨ a = 488 ∨ a = 496 ∨ a = 504 ∨ (lvBase 1 ≤ a ∧ a < 0xB0000)

def plevRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x15, .x16, .x17, .x19, .x25]

/-- Invariant after `j` levels (`levels` = levels `0 .. j`). -/
def PLevInv (t0 : MachineState) (j : Nat) (levels : List (List Val)) (t : MachineState) : Prop :=
  j ≤ 14 ∧ levels.length = j + 1 ∧
  (∀ l (hl : l < levels.length), levels[l].length = 2 ^ (14 - l) ∧ (∀ v ∈ levels[l], v.length = 16) ∧
    Slots t (lvBase l) levels[l]) ∧
  t.pc = (if j < 14 then pcOf 211 else pcOf 238) ∧ t.getReg .x15 = BitVec.ofNat 64 (j + 1) ∧
  t.getReg .x17 = BitVec.ofNat 64 (2 ^ (14 - j)) ∧ t.getReg .x19 = BitVec.ofNat 64 (lvBase j) ∧
  RegsEq t0 t plevRegs ∧ Frame t0 t plevW ∧
  lo32 (t.getMem (BitVec.ofNat 64 456)) = lo32 (t0.getMem (BitVec.ofNat 64 456))

theorem getD_levels {levels : List (List Val)} {j : Nat} (h : j < levels.length) :
    levels.getD j [] = levels[j] := getD_of_lt h

theorem plev_body (idx : Nat) (t0 : MachineState) (ctx : PLevCtx idx t0) (j : Nat) (hj : j < 14)
    (levels : List (List Val)) (t : MachineState) (h : PLevInv t0 j levels t) :
    Sim image t (4 + (2 ^ 13 * 26 + 4))
      (buildLevel (porsNodeFmt idx) (1 + j) (levels.getD (1 + j - 1) []) >>= fun level =>
        pure (levels ++ [level])) (PLevInv t0 (j + 1)) := by
  obtain ⟨-, hlen, hlv, tpc, t15, t17, t19, tregs, tframe, tlo⟩ := h
  rw [if_pos hj] at tpc
  rw [show 1 + j - 1 = j by omega, getD_levels (by omega)]
  obtain ⟨hl0, hv0, hs0⟩ := hlv j (by omega)
  have hm1 : 1 ≤ 2 ^ (13 - j) := Nat.one_le_two_pow
  have hm2 : 2 ^ (13 - j) ≤ 2 ^ 13 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmm : 2 ^ (14 - j) = 2 * 2 ^ (13 - j) := by rw [← Nat.pow_succ']; congr 1; omega
  -- block 211
  have hs1 := symRun_sound blk211 codeAt_211 t tpc (by simp only [blk211.res, rv_simp])
  set t1 := blk211.res.toState t with ht1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk211.res.st.mem = [] from rfl, memEval_nil]
  have r1 : RegsEq t t1 [.x3, .x16, .x17, .x25] := by
    intro q hq; rw [ht1, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have x25 : t1.getReg .x25 = BitVec.ofNat 64 (lvBase (j + 1)) := by
    simp only [ht1, blk211.res, rv_simp, t19, t17]; bvsimp []
    rw [← lvBase_succ j (by omega)]; exact ofNat_congr (by ring)
  have x17 : t1.getReg .x17 = BitVec.ofNat 64 (2 ^ (13 - j)) := by
    simp only [ht1, blk211.res, rv_simp, t17]; bvsimp []
    rw [hmm]; exact ofNat_congr (by omega)
  have x16 : t1.getReg .x16 = 0 := by simp only [ht1, blk211.res, rv_simp] <;> rfl
  have pc1 : t1.pc = pcOf 215 := by simp only [ht1, blk211.res, rv_simp]
  have hc1 : blk211.res.cycles = 4 := rfl
  rw [hc1] at hs1
  let c : NodeCtxD := ⟨10, 0, idx, 1 + j, lvBase j, lvBase (j + 1), 2 ^ (13 - j)⟩
  have hbase := lvBase_succ j (by omega)
  have hge := lvBase_ge j
  have hle := lvBase_le (j + 1) (by omega)
  rw [show 14 - (j + 1) = 13 - j by omega] at hle
  have hnode := nodeLoopD_sim (porsNodeFmt idx) c levels[j] (by simp only [c]; rw [hl0, hmm]) hv0
    hm1 (by simp only [c]; omega) (by simp only [c]; unfold lvBase; omega) (by simp only [c]; omega)
    (by simp only [c]; unfold lvBase; omega) (by simp only [c]; omega)
    t1 pc1 x16 x17 (by rw [r1.get .x19, t19]) x25
    (by rw [r1.get .x5, tregs.get .x5 (by simp [plevRegs]), ctx.x5]) (by simp only [c]; omega)
    (fun jj l r hjj hl hr => by
      simp only [c, porsNodeFmt, porsNodeInput, heapIndex, porsH, nodeFmt]
      rw [fmt_thInput _ _ _ _ _ _ (by decide), show 14 - (1 + j) = 13 - j by omega])
    (by simp only [c]; rw [m1, tframe.getMem (by norm_num) (by simp only [plevW, lvBase]; omega), ctx.nb0])
    (by simp only [c]; rw [m1, tlo, ctx.nb8])
    (by rw [m1, tframe.getMem (by norm_num) (by simp only [plevW, lvBase]; omega)]
        exact (getMem_of_readWords t0 2 0x1D0 0 _ ctx.nbP (by norm_num)))
    (by rw [m1, tframe.getMem (by norm_num) (by simp only [plevW, lvBase]; omega)]
        exact (getMem_of_readWords t0 2 0x1D0 1 _ ctx.nbP (by norm_num)))
    (fun i hi => by
      rw [show c.B = lvBase j from rfl, readWords_congr t t1 _ 2 (fun k _ => m1 _)]; exact hs0 i hi)
  refine (Sim.steps hs1 (Sim.bind (W₂ := 4) hnode (fun level t2 h2 => ?_))).mono (by
    have : c.m * 26 ≤ 2 ^ 13 * 26 := by simp only [c]; omega
    omega) (fun _ _ h => h)
  obtain ⟨-, hlev, hlevv, hacc, hsrc, pc2, -, regs2, fr2⟩ := h2
  simp only [c, show (if 2 ^ (13 - j) < 2 ^ (13 - j) then pcOf 215 else pcOf 234) = pcOf 234 by simp] at pc2
  have hs3 := symRun_sound blk234 codeAt_234 t2 pc2 (by simp only [blk234.res, rv_simp])
  have hc3 : blk234.res.cycles = 4 := rfl
  rw [hc3] at hs3
  set t3 := blk234.res.toState t2 with ht3
  have m3 : ∀ z, t3.getMem z = t2.getMem z := fun z => by
    rw [ht3, Result.toState_getMem, show blk234.res.st.mem = [] from rfl, memEval_nil]
  have r3 : RegsEq t2 t3 [.x3, .x15, .x19] := by
    intro q hq; rw [ht3, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have rg2 := regs2.toRegsEq
  have t215 : t2.getReg .x15 = BitVec.ofNat 64 (j + 1) := by rw [rg2.get .x15, r1.get .x15, t15]
  have t225 : t2.getReg .x25 = BitVec.ofNat 64 (lvBase (j + 1)) := by rw [rg2.get .x25, x25]
  have t217 : t2.getReg .x17 = BitVec.ofNat 64 (2 ^ (13 - j)) := by rw [rg2.get .x17, x17]
  refine Sim.pure_steps hs3 ⟨by omega, by simp [hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l hl
    simp only [List.length_append, List.length_singleton] at hl
    rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | hl
    · rw [List.getElem_append_left (by omega)]
      obtain ⟨a1, a2, a3⟩ := hlv l (by omega)
      refine ⟨a1, a2, fun i hi => ?_⟩
      have hb2 : lvBase l + 16 * 2 ^ (14 - l) ≤ lvBase (j + 1) := by
        rw [lvBase_succ l (by omega)]; exact lvBase_mono' (by omega) (by omega)
      have hge := lvBase_ge l
      have hi' := hi
      rw [a1] at hi'
      rw [readWords_congr t t3 _ 2 (fun k hk => by
        rw [m3, fr2.1 _ (by omega) (by simp only [c]; omega) (by omega) (by omega) (by omega) (by omega)
          (by omega), m1])]
      exact a3 i hi
    · subst hl
      rw [List.getElem_append_right (by omega)]
      simp only [hlen, Nat.sub_self, List.getElem_singleton]
      refine ⟨by rw [hlev, show 14 - (j + 1) = 13 - j by omega], hlevv, fun i hi => ?_⟩
      rw [readWords_congr t2 t3 _ 2 (fun k _ => m3 _)]
      exact hacc i hi
  · simp only [ht3, blk234.res, rv_simp, t215, ofNat_add_ofNat, ofNat_bne_ofNat]
    by_cases h : j + 1 < 14
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · simp only [ht3, blk234.res, rv_simp, t215, ofNat_add_ofNat]
  · rw [r3.get .x17, t217, show 14 - (j + 1) = 13 - j by omega]
  · simp only [ht3, blk234.res, rv_simp, t225]
  · exact (((tregs.trans r1).trans rg2).trans r3).mono (by decide)
  · intro a ha hW
    rw [m3]
    by_cases hin : lvBase (j + 1) ≤ a ∧ a < lvBase (j + 1) + 16 * 2 ^ (13 - j) + 16
    · exfalso; apply hW; simp only [plevW]; right; right; right; right; right
      have := lvBase_mono (show 1 ≤ j + 1 by omega) (by omega)
      have : 2 ^ (15 - (j + 1)) ≤ 2 ^ (15 - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      unfold lvBase at *; omega
    · simp only [plevW, not_or] at hW
      rw [fr2.1 a ha (by simp only [c]; omega) hW.1 hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2.1, m1,
        tframe a ha (by simp only [plevW]; omega)]
  · rw [m3, fr2.2, m1, tlo]

/-- **PORS levels** `1 .. 14`. -/
theorem porsLevels_sim (idx : Nat) (t0 : MachineState) (ctx : PLevCtx idx t0) (leaves : List Val)
    (hlen : leaves.length = 2 ^ 14) (hvals : ∀ v ∈ leaves, v.length = 16)
    (hslots : Slots t0 (lvBase 0) leaves) (hpc : t0.pc = pcOf 211)
    (h15 : t0.getReg .x15 = BitVec.ofNat 64 1) (h17 : t0.getReg .x17 = BitVec.ofNat 64 (2 ^ 14))
    (h19 : t0.getReg .x19 = BitVec.ofNat 64 (lvBase 0)) :
    Sim image t0 (14 * (4 + (2 ^ 13 * 26 + 4))) (buildAllLevels (porsNodeFmt idx) porsH leaves)
      (PLevInv t0 14) := by
  unfold buildAllLevels porsH
  apply Sim.foldlM_range' 1 14 _ [leaves] (PLevInv t0) _ (fun j hj acc t h => plev_body idx t0 ctx j hj acc t h)
  refine ⟨by omega, rfl, fun l hl => ?_, by simpa using hpc, h15, h17, h19, RegsEq.refl _ _,
    Frame.refl _ _, rfl⟩
  simp at hl; subst hl
  exact ⟨hlen, hvals, hslots⟩

end SigGolfCandidate.Sign
