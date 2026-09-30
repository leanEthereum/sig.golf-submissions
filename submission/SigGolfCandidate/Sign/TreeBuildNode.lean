import SigGolfCandidate.Sign.Inv

/-!
# The node loop (`node_hash`), shared by sign (FORS, tree_build) and keygen (tree_build)

Code (identical words wherever it occurs; relocatable):
```
L: sw a6,460(x0); slli gp,a6,5; add gp,gp,s3; ld/sd ×4 (FA[2JJ],FA[2JJ+1] → NB+32..64);
   addi a0,x0,448; addi a1,x0,64; slli gp,a6,4; add a2,s3,gp; ecall      -- nodeSegA (16 words)
   addi a6,a6,1; bne a6,a7,L                                             -- nodeSegB (2 words)
```
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def nodeSegA : List (BitVec 32) := [0x1d002623#32, 0x00581193#32, 0x013181b3#32, 0x0001b083#32,
  0x1e103023#32, 0x0081b083#32, 0x1e103423#32, 0x0101b083#32, 0x1e103823#32, 0x0181b083#32,
  0x1e103c23#32, 0x1c000513#32, 0x04000593#32, 0x00481193#32, 0x00398633#32, 0x00000073#32]
def nodeSegB : List (BitVec 32) := [0x00180813#32, 0xfb181ee3#32]

sym_block nodeA0 := symRun { noAlias := true } nodeSegA 0x1000 17
sym_block nodeB0 := symRun { noAlias := true } nodeSegB 0x1000 3

def nodeARes (pc : Word) : Result := { nodeA0.res with pc := .c (addN pc 15) }
def nodeBRes (pc : Word) : Result :=
  { nodeB0.res with pc := retarget nodeB0.res.pc (addN pc 1 + 0xffffffffffffffbc#64) (addN pc 1 + 4) }

kernel_theorem nodeA_run : ∀ pc : Word, symRun { noAlias := true } nodeSegA pc 17 = some (nodeARes pc)
kernel_theorem nodeB_run : ∀ pc : Word, symRun { noAlias := true } nodeSegB pc 3 = some (nodeBRes pc)

theorem nodeA_spec {image : Image} {P : Nat} (hcode : CodeAt image (pcOf P) nodeSegA)
    (s : MachineState) (hpc : s.pc = pcOf P) (j B : Nat) (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 B) (hB : 0x210 ≤ B) (hB8 : B % 8 = 0)
    (hjB : B + 32 * j + 32 ≤ 2 ^ 24) :
    ∃ t, Steps image s 15 15 t ∧ fetch image t = some (.base .ECALL) ∧ t.pc = pcOf (P + 15) ∧
      t.getReg .x10 = BitVec.ofNat 64 448 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (B + 16 * j) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      ∀ a : Nat, a < 2 ^ 64 → t.getMem (BitVec.ofNat 64 a) =
        if a = 504 then s.getMem (BitVec.ofNat 64 (B + 32 * j + 24))
        else if a = 496 then s.getMem (BitVec.ofNat 64 (B + 32 * j + 16))
        else if a = 488 then s.getMem (BitVec.ofNat 64 (B + 32 * j + 8))
        else if a = 480 then s.getMem (BitVec.ofNat 64 (B + 32 * j))
        else if a = 456 then replaceWord32 (s.getMem (BitVec.ofNat 64 456)) 1 (BitVec.ofNat 32 j)
        else s.getMem (BitVec.ofNat 64 a) := by
  have hobl : (nodeARes (pcOf P)).obligs s := by
    simp only [nodeARes, nodeA0.res, rv_simp, h16, h19, ofNat_shiftLeft, ofNat_add_ofNat,
      ne_eq, ofNat_eq_iff, accessValid_ofNat, BitVec.toNat_ofNat]
    norm_num
    omega
  refine ⟨_, symRun_sound (nodeA_run _) hcode s hpc hobl, symRun_ecall (nodeA_run _) hcode s hobl rfl,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [nodeARes, nodeA0.res, rv_simp, addN_pcOf]
  · simp only [nodeARes, nodeA0.res, rv_simp]
  · simp only [nodeARes, nodeA0.res, rv_simp]
  · simp only [nodeARes, nodeA0.res, rv_simp, h16, h19, ofNat_shiftLeft, ofNat_add_ofNat,
      BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
    congr 1; ring
  · intro r h1 h3 h10 h11 h12
    cases r <;> (try contradiction) <;> simp only [nodeARes, nodeA0.res, rv_simp] <;> rfl
  · intro a ha
    simp only [nodeARes, nodeA0.res, rv_simp, h16, h19, ofNat_shiftLeft, ofNat_add_ofNat,
      ofNat_eq_iff, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow, truncate32_ofNat]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega)

/-- Block B at index `L + 16` (loop head `L`): `JJ += 1`, back to `L` unless `JJ = NCNT`. -/
theorem nodeB_spec {image : Image} {L : Nat} (hcode : CodeAt image (pcOf (L + 16)) nodeSegB)
    (s : MachineState) (hpc : s.pc = pcOf (L + 16)) (j m : Nat) (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 m) (hj : j + 1 < 2 ^ 64) (hm : m < 2 ^ 64) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = (if j + 1 = m then pcOf (L + 18) else pcOf L) ∧
      t.getReg .x16 = BitVec.ofNat 64 (j + 1) ∧
      (∀ r, r ≠ .x16 → t.getReg r = s.getReg r) ∧ (∀ a, t.getMem a = s.getMem a) := by
  have hobl : (nodeBRes (pcOf (L + 16))).obligs s := by
    simp only [nodeBRes, nodeB0.res, rv_simp]
  refine ⟨_, symRun_sound (nodeB_run _) hcode s hpc hobl, ?_, ?_, ?_, ?_⟩
  · simp only [nodeBRes, nodeB0.res, retarget, rv_simp, addN_pcOf, h16, h17, ofNat_add_ofNat,
      ofNat_bne_ofNat]
    by_cases h : j + 1 = m
    · subst h; simp only [if_true]; apply BitVec.eq_of_toNat_eq; simp; omega
    · rw [if_neg h]
      simp only [show ¬ ((j + 1) % 2 ^ 64 = m % 2 ^ 64) by omega, decide_false, Bool.not_false,
        if_true]
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega
  · simp only [nodeBRes, nodeB0.res, rv_simp, h16, ofNat_add_ofNat]
  · intro r h
    cases r <;> (try contradiction) <;> simp only [nodeBRes, nodeB0.res, rv_simp] <;> rfl
  · intro a; simp only [nodeBRes, nodeB0.res, rv_simp]

/-- Tree / FORS node format `tw(tt, lay, tau, lam, j) | P | l | r`. -/
def nodeFmt (tt lay tau : Nat) : NodeFmt := fun lam j l r => thInput (tweak tt lay tau lam j) (l ++ r)

theorem nodeInput_eq (lay tau : Nat) : nodeInput lay tau = nodeFmt 3 lay tau := rfl
theorem ftsNodeInput_eq (k idx : Nat) : ftsNodeInput k idx = nodeFmt 10 k idx := rfl

/-- The node-loop state facts (`NB` buffer, registers) at iteration `j`. -/
structure NodeCtx where
  tt : Nat
  lay : Nat
  tau : Nat
  lam : Nat
  B : Nat
  m : Nat

/-- Memory frame of the node loop: outside the array prefix `[B, B + 32 m)` and the `NB` dwords
`456, 480, 488, 496, 504` nothing changes. -/
def NodeFrame (c : NodeCtx) (s t : MachineState) : Prop :=
  (∀ a : Nat, a < 2 ^ 64 → (a < c.B ∨ c.B + 32 * c.m ≤ a) → a ≠ 456 → a ≠ 480 → a ≠ 488 → a ≠ 496 →
    a ≠ 504 → t.getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 456)) = lo32 (s.getMem (BitVec.ofNat 64 456))

/-- Registers clobbered by the node loop. -/
def NodeRegs (s t : MachineState) : Prop :=
  ∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x16 → t.getReg r = s.getReg r

/-- Loop invariant after `j` nodes. -/
def NodeInv (c : NodeCtx) (L : Nat) (lvl : List Val) (s : MachineState) (j : Nat) (acc : List Val)
    (t : MachineState) : Prop :=
  j ≤ c.m ∧ acc.length = j ∧ (∀ v ∈ acc, v.length = 16) ∧
  (∀ i (hi : i < acc.length), t.readWords (BitVec.ofNat 64 (c.B + 16 * i)) 2 = wordsOf acc[i]) ∧
  (∀ i (hi : i < lvl.length), 2 * j ≤ i →
    t.readWords (BitVec.ofNat 64 (c.B + 16 * i)) 2 = wordsOf lvl[i]) ∧
  t.pc = (if j < c.m then pcOf L else pcOf (L + 18)) ∧
  t.getReg .x16 = BitVec.ofNat 64 j ∧ NodeRegs s t ∧ NodeFrame c s t

theorem getD_of_lt {α : Type} {l : List α} {i : Nat} {d : α} (h : i < l.length) :
    l.getD i d = l[i] := by
  simp [List.getD, List.getElem?_eq_getElem h]

theorem pad64_blocks_one (x : List Byte) (h : padBlocks x.length = 0) : (pad64 x).blocks = 1 := by
  simp [pad64, Query.blocks, h]

/-- The HASH input of the node buffer `NB = 448`. -/
theorem node_hashInput (t : MachineState) (tt lay tau lam j : Nat) (l r : Val) (hl : l.length = 16)
    (hr : r.length = 16) (h10 : t.getReg .x10 = BitVec.ofNat 64 448)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hw0 : t.getMem (BitVec.ofNat 64 448) = twWord0 tt lay tau lam)
    (hw1 : t.getMem (BitVec.ofNat 64 456) = BitVec.ofNat 64 (tau % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32)))
    (hz0 : t.getMem (BitVec.ofNat 64 464) = 0) (hz1 : t.getMem (BitVec.ofNat 64 472) = 0)
    (hL : t.readWords (BitVec.ofNat 64 480) 2 = wordsOf l)
    (hR : t.readWords (BitVec.ofNat 64 496) 2 = wordsOf r) :
    hashInput t = pad64 (nodeFmt tt lay tau lam j l r) := by
  obtain ⟨hn, hw⟩ := words_th32 tt lay tau lam j l r hl hr
  refine hashInput_eq_pad64 t _ 0 hn (by rw [h11]) (by norm_num) (by rw [h10]; decide) ?_
  rw [nodeFmt, hw, h10, twWords_eq, ← hL, ← hR,
    show 8 * (0 + 1) = 4 + 2 + 2 from rfl, readWords_ofNat_add, readWords_ofNat_add]
  simp only [readWords_ofNat_succ, hw0, hw1, hz0, hz1]
  rfl

/-- **Node loop**: `m` nodes of level `lam` from the `2m` values `lvl` in slots `B + 16 i`;
the results land in slots `0 .. m-1`; `25 m` cycles. -/
theorem nodeLoop_sim {image : Image} {L : Nat} (hA : CodeAt image (pcOf L) nodeSegA)
    (hB : CodeAt image (pcOf (L + 16)) nodeSegB) (c : NodeCtx) (lvl : List Val)
    (hlen : lvl.length = 2 * c.m) (hvals : ∀ v ∈ lvl, v.length = 16) (hm : 0 < c.m)
    (hB0 : 0x210 ≤ c.B) (hB8 : c.B % 8 = 0) (hBm : c.B + 32 * c.m + 32 ≤ 2 ^ 24)
    (s : MachineState) (hpc : s.pc = pcOf L) (h16 : s.getReg .x16 = 0)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c.m) (h19 : s.getReg .x19 = BitVec.ofNat 64 c.B)
    (h5 : s.getReg .x5 = 0)
    (hw0 : s.getMem (BitVec.ofNat 64 448) = twWord0 c.tt c.lay c.tau c.lam)
    (hw1 : lo32 (s.getMem (BitVec.ofNat 64 456)) = BitVec.ofNat 32 c.tau)
    (hz0 : s.getMem (BitVec.ofNat 64 464) = 0) (hz1 : s.getMem (BitVec.ofNat 64 472) = 0)
    (hslots : ∀ i (hi : i < lvl.length), s.readWords (BitVec.ofNat 64 (c.B + 16 * i)) 2 = wordsOf lvl[i]) :
    Sim image s (c.m * 25) (buildLevel (nodeFmt c.tt c.lay c.tau) c.lam lvl)
      (NodeInv c L lvl s c.m) := by
  unfold buildLevel
  rw [hlen, show 2 * c.m / 2 = c.m by omega]
  apply Sim.foldlM_range c.m _ [] (NodeInv c L lvl s) 25
  · intro j hj acc t ⟨hjm, hacc, haccv, hslot, hlvl, tpc, t16, tregs, tframe⟩
    have t19 : t.getReg .x19 = BitVec.ofNat 64 c.B := by rw [tregs .x19 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), h19]
    have t17 : t.getReg .x17 = BitVec.ofNat 64 c.m := by rw [tregs .x17 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), h17]
    have t5 : t.getReg .x5 = 0 := by rw [tregs .x5 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide), h5]
    obtain ⟨t1, st1, f1, pc1, a10, a11, a12, regs1, mem1⟩ :=
      nodeA_spec hA t (by rw [tpc, if_pos hj]) j c.B t16 t19 hB0 hB8 (by omega)
    have hl : (lvl.getD (2 * j) []).length = 16 := by
      rw [getD_of_lt (by omega)]; exact hvals _ (List.getElem_mem _)
    have hr : (lvl.getD (2 * j + 1) []).length = 16 := by
      rw [getD_of_lt (by omega)]; exact hvals _ (List.getElem_mem _)
    have hmemT : ∀ a : Nat, a < 2 ^ 64 → c.B ≤ a → t1.getMem (BitVec.ofNat 64 a) = t.getMem (BitVec.ofNat 64 a) := by
      intro a ha hBa
      rw [mem1 a ha, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        if_neg (by omega)]
    have hq : hashInput t1 = pad64 (nodeFmt c.tt c.lay c.tau c.lam j (lvl.getD (2 * j) [])
        (lvl.getD (2 * j + 1) [])) := by
      apply node_hashInput t1 _ _ _ _ _ _ _ hl hr (by rw [a10]) (by rw [a11])
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
        rw [tframe.1 448 (by norm_num) (by omega) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), hw0]
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num),
          if_neg (by norm_num), if_pos rfl]
        exact word_of_halves _ c.tau j (by rw [lo32_replace1, tframe.2, hw1]) (by rw [hi32_replace1])
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
        rw [tframe.1 464 (by norm_num) (by omega) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), hz0]
      · rw [mem1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]
        rw [tframe.1 472 (by norm_num) (by omega) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num), hz1]
      · rw [readWords_ofNat_two, mem1 _ (by norm_num), mem1 _ (by norm_num), getD_of_lt (by omega),
          ← hlvl (2 * j) (by omega) (le_refl _), readWords_ofNat_two]
        simp; constructor <;> congr 2 <;> omega
      · rw [readWords_ofNat_two, mem1 _ (by norm_num), mem1 _ (by norm_num), getD_of_lt (by omega),
          ← hlvl (2 * j + 1) (by omega) (by omega), readWords_ofNat_two]
        simp; constructor <;> congr 2 <;> omega
    have hblk : (pad64 (nodeFmt c.tt c.lay c.tau c.lam j (lvl.getD (2 * j) [])
        (lvl.getD (2 * j + 1) []))).blocks = 1 :=
      pad64_blocks_one _ (words_th32 c.tt c.lay c.tau c.lam j _ _ hl hr).1
    have := Sim.steps st1 (Sim.hash16_bind (f := fun v => pure (acc ++ [v])) (W := 2) (Q := NodeInv c L lvl s (j + 1)) f1
      (by rw [regs1 .x5 (by decide) (by decide) (by decide) (by decide) (by decide), t5])
      (hashArgs_of a10 a11 a12 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega) (by omega))
      hq (fun a => by
        obtain ⟨t3, st3, pc3, x16', regs3, mem3⟩ := nodeB_spec (L := L) hB (writeHash t1 a)
          (by rw [writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp; omega) j c.m
          (by rw [writeHash_getReg, regs1 .x16 (by decide) (by decide) (by decide) (by decide) (by decide), t16])
          (by rw [writeHash_getReg, regs1 .x17 (by decide) (by decide) (by decide) (by decide) (by decide), t17])
          (by omega) (by omega)
        apply Sim.pure_steps st3
        have hwf : ∀ x : Nat, x < 2 ^ 64 → (x < c.B + 16 * j ∨ c.B + 16 * j + 32 ≤ x) →
            t3.getMem (BitVec.ofNat 64 x) = t1.getMem (BitVec.ofNat 64 x) := by
          intro x hx hout
          rw [mem3, writeHash_getMem_frame t1 a (c.B + 16 * j) x a12 (by omega) hx (by omega)]
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
            rw [← writeHash_readWords_val t1 a (c.B + 16 * acc.length) (by rw [a12, hacc]) (by omega),
              readWords_ofNat_two, mem3, mem3, hacc]
        · intro i hi h2
          rw [readWords_ofNat_two, hwf _ (by omega) (by omega), hwf _ (by omega) (by omega),
            hmemT _ (by omega) (by omega), hmemT _ (by omega) (by omega), ← readWords_ofNat_two]
          exact hlvl i hi (by omega)
        · rw [pc3]; by_cases h : j + 1 = c.m
          · simp [h]
          · rw [if_neg h, if_pos (by omega)]
        · intro r h1 h3 h10 h11 h12 h16'
          rw [regs3 r h16', writeHash_getReg, regs1 r h1 h3 h10 h11 h12, tregs r h1 h3 h10 h11 h12 h16']
        · intro x hx hout n1 n2 n3 n4 n5
          rw [hwf x hx (by omega), mem1 x hx, if_neg n5, if_neg n4, if_neg n3, if_neg n2, if_neg n1]
          exact tframe.1 x hx hout n1 n2 n3 n4 n5
        · rw [hwf 456 (by norm_num) (by omega), mem1 456 (by norm_num)]
          simp only [show ¬ ((456 : Nat) = 504) by norm_num, show ¬ ((456 : Nat) = 496) by norm_num,
            show ¬ ((456 : Nat) = 488) by norm_num, show ¬ ((456 : Nat) = 480) by norm_num, if_false,
            if_true, lo32_replace1]
          exact tframe.2))
    refine this.mono ?_ (fun _ _ h => h)
    rw [hblk]
  · refine ⟨Nat.zero_le _, rfl, by simp, by simp, fun i hi _ => hslots i hi, by simp [hpc, hm],
      by simpa using h16, fun r _ _ _ _ _ _ => rfl, fun a _ _ _ _ _ _ _ => rfl, rfl⟩

theorem NodeRegs.toRegsEq {s t : MachineState} (h : NodeRegs s t) :
    RegsEq s t [.x1, .x3, .x10, .x11, .x12, .x16] := by
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hr
  exact h r hr.1 hr.2.1 hr.2.2.1 hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2

theorem NodeFrame.toFrame {c : NodeCtx} {s t : MachineState} (h : NodeFrame c s t) :
    Frame s t (fun a => (c.B ≤ a ∧ a < c.B + 32 * c.m) ∨ a = 456 ∨ a = 480 ∨ a = 488 ∨ a = 496 ∨
      a = 504) := by
  intro a ha hW
  simp only [not_or, not_and, not_lt] at hW
  exact h.1 a ha (by omega) hW.2.1 hW.2.2.1 hW.2.2.2.1 hW.2.2.2.2.1 hW.2.2.2.2.2

end SigGolfCandidate.Sign
