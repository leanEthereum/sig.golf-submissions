import SigGolfCandidate.Sign.Blocks
import SigGolfCandidate.Sign.Inv

/-!
# `sign`, FORS leaves (`fors_leaf_loop`, instructions 120 .. 139)

`forsLeaves_sim` : from `fors_leaf_loop` with `J = 0`, the machine refines
`buildFtsLeaves S k idx 10 u`: leaf `j` is stored at `FA + 16 j`, the secret of leaf `u` at
`SIGL + 16`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref


/-- The (fixed) facts at the start of the leaf loop of tree `k`. -/
structure LeafCtx (S : List Byte) (k idx u : Nat) (t0 : MachineState) : Prop where
  pb0 : t0.getMem (BitVec.ofNat 64 0x6A0) = twWord0 8 k idx 0
  pb8 : lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) = BitVec.ofNat 32 idx
  pbP : t0.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t0.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cb0 : t0.getMem (BitVec.ofNat 64 0xC0) = twWord0 9 k idx 0
  cb8 : lo32 (t0.getMem (BitVec.ofNat 64 0xC8)) = BitVec.ofNat 32 idx
  cbP : t0.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]
  x5 : t0.getReg .x5 = 0
  x13 : t0.getReg .x13 = BitVec.ofNat 64 u
  x18 : t0.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k)
  x19 : t0.getReg .x19 = BitVec.ofNat 64 0x30000

/-- Addresses written by the leaf loop of tree `k`. -/
def leafW (k : Nat) (a : Nat) : Prop :=
  a = 0x6A8 ∨ a = 0xC8 ∨ (0xE0 ≤ a ∧ a < 0x100) ∨ (0x30000 ≤ a ∧ a < 0x30000 + 16 * 1025) ∨
    a = 0x2650 + 176 * k + 16 ∨ a = 0x2650 + 176 * k + 24

def leafRegs : List Reg := [.x1, .x2, .x3, .x9, .x10, .x11, .x12]

/-- Invariant after `j` leaves. -/
def LeafInv (k u : Nat) (t0 : MachineState) (j : Nat) (st : List Val × Val) (t : MachineState) : Prop :=
  j ≤ 1024 ∧ st.1.length = j ∧ (∀ v ∈ st.1, v.length = 16) ∧ Slots t 0x30000 st.1 ∧
  (u < j → st.2.length = 16 ∧ t.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf st.2) ∧
  t.pc = (if j < 1024 then pcOf 120 else pcOf 140) ∧ t.getReg .x9 = BitVec.ofNat 64 j ∧
  RegsEq t0 t leafRegs ∧ Frame t0 t (leafW k) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8))

/-- From `fors_nocap` (instruction 132): the leaf hash and the loop step. -/
theorem forsLeaf_tail (S : List Byte) (k idx u : Nat) (hk : k < 14) (hidx : idx < 2 ^ 34) (hu : u < 1024)
    (t0 : MachineState) (ctx : LeafCtx S k idx u t0) (j : Nat) (hj : j < 1024)
    (acc : List Val) (hlen : acc.length = j) (hvals : ∀ v ∈ acc, v.length = 16) (s cap : Val)
    (hs : s.length = 16) (t : MachineState) (tpc : t.pc = pcOf 132)
    (t9 : t.getReg .x9 = BitVec.ofNat 64 j) (t11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (tregs : RegsEq t0 t leafRegs) (tframe : Frame t0 t (leafW k))
    (tlo1 : lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)))
    (tlo2 : lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8)))
    (tsv : t.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf s)
    (tz : t.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]) (hslots : Slots t 0x30000 acc)
    (hcap : u < j + 1 → cap.length = 16 ∧
      t.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf cap) :
    Sim image t 15 (hash16 (ftsLeafInput k idx j s) >>= fun leaf => pure (acc ++ [leaf], cap))
      (LeafInv k u t0 (j + 1)) := by
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by simp [leafRegs]), ctx.x5]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x30000 := by
    rw [tregs.get .x19 (by simp [leafRegs]), ctx.x19]
  have hs1 := symRun_sound blk132 codeAt_132 t tpc (by simp only [blk132.res, rv_simp])
  have hc1 : blk132.res.cycles = 4 := rfl
  rw [hc1] at hs1
  set t1 := blk132.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0xC8) := by
    apply frame_toState; intro x hx hW
    simp only [blk132.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x3, .x10, .x12] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk132 codeAt_132 t (by simp only [blk132.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0xC0 := by simp only [ht1, blk132.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by rw [r1.get .x11, t11]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 (0x30000 + 16 * j) := by
    rvs [ht1, blk132.res, t9, tx19]; congr 1; ring
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have pc1 : t1.pc = pcOf 136 := by simp only [ht1, blk132.res, rv_simp]
  have mC8 : t1.getMem (BitVec.ofNat 64 0xC8) =
      BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32)) := by
    rvs [ht1, blk132.res, t9]
    exact word_of_halves _ idx j (by rw [lo32_replace1, tlo2, ctx.cb8]) (by rw [hi32_replace1])
  have hq : hashInput t1 = pad64 (ftsLeafInput k idx j s) := by
    obtain ⟨hn, hw⟩ := words_th16 9 k idx 0 j s hs
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [ftsLeafInput, hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 2 + 2 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, mC8, f1.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [leafW]; omega), ctx.cb0,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega), ctx.cbP, tsv, tz]
    simp [twWords_eq]
  have hb : (pad64 (ftsLeafInput k idx j s)).blocks = 1 :=
    congrArg (· + 1) (words_th16 9 k idx 0 j s hs).1
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 3) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)
      (by norm_num)) hq (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x30000 + 16 * j ≤ x ∧ x < 0x30000 + 16 * j + 32) :=
    frame_writeHash t1 a _ x12 (by omega)
  have v2 : t2.readWords (BitVec.ofNat 64 (0x30000 + 16 * j)) 2 = wordsOf (answerBytes 16 a) :=
    writeHash_readWords_val t1 a _ x12 (by omega)
  have pc2 : t2.pc = pcOf 137 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have hs2 := symRun_sound blk137 codeAt_137 t2 pc2 (by simp only [blk137.res, rv_simp])
  have hc2 : blk137.res.cycles = 3 := rfl
  rw [hc2] at hs2
  set t3 := blk137.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk137.res]
  have r3 : RegsEq t2 t3 [.x3, .x9] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have t29 : t2.getReg .x9 = BitVec.ofNat 64 j := by rw [ht2, writeHash_getReg, r1.get .x9, t9]
  have ftot : Frame t t3 (fun x => x = 0xC8 ∨ (0x30000 + 16 * j ≤ x ∧ x < 0x30000 + 16 * j + 32)) :=
    ((f1.trans f2).trans f3).mono (by intro x hx; (try simp only [or_false] at hx ⊢); omega)
  refine Sim.pure_steps hs2 ⟨by omega, by simp [hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hvals v hv
    · simp at hv; subst hv; simp
  · apply Slots.snoc
    · exact hslots.frame ftot (by omega) (by intro i hi; constructor <;> ((try simp only); omega))
    · rw [hlen, f3.readWords _ _ (by omega) (by simp), v2]
  · intro h
    obtain ⟨h1, h2⟩ := hcap h
    refine ⟨h1, ?_⟩
    rw [ftot.readWords _ _ (by omega) (by intro i hi; omega), h2]
  · simp only [ht3, blk137.res, rv_simp, t29, ofNat_add_ofNat, ofNat_bne_ofNat]
    by_cases h : j + 1 < 1024
    · rw [if_pos (by simp; omega), if_pos h]
    · rw [if_neg (by simp; omega), if_neg h]
  · simp only [ht3, blk137.res, rv_simp, t29, ofNat_add_ofNat]
  · exact ((((tregs.trans r1).trans (regsEq_writeHash _ _ [])).trans r3)).mono (by decide)
  · exact (tframe.trans ftot).mono (by intro x hx; simp only [leafW] at hx ⊢; omega)
  · rw [ftot.getMem (by norm_num) (by omega), tlo1]
  · rw [f3.getMem (by norm_num) (by simp), f2.getMem (by norm_num) (by omega)]
    rvs [ht1, blk132.res, t9]
    rw [lo32_replace1, tlo2]

theorem forsLeaf_body (S : List Byte) (hS : S.length = 32) (k idx u : Nat) (hk : k < 14)
    (hidx : idx < 2 ^ 34) (hu : u < 1024) (t0 : MachineState) (ctx : LeafCtx S k idx u t0)
    (j : Nat) (hj : j < 1024) (st : List Val × Val) (t : MachineState)
    (hinv : LeafInv k u t0 j st t) :
    Sim image t 34 (do
        let s ← hash16 (ftsPrfInput S k idx j)
        let leaf ← hash16 (ftsLeafInput k idx j s)
        pure (st.1 ++ [leaf], if j = u then s else st.2))
      (LeafInv k u t0 (j + 1)) := by
  obtain ⟨-, hlen, hvals, hslots, hcap, tpc, t9, tregs, tframe, tlo1, tlo2⟩ := hinv
  have tpc' : t.pc = pcOf 120 := by rw [tpc, if_pos hj]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by simp [leafRegs]), ctx.x5]
  have tx13 : t.getReg .x13 = BitVec.ofNat 64 u := by rw [tregs.get .x13 (by simp [leafRegs]), ctx.x13]
  have tx18 : t.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) := by
    rw [tregs.get .x18 (by simp [leafRegs]), ctx.x18]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x30000 := by rw [tregs.get .x19 (by simp [leafRegs]), ctx.x19]
  -- block 120: prf input
  have hs1 := symRun_sound blk120 codeAt_120 t tpc' (by simp only [blk120.res, rv_simp])
  have hc1 : blk120.res.cycles = 4 := rfl
  rw [hc1] at hs1
  set t1 := blk120.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x6A8) := by
    apply frame_toState; intro x hx hW
    simp only [blk120.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x11, .x12] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk120 codeAt_120 t (by simp only [blk120.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht1, blk120.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht1, blk120.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0xE0 := by simp only [ht1, blk120.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have pc1 : t1.pc = pcOf 124 := by simp only [ht1, blk120.res, rv_simp]
  have m6A8 : t1.getMem (BitVec.ofNat 64 0x6A8) =
      BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32)) := by
    rvs [ht1, blk120.res, t9]
    exact word_of_halves _ idx j (by rw [lo32_replace1, tlo1, ctx.pb8]) (by rw [hi32_replace1])
  have hq1 : hashInput t1 = pad64 (ftsPrfInput S k idx j) := by
    obtain ⟨hn, hw⟩ := words_ftsPrfInput S hS k idx j
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m6A8, f1.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [leafW]; omega), ctx.pb0,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega), ctx.pbP, ctx.pbS]
    simp [twWords_eq]
  have hb1 : (pad64 (ftsPrfInput S k idx j)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_ftsPrfInput S hS k idx j).1]
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 3 + 4 + 15) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq1 (fun a => ?_))).mono (by rw [hb1]) (fun _ _ h => h)
  set sv := answerBytes 16 a with hsv
  have hsl : sv.length = 16 := by simp [hsv]
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0xE0 ≤ x ∧ x < 0xE0 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have v2 : t2.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf sv := writeHash_readWords_val t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 125 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have hs2 := symRun_sound blk125 codeAt_125 t2 pc2 (by simp only [blk125.res, rv_simp])
  have hc2 : blk125.res.cycles = 3 := rfl
  rw [hc2] at hs2
  set t3 := blk125.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun x => x = 0xF0 ∨ x = 0xF8) := by
    apply frame_toState; intro x hx hW
    simp only [blk125.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t2 t3 [] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have t29 : t2.getReg .x9 = BitVec.ofNat 64 j := by rw [ht2, writeHash_getReg, r1.get .x9, t9]
  have t213 : t2.getReg .x13 = BitVec.ofNat 64 u := by rw [ht2, writeHash_getReg, r1.get .x13, tx13]
  have z3 : t3.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0] := by
    rw [readWords_ofNat_two]; simp only [ht3, blk125.res, rv_simp]; rfl
  have ft3 : Frame t t3 (fun x => x = 0x6A8 ∨ (0xE0 ≤ x ∧ x < 0x100)) :=
    ((f1.trans f2).trans f3).mono (by intro x hx; (try simp only [or_false] at hx ⊢); omega)
  have rt3 : RegsEq t0 t3 leafRegs := (((tregs.trans r1).trans (regsEq_writeHash _ _ [])).trans r3).mono
    (by decide)
  have x39 : t3.getReg .x9 = BitVec.ofNat 64 j := by rw [r3.get .x9, t29]
  have x311 : t3.getReg .x11 = BitVec.ofNat 64 64 := by
    rw [r3.get .x11, ht2, writeHash_getReg, x11]
  have v3 : t3.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf sv := by
    rw [f3.readWords _ _ (by norm_num) (by intro i hi; omega), v2]
  have lo3a : lo32 (t3.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) := by
    rw [f3.getMem (by norm_num) (by omega), f2.getMem (by norm_num) (by omega)]
    rvs [ht1, blk120.res, t9]; rw [lo32_replace1, tlo1]
  have lo3b : lo32 (t3.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8)) := by
    rw [ft3.getMem (by norm_num) (by omega), tlo2]
  have pc3 : t3.pc = if j = u then pcOf 128 else pcOf 132 := by
    simp only [ht3, blk125.res, rv_simp, t29, t213, ofNat_bne_ofNat]
    by_cases h : j = u
    · rw [if_pos h, if_neg (by simp; omega)]
    · rw [if_neg h, if_pos (by simp; omega)]
  have hslots3 : Slots t3 0x30000 st.1 := hslots.frame ft3 (by omega)
    (by intro i hi; constructor <;> ((try simp only); omega))
  by_cases hju : j = u
  · -- capture
    have hs4 := symRun_sound blk128 codeAt_128 t3 (by rw [pc3, if_pos hju]) (by
      simp only [blk128.res, rv_simp, r3.get .x18, ht2, writeHash_getReg, r1.get .x18, tx18,
        ofNat_add_ofNat, accessValid_ofNat, Nat.reducePow]
      bvomega)
    have hc4 : blk128.res.cycles = 4 := rfl
    rw [hc4] at hs4
    set t4 := blk128.res.toState t3 with ht4
    have t318 : t3.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) := by
      rw [r3.get .x18, ht2, writeHash_getReg, r1.get .x18, tx18]
    have f4 : Frame t3 t4 (fun x => x = 0x2650 + 176 * k + 16 ∨ x = 0x2650 + 176 * k + 24) := by
      apply frame_toState; intro x hx hW
      simp only [blk128.res, rv_simp, t318, ofNat_add_ofNat, List.forall_mem_cons, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, and_true, ne_eq, ofNat_eq_iff]
      omega
    have r4 : RegsEq t3 t4 [.x1, .x2] := by
      intro r hr; rw [ht4, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    have sig4 : t4.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf sv := by
      rw [← v3, readWords_ofNat_two, readWords_ofNat_two]
      simp only [ht4, blk128.res, rv_simp, t318, ofNat_add_ofNat, ofNat_eq_iff]
      simp (disch := bvomega) only [if_pos, if_neg, if_true, Nat.reduceAdd]
    have := forsLeaf_tail S k idx u hk hidx hu t0 ctx j hj st.1 hlen hvals sv sv hsl t4
      (by simp only [ht4, blk128.res, rv_simp])
      (by rw [r4.get .x9, x39]) (by rw [r4.get .x11, x311])
      (rt3.trans r4 |>.mono (by decide))
      ((tframe.trans (ft3.trans f4)).mono (by
        intro x hx; (try simp only [or_false] at hx ⊢); simp only [leafW] at hx ⊢; omega))
      (by rw [f4.getMem (by norm_num) (by omega), lo3a])
      (by rw [f4.getMem (by norm_num) (by omega), lo3b])
      (by rw [f4.readWords _ _ (by norm_num) (by intro i hi; omega), v3])
      (by rw [f4.readWords _ _ (by norm_num) (by intro i hi; omega), z3])
      (hslots3.frame f4 (by omega) (by intro i hi; constructor <;> ((try simp only); omega)))
      (fun _ => ⟨hsl, sig4⟩)
    rw [if_pos hju]
    exact (Sim.steps hs2 (Sim.steps hs4 this)).mono (by norm_num) (fun _ _ h => h)
  · have := forsLeaf_tail S k idx u hk hidx hu t0 ctx j hj st.1 hlen hvals sv st.2 hsl t3
      (by rw [pc3, if_neg hju]) x39 x311 rt3
      ((tframe.trans ft3).mono (by
        intro x hx; (try simp only [or_false] at hx ⊢); simp only [leafW] at hx ⊢; omega))
      lo3a lo3b v3 z3 hslots3
      (fun h => by
        obtain ⟨h1, h2⟩ := hcap (by omega)
        exact ⟨h1, by rw [ft3.readWords _ _ (by omega) (by intro i hi; omega), h2]⟩)
    rw [if_neg hju]
    exact (Sim.steps hs2 this).mono (by norm_num) (fun _ _ h => h)

theorem LeafInv.init (k u : Nat) (t0 : MachineState) (hpc : t0.pc = pcOf 120)
    (h9 : t0.getReg .x9 = BitVec.ofNat 64 0) : LeafInv k u t0 0 ([], []) t0 :=
  ⟨by norm_num, rfl, by simp, Slots.nil _ _, fun h => absurd h (by omega), by simpa using hpc, h9,
    RegsEq.refl _ _, Frame.refl _ _, rfl, rfl⟩

/-- **FORS leaves** of tree `k`. -/
theorem forsLeaves_sim (S : List Byte) (hS : S.length = 32) (k idx u : Nat) (hk : k < 14)
    (hidx : idx < 2 ^ 34) (hu : u < 1024) (t0 : MachineState) (ctx : LeafCtx S k idx u t0)
    (hpc : t0.pc = pcOf 120) (h9 : t0.getReg .x9 = BitVec.ofNat 64 0) :
    Sim image t0 (1024 * 34) (buildFtsLeaves S k idx 10 u) (LeafInv k u t0 1024) := by
  unfold buildFtsLeaves
  exact Sim.foldlM_range (2 ^ 10) _ ([], []) (LeafInv k u t0) 34
    (fun j hj st t h => forsLeaf_body S hS k idx u hk hidx hu t0 ctx j hj st t h)
    (LeafInv.init k u t0 hpc h9)

end SigGolfCandidate.Sign
