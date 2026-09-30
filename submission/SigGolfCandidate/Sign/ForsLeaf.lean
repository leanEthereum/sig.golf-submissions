import SigGolfCandidate.Sign.Pair

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
  cbZ : t0.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]
  x5 : t0.getReg .x5 = 0
  x13 : t0.getReg .x13 = BitVec.ofNat 64 u
  x18 : t0.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k)
  x19 : t0.getReg .x19 = BitVec.ofNat 64 0x30000

/-- Addresses written by the leaf loop of tree `k`. -/
def leafW (k : Nat) (a : Nat) : Prop :=
  a = 0x6A8 ∨ a = 0xC8 ∨ (0xE0 ≤ a ∧ a < 0xF0) ∨ (0x140 ≤ a ∧ a < 0x160) ∨
    (0x30000 ≤ a ∧ a < 0x30000 + 16 * 1025) ∨
    a = 0x2650 + 176 * k + 16 ∨ a = 0x2650 + 176 * k + 24

def leafRegs : List Reg := [.x1, .x2, .x3, .x9, .x10, .x11, .x12]

/-- Invariant after `j` leaves. -/
def LeafInv (k u : Nat) (t0 : MachineState) (j : Nat) (st : List Val × Val) (t : MachineState) : Prop :=
  j ≤ 1024 ∧ st.1.length = j ∧ (∀ v ∈ st.1, v.length = 16) ∧ Slots t 0x30000 st.1 ∧
  (u < j → st.2.length = 16 ∧ t.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf st.2) ∧
  t.pc = (if j < 1024 then pcOf 161 else pcOf 188) ∧ t.getReg .x9 = BitVec.ofNat 64 j ∧
  RegsEq t0 t leafRegs ∧ Frame t0 t (leafW k) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8))

/-- From `fors_nocap` (instruction 132): the leaf hash and the loop step. -/
theorem forsLeaf_tail (S : List Byte) (k idx u : Nat) (hk : k < 14) (hidx : idx < 2 ^ 34) (hu : u < 1024)
    (t0 : MachineState) (ctx : LeafCtx S k idx u t0) (j : Nat) (hj : j < 1024)
    (acc : List Val) (hlen : acc.length = j) (hvals : ∀ v ∈ acc, v.length = 16) (s cap : Val)
    (hs : s.length = 16) (t : MachineState) (tpc : t.pc = pcOf 180)
    (t9 : t.getReg .x9 = BitVec.ofNat 64 j) (t11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (tregs : RegsEq t0 t leafRegs) (tframe : Frame t0 t (leafW k))
    (tlo1 : lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)))
    (tlo2 : lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8)))
    (tsv : t.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf s)
    (tz : t.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]) (hslots : Slots t 0x30000 acc)
    (hcap : u < j + 1 → cap.length = 16 ∧
      t.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf cap) :
    Sim image t 15 (hash16 (ftsLeafInput k idx j s) >>= fun leaf => pure (acc ++ [leaf], cap))
      (fun r t' => LeafInv k u t0 (j + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧
        ∀ x, x < 2 ^ 64 → 0x140 ≤ x → x < 0x160 →
        t'.getMem (BitVec.ofNat 64 x) = t.getMem (BitVec.ofNat 64 x)) := by
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by simp [leafRegs]), ctx.x5]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x30000 := by
    rw [tregs.get .x19 (by simp [leafRegs]), ctx.x19]
  have hs1 := symRun_sound blk180 codeAt_180 t tpc (by simp only [blk180.res, rv_simp])
  have hc1 : blk180.res.cycles = 4 := rfl
  rw [hc1] at hs1
  set t1 := blk180.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0xC8) := by
    apply frame_toState; intro x hx hW
    simp only [blk180.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x3, .x10, .x12] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk180 codeAt_180 t (by simp only [blk180.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0xC0 := by simp only [ht1, blk180.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by rw [r1.get .x11, t11]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 (0x30000 + 16 * j) := by
    rvs [ht1, blk180.res, t9, tx19]; congr 1; ring
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have pc1 : t1.pc = pcOf 184 := by simp only [ht1, blk180.res, rv_simp]
  have mC8 : t1.getMem (BitVec.ofNat 64 0xC8) =
      BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32)) := by
    rvs [ht1, blk180.res, t9]
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
      (by norm_num)) hq (fmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x30000 + 16 * j ≤ x ∧ x < 0x30000 + 16 * j + 32) :=
    frame_writeHash t1 a _ x12 (by omega)
  have v2 : t2.readWords (BitVec.ofNat 64 (0x30000 + 16 * j)) 2 = wordsOf (answerBytes 16 a) :=
    writeHash_readWords_val t1 a _ x12 (by omega)
  have pc2 : t2.pc = pcOf 185 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have hs2 := symRun_sound blk185 codeAt_185 t2 pc2 (by simp only [blk185.res, rv_simp])
  have hc2 : blk185.res.cycles = 3 := rfl
  rw [hc2] at hs2
  set t3 := blk185.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk185.res]
  have r3 : RegsEq t2 t3 [.x3, .x9] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have t29 : t2.getReg .x9 = BitVec.ofNat 64 j := by rw [ht2, writeHash_getReg, r1.get .x9, t9]
  have ftot : Frame t t3 (fun x => x = 0xC8 ∨ (0x30000 + 16 * j ≤ x ∧ x < 0x30000 + 16 * j + 32)) :=
    ((f1.trans f2).trans f3).mono (by intro x hx; (try simp only [or_false] at hx ⊢); omega)
  refine Sim.pure_steps hs2 ⟨⟨by omega, by simp [hlen], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [r3.get .x11, ht2, writeHash_getReg, x11], fun x hx h1 h2 => ftot.getMem hx (by omega)⟩
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
  · simp only [ht3, blk185.res, rv_simp, t29, ofNat_add_ofNat, ofNat_bne_ofNat]
    by_cases h : j + 1 < 1024
    · rw [if_pos (by simp; omega), if_pos h]
    · rw [if_neg (by simp; omega), if_neg h]
  · simp only [ht3, blk185.res, rv_simp, t29, ofNat_add_ofNat]
  · exact ((((tregs.trans r1).trans (regsEq_writeHash _ _ [])).trans r3)).mono (by decide)
  · exact (tframe.trans ftot).mono (by intro x hx; simp only [leafW] at hx ⊢; omega)
  · rw [ftot.getMem (by norm_num) (by omega), tlo1]
  · rw [f3.getMem (by norm_num) (by simp), f2.getMem (by norm_num) (by omega)]
    rvs [ht1, blk180.res, t9]
    rw [lo32_replace1, tlo2]

/-- From `prf_have` (instruction 169) for leaf `j` whose secret `s` sits at `SEC + 16 (j & 1)`: the
copy to `CB+32`, the capture, the leaf hash, the loop step. -/
theorem forsLeaf_B (S : List Byte) (k idx u : Nat) (hk : k < 14) (hidx : idx < 2 ^ 34) (hu : u < 1024)
    (t0 : MachineState) (ctx : LeafCtx S k idx u t0) (j : Nat) (hj : j < 1024)
    (acc : List Val) (hlen : acc.length = j) (hvals : ∀ v ∈ acc, v.length = 16) (s cap : Val)
    (hs : s.length = 16) (t : MachineState) (tpc : t.pc = pcOf 169)
    (t9 : t.getReg .x9 = BitVec.ofNat 64 j) (t11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (hsec : t.readWords (BitVec.ofNat 64 (0x140 + 16 * (j % 2))) 2 = wordsOf s)
    (hslots : Slots t 0x30000 acc)
    (hcap : u < j → cap.length = 16 ∧ t.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf cap)
    (tregs : RegsEq t0 t leafRegs) (tframe : Frame t0 t (leafW k))
    (tlo1 : lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)))
    (tlo2 : lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8))) :
    Sim image t 26 (hash16 (ftsLeafInput k idx j s) >>= fun leaf => pure (acc ++ [leaf], if j = u then s else cap))
      (fun r t' => LeafInv k u t0 (j + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧
        ∀ x, x < 2 ^ 64 → 0x140 ≤ x → x < 0x160 →
        t'.getMem (BitVec.ofNat 64 x) = t.getMem (BitVec.ofNat 64 x)) := by
  have tx13 : t.getReg .x13 = BitVec.ofNat 64 u := by rw [tregs.get .x13 (by simp [leafRegs]), ctx.x13]
  have tx18 : t.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) := by
    rw [tregs.get .x18 (by simp [leafRegs]), ctx.x18]
  have hj2 : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  -- block 169: copy the secret to CB+32, test J = U
  have hs3 := symRun_sound blk169 codeAt_169 t tpc (by
    simp only [blk169.res, rv_simp, t9]; rw [secAddr j (by omega) 328 (by norm_num), secAddr j (by omega) 320 (by norm_num)]
    simp only [accessValid_ofNat]; omega)
  have hc3 : blk169.res.cycles = 7 := rfl
  rw [hc3] at hs3
  set t3 := blk169.res.toState t with ht3
  have f3 : Frame t t3 (fun x => x = 0xE0 ∨ x = 0xE8) := by
    apply frame_toState; intro x hx hW
    simp only [blk169.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t t3 [.x1, .x2, .x3] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have x39 : t3.getReg .x9 = BitVec.ofNat 64 j := by rw [r3.get .x9, t9]
  have x311 : t3.getReg .x11 = BitVec.ofNat 64 64 := by rw [r3.get .x11, t11]
  have v3 : t3.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf s := by
    rw [← hsec, readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht3, blk169.res, rv_simp, t9]
    rw [secAddr j (by omega) 328 (by norm_num), secAddr j (by omega) 320 (by norm_num)]
    simp (config := { decide := true }) only [↓reduceIte]
    rw [show 328 + 16 * (j % 2) = 0x140 + 16 * (j % 2) + 8 by omega]
  have pc3 : t3.pc = if j = u then pcOf 176 else pcOf 180 := by
    simp only [ht3, blk169.res, rv_simp, t9, tx13, ofNat_bne_ofNat]
    by_cases h : j = u
    · rw [if_pos h, if_neg (by simp; omega)]
    · rw [if_neg h, if_pos (by simp; omega)]
  have ft3 : Frame t0 t3 (leafW k) := (tframe.trans f3).mono (by
    intro x hx; simp only [leafW] at hx ⊢; omega)
  have rt3 : RegsEq t0 t3 leafRegs := (tregs.trans r3).mono (by decide)
  have z3 : t3.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0] := by
    rw [ft3.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega), ctx.cbZ]
  have lo3a : lo32 (t3.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) := by
    rw [f3.getMem (by norm_num) (by omega), tlo1]
  have lo3b : lo32 (t3.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8)) := by
    rw [f3.getMem (by norm_num) (by omega), tlo2]
  have hslots3 : Slots t3 0x30000 acc := hslots.frame f3 (by omega)
    (by intro i hi; constructor <;> omega)
  have sec3 : ∀ x, x < 2 ^ 64 → 0x140 ≤ x → x < 0x160 →
      t3.getMem (BitVec.ofNat 64 x) = t.getMem (BitVec.ofNat 64 x) := fun x hx h1 h2 =>
    f3.getMem hx (by omega)
  by_cases hju : j = u
  · -- capture
    have hs4 := symRun_sound blk176 codeAt_176 t3 (by rw [pc3, if_pos hju]) (by
      simp only [blk176.res, rv_simp, r3.get .x18, tx18,
        ofNat_add_ofNat, accessValid_ofNat, Nat.reducePow]
      bvomega)
    have hc4 : blk176.res.cycles = 4 := rfl
    rw [hc4] at hs4
    set t4 := blk176.res.toState t3 with ht4
    have t318 : t3.getReg .x18 = BitVec.ofNat 64 (0x2650 + 176 * k) := by rw [r3.get .x18, tx18]
    have f4 : Frame t3 t4 (fun x => x = 0x2650 + 176 * k + 16 ∨ x = 0x2650 + 176 * k + 24) := by
      apply frame_toState; intro x hx hW
      simp only [blk176.res, rv_simp, t318, ofNat_add_ofNat, List.forall_mem_cons, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, and_true, ne_eq, ofNat_eq_iff]
      omega
    have r4 : RegsEq t3 t4 [.x1, .x2] := by
      intro r hr; rw [ht4, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    have sig4 : t4.readWords (BitVec.ofNat 64 (0x2650 + 176 * k + 16)) 2 = wordsOf s := by
      rw [← v3, readWords_ofNat_two, readWords_ofNat_two]
      simp only [ht4, blk176.res, rv_simp, t318, ofNat_add_ofNat, ofNat_eq_iff]
      simp (disch := bvomega) only [if_pos, if_neg, if_true, Nat.reduceAdd]
    have := forsLeaf_tail S k idx u hk hidx hu t0 ctx j hj acc hlen hvals s s hs t4
      (by simp only [ht4, blk176.res, rv_simp])
      (by rw [r4.get .x9, x39]) (by rw [r4.get .x11, x311])
      (rt3.trans r4 |>.mono (by decide))
      ((ft3.trans f4).mono (by
        intro x hx; (try simp only [or_false] at hx ⊢); simp only [leafW] at hx ⊢; omega))
      (by rw [f4.getMem (by norm_num) (by omega), lo3a])
      (by rw [f4.getMem (by norm_num) (by omega), lo3b])
      (by rw [f4.readWords _ _ (by norm_num) (by intro i hi; omega), v3])
      (by rw [f4.readWords _ _ (by norm_num) (by intro i hi; omega), z3])
      (hslots3.frame f4 (by omega) (by intro i hi; constructor <;> ((try simp only); omega)))
      (fun _ => ⟨hs, sig4⟩)
    rw [if_pos hju]
    exact (Sim.steps hs3 (Sim.steps hs4 this)).mono (by norm_num) (fun _ _ h => ⟨h.1, h.2.1, fun x hx h1 h2 => by
      rw [h.2.2 x hx h1 h2, f4.getMem hx (by omega), sec3 x hx h1 h2]⟩)
  · have := forsLeaf_tail S k idx u hk hidx hu t0 ctx j hj acc hlen hvals s cap hs t3
      (by rw [pc3, if_neg hju]) x39 x311 rt3 ft3 lo3a lo3b v3 z3 hslots3
      (fun h => by
        obtain ⟨h1, h2⟩ := hcap (by omega)
        exact ⟨h1, by rw [f3.readWords _ _ (by omega) (by intro i hi; omega), h2]⟩)
    rw [if_neg hju]
    exact (Sim.steps hs3 this).mono (by norm_num) (fun _ _ h => ⟨h.1, h.2.1, fun x hx h1 h2 => by
      rw [h.2.2 x hx h1 h2, sec3 x hx h1 h2]⟩)

theorem LeafInv.init (k u : Nat) (t0 : MachineState) (hpc : t0.pc = pcOf 161)
    (h9 : t0.getReg .x9 = BitVec.ofNat 64 0) : LeafInv k u t0 0 ([], []) t0 :=
  ⟨by norm_num, rfl, by simp, Slots.nil _ _, fun h => absurd h (by omega), by simpa using hpc, h9,
    RegsEq.refl _ _, Frame.refl _ _, rfl, rfl⟩

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem fors_pair_spec (S : List Byte) (k idx u p : Nat) (st : List Val × Val) :
    (do
      let (s0, s1) ← prf2 (ftsPrfInput S k idx p)
      let l0 ← hash16 (ftsLeafInput k idx (2 * p) s0)
      let l1 ← hash16 (ftsLeafInput k idx (2 * p + 1) s1)
      pure (st.1 ++ [l0, l1], if 2 * p = u then s0 else if 2 * p + 1 = u then s1 else st.2) :
        OracleComp HashSpec (List Val × Val)) =
    H (ftsPrfInput S k idx p) >>= fun a =>
      (hash16 (ftsLeafInput k idx (2 * p) (answerBytes 16 a)) >>= fun l0 =>
        pure (st.1 ++ [l0], if 2 * p = u then answerBytes 16 a else st.2)) >>= fun r =>
      hash16 (ftsLeafInput k idx (2 * p + 1) (hiVal a)) >>= fun l1 =>
        pure (r.1 ++ [l1], if 2 * p + 1 = u then hiVal a else r.2) := by
  simp only [prf2_eq, bind_assoc, pure_bind, List.append_assoc, List.cons_append, List.nil_append]
  congr 1; funext a; congr 1; funext l0; congr 1; funext l1
  congr 2
  by_cases h1 : 2 * p = u
  · rw [if_pos h1, if_neg (by omega), if_pos h1]
  · rw [if_neg h1, if_neg h1]

theorem forsLeaf_pair (S : List Byte) (hS : S.length = 32) (k idx u : Nat) (hk : k < 14)
    (hidx : idx < 2 ^ 34) (hu : u < 1024) (t0 : MachineState) (ctx : LeafCtx S k idx u t0)
    (p : Nat) (hp : p < 512) (st : List Val × Val) (t : MachineState)
    (hinv : LeafInv k u t0 (2 * p) st t) :
    Sim image t 70 (do
        let (s0, s1) ← prf2 (ftsPrfInput S k idx p)
        let l0 ← hash16 (ftsLeafInput k idx (2 * p) s0)
        let l1 ← hash16 (ftsLeafInput k idx (2 * p + 1) s1)
        pure (st.1 ++ [l0, l1], if 2 * p = u then s0 else if 2 * p + 1 = u then s1 else st.2))
      (LeafInv k u t0 (2 * p + 2)) := by
  rw [fors_pair_spec]
  obtain ⟨-, hlen, hvals, hslots, hcap, tpc, t9, tregs, tframe, tlo1, tlo2⟩ := hinv
  have tpc' : t.pc = pcOf 161 := by rw [tpc, if_pos (by omega)]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by simp [leafRegs]), ctx.x5]
  -- block 161: even
  have hs0 := symRun_sound blk161 codeAt_161 t tpc' (by simp only [blk161.res, rv_simp])
  have hc0 : blk161.res.cycles = 2 := rfl
  rw [hc0] at hs0
  set t1 := blk161.res.toState t with ht1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk161.res.st.mem = [] from rfl, memEval_nil]
  have r1 : RegsEq t t1 [.x3] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc1 : t1.pc = pcOf 163 := by
    simp only [ht1, blk161.res, rv_simp, t9]
    rw [and_one_ofNat _ (by omega), if_neg (by rw [ofNat_bne_ofNat]; simp)]
  -- block 163: the paired prf query
  have hs2 := symRun_sound blk163 codeAt_163 t1 pc1 (by simp only [blk163.res, rv_simp])
  have hc2 : blk163.res.cycles = 5 := rfl
  rw [hc2] at hs2
  set t2 := blk163.res.toState t1 with ht2
  have f2 : Frame t1 t2 (fun x => x = 0x6A8) := by
    apply frame_toState; intro x hx hW
    simp only [blk163.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r2 : RegsEq t1 t2 [.x3, .x10, .x11, .x12] := by
    intro r hr; rw [ht2, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e2 := symRun_ecall blk163 codeAt_163 t1 (by simp only [blk163.res, rv_simp]) rfl
  have x10 : t2.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht2, blk163.res, rv_simp]
  have x11 : t2.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht2, blk163.res, rv_simp]
  have x12 : t2.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht2, blk163.res, rv_simp]
  have x5 : t2.getReg .x5 = 0 := by rw [r2.get .x5, r1.get .x5, tx5]
  have pc2 : t2.pc = pcOf 168 := by simp only [ht2, blk163.res, rv_simp]
  have t19 : t1.getReg .x9 = BitVec.ofNat 64 (2 * p) := by rw [r1.get .x9, t9]
  have m6A8 : t2.getMem (BitVec.ofNat 64 0x6A8) =
      BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * (p % 2 ^ 32)) := by
    simp only [ht2, blk163.res, rv_simp, t19]
    bvsimp []
    rw [show 2 * p / 2 = p by omega]
    refine (word_of_halves _ idx p ?_ ?_).trans (ofNat_congr (by omega))
    · rw [lo32_replace1, m1, tlo1, ctx.pb8]
    · rw [hi32_replace1]
  have ft2 : Frame t t2 (fun x => x = 0x6A8) := fun z hz hW => by rw [f2.getMem hz hW, m1]
  have hq : hashInput t2 = pad64 (ftsPrfInput S k idx p) := by
    obtain ⟨hn, hw⟩ := words_ftsPrfInput S hS k idx p
    refine hashInput_eq_pad64 t2 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m6A8, ft2.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [leafW]; omega), ctx.pb0,
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [leafW]; omega), ctx.pbP, ctx.pbS]
    simp [twWords_eq]
  have hb : (pad64 (ftsPrfInput S k idx p)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_ftsPrfInput S hS k idx p).1]
  refine (Sim.steps hs0 (Sim.steps hs2 (Sim.query_bind (W := 26 + (2 + 26)) e2 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (hq.trans (fmt_thInput _ _ _ _ _ _ (by decide)).symm) (fun a => ?_)))).mono
    (by rw [blocks_fmt, show ftsPrfInput S k idx p = thInput (tweak 8 k idx 0 p) S from rfl] at *; rw [hb]; norm_num)
    (fun _ _ h => h)
  set t3 := writeHash t2 a with ht3
  have f3 : Frame t2 t3 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t2 a _ x12 (by norm_num)
  have pc3 : t3.pc = pcOf 169 := by rw [ht3, writeHash_pc, pc2]; apply BitVec.eq_of_toNat_eq; simp
  have g3 : ∀ q, t3.getReg q = t2.getReg q := fun q => by rw [ht3, writeHash_getReg]
  have ft3 : Frame t t3 (fun x => x = 0x6A8 ∨ (0x140 ≤ x ∧ x < 0x140 + 32)) := ft2.trans f3
  have rt3 : RegsEq t0 t3 leafRegs := ((tregs.trans r1).trans r2 |>.trans
    (show RegsEq t2 t3 [] from fun q _ => g3 q)).mono (by decide)
  have lo3 : lo32 (t3.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) := by
    rw [f3.getMem (by norm_num) (by omega), m6A8, ctx.pb8, lo32_ofNat]
    apply BitVec.eq_of_toNat_eq; simp
  have hA := forsLeaf_B S k idx u hk hidx hu t0 ctx (2 * p) (by omega) st.1 hlen hvals (answerBytes 16 a)
    st.2 (by simp) t3 pc3 (by rw [g3, r2.get .x9, t19]) (by rw [g3, x11])
    (by rw [show 0x140 + 16 * (2 * p % 2) = 0x140 by omega]; exact sec_lo t2 a x12)
    (hslots.frame ft3 (by omega) (by intro i hi; constructor <;> omega))
    (fun h => by
      obtain ⟨h1, h2⟩ := hcap h
      exact ⟨h1, by rw [ft3.readWords _ _ (by omega) (by intro i hi; omega), h2]⟩)
    rt3 ((tframe.trans ft3).mono (by intro x hx; simp only [leafW] at hx ⊢; omega)) lo3
    (by rw [ft3.getMem (by norm_num) (by omega), tlo2])
  refine Sim.bind hA (fun r t4 h4 => ?_)
  obtain ⟨⟨-, hlen4, hvals4, hslots4, hcap4, tpc4, t49, tregs4, tframe4, tlo14, tlo24⟩, x411, sec4⟩ := h4
  -- block 161: odd
  have hs5 := symRun_sound blk161 codeAt_161 t4 (by rw [tpc4, if_pos (by omega)])
    (by simp only [blk161.res, rv_simp])
  have hc5 : blk161.res.cycles = 2 := rfl
  rw [hc5] at hs5
  set t5 := blk161.res.toState t4 with ht5
  have m5 : ∀ z, t5.getMem z = t4.getMem z := fun z => by
    rw [ht5, Result.toState_getMem, show blk161.res.st.mem = [] from rfl, memEval_nil]
  have r5 : RegsEq t4 t5 [.x3] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc5 : t5.pc = pcOf 169 := by
    simp only [ht5, blk161.res, rv_simp, t49]
    rw [and_one_ofNat _ (by omega), if_pos (by rw [ofNat_bne_ofNat]; simp)]
  have fr5 : Frame t4 t5 (fun _ => False) := fun z _ _ => m5 _
  have hB := forsLeaf_B S k idx u hk hidx hu t0 ctx (2 * p + 1) (by omega) r.1 hlen4 hvals4 (hiVal a)
    r.2 (by simp) t5 pc5 (by rw [r5.get .x9, t49]) (by rw [r5.get .x11, x411])
    (by
      rw [show 0x140 + 16 * ((2 * p + 1) % 2) = 0x150 by omega, readWords_ofNat_two, m5, m5,
        sec4 _ (by norm_num) (by norm_num) (by norm_num), sec4 _ (by norm_num) (by norm_num) (by norm_num),
        ← readWords_ofNat_two]
      exact sec_hi t2 a x12)
    (hslots4.frame fr5 (by omega) (by simp))
    (fun h => by
      obtain ⟨h1, h2⟩ := hcap4 h
      exact ⟨h1, by rw [fr5.readWords _ _ (by omega) (by simp), h2]⟩)
    ((tregs4.trans r5).mono (by decide)) ((tframe4.trans fr5).mono (by intro x hx; rcases hx with h | h; exact h; exact h.elim))
    (by rw [m5, tlo14]) (by rw [m5, tlo24])
  exact (Sim.steps hs5 hB).mono (by norm_num) (fun _ _ h => h.1)

/-- **FORS leaves** of tree `k` (pairs `p = 0 .. 511`). -/
theorem forsLeaves_sim (S : List Byte) (hS : S.length = 32) (k idx u : Nat) (hk : k < 14)
    (hidx : idx < 2 ^ 34) (hu : u < 1024) (t0 : MachineState) (ctx : LeafCtx S k idx u t0)
    (hpc : t0.pc = pcOf 161) (h9 : t0.getReg .x9 = BitVec.ofNat 64 0) :
    Sim image t0 (512 * 70) (buildFtsLeaves S k idx 10 u) (LeafInv k u t0 1024) := by
  unfold buildFtsLeaves
  exact Sim.foldlM_range (2 ^ 10 / 2) _ ([], []) (fun p => LeafInv k u t0 (2 * p)) 70
    (fun p hp st t h => forsLeaf_pair S hS k idx u hk hidx hu t0 ctx p (by omega) st t h)
    (LeafInv.init k u t0 hpc h9)

end SigGolfCandidate.Sign
