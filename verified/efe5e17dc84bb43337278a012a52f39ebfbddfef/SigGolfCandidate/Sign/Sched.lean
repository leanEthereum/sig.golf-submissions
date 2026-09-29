import SigGolfCandidate.Sign.SchedB

/-!
# `sign`, the authentication nodes in read order (`schedule_loop`, instructions 238 .. 295)

`sched_run` : from `238` (the PORS levels in memory, `levels[l]` at `lvBase l`), the root goes
to `EB + 32` and the schedule of the sorted leaves `vs` (`Ref.schedule`) copies the read node
`levels[h][j]` of read `r` to `SIG + 256 + 16 r` (`AP`, `x29`). The machine keeps the stack of
pending sibling heap indices at `STK + 8 ..` (`STP`, `x23`; `STK + 0 = 0` is the bottom sentinel).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- `top` of leaf `s`. -/
def topOf (vs : List Nat) (s : Nat) : Nat :=
  if s + 1 < vs.length then bitLen (vs.getD s 0 ^^^ vs.getD (s + 1) 0) - 1 else porsH

/-- The fold of leaf `s`. -/
def Yof (vs : List Nat) (st : SchedState) (s : Nat) : SchedState × Nat × Nat × Nat :=
  (List.range (topOf vs s)).foldl schedStep (st, porsT ||| vs.getD s 0, 0, (porsT ||| vs.getD s 0) % 2)

/-- `schedLeaf` through its fold. -/
theorem schedLeaf_eq (vs : List Nat) (st : SchedState) (s : Nat) :
    (schedLeaf vs st s).reads = (Yof vs st s).1.reads ∧
      (schedLeaf vs st s).stack = if s + 1 < vs.length then ((Yof vs st s).2.1 ^^^ 1) :: (Yof vs st s).1.stack
        else (Yof vs st s).1.stack := by
  unfold schedLeaf Yof topOf
  simp only
  generalize (List.range (if s + 1 < vs.length then bitLen (vs.getD s 0 ^^^ vs.getD (s + 1) 0) - 1 else porsH)).foldl
    schedStep (st, porsT ||| vs.getD s 0, 0, (porsT ||| vs.getD s 0) % 2) = Z
  obtain ⟨st', E', cnt', t'⟩ := Z
  simp only
  split <;> simp

/-- The bit-length loop of the schedule (`bitlen_3`, 256 .. 258). -/
theorem bitlen3_loop : ∀ (y : Nat) (w : Word) (t : MachineState), y ≠ 0 → y < 2 ^ 15 →
    t.pc = pcOf 256 → t.getReg .x13 = BitVec.ofNat 64 y → t.getReg .x20 = w →
    ∃ k c t', Steps image t k c t' ∧ c = 3 * blen y ∧ t'.pc = pcOf 259 ∧
      t'.getReg .x20 = w + BitVec.ofNat 64 (blen y) ∧ RegsEq t t' [.x13, .x20] ∧ (∀ z, t'.getMem z = t.getMem z)
  | y, w, t, hy, hy15, tpc, t13, t20 => by
    have hs1 := symRun_sound blk256 codeAt_256 t tpc (by simp only [blk256.res, rv_simp])
    set t1 := blk256.res.toState t with ht1
    have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
      rw [ht1, Result.toState_getMem, show blk256.res.st.mem = [] from rfl, memEval_nil]
    have r1 : RegsEq t t1 [.x13, .x20] := by
      intro q hq; rw [ht1, Result.toState_getReg]
      cases q <;> first | exact absurd (by decide) hq | rfl
    have x13 : t1.getReg .x13 = BitVec.ofNat 64 (y / 2) := by
      simp only [ht1, blk256.res, rv_simp, t13]; bvsimp []
    have x20 : t1.getReg .x20 = w + BitVec.ofNat 64 1 := by
      simp only [ht1, blk256.res, rv_simp, t20] <;> rfl
    have hb := SchedMath.bitLen_div_two hy
    have hc1 : blk256.res.cycles = 3 := rfl
    by_cases h2 : y / 2 = 0
    · refine ⟨_, _, t1, hs1, by rw [hc1, show blen y = bitLen y from rfl, hb, h2]; rfl, ?_, ?_, r1, m1⟩
      · simp only [ht1, blk256.res, rv_simp, t13]; bvsimp [ofNat_bne_ofNat]
        try rw [if_neg (by simp; omega)]
      · rw [x20, show blen y = bitLen y from rfl, hb, h2]; rfl
    · have pc1 : t1.pc = pcOf 256 := by
        simp only [ht1, blk256.res, rv_simp, t13]; bvsimp [ofNat_bne_ofNat]
        rw [if_pos (by simp; omega)]
      obtain ⟨k, c, t', hs', hc', pc', x20', r', m'⟩ := bitlen3_loop (y / 2) _ t1 h2 (by omega) pc1 x13 x20
      refine ⟨_, _, t', hs1.trans hs', by rw [hc1, hc', show blen y = bitLen y from rfl, hb]; ring,
        pc', ?_, (r1.trans r').mono (by decide), fun z => by rw [m', m1]⟩
      rw [x20', show blen y = bitLen y from rfl, hb, BitVec.add_assoc, ofNat_add_ofNat]
      congr 2; simp only [blen]; omega
  termination_by y => y
  decreasing_by omega

/-- Facts about the sorted keys and the levels at the start of the schedule. -/
structure SchCtx (levels : List (List Val)) (L : List Nat) (t0 : MachineState) : Prop where
  hlen : L.length = 15
  hsort : (L.map keyV).Pairwise (· < ·)
  hlt : ∀ v ∈ L.map keyV, v < 2 ^ 14
  hbound : KeysBound L
  keys : KeysAt t0 L
  sent : t0.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22)
  lvlen : ∀ l, l < 15 → (levels.getD l []).length = 2 ^ (14 - l)
  lvvals : ∀ l, l < 15 → ∀ v ∈ levels.getD l [], v.length = 16
  lvslots : ∀ l (hl : l < 15), Slots t0 (lvBase l) (levels.getD l [])

/-- Addresses written by the schedule loop (given the reads so far). -/
def schW' (n : Nat) (a : Nat) : Prop := (0x760 ≤ a ∧ a < 0x7E0) ∨ (0x3400 ≤ a ∧ a < 0x3400 + 16 * n)

/-- Invariant of the leaf loop before leaf `s`. -/
def SchInv (levels : List (List Val)) (t0 : MachineState) (s : Nat) (st : SchedState) (t : MachineState) : Prop :=
  s ≤ 15 ∧ t.pc = (if s < 15 then pcOf 249 else pcOf 296) ∧ t.getReg .x8 = BitVec.ofNat 64 s ∧
  t.getReg .x24 = BitVec.ofNat 64 (2 ^ 14) ∧ t.getReg .x30 = BitVec.ofNat 64 0xB0000 ∧
  StackAt st.stack t ∧ st.stack.length ≤ s ∧ ReadsAt levels st.reads t ∧ st.reads.length ≤ 14 * s ∧
  RegsEq t0 t schRegs ∧ Frame t0 t (schW' st.reads.length)

theorem bitLen_top (v : Nat) (hv : v < 2 ^ 14) : bitLen (2 ^ 14 ^^^ v) = 15 := by
  have h1 : 2 ^ 14 ^^^ v < 2 ^ 15 := Nat.xor_lt_two_pow (by norm_num) (by omega)
  have h2 : (2 ^ 14 ^^^ v) / 2 ^ 14 = 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self (by norm_num), Nat.div_eq_of_lt hv]; rfl
  apply Nat.le_antisymm ((SchedMath.bitLen_le_iff _ _).2 h1)
  by_contra h
  have := (SchedMath.bitLen_le_iff (2 ^ 14 ^^^ v) 14).1 (by omega)
  rw [Nat.div_eq_of_lt this] at h2
  omega

theorem ushr8' (k : Nat) (hk : k < 2 ^ 64) :
    BitVec.ofNat 64 k >>> ((8#64 : Word).toNat % 64) = BitVec.ofNat 64 (keyV k) := by
  rw [show (8#64 : Word).toNat % 64 = 8 from rfl]; exact ushr8 k hk

theorem sch_leaf (levels : List (List Val)) (L : List Nat) (t0 : MachineState) (ctx : SchCtx levels L t0)
    (s : Nat) (hs : s < 15) (st : SchedState) (t : MachineState) (h : SchInv levels t0 s st t) :
    ∃ k c t', Steps image t k c t' ∧ c ≤ 345 ∧ SchInv levels t0 (s + 1) (schedLeaf (L.map keyV) st s) t' := by
  obtain ⟨-, tpc, t8, t24, t30, hst, hsl, hrd, hrl, tregs, tframe⟩ := h
  rw [if_pos hs] at tpc
  have hvsl : (L.map keyV).length = 15 := by rw [List.length_map, ctx.hlen]
  have hvlt : (L.map keyV).getD s 0 < 2 ^ 14 := vs_lt_T L ctx.hlen ctx.hlt s hs
  -- the key words
  have hk : ∀ i, i < 16 → t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * i)) = t0.getMem (BitVec.ofNat 64 (0x6E0 + 8 * i)) :=
    fun i hi => tframe.getMem (by omega) (by simp only [schW']; omega)
  have hvs0 : t.getMem (BitVec.ofNat 64 (s * 8 + 1760)) = BitVec.ofNat 64 (L.getD s 0) := by
    rw [show s * 8 + 1760 = 0x6E0 + 8 * s by ring, hk s (by omega), ctx.keys s hs]
  set w := if s + 1 < 15 then (L.map keyV).getD (s + 1) 0 else 2 ^ 14 with hw
  have hvs1 : t.getMem (BitVec.ofNat 64 (s * 8 + 1768)) >>> 8 = BitVec.ofNat 64 w := by
    rw [show s * 8 + 1768 = 0x6E0 + 8 * (s + 1) by ring, hk (s + 1) (by omega)]
    by_cases h1 : s + 1 < 15
    · rw [ctx.keys (s + 1) h1, ushr8 _ (by have := keysBound_getD ctx.hbound (s + 1); omega), hw, if_pos h1,
        vs_getD]
    · rw [show s + 1 = 15 by omega, show 0x6E0 + 8 * 15 = 0x758 from rfl, ctx.sent, ushr8 _ (by norm_num), hw,
        if_neg h1]; rfl
  have hwlt : w < 2 ^ 15 := by
    rw [hw]; split
    · have := vs_lt_T L ctx.hlen ctx.hlt (s + 1) (by omega); omega
    · norm_num
  set y := w ^^^ (L.map keyV).getD s 0 with hy
  have hy0 : y ≠ 0 := by
    intro h0
    have := SchedMath.xor_eq_zero h0
    rw [hw] at this; split at this
    · have := vs_lt_succ L ctx.hlen ctx.hsort s (by omega); omega
    · omega
  have hy15 : y < 2 ^ 15 := Nat.xor_lt_two_pow hwlt (by omega)
  -- block 249
  have hs1 := symRun_sound blk249 codeAt_249 t tpc (by
    simp only [blk249.res, rv_simp, t8]; bvsimp [accessValid_ofNat]; omega)
  set t1 := blk249.res.toState t with ht1
  have hc1 : blk249.res.cycles = 7 := rfl
  rw [hc1] at hs1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk249.res.st.mem = [] from rfl, memEval_nil]
  have r1 : RegsEq t t1 [.x3, .x9, .x13, .x20] := by
    intro q hq; rw [ht1, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have x9 : t1.getReg .x9 = BitVec.ofNat 64 ((L.map keyV).getD s 0) := by
    simp only [ht1, blk249.res, rv_simp, t8]; bvsimp []
    rw [hvs0, ushr8 _ (by have := keysBound_getD ctx.hbound s; omega), vs_getD]
  have x13 : t1.getReg .x13 = BitVec.ofNat 64 y := by
    simp only [ht1, blk249.res, rv_simp, t8]; bvsimp []
    rw [hvs0, ushr8 _ (by have := keysBound_getD ctx.hbound s; omega), hvs1, ← vs_getD,
      ofNat_xor_ofNat _ _ (by omega) (by omega)]
  -- the bit-length loop: TOP = bitlen(y) - 1
  obtain ⟨k2, c2, t2, hs2, hc2, pc2, x20, r2, m2⟩ := bitlen3_loop y (t1.getReg .x20) t1 hy0 hy15
    (by simp only [ht1, blk249.res, rv_simp]) x13 rfl
  have hbl1 : 1 ≤ blen y := SchedMath.one_le_bitLen hy0
  have hbl15 : blen y ≤ 15 := (SchedMath.bitLen_le_iff y 15).2 hy15
  have x20' : t2.getReg .x20 = BitVec.ofNat 64 (blen y - 1) := by
    rw [x20]; simp only [ht1, blk249.res, rv_simp]
    rw [show (18446744073709551615#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 1) from rfl, ofNat_add_ofNat,
      ofNat_eq_iff]; omega
  -- `top` is the Ref's
  have htop : blen y - 1 = topOf (L.map keyV) s := by
    unfold topOf; rw [hvsl]
    by_cases h1 : s + 1 < 15
    · rw [if_pos h1, show blen y = bitLen y from rfl, hy, hw, if_pos h1, Nat.xor_comm]
    · rw [if_neg h1, show blen y = bitLen y from rfl, hy, hw, if_neg h1, bitLen_top _ hvlt]; rfl
  have htop14 : topOf (L.map keyV) s ≤ 14 := by rw [← htop]; omega
  -- block 259
  have hs3 := symRun_sound blk259 codeAt_259 t2 pc2 (by simp only [blk259.res, rv_simp])
  set t3 := blk259.res.toState t2 with ht3
  have hc3 : blk259.res.cycles = 4 := rfl
  rw [hc3] at hs3
  have m3 : ∀ z, t3.getMem z = t.getMem z := fun z => by
    rw [ht3, Result.toState_getMem, show blk259.res.st.mem = [] from rfl, memEval_nil, m2, m1]
  have r3 : RegsEq t2 t3 [.x15, .x18, .x19, .x21] := by
    intro q hq; rw [ht3, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  set E0 := porsT ||| (L.map keyV).getD s 0 with hE0
  have hE0v : E0 = 2 ^ 14 + (L.map keyV).getD s 0 := SchedMath.porsT_or hvlt
  have x18 : t3.getReg .x18 = BitVec.ofNat 64 E0 := by
    simp only [ht3, blk259.res, rv_simp, r2.get .x9, x9, r2.get .x24, r1.get .x24, t24]
    rw [ofNat_or_ofNat _ _ (by omega) (by norm_num), Nat.or_comm]; rfl
  have rt3 : RegsEq t t3 ([.x3, .x9, .x13, .x20] ++ [.x13, .x20] ++ [.x15, .x18, .x19, .x21]) := (r1.trans r2).trans r3
  -- the inner loop
  have hst3 : StackAt st.stack t3 := ⟨hst.1, by rw [rt3.get .x23, hst.2.1], fun i hi => by rw [m3]; exact hst.2.2.1 i hi,
    by rw [m3, hst.2.2.2.1], hst.2.2.2.2⟩
  have hrd3 : ReadsAt levels st.reads t3 := ⟨hrd.1, by rw [rt3.get .x29, hrd.2.1], fun r hr => by
    rw [readWords_congr t t3 _ 2 (fun k _ => m3 _)]; exact hrd.2.2.1 r hr, hrd.2.2.2⟩
  have hlvt3 : ∀ l (hl : l < 15), Slots t3 (lvBase l) (levels.getD l []) := fun l hl i hi => by
    rw [readWords_congr t t3 _ 2 (fun k _ => m3 _), tframe.readWords _ _ (by
      have := lvBase_le l (by omega)
      have : i < 2 ^ (14 - l) := by rw [ctx.lvlen l hl] at hi; exact hi
      omega) (by
      intro k hk
      have := lvBase_le l (by omega)
      have := lvBase_ge l
      have : i < 2 ^ (14 - l) := by rw [ctx.lvlen l hl] at hi; exact hi
      simp only [schW']; omega)]
    exact ctx.lvslots l hl i hi
  obtain ⟨k4, c4, t4, hs4, hc4, pc4, x18', hE1', hE2', x30', st4, rd4, hR4, hmono4, r4, f4⟩ :=
    sch_inner levels ctx.lvlen ctx.lvvals (topOf (L.map keyV) s) htop14 (14 * s) (by omega) (topOf (L.map keyV) s) 0
      (st, E0, 0, E0 % 2) t3 (by omega) (by simp only [ht3, blk259.res, rv_simp])
      (by simp only [ht3, blk259.res, rv_simp] <;> rfl) (by rw [r3.get .x20, x20', htop])
      x18 (by simp only; omega) (by simp only; omega) (by rw [rt3.get .x30, t30]) hst3 hrd3
      (by simp only; omega) hlvt3
  rw [← List.range_eq_range'] at x18' hE1' hE2' st4 rd4 hR4 hmono4 f4
  have hY : (List.range (topOf (L.map keyV) s)).foldl schedStep (st, E0, 0, E0 % 2) = Yof (L.map keyV) st s := rfl
  rw [hY] at x18' hE1' hE2' st4 rd4 hR4 hmono4 f4
  simp only at hmono4 f4
  obtain ⟨hlr, hls⟩ := schedLeaf_eq (L.map keyV) st s
  have t48 : t4.getReg .x8 = BitVec.ofNat 64 s := by rw [r4.get .x8, rt3.get .x8, t8]
  -- block 288
  have hs5 := symRun_sound blk288 codeAt_288 t4 pc4 (by simp only [blk288.res, rv_simp])
  set t5 := blk288.res.toState t4 with ht5
  have hc5 : blk288.res.cycles = 2 := rfl
  rw [hc5] at hs5
  have m5 : ∀ z, t5.getMem z = t4.getMem z := fun z => by
    rw [ht5, Result.toState_getMem, show blk288.res.st.mem = [] from rfl, memEval_nil]
  have r5 : RegsEq t4 t5 [.x17] := by
    intro q hq; rw [ht5, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have hstl : (Yof (L.map keyV) st s).1.stack.length ≤ st.stack.length := foldl_stack_len _ _
  -- the common tail (block 293) from a state at 293
  have tail : ∀ t6 : MachineState, t6.pc = pcOf 293 → RegsEq t4 t6 [.x3, .x17, .x23] →
      StackAt (schedLeaf (L.map keyV) st s).stack t6 →
      (∀ a : Nat, a < 2 ^ 64 → (a < 0x760 ∨ 0x7E0 ≤ a) → t6.getMem (BitVec.ofNat 64 a) = t4.getMem (BitVec.ofNat 64 a)) →
      ∃ k c t', Steps image t6 k c t' ∧ c = 3 ∧ SchInv levels t0 (s + 1) (schedLeaf (L.map keyV) st s) t' := by
    intro t6 pc6 r6 st6 m6
    have hs7 := symRun_sound blk293 codeAt_293 t6 pc6 (by simp only [blk293.res, rv_simp])
    set t7 := blk293.res.toState t6 with ht7
    have r7 : RegsEq t6 t7 [.x8, .x17] := by
      intro q hq; rw [ht7, Result.toState_getReg]
      cases q <;> first | exact absurd (by decide) hq | rfl
    have m7 : ∀ z, t7.getMem z = t6.getMem z := fun z => by
      rw [ht7, Result.toState_getMem, show blk293.res.st.mem = [] from rfl, memEval_nil]
    have x86 : t6.getReg .x8 = BitVec.ofNat 64 s := by rw [r6.get .x8, t48]
    have rt7 := ((rt3.trans r4).trans r6).trans r7
    refine ⟨_, _, t7, hs7, rfl, by omega, ?_, ?_, by rw [rt7.get .x24, t24], by rw [rt7.get .x30, t30],
      ⟨st6.1, by rw [r7.get .x23, st6.2.1], fun i hi => by rw [m7]; exact st6.2.2.1 i hi, by rw [m7, st6.2.2.2.1],
        st6.2.2.2.2⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ht7, blk293.res, rv_simp, x86, ofNat_add_ofNat, ofNat_bne_ofNat]
      by_cases h : s + 1 < 15
      · rw [if_pos (by simp; omega), if_pos h]
      · rw [if_neg (by simp; omega), if_neg h]
    · simp only [ht7, blk293.res, rv_simp, x86, ofNat_add_ofNat]
    · rw [hls]; split
      · simp only [List.length_cons]; omega
      · omega
    · rw [hlr]
      refine ⟨rd4.1, by rw [r7.get .x29, r6.get .x29, rd4.2.1], fun r hr => ?_, rd4.2.2.2⟩
      rw [readWords_congr t4 t7 _ 2 (fun k hk => by
        rw [m7, m6 _ (by have := rd4.1; omega) (by have := rd4.1; omega)])]
      exact rd4.2.2.1 r hr
    · rw [hlr]; omega
    · exact (tregs.trans rt7).mono (by decide)
    · rw [hlr]
      intro a ha hW
      simp only [schW', not_or, not_and, not_lt] at hW
      rw [m7, m6 a ha (by omega), f4 a ha (by omega), m3, tframe a ha (by simp only [schW']; omega)]
  have hcost : 7 + c2 + 4 + c4 + 2 + 3 + 3 ≤ 345 := by
    have : c4 ≤ 20 * 14 + 1 := le_trans hc4 (by omega)
    omega
  have pc5 : t5.pc = if s = 14 then pcOf 293 else pcOf 290 := by
    simp only [ht5, blk288.res, rv_simp, t48, ofNat_beq_ofNat]
    by_cases h : s = 14
    · rw [if_pos (by simp [h]), if_pos h]
    · rw [if_neg (by simp; omega), if_neg h]
  by_cases h14 : s = 14
  · -- the last leaf: no push
    have hnp : ¬ s + 1 < (L.map keyV).length := by rw [hvsl]; omega
    rw [if_neg hnp] at hls
    obtain ⟨k6, c6, t6, hs6, hc6, inv6⟩ := tail t5 (by rw [pc5, if_pos h14]) (r5.mono (by decide))
      (by rw [hls]; exact ⟨st4.1, by rw [r5.get .x23, st4.2.1], fun i hi => by rw [m5]; exact st4.2.2.1 i hi,
        by rw [m5, st4.2.2.2.1], st4.2.2.2.2⟩)
      (fun a _ _ => m5 _)
    exact ⟨_, _, t6, hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans hs6)))), by rw [hc2, hc6]; omega, inv6⟩
  · -- push `E xor 1`
    have hp : s + 1 < (L.map keyV).length := by rw [hvsl]; omega
    rw [if_pos hp] at hls
    have htop13 : topOf (L.map keyV) s ≤ 13 := by
      rw [← htop, show blen y = bitLen y from rfl]
      have : y < 2 ^ 14 := by
        rw [hy, hw, if_pos (by omega)]
        exact Nat.xor_lt_two_pow (vs_lt_T L ctx.hlen ctx.hlt (s + 1) (by omega)) hvlt
      have := (SchedMath.bitLen_le_iff y 14).2 this
      omega
    set E' := (Yof (L.map keyV) st s).2.1 with hE'
    have hm : 2 ^ (15 - topOf (L.map keyV) s) = 2 * 2 ^ (14 - topOf (L.map keyV) s) := by
      rw [← Nat.pow_succ']; congr 1; omega
    have hm2 : 2 ≤ 2 ^ (14 - topOf (L.map keyV) s) := by
      calc 2 = 2 ^ 1 := rfl
        _ ≤ 2 ^ (14 - topOf (L.map keyV) s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hm15 : 2 ^ (15 - topOf (L.map keyV) s) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hx1 := xor1_eq E'
    have hQ1 : 1 ≤ E' ^^^ 1 ∧ E' ^^^ 1 < 2 ^ 15 := by omega
    have hsl4 : (Yof (L.map keyV) st s).1.stack.length ≤ 13 := by omega
    have t523 : t5.getReg .x23 = BitVec.ofNat 64 (0x760 + 8 * (Yof (L.map keyV) st s).1.stack.length) := by
      rw [r5.get .x23, st4.2.1]
    have hs6 := symRun_sound blk290 codeAt_290 t5 (by rw [pc5, if_neg h14]) (by
      simp only [blk290.res, rv_simp, t523, ofNat_add_ofNat, accessValid_ofNat]; omega)
    set t6 := blk290.res.toState t5 with ht6
    have hc6 : blk290.res.cycles = 3 := rfl
    rw [hc6] at hs6
    have hm6 : ∀ a : Nat, a < 2 ^ 64 → t6.getMem (BitVec.ofNat 64 a) =
        if a = 0x760 + 8 * ((Yof (L.map keyV) st s).1.stack.length + 1) then BitVec.ofNat 64 (E' ^^^ 1)
        else t5.getMem (BitVec.ofNat 64 a) := by
      intro a ha
      simp only [ht6, blk290.res, rv_simp, t523, ofNat_add_ofNat, r5.get .x18, x18']
      rw [show (1#64 : Word) = BitVec.ofNat 64 1 from rfl, ofNat_xor_ofNat _ _ (by omega) (by norm_num)]
      by_cases h : a = 0x760 + 8 * ((Yof (L.map keyV) st s).1.stack.length + 1)
      · rw [if_pos (by rw [h]; exact ofNat_congr (by ring)), if_pos h]
      · rw [if_neg (by rw [ofNat_eq_iff]; omega), if_neg h]
    have r6 : RegsEq t5 t6 [.x3, .x23] := by
      intro q hq; rw [ht6, Result.toState_getReg]
      cases q <;> first | exact absurd (by decide) hq | rfl
    obtain ⟨k7, c7, t7, hs7, hc7, inv7⟩ := tail t6 (by simp only [ht6, blk290.res, rv_simp])
      ((r5.trans r6).mono (by decide))
      (by
        rw [hls]
        refine ⟨by simp only [List.length_cons]; omega, ?_, fun i hi => ?_, ?_, ?_⟩
        · simp only [ht6, blk290.res, rv_simp, t523, ofNat_add_ofNat, List.length_cons]
          exact ofNat_congr (by ring)
        · simp only [List.length_cons] at hi ⊢
          rw [hm6 _ (by omega)]
          rcases i with _ | i
          · rw [if_pos (by omega)]; rfl
          · rw [if_neg (by omega), m5, show (Yof (L.map keyV) st s).1.stack.length + 1 - (i + 1) =
              (Yof (L.map keyV) st s).1.stack.length - i by omega]
            exact st4.2.2.1 i (by omega)
        · rw [hm6 _ (by norm_num), if_neg (by omega), m5, st4.2.2.2.1]
        · intro Q hQ
          rcases List.mem_cons.mp hQ with hQ | hQ
          · rw [hQ]; exact hQ1
          · exact st4.2.2.2.2 Q hQ)
      (fun a ha hout => by rw [hm6 a ha, if_neg (by omega), m5])
    exact ⟨_, _, t7, hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans hs7))))),
      by rw [hc2, hc7]; omega, inv7⟩

theorem sch_loop (levels : List (List Val)) (L : List Nat) (t0 : MachineState) (ctx : SchCtx levels L t0) :
    ∀ n, n ≤ 15 → ∀ t, SchInv levels t0 0 ⟨[], [], []⟩ t →
      ∃ k c t', Steps image t k c t' ∧ c ≤ n * 345 ∧
        SchInv levels t0 n ((List.range n).foldl (schedLeaf (L.map keyV)) ⟨[], [], []⟩) t' := by
  intro n
  induction n with
  | zero => intro _ t h; exact ⟨0, 0, t, Steps.refl t, by simp, by simpa using h⟩
  | succ n ih =>
    intro hn t h
    obtain ⟨k1, c1, t1, s1, hc1, h1⟩ := ih (by omega) t h
    obtain ⟨k2, c2, t2, s2, hc2, h2⟩ := sch_leaf levels L t0 ctx n (by omega) _ t1 h1
    refine ⟨_, _, t2, s1.trans s2, by rw [Nat.succ_mul]; omega, ?_⟩
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    exact h2

/-- **The schedule** (from 238): the root to `EB + 32`, the reads of `schedule vs` to the
signature's auth slots; ends at 296. -/
theorem sched_run (levels : List (List Val)) (L : List Nat) (t : MachineState) (ctx : SchCtx levels L t)
    (tpc : t.pc = pcOf 238) (t19 : t.getReg .x19 = BitVec.ofNat 64 (lvBase 14)) :
    ∃ k c t', Steps image t k c t' ∧ c ≤ 11 + 15 * 345 ∧ t'.pc = pcOf 296 ∧
      t'.readWords (BitVec.ofNat 64 0x120) 2 = wordsOf ((levels.getD 14 []).getD 0 []) ∧
      ReadsAt levels (schedule (L.map keyV)).2 t' ∧
      RegsEq t t' schRegs ∧
      Frame t t' (fun a => (0x120 ≤ a ∧ a < 0x130) ∨ schW' (schedule (L.map keyV)).2.length a) := by
  have hs1 := symRun_sound blk238 codeAt_238 t tpc (by
    simp only [blk238.res, rv_simp, t19, accessValid_ofNat, ofNat_add_ofNat]; unfold lvBase; norm_num)
  set t1 := blk238.res.toState t with ht1
  have hc1 : blk238.res.cycles = 11 := rfl
  rw [hc1] at hs1
  have hroot := (ctx.lvslots 14 (by norm_num)) 0 (by rw [ctx.lvlen 14 (by norm_num)]; norm_num)
  simp only [Nat.mul_zero, Nat.add_zero] at hroot
  have hm1 : ∀ a : Nat, a < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 a) =
      if a = 0x760 then 0 else if a = 0x128 then t.getMem (BitVec.ofNat 64 (lvBase 14 + 8))
      else if a = 0x120 then t.getMem (BitVec.ofNat 64 (lvBase 14)) else t.getMem (BitVec.ofNat 64 a) := by
    intro a ha
    simp only [ht1, blk238.res, rv_simp, t19, ofNat_add_ofNat, ofNat_eq_iff]
    have : lvBase 14 = 0xB0000 - 32 := rfl
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega)
  have r1 : RegsEq t t1 [.x1, .x2, .x8, .x23, .x24, .x29, .x30] := by
    intro q hq; rw [ht1, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have hl14 : lvBase 14 = 0xB0000 - 32 := rfl
  have ctx1 : SchCtx levels L t1 := by
    refine ⟨ctx.hlen, ctx.hsort, ctx.hlt, ctx.hbound, fun i hi => ?_, ?_, ctx.lvlen, ctx.lvvals, fun l hl i hi => ?_⟩
    · rw [hm1 _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]; exact ctx.keys i hi
    · rw [hm1 _ (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num)]; exact ctx.sent
    · have := lvBase_le l (by omega)
      have := lvBase_ge l
      have : i < 2 ^ (14 - l) := by rw [ctx.lvlen l hl] at hi; exact hi
      rw [readWords_congr t t1 _ 2 (fun k hk => by
        rw [hm1 _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)])]
      exact ctx.lvslots l hl i hi
  have inv0 : SchInv levels t1 0 ⟨[], [], []⟩ t1 := by
    refine ⟨by omega, by simp only [ht1, blk238.res, rv_simp] <;> rfl, by simp only [ht1, blk238.res, rv_simp] <;> rfl,
      by simp only [ht1, blk238.res, rv_simp] <;> rfl, by simp only [ht1, blk238.res, rv_simp] <;> rfl,
      ⟨by simp, by simp only [ht1, blk238.res, rv_simp] <;> rfl, fun i hi => by simp at hi,
        by rw [hm1 _ (by norm_num), if_pos rfl], fun Q hQ => by simp at hQ⟩,
      by simp, ⟨by simp, by simp only [ht1, blk238.res, rv_simp] <;> rfl, fun r hr => by simp at hr,
        fun r hr => by simp at hr⟩,
      by simp, RegsEq.refl _ _, Frame.refl _ _⟩
  obtain ⟨k2, c2, t2, hs2, hc2, ⟨-, pc2, -, -, -, -, -, rd2, -, rg2, fr2⟩⟩ := sch_loop levels L t1 ctx1 15 le_rfl t1 inv0
  have hsch : schedule (L.map keyV) = (((List.range 15).foldl (schedLeaf (L.map keyV)) ⟨[], [], []⟩).segs,
      ((List.range 15).foldl (schedLeaf (L.map keyV)) ⟨[], [], []⟩).reads) := by
    unfold schedule; rw [List.length_map, ctx.hlen]
  refine ⟨_, _, t2, hs1.trans hs2, by omega, by simpa using pc2, ?_, by rw [hsch]; exact rd2,
    (r1.trans rg2).mono (by intro q hq; simp [schRegs] at hq ⊢; tauto), ?_⟩
  · rw [fr2.readWords _ _ (by norm_num) (by intro i hi; simp only [schW']; omega), readWords_ofNat_two,
      hm1 _ (by norm_num), hm1 _ (by norm_num)]
    simp only [show ¬ ((0x120 : Nat) = 0x760) by norm_num, show ¬ ((0x128 : Nat) = 0x760) by norm_num,
      show ¬ ((0x120 : Nat) = 0x128) by norm_num, if_false, if_true]
    rw [← readWords_ofNat_two, hroot]
    exact congrArg wordsOf (getD_of_lt (by rw [ctx.lvlen 14 (by norm_num)]; norm_num)).symm
  · intro a ha hW
    rw [hsch] at hW
    simp only [not_or] at hW
    rw [fr2 a ha hW.2, hm1 a ha, if_neg (by simp only [schW'] at hW; omega), if_neg (by omega), if_neg (by omega)]

end SigGolfCandidate.Sign
