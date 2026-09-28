import SigGolfCandidate.Sign.PorsLevel

/-! # `sign` schedule, part A: definitions, `readAddr`, the fold and merge branches (see `Sched.lean`). -/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem xor1_eq (E : Nat) : E ^^^ 1 = 2 * (E / 2) + (E + 1) % 2 := by
  have h1 : (E ^^^ 1) / 2 = E / 2 := by rw [Nat.xor_div_two]; simp
  have h2 : (E ^^^ 1) % 2 = (E + 1) % 2 := Nat.xor_mod_two_eq
  have := Nat.div_add_mod (E ^^^ 1) 2
  omega

/-- The value of a read position. -/
def readVal (levels : List (List Val)) (hj : Nat × Nat) : Val := (levels.getD hj.1 []).getD hj.2 []

theorem sub_neg (x y : Nat) (hy : y < 2 ^ 64) (hxy : x < y) :
    BitVec.ofNat 64 x - BitVec.ofNat 64 y = BitVec.ofNat 64 (2 ^ 64 - (y - x)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hy,
    Nat.mod_eq_of_lt (by omega : x < 2 ^ 64)]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  omega

theorem shl4_neg (D : Nat) (h0 : 0 < D) (hD : 16 * D < 2 ^ 64) :
    BitVec.ofNat 64 (2 ^ 64 - D) <<< 4 = BitVec.ofNat 64 (2 ^ 64 - 16 * D) := by
  rw [ofNat_shiftLeft]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : (2 ^ 64 - D) * 2 ^ 4 = 15 * 2 ^ 64 + (2 ^ 64 - 16 * D) := by omega
  rw [this, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - 16 * D < 2 ^ 64)]
  omega

theorem add_neg (D c : Nat) (hD : D ≤ c) (hc : c < 2 ^ 64) :
    BitVec.ofNat 64 (2 ^ 64 - D) + BitVec.ofNat 64 c = BitVec.ofNat 64 (c - D) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  rcases Nat.eq_zero_or_pos D with rfl | hpos
  · simp
  · rw [Nat.mod_eq_of_lt (by omega : 2 ^ 64 - D < 2 ^ 64), Nat.mod_eq_of_lt hc,
      show 2 ^ 64 - D + c = 2 ^ 64 + (c - D) by omega, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]

/-- The address of the `on_read` load. -/
theorem readAddr (E h : Nat) (hh : h ≤ 13) (hE1 : 2 ^ (14 - h) ≤ E) (hE2 : E < 2 ^ (15 - h)) :
    ((BitVec.ofNat 64 E ^^^ 1#64) - 3#64 <<< ((14#64 - BitVec.ofNat 64 h).toNat % 64)) <<< ((4#64).toNat % 64) +
      BitVec.ofNat 64 0xB0000 = BitVec.ofNat 64 (lvBase h + 16 * ((E ^^^ 1) - 2 ^ (14 - h))) := by
  have hm : 2 ^ (15 - h) = 2 * 2 ^ (14 - h) := by rw [← Nat.pow_succ']; congr 1; omega
  have hm2 : 2 ≤ 2 ^ (14 - h) := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ (14 - h) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hm14 : 2 ^ (14 - h) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmev : 2 ^ (14 - h) % 2 = 0 := by
    rw [show 14 - h = (13 - h) + 1 by omega, Nat.pow_succ]; omega
  have hx := xor1_eq E
  have hsh : (14#64 - BitVec.ofNat 64 h).toNat % 64 = 14 - h := by
    rw [BitVec.toNat_sub]; simp; omega
  rw [hsh, show (1#64 : Word) = BitVec.ofNat 64 1 from rfl, ofNat_xor_ofNat _ _ (by omega) (by norm_num),
    show (3#64 : Word) = BitVec.ofNat 64 3 from rfl, ofNat_shiftLeft, show (4#64 : Word).toNat % 64 = 4 from rfl]
  unfold lvBase
  rw [hm]
  generalize hmdef : 2 ^ (14 - h) = m at *
  generalize hxdef : E ^^^ 1 = x at *
  have hxm : m ≤ x ∧ x < 2 * m := by omega
  rw [sub_neg x (3 * m) (by omega) (by omega),
    shl4_neg (3 * m - x) (by omega) (by omega), show (720896#64 : Word) = BitVec.ofNat 64 0xB0000 from rfl,
    add_neg (16 * (3 * m - x)) 0xB0000 (by omega) (by norm_num)]
  exact ofNat_congr (by omega)

/-- The stack of pending sibling heap indices in memory (head = top, at `STP`). -/
def StackAt (stack : List Nat) (t : MachineState) : Prop :=
  stack.length ≤ 14 ∧ t.getReg .x23 = BitVec.ofNat 64 (0x760 + 8 * stack.length) ∧
  (∀ i (hi : i < stack.length), t.getMem (BitVec.ofNat 64 (0x760 + 8 * (stack.length - i))) =
    BitVec.ofNat 64 stack[i]) ∧
  t.getMem (BitVec.ofNat 64 0x760) = 0 ∧ (∀ Q ∈ stack, 1 ≤ Q ∧ Q < 2 ^ 15)

/-- The reads so far, copied to the signature's auth slots. -/
def ReadsAt (levels : List (List Val)) (reads : List (Nat × Nat)) (t : MachineState) : Prop :=
  reads.length ≤ 210 ∧ t.getReg .x29 = BitVec.ofNat 64 (0x3400 + 16 * reads.length) ∧
  (∀ r (hr : r < reads.length), t.readWords (BitVec.ofNat 64 (0x3400 + 16 * r)) 2 = wordsOf (readVal levels reads[r])) ∧
  ∀ r (hr : r < reads.length), (readVal levels reads[r]).length = 16

/-- The PORS levels in memory. -/
structure LevelsAt (levels : List (List Val)) (t : MachineState) : Prop where
  len : levels.length = 15
  lvl : ∀ l (hl : l < 15), (levels.getD l []).length = 2 ^ (14 - l) ∧
    (∀ v ∈ levels.getD l [], v.length = 16) ∧ Slots t (lvBase l) (levels.getD l [])

/-- Addresses written by the schedule. -/
def schW (a : Nat) : Prop := (0x120 ≤ a ∧ a < 0x130) ∨ (0x760 ≤ a ∧ a < 0x7E0) ∨ (0x3400 ≤ a ∧ a < 0x3400 + 16 * 210)

def schRegs : List Reg :=
  [.x1, .x2, .x3, .x8, .x9, .x13, .x15, .x17, .x18, .x19, .x20, .x21, .x23, .x24, .x25, .x26, .x29, .x30]

/-- `sch_next` (286 .. 287): `H += 1`, back to `sch_h`. -/
theorem sch_next (t : MachineState) (tpc : t.pc = pcOf 286) (h : Nat) (t19 : t.getReg .x19 = BitVec.ofNat 64 h) :
    Steps image t 2 2 (blk286.res.toState t) ∧ (blk286.res.toState t).pc = pcOf 263 ∧
      (blk286.res.toState t).getReg .x19 = BitVec.ofNat 64 (h + 1) ∧
      RegsEq t (blk286.res.toState t) [.x19] ∧ (∀ z, (blk286.res.toState t).getMem z = t.getMem z) := by
  refine ⟨symRun_sound blk286 codeAt_286 t tpc (by simp only [blk286.res, rv_simp]),
    by simp only [blk286.res, rv_simp], by simp only [blk286.res, rv_simp, t19, ofNat_add_ofNat], ?_,
    fun z => by rw [Result.toState_getMem, show blk286.res.st.mem = [] from rfl, memEval_nil]⟩
  intro q hq; rw [Result.toState_getReg]
  cases q <;> first | exact absurd (by decide) hq | rfl

/-- The fold branch (`sch_fold` 271 .. 285, then `sch_next`): copy node `(h, (E xor 1) - 2^(14-h))`. -/
theorem sch_fold (levels : List (List Val))
    (hlen : ∀ l, l < 15 → (levels.getD l []).length = 2 ^ (14 - l))
    (hvv : ∀ l, l < 15 → ∀ v ∈ levels.getD l [], v.length = 16)
    (st : SchedState) (E h : Nat) (hh : h ≤ 13) (hE1 : 2 ^ (14 - h) ≤ E) (hE2 : E < 2 ^ (15 - h))
    (t : MachineState) (tpc : t.pc = pcOf 271)
    (t19 : t.getReg .x19 = BitVec.ofNat 64 h) (t18 : t.getReg .x18 = BitVec.ofNat 64 E)
    (t30 : t.getReg .x30 = BitVec.ofNat 64 0xB0000) (hrd : ReadsAt levels st.reads t)
    (hrl : st.reads.length < 210)
    (hlvt : ∀ l (hl : l < 15), Slots t (lvBase l) (levels.getD l [])) :
    ∃ t', Steps image t 17 17 t' ∧ t'.pc = pcOf 263 ∧
      t'.getReg .x19 = BitVec.ofNat 64 (h + 1) ∧ t'.getReg .x18 = BitVec.ofNat 64 (E / 2) ∧
      ReadsAt levels (st.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)]) t' ∧
      RegsEq t t' [.x1, .x2, .x18, .x19, .x21, .x25, .x26, .x29] ∧
      Frame t t' (fun a => 0x3400 + 16 * st.reads.length ≤ a ∧ a < 0x3400 + 16 * (st.reads.length + 1)) := by
  obtain ⟨-, h29, hrm, hrlen⟩ := hrd
  have hT : porsT / 2 ^ h = 2 ^ (14 - h) := by
    unfold porsT porsH; rw [Nat.pow_div (by omega) (by norm_num)]
  have hx := xor1_eq E
  have hm : 2 ^ (15 - h) = 2 * 2 ^ (14 - h) := by rw [← Nat.pow_succ']; congr 1; omega
  have hmev : 2 ^ (14 - h) % 2 = 0 := by
    rw [show 14 - h = (13 - h) + 1 by omega, Nat.pow_succ]; omega
  have hj1 : 2 ^ (14 - h) ≤ E ^^^ 1 := by omega
  have hj2 : (E ^^^ 1) - 2 ^ (14 - h) < 2 ^ (14 - h) := by omega
  set j := (E ^^^ 1) - 2 ^ (14 - h) with hj
  have hlh := hlen h (by omega)
  have hbase := lvBase_le h (by omega)
  have hge := lvBase_ge h
  have haddr := readAddr E h hh hE1 hE2
  have hb8 : lvBase h % 16 = 0 := by
    unfold lvBase
    have : 2 ^ (15 - h) ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hs1 := symRun_sound blk271 codeAt_271 t tpc (by
    simp only [blk271.res, rv_simp, t18, t19, t30, h29]
    rw [haddr]
    simp only [ofNat_add_ofNat, accessValid_ofNat]
    have : 2 ^ (14 - h) ≤ 2 ^ 14 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega)
  set t1 := blk271.res.toState t with ht1
  have hc1 : blk271.res.cycles = 15 := rfl
  have hk1 : blk271.res.steps = 15 := rfl
  rw [hc1, hk1] at hs1
  have hval := (hlvt h (by omega)) j (by rw [hlh]; exact hj2)
  have hm1 : ∀ a : Nat, a < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 a) =
      if a = 0x3400 + 16 * st.reads.length + 8 then t.getMem (BitVec.ofNat 64 (lvBase h + 16 * j + 8))
      else if a = 0x3400 + 16 * st.reads.length then t.getMem (BitVec.ofNat 64 (lvBase h + 16 * j))
      else t.getMem (BitVec.ofNat 64 a) := by
    intro a ha
    simp only [ht1, blk271.res, rv_simp, t18, t19, t30, h29]
    rw [haddr]
    simp only [ofNat_add_ofNat, ofNat_eq_iff]
    split_ifs <;> first | rfl | (exfalso; omega) | (congr 2; omega)
  obtain ⟨hs2, pc2, x19', r2, m2⟩ := sch_next t1 (by simp only [ht1, blk271.res, rv_simp])
    h (by rw [ht1, Result.toState_getReg]; exact t19)
  set t2 := blk286.res.toState t1 with ht2
  have r1 : RegsEq t t1 [.x1, .x2, .x18, .x21, .x25, .x26, .x29] := by
    intro q hq; rw [ht1, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have hlw : (levels.getD h []).getD j [] = (levels.getD h [])[j]'(by rw [hlh]; exact hj2) :=
    getD_of_lt _
  refine ⟨t2, hs1.trans hs2, pc2, x19', ?_, ⟨by simp; omega, ?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [r2.get .x18]; simp only [ht1, blk271.res, rv_simp, t18]; bvsimp []
  · rw [r2.get .x29]; simp only [ht1, blk271.res, rv_simp, h29, ofNat_add_ofNat]; simp; exact ofNat_congr (by ring)
  · intro r hr
    simp only [List.length_append, List.length_singleton] at hr
    rw [readWords_ofNat_two, m2, m2, hm1 _ (by omega), hm1 _ (by omega)]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | hr
    · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
        ← readWords_ofNat_two, List.getElem_append_left hr]
      exact hrm r hr
    · subst hr
      rw [if_neg (by omega), if_pos rfl, if_pos (by omega), List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton, readVal, hT]
      rw [← hj, hlw, ← hval, readWords_ofNat_two]
  · intro r hr
    simp only [List.length_append, List.length_singleton] at hr
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | hr
    · rw [List.getElem_append_left hr]; exact hrlen r hr
    · subst hr
      rw [List.getElem_append_right (le_refl _)]
      simp only [Nat.sub_self, List.getElem_singleton, readVal, hT]
      rw [← hj, hlw]
      exact hvv h (by omega) _ (List.getElem_mem _)
  · exact (r1.trans r2).mono (by decide)
  · intro a ha hW
    rw [m2, hm1 a ha, if_neg (by omega), if_neg (by omega)]

/-- The merge branch (266 .. 270, then `sch_next`): pop, go up. -/
theorem sch_merge (Q : Nat) (rest : List Nat) (E h : Nat) (hE : E < 2 ^ 64) (t : MachineState) (tpc : t.pc = pcOf 266)
    (t19 : t.getReg .x19 = BitVec.ofNat 64 h) (t18 : t.getReg .x18 = BitVec.ofNat 64 E)
    (hst : StackAt (Q :: rest) t) :
    ∃ t', Steps image t 7 7 t' ∧ t'.pc = pcOf 263 ∧
      t'.getReg .x19 = BitVec.ofNat 64 (h + 1) ∧ t'.getReg .x18 = BitVec.ofNat 64 (E / 2) ∧
      StackAt rest t' ∧ RegsEq t t' [.x15, .x18, .x19, .x21, .x23] ∧ (∀ z, t'.getMem z = t.getMem z) := by
  obtain ⟨hsl, h23, hsm, hs0, hsv⟩ := hst
  simp only [List.length_cons] at hsl h23 hsm
  have hs1 := symRun_sound blk266 codeAt_266 t tpc (by simp only [blk266.res, rv_simp])
  set t1 := blk266.res.toState t with ht1
  have hc1 : blk266.res.cycles = 5 := rfl
  have hk1 : blk266.res.steps = 5 := rfl
  rw [hc1, hk1] at hs1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk266.res.st.mem = [] from rfl, memEval_nil]
  obtain ⟨hs2, pc2, x19', r2, m2⟩ := sch_next t1 (by simp only [ht1, blk266.res, rv_simp])
    h (by rw [ht1, Result.toState_getReg]; exact t19)
  set t2 := blk286.res.toState t1 with ht2
  have r1 : RegsEq t t1 [.x15, .x18, .x21, .x23] := by
    intro q hq; rw [ht1, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  refine ⟨t2, hs1.trans hs2, pc2, x19', ?_, ⟨by omega, ?_, fun i hi => ?_, by rw [m2, m1, hs0],
    fun q hq => hsv q (List.mem_cons_of_mem _ hq)⟩, (r1.trans r2).mono (by decide), fun z => by rw [m2, m1]⟩
  · rw [r2.get .x18]; simp only [ht1, blk266.res, rv_simp, t18]
    rw [show (1#64 : Word).toNat % 64 = 1 from rfl, ofNat_ushiftRight _ _ hE, Nat.pow_one]
  · rw [r2.get .x23]; simp only [ht1, blk266.res, rv_simp, h23]
    rw [ofNat_sub_ofNat _ _ (by omega) (by omega)]; exact ofNat_congr (by omega)
  · rw [m2, m1]
    have := hsm (i + 1) (by simp; omega)
    rw [show rest.length + 1 - (i + 1) = rest.length - i by omega] at this
    rw [this]; rfl

end SigGolfCandidate.Sign
