import SigGolfCandidate.Expand.Run

/-!
# `expand`: key extraction (`da_ext`, instructions 14 .. 39)

After the digest query (answer `ans`, `N = ans.toNat`, its four dwords at `DO = 0x160`), the
program stores `KEYS[15] = 2^22` (sentinel `2^14 << 8`) and, for `r = 0 .. 14`,
`KEYS[r] = keyOf N r = v_r << 8 | 8 r` (`v_r = leafOf N r`, bit position `b = 34 + 14 r`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem and63 (b : Nat) : b &&& 63 = b % 64 := Nat.and_two_pow_sub_one_eq_mod b 6

/-- `KEYS[r]`: the leaf index `v_r` in bits `8 ..`, `8 r` (the digest slot) in the low byte. -/
def keyOf (N r : Nat) : Nat := leafOf N r * 256 + 8 * r

/-- The KEYS array (16 dwords at `0x6E0`). -/
def KW (a : Nat) : Prop := 0x6E0 ≤ a ∧ a < 0x760

/-- The digest answer's dwords at `DO = 0x160`. -/
def DOk (ans : BitVec 256) (t : MachineState) : Prop :=
  ∀ i < 4, t.getMem (BitVec.ofNat 64 (0x160 + 8 * i)) = ans.extractLsb' (64 * i) 64

/-- Dword `i` of `N`. -/
def wd (N i : Nat) : Nat := N / 2 ^ (64 * i) % 2 ^ 64

theorem key_arith (N r : Nat) (hr : r < 15) :
    (if (34 + 14 * r) % 64 ≤ 50 then wd N ((34 + 14 * r) / 64) / 2 ^ ((34 + 14 * r) % 64)
      else wd N ((34 + 14 * r) / 64) / 2 ^ ((34 + 14 * r) % 64) +
        wd N ((34 + 14 * r) / 64 + 1) * 2 ^ (64 - (34 + 14 * r) % 64) % 2 ^ 64) % 2 ^ 14 =
      leafOf N r := by
  unfold wd leafOf totalH porsH
  interval_cases r <;> simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, Nat.reduceDiv,
    Nat.reduceLeDiff, if_true, if_false, Nat.reducePow, Nat.reduceSub] <;> omega

theorem keyword_eq (X : Word) (r : Nat) (hr : r < 32) :
    X <<< 50 >>> 50 <<< 8 ||| BitVec.ofNat 64 (r * 8) = BitVec.ofNat 64 (X.toNat % 2 ^ 14 * 256 + 8 * r) := by
  have h1 : X <<< 50 >>> 50 <<< 8 = BitVec.ofNat 64 (X.toNat % 2 ^ 14 * 256) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
      Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    have := X.isLt
    omega
  rw [h1, ofNat_or_disjoint _ _ 8 (by omega) (by omega) (by omega)]
  congr 1; omega

theorem toNat_ushiftRight_or {w0 w1 : Word} {k : Nat} (hk : 0 < k) (hk' : k < 64) :
    (w0 >>> k ||| w1 <<< (64 - k)).toNat = w0.toNat / 2 ^ k + w1.toNat * 2 ^ (64 - k) % 2 ^ 64 := by
  have hAB : 2 ^ 64 = 2 ^ (64 - k) * 2 ^ k := by rw [← Nat.pow_add]; congr 1; omega
  have hx : w1.toNat * 2 ^ (64 - k) % 2 ^ 64 = 2 ^ (64 - k) * (w1.toNat % 2 ^ k) := by
    rw [hAB, Nat.mul_comm w1.toNat, Nat.mul_mod_mul_left]
  have e1 : w0 >>> k = BitVec.ofNat 64 (w0.toNat / 2 ^ k) := by
    apply BitVec.eq_of_toNat_eq; simp [Nat.shiftRight_eq_div_pow]
    exact (Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) w0.isLt)).symm
  have e2 : w1 <<< (64 - k) = BitVec.ofNat 64 (2 ^ (64 - k) * (w1.toNat % 2 ^ k)) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq, hx,
      Nat.mod_eq_of_lt (a := 2 ^ (64 - k) * (w1.toNat % 2 ^ k)) (by rw [← hx]; exact Nat.mod_lt _ (by norm_num))]
  have hlt : w0.toNat / 2 ^ k < 2 ^ (64 - k) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k), ← hAB]
    exact w0.isLt
  have hsum : 2 ^ (64 - k) * (w1.toNat % 2 ^ k) + w0.toNat / 2 ^ k < 2 ^ 64 := by
    have h1 : w1.toNat % 2 ^ k + 1 ≤ 2 ^ k := Nat.mod_lt _ (Nat.two_pow_pos k)
    have h2 := Nat.mul_le_mul_left (2 ^ (64 - k)) h1
    rw [Nat.mul_add, Nat.mul_one, ← hAB] at h2
    omega
  rw [e1, e2, ofNat_or_disjoint' _ _ (64 - k) (Nat.mul_mod_right _ _) hlt hsum, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hsum, hx]
  omega

/-- Loop invariant at `da_ext` (instruction 18) with `r` keys stored. -/
structure ExtInv (ans : BitVec 256) (s0 : MachineState) (r : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 18
  x8 : t.getReg .x8 = BitVec.ofNat 64 r
  x16 : t.getReg .x16 = BitVec.ofNat 64 (34 + 14 * r)
  r15 : r < 15
  keys : ∀ j < r, t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * j)) = BitVec.ofNat 64 (keyOf ans.toNat j)
  sent : t.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22)
  frame : Frame s0 t KW

/-- After the extraction (instruction 40). -/
structure ExtDone (ans : BitVec 256) (s0 : MachineState) (t : MachineState) : Prop where
  pc : t.pc = pcOf 40
  keys : ∀ j < 15, t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * j)) = BitVec.ofNat 64 (keyOf ans.toNat j)
  sent : t.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22)
  frame : Frame s0 t KW

theorem ext_tail (ans : BitVec 256) (s0 : MachineState) (r : Nat) (hr : r < 15) (t : MachineState)
    (tpc : t.pc = pcOf 30) (t8 : t.getReg .x8 = BitVec.ofNat 64 r)
    (t16 : t.getReg .x16 = BitVec.ofNat 64 (34 + 14 * r))
    (t9 : (t.getReg .x9).toNat % 2 ^ 14 = leafOf ans.toNat r)
    (tkeys : ∀ j < r, t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * j)) = BitVec.ofNat 64 (keyOf ans.toNat j))
    (tsent : t.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22)) (tframe : Frame s0 t KW) :
    Run t 10 (fun u => if r + 1 < 15 then ExtInv ans s0 (r + 1) u else ExtDone ans s0 u) := by
  have hobl : blk30.res.obligs t := by
    simp only [blk30.res, rv_simp, t8]; ex_bvsimp [accessValid_ofNat]; omega
  refine Run.of (symRun_sound blk30 codeAt_30 t tpc hobl) (le_refl _) ?_
  set u := blk30.res.toState t with hu
  have hmem : ∀ a : Nat, a < 2 ^ 64 → u.getMem (BitVec.ofNat 64 a) =
      if a = 0x6E0 + 8 * r then BitVec.ofNat 64 (keyOf ans.toNat r) else t.getMem (BitVec.ofNat 64 a) := by
    intro a ha
    simp only [hu, blk30.res, rv_simp, t8]; ex_bvsimp []
    rw [keyword_eq _ _ (by omega), t9]
    by_cases h : a = 0x6E0 + 8 * r
    · subst h
      rw [if_pos (ofNat_congr (by ring)), if_pos rfl]; unfold keyOf; congr 1
    · rw [if_neg, if_neg h]; rw [ofNat_eq_iff]; omega
  have u8 : u.getReg .x8 = BitVec.ofNat 64 (r + 1) := by simp only [hu, blk30.res, rv_simp, t8]; ex_bvsimp []
  have u16 : u.getReg .x16 = BitVec.ofNat 64 (34 + 14 * (r + 1)) := by
    rw [show 34 + 14 * (r + 1) = 34 + 14 * r + 14 by ring]
    simp only [hu, blk30.res, rv_simp, t16]; ex_bvsimp []
  have upc : u.pc = if r + 1 < 15 then pcOf 18 else pcOf 40 := by
    simp only [hu, blk30.res, rv_simp, t8]; ex_bvsimp [ofNat_bne_ofNat]
    by_cases h : r + 1 < 15
    · simp [h]; omega
    · simp [h]; omega
  have uframe : Frame s0 u KW := by
    intro a ha hW
    rw [hmem a ha, if_neg (by unfold KW at hW; omega), tframe a ha hW]
  have ukeys : ∀ j < r + 1, u.getMem (BitVec.ofNat 64 (0x6E0 + 8 * j)) = BitVec.ofNat 64 (keyOf ans.toNat j) := by
    intro j hj
    rw [hmem _ (by omega)]
    by_cases h : j = r
    · subst h; simp
    · rw [if_neg (by omega), tkeys j (by omega)]
  have usent : u.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22) := by
    rw [hmem _ (by omega), if_neg (by omega), tsent]
  by_cases h : r + 1 < 15
  · rw [if_pos h]; rw [if_pos h] at upc
    exact ⟨upc, u8, u16, h, ukeys, usent, uframe⟩
  · rw [if_neg h]; rw [if_neg h] at upc
    exact ⟨upc, fun j hj => ukeys j (by omega), usent, uframe⟩

theorem ext_body (ans : BitVec 256) (s0 : MachineState) (hdo : DOk ans s0) (r : Nat) (t : MachineState)
    (h : ExtInv ans s0 r t) :
    Run t 22 (fun u => if r + 1 < 15 then ExtInv ans s0 (r + 1) u else ExtDone ans s0 u) := by
  obtain ⟨tpc, t8, t16, hr, tkeys, tsent, tframe⟩ := h
  set b := 34 + 14 * r with hbdef
  have hb : b < 256 := by omega
  have hobl1 : blk18.res.obligs t := by
    simp only [blk18.res, rv_simp, t16]; ex_bvsimp [accessValid_ofNat]; omega
  refine (Run.blk blk18 codeAt_18 tpc hobl1 (B := 15) ?_).mono
    (by rw [show blk18.res.cycles = 7 from rfl]) (fun _ h => h)
  set t1 := blk18.res.toState t with ht1
  have p1 : t1.pc = if b % 64 ≤ 50 then pcOf 30 else pcOf 25 := by
    simp only [ht1, blk18.res, rv_simp, t16]; ex_bvsimp [ofNat_slt_ofNat, and63]
    by_cases hk : b % 64 ≤ 50 <;> simp [hk]
  have w0 : t.getMem (BitVec.ofNat 64 (b / 64 * 8 + 352)) = ans.extractLsb' (64 * (b / 64)) 64 := by
    rw [tframe _ (by omega) (by unfold KW; omega), ← hdo (b / 64) (by omega)]; congr 2; omega
  have x9 : t1.getReg .x9 = ans.extractLsb' (64 * (b / 64)) 64 >>> (b % 64) := by
    simp only [ht1, blk18.res, rv_simp, t16]; ex_bvsimp []; rw [w0]
  have x13 : t1.getReg .x13 = BitVec.ofNat 64 (b / 64 * 8) := by
    simp only [ht1, blk18.res, rv_simp, t16]; ex_bvsimp []
  have x4 : t1.getReg .x4 = BitVec.ofNat 64 (b % 64) := by
    simp only [ht1, blk18.res, rv_simp, t16]; ex_bvsimp [and63]
  have x8' : t1.getReg .x8 = BitVec.ofNat 64 r := by simp only [ht1, blk18.res, rv_simp, t8]
  have x16' : t1.getReg .x16 = BitVec.ofNat 64 b := by simp only [ht1, blk18.res, rv_simp, t16]
  have m1 : ∀ a, t1.getMem a = t.getMem a := by intro a; simp only [ht1, blk18.res, rv_simp]
  have hframe1 : Frame s0 t1 KW := fun a ha hW => by rw [m1]; exact tframe a ha hW
  have hkeys1 : ∀ j < r, t1.getMem (BitVec.ofNat 64 (0x6E0 + 8 * j)) = BitVec.ofNat 64 (keyOf ans.toNat j) :=
    fun j hj => by rw [m1]; exact tkeys j hj
  have hsent1 : t1.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22) := by rw [m1]; exact tsent
  have hwd : ∀ i, (ans.extractLsb' (64 * i) 64).toNat = wd ans.toNat i := by
    intro i; simp [wd, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have ka := key_arith ans.toNat r hr
  rw [← hbdef] at ka
  by_cases hk : b % 64 ≤ 50
  · rw [if_pos hk] at p1 ka
    refine (ext_tail ans s0 r hr t1 p1 x8' x16' ?_ hkeys1 hsent1 hframe1).mono (by omega) (fun _ h => h)
    rw [x9, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, hwd, ka]
  · rw [if_neg hk] at p1 ka
    have hq : b / 64 + 1 < 4 := by omega
    have hobl2 : blk25.res.obligs t1 := by
      simp only [blk25.res, rv_simp, x13]; ex_bvsimp [accessValid_ofNat]; omega
    refine (Run.blk blk25 codeAt_25 p1 hobl2 (B := 10) ?_).mono
      (by rw [show blk25.res.cycles = 5 from rfl]) (fun _ h => h)
    set t2 := blk25.res.toState t1 with ht2
    have w1 : t1.getMem (BitVec.ofNat 64 (b / 64 * 8 + 360)) = ans.extractLsb' (64 * (b / 64 + 1)) 64 := by
      rw [m1, tframe _ (by omega) (by unfold KW; omega), ← hdo (b / 64 + 1) hq]; congr 2; omega
    have x9' : t2.getReg .x9 = ans.extractLsb' (64 * (b / 64)) 64 >>> (b % 64) |||
        ans.extractLsb' (64 * (b / 64 + 1)) 64 <<< (64 - b % 64) := by
      simp only [ht2, blk25.res, rv_simp, x13, x9, x4]; ex_bvsimp []
      rw [w1]
    have p2 : t2.pc = pcOf 30 := by simp only [ht2, blk25.res, rv_simp]
    have y8 : t2.getReg .x8 = BitVec.ofNat 64 r := by simp only [ht2, blk25.res, rv_simp, x8']
    have y16 : t2.getReg .x16 = BitVec.ofNat 64 b := by simp only [ht2, blk25.res, rv_simp, x16']
    have m2 : ∀ a, t2.getMem a = t1.getMem a := by intro a; simp only [ht2, blk25.res, rv_simp]
    refine ext_tail ans s0 r hr t2 p2 y8 y16 ?_ (fun j hj => by rw [m2]; exact hkeys1 j hj)
      (by rw [m2]; exact hsent1) (fun a ha hW => by rw [m2]; exact hframe1 a ha hW)
    rw [x9', toNat_ushiftRight_or (by omega) (by omega), hwd, hwd, ka]

/-- The extraction phase: instructions 14 .. 39, from right after the digest query. -/
theorem ext_run (ans : BitVec 256) (s0 : MachineState) (hdo : DOk ans s0) (t : MachineState)
    (tpc : t.pc = pcOf 14) (tframe : Frame s0 t KW) : Run t (4 + 15 * 22) (ExtDone ans s0) := by
  refine Run.blk blk14 codeAt_14 tpc (by simp only [blk14.res, rv_simp]) ?_
  set t1 := blk14.res.toState t with ht1
  have hmem : ∀ a : Nat, a < 2 ^ 64 → t1.getMem (BitVec.ofNat 64 a) =
      if a = 0x758 then BitVec.ofNat 64 (2 ^ 22) else t.getMem (BitVec.ofNat 64 a) := by
    intro a ha
    simp only [ht1, blk14.res, rv_simp]
    by_cases h : a = 0x758
    · subst h; rfl
    · rw [if_neg h]; exact if_neg (fun hh => h (by rw [ofNat_eq_iff] at hh; omega))
  let Inv : Nat → MachineState → Prop := fun i u =>
    i ≤ 15 ∧ if i = 0 then ExtDone ans s0 u else ExtInv ans s0 (15 - i) u
  have h0 : Inv 15 t1 := by
    simp only [Inv, if_neg (show (15 : Nat) ≠ 0 by decide), Nat.sub_self]
    refine ⟨le_refl _, by simp only [ht1, blk14.res, rv_simp] <;> rfl, by simp only [ht1, blk14.res, rv_simp] <;> rfl,
      by simp only [ht1, blk14.res, rv_simp] <;> rfl, by decide, fun j hj => absurd hj (by omega),
      by rw [hmem _ (by omega), if_pos rfl], ?_⟩
    intro a ha hW
    rw [hmem a ha, if_neg (by unfold KW at hW; omega), tframe a ha hW]
  have hl := Run.loop Inv 22 (fun i u hu => by
    simp only [Inv, if_neg (Nat.succ_ne_zero i)] at hu
    have := ext_body ans s0 hdo _ u hu.2
    refine this.mono (le_refl _) (fun v hv => ⟨by omega, ?_⟩)
    by_cases hi : i = 0
    · subst hi; simpa using hv
    · rw [if_neg hi]
      simp only [show 15 - (i + 1) + 1 = 15 - i from by omega] at hv
      rw [if_pos (by omega)] at hv; exact hv) 15 t1 h0
  exact hl.mono (le_refl _) (fun u hu => by simpa [Inv] using hu.2)

end SigGolfCandidate.Expand
