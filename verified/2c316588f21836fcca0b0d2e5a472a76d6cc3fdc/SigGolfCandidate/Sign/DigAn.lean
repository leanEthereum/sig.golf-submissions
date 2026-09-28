import SigGolfCandidate.Sign.Blocks
import SigGolfCandidate.Sign.Inv
import SigGolfCandidate.Sign.AnSpec

/-!
# `sign`: the digest analysis (instructions 78 .. 136)

From `78` (right after the digest HASH, the answer in `DO = 0x160 .. 0x180`) the machine
* extracts the 15 keys `v_r * 256 + 8 r` into `KEYS = 0x6E0 + 8 r` (`KEYS[15] = 2^22`, the
  sentinel `2^14 << 8`),
* sorts `KEYS[0 .. 14]` (insertion sort, `sortKeys`),
* passes over the sorted keys (duplicates, bit-length sum),
and reaches `dig_ok` (145) iff `admissibleM N`, else `dig_next` (137); `analysis_run`.
No oracle queries; at most `anCyc` cycles.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-! ## Generic: pure loops -/

/-- A loop of `n` iterations, each at most `C` cycles. -/
theorem steps_loop {image : Image} (P : Nat → MachineState → Prop) (C n : Nat)
    (hstep : ∀ i < n, ∀ t, P i t → ∃ k c t', Steps image t k c t' ∧ c ≤ C ∧ P (i + 1) t') :
    ∀ t, P 0 t → ∃ k c t', Steps image t k c t' ∧ c ≤ n * C ∧ P n t' := by
  induction n with
  | zero => intro t h; exact ⟨0, 0, t, Steps.refl t, by simp, h⟩
  | succ n ih =>
    intro t h
    obtain ⟨k1, c1, t1, s1, hc1, h1⟩ := ih (fun i hi => hstep i (by omega)) t h
    obtain ⟨k2, c2, t2, s2, hc2, h2⟩ := hstep n (by omega) t1 h1
    exact ⟨_, _, t2, s1.trans s2, by rw [Nat.succ_mul]; omega, h2⟩

/-- The 15 key slots hold `l`. -/
def KeysAt (t : MachineState) (l : List Nat) : Prop :=
  ∀ i < 15, t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * i)) = BitVec.ofNat 64 (l.getD i 0)

/-- Registers clobbered by the analysis. -/
def anRegs : List Reg := [.x3, .x4, .x8, .x9, .x13, .x14, .x15, .x16, .x17]

/-- Memory written by the analysis: `KEYS[0 .. 15]`. -/
def anW (a : Nat) : Prop := 0x6E0 ≤ a ∧ a < 0x760

theorem pcOf_eq' (i : Nat) (h : 0x1000 + 4 * i < 2 ^ 64) (w : Word) (hw : w.toNat = 0x1000 + 4 * i) :
    w = pcOf i := by
  apply BitVec.eq_of_toNat_eq; rw [hw]; simp; omega

/-! ## Key extraction -/

/-- The word `k` of the digest answer. -/
abbrev dword (ans : BitVec 256) (k : Nat) : Word := ans.extractLsb' (64 * k) 64

theorem dword_toNat (ans : BitVec 256) (k : Nat) : (dword ans k).toNat = ans.toNat / 2 ^ (64 * k) % 2 ^ 64 := by
  simp [dword, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]

theorem keyOf_lt (N r : Nat) (hr : r < 32) : keyOf N r < 2 ^ 22 := by
  unfold keyOf fieldOf; have := Nat.mod_lt (N / 2 ^ (34 + 14 * r)) (show 0 < 2 ^ 14 by norm_num); omega

/-- Final shaping of a key: `((X << 50) >> 50) << 8 | r << 3`. -/
theorem key_shape (X : Word) (r f : Nat) (hr : r < 32) (hX : X.toNat % 2 ^ 14 = f) :
    (X <<< ((50#64).toNat % 64) >>> ((50#64).toNat % 64) <<< ((8#64).toNat % 64) |||
      BitVec.ofNat 64 r <<< ((3#64).toNat % 64)) = BitVec.ofNat 64 (f * 256 + 8 * r) := by
  have hf : f < 2 ^ 14 := by rw [← hX]; exact Nat.mod_lt _ (by norm_num)
  have h1 : (X <<< ((50#64).toNat % 64) >>> ((50#64).toNat % 64) <<< ((8#64).toNat % 64)) =
      BitVec.ofNat 64 (f * 256) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      show (50#64 : Word).toNat % 64 = 50 from rfl, show (8#64 : Word).toNat % 64 = 8 from rfl,
      BitVec.toNat_ofNat]
    have hx := X.isLt
    have e1 : X.toNat * 2 ^ 50 % 2 ^ 64 = X.toNat % 2 ^ 14 * 2 ^ 50 := by
      rw [show (2 : Nat) ^ 64 = 2 ^ 14 * 2 ^ 50 by norm_num, Nat.mul_mod_mul_right]
    rw [e1, Nat.mul_div_cancel _ (by norm_num), hX]
  rw [h1, show (3#64 : Word).toNat % 64 = 3 from rfl, ofNat_shiftLeft,
    show r * 2 ^ 3 = 8 * r by ring, ofNat_or_disjoint (f * 256) (8 * r) 8 (by omega) (by omega) (by omega)]

theorem ext_hi (w w' : Word) (m : Nat) (hm : 0 < m) (hm' : m < 64) :
    (w >>> m ||| w' <<< (64 - m)).toNat = w.toNat / 2 ^ m + w'.toNat * 2 ^ (64 - m) % 2 ^ 64 := by
  rw [BitVec.toNat_or, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftRight_eq_div_pow,
    Nat.shiftLeft_eq]
  have hw := w.isLt
  have e : w'.toNat * 2 ^ (64 - m) % 2 ^ 64 = 2 ^ (64 - m) * (w'.toNat % 2 ^ m) := by
    rw [show (2 : Nat) ^ 64 = 2 ^ (64 - m) * 2 ^ m by rw [← Nat.pow_add]; congr 1; omega,
      Nat.mul_comm, Nat.mul_mod_mul_left]
  have ha : w.toNat / 2 ^ m < 2 ^ (64 - m) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 64 - m + m = 64 by omega]; exact hw
  rw [e, Nat.or_comm, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm]

/-- The extraction of slot `r` (bit position `b = 34 + 14 r`, word `b / 64`, shift `b % 64`). -/
theorem ext_lo_nat (N r : Nat) (hr : r < 15) (hm : (34 + 14 * r) % 64 ≤ 50) :
    N / 2 ^ (64 * ((34 + 14 * r) / 64)) % 2 ^ 64 / 2 ^ ((34 + 14 * r) % 64) % 2 ^ 14 = fieldOf N r := by
  unfold fieldOf
  interval_cases r <;> (try norm_num at hm ⊢) <;> (try omega)

theorem ext_hi_nat (N r : Nat) (hr : r < 15) (hm : ¬ (34 + 14 * r) % 64 ≤ 50) :
    (N / 2 ^ (64 * ((34 + 14 * r) / 64)) % 2 ^ 64 / 2 ^ ((34 + 14 * r) % 64) +
      N / 2 ^ (64 * ((34 + 14 * r) / 64 + 1)) % 2 ^ 64 * 2 ^ (64 - (34 + 14 * r) % 64) % 2 ^ 64) % 2 ^ 14 =
      fieldOf N r := by
  unfold fieldOf
  interval_cases r <;> (try norm_num at hm ⊢) <;> (try omega)

/-! ## The extraction loop (82 .. 103) -/

/-- Invariant of the extraction loop after `r` keys. -/
def ExtInv (ans : BitVec 256) (t0 : MachineState) (r : Nat) (t : MachineState) : Prop :=
  r ≤ 15 ∧ t.pc = (if r < 15 then pcOf 82 else pcOf 104) ∧ t.getReg .x8 = BitVec.ofNat 64 r ∧
  t.getReg .x16 = BitVec.ofNat 64 (34 + 14 * r) ∧
  (∀ i < r, t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * i)) = BitVec.ofNat 64 (keyOf ans.toNat i)) ∧
  RegsEq t0 t anRegs ∧ Frame t0 t (fun a => 0x6E0 ≤ a ∧ a < 0x758)

theorem ext_iter (ans : BitVec 256) (t0 : MachineState)
    (hdo : ∀ k < 4, t0.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = dword ans k)
    (r : Nat) (hr : r < 15) (t : MachineState) (h : ExtInv ans t0 r t) :
    ∃ k c t', Steps image t k c t' ∧ c ≤ 22 ∧ ExtInv ans t0 (r + 1) t' := by
  obtain ⟨-, tpc, t8, t16, tkeys, tregs, tframe⟩ := h
  rw [if_pos hr] at tpc
  have hdo' : ∀ k < 4, t.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = dword ans k := fun k hk => by
    rw [tframe.getMem (by omega) (by omega), hdo k hk]
  have hb : (34 + 14 * r) / 64 < 4 := by omega
  have hs1 := symRun_sound blk82 codeAt_82 t tpc (by
    simp only [blk82.res, rv_simp, t16]
    bvsimp [accessValid_ofNat]
    omega)
  set t1 := blk82.res.toState t with ht1
  have r1 : RegsEq t t1 [.x4, .x9, .x13, .x17] := by
    intro q hq; rw [ht1, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk82.res.st.mem = [] from rfl, memEval_nil]
  have w1 : t.getMem (BitVec.ofNat 64 ((34 + 14 * r) / 64 * 8 + 352)) = dword ans ((34 + 14 * r) / 64) := by
    rw [show (34 + 14 * r) / 64 * 8 + 352 = 0x160 + 8 * ((34 + 14 * r) / 64) by ring, hdo' _ hb]
  have x9 : t1.getReg .x9 = dword ans ((34 + 14 * r) / 64) >>> ((34 + 14 * r) % 64) := by
    simp only [ht1, blk82.res, rv_simp, t16]
    bvsimp []
    rw [w1]
  have x13 : t1.getReg .x13 = BitVec.ofNat 64 (8 * ((34 + 14 * r) / 64)) := by
    simp only [ht1, blk82.res, rv_simp, t16]; bvsimp []; congr 1; ring
  have x4 : t1.getReg .x4 = BitVec.ofNat 64 ((34 + 14 * r) % 64) := by
    simp only [ht1, blk82.res, rv_simp, t16]
    rw [show (63#64 : Word) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl, ofNat_and_ofNat _ _ (by omega) (by norm_num),
      Nat.and_two_pow_sub_one_eq_mod]
  have pc1 : t1.pc = if (34 + 14 * r) % 64 ≤ 50 then pcOf 94 else pcOf 89 := by
    simp only [ht1, blk82.res, rv_simp, t16]
    rw [show (63#64 : Word) = BitVec.ofNat 64 (2 ^ 6 - 1) from rfl, ofNat_and_ofNat _ _ (by omega) (by norm_num),
      Nat.and_two_pow_sub_one_eq_mod, show (50#64 : Word) = BitVec.ofNat 64 50 from rfl,
      ofNat_slt_ofNat _ _ (by norm_num) (by omega)]
    by_cases h : (34 + 14 * r) % 64 ≤ 50
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  have hc1 : blk82.res.cycles = 7 := rfl
  rw [hc1] at hs1
  -- the (possibly) two-word value in x9 at `da_one`
  obtain ⟨k2, c2, t2, hs2, hc2, pc2, x9', r2, m2⟩ : ∃ k c t2, Steps image t1 k c t2 ∧ c ≤ 5 ∧
      t2.pc = pcOf 94 ∧ t2.getReg .x9 = (if (34 + 14 * r) % 64 ≤ 50 then
        dword ans ((34 + 14 * r) / 64) >>> ((34 + 14 * r) % 64) else
        dword ans ((34 + 14 * r) / 64) >>> ((34 + 14 * r) % 64) |||
          dword ans ((34 + 14 * r) / 64 + 1) <<< (64 - (34 + 14 * r) % 64)) ∧
      RegsEq t1 t2 [.x9, .x14, .x17] ∧ (∀ z, t2.getMem z = t1.getMem z) := by
    by_cases hm : (34 + 14 * r) % 64 ≤ 50
    · refine ⟨0, 0, t1, Steps.refl _, by omega, by rw [pc1, if_pos hm], by rw [if_pos hm, x9], RegsEq.refl _ _,
        fun _ => rfl⟩
    · have hb2 : (34 + 14 * r) / 64 + 1 < 4 := by omega
      have hs2 := symRun_sound blk89 codeAt_89 t1 (by rw [pc1, if_neg hm]) (by
        simp only [blk89.res, rv_simp, x13]
        bvsimp [accessValid_ofNat]
        omega)
      set t2 := blk89.res.toState t1 with ht2
      refine ⟨_, _, t2, hs2, by rw [show blk89.res.cycles = 5 from rfl], by simp only [ht2, blk89.res, rv_simp], ?_,
        ?_, fun z => by rw [ht2, Result.toState_getMem, show blk89.res.st.mem = [] from rfl, memEval_nil]⟩
      · rw [if_neg hm]
        simp only [ht2, blk89.res, rv_simp, x13, x9, x4]
        rw [m1, show (64#64 : Word) = BitVec.ofNat 64 64 from rfl, ofNat_sub_ofNat _ _ (by omega) (by norm_num),
          ofNat_add_ofNat, show 8 * ((34 + 14 * r) / 64) + 360 = 0x160 + 8 * ((34 + 14 * r) / 64 + 1) by ring,
          hdo' _ hb2]
        congr 2
        simp only [BitVec.toNat_ofNat]; omega
      · intro q hq; rw [ht2, Result.toState_getReg]
        cases q <;> first | exact absurd (by decide) hq | rfl
  -- block 94: shape, store, loop test
  have t28 : t2.getReg .x8 = BitVec.ofNat 64 r := by rw [r2.get .x8, r1.get .x8, t8]
  have t216 : t2.getReg .x16 = BitVec.ofNat 64 (34 + 14 * r) := by rw [r2.get .x16, r1.get .x16, t16]
  have hs3 := symRun_sound blk94 codeAt_94 t2 pc2 (by
    simp only [blk94.res, rv_simp, t28]
    bvsimp [accessValid_ofNat]
    omega)
  set t3 := blk94.res.toState t2 with ht3
  have hkey : (t2.getReg .x9 <<< ((50#64).toNat % 64) >>> ((50#64).toNat % 64) <<< ((8#64).toNat % 64) |||
      BitVec.ofNat 64 r <<< ((3#64).toNat % 64)) = BitVec.ofNat 64 (keyOf ans.toNat r) := by
    apply key_shape _ r _ (by omega)
    rw [x9']
    by_cases hm : (34 + 14 * r) % 64 ≤ 50
    · rw [if_pos hm, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, dword_toNat]
      exact ext_lo_nat _ r hr hm
    · rw [if_neg hm, ext_hi _ _ _ (by omega) (by omega), dword_toNat, dword_toNat]
      exact ext_hi_nat _ r hr hm
  have hm3 : ∀ a : Nat, a < 2 ^ 64 → t3.getMem (BitVec.ofNat 64 a) =
      if a = 0x6E0 + 8 * r then BitVec.ofNat 64 (keyOf ans.toNat r) else t2.getMem (BitVec.ofNat 64 a) := by
    intro a ha
    simp only [ht3, blk94.res, rv_simp, t28]
    rw [hkey]
    bvsimp [ofNat_eq_iff]
    by_cases h : a = 0x6E0 + 8 * r
    · rw [if_pos (by omega), if_pos h]
    · rw [if_neg (by omega), if_neg h]
  refine ⟨_, _, t3, hs1.trans (hs2.trans hs3), by rw [show blk94.res.cycles = 10 from rfl]; omega, by omega,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ht3, blk94.res, rv_simp, t28, ofNat_add_ofNat, ofNat_bne_ofNat]
    by_cases h : r + 1 < 15
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · simp only [ht3, blk94.res, rv_simp, t28, ofNat_add_ofNat]
  · simp only [ht3, blk94.res, rv_simp, t216, ofNat_add_ofNat]; exact ofNat_congr (by ring)
  · intro i hi
    rw [hm3 _ (by omega)]
    by_cases h : i = r
    · rw [if_pos (by rw [h]), h]
    · rw [if_neg (by omega), m2, m1, tkeys i (by omega)]
  · refine ((tregs.trans r1).trans r2 |>.trans (show RegsEq t2 t3 [.x3, .x8, .x9, .x16, .x17] by
      intro q hq; rw [ht3, Result.toState_getReg]
      cases q <;> first | exact absurd (by decide) hq | rfl)).mono (by decide)
  · intro a ha hW
    rw [hm3 a ha, if_neg (by omega), m2, m1]
    exact tframe a ha hW

/-! ## The insertion sort (104 .. 118) -/

theorem KeysAt.set {t t' : MachineState} {M : List Nat} {p v : Nat} (h : KeysAt t M) (hlen : M.length = 15)
    (hp : p < 15) (hmem : ∀ a : Nat, a < 2 ^ 64 → t'.getMem (BitVec.ofNat 64 a) =
      if a = 0x6E0 + 8 * p then BitVec.ofNat 64 v else t.getMem (BitVec.ofNat 64 a)) :
    KeysAt t' (M.set p v) := by
  intro i hi
  rw [hmem _ (by omega)]
  by_cases hip : i = p
  · subst hip
    rw [if_pos rfl, List.getD_eq_getElem?_getD, List.getElem?_set_self (by omega)]; rfl
  · rw [if_neg (by omega), List.getD_eq_getElem?_getD, List.getElem?_set_ne (by omega), h i hi,
      List.getD_eq_getElem?_getD]

theorem set_shift (r post : List Nat) (y junk v : Nat) :
    (r.reverse ++ y :: junk :: post).set (r.length + 1) v = r.reverse ++ y :: v :: post := by
  rw [List.set_append_right _ _ (by simp)]
  simp

theorem getD_shift (r post : List Nat) (y junk : Nat) :
    (r.reverse ++ y :: junk :: post).getD r.length 0 = y := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

/-- Values of the key array are below `2^64`. -/
def KeysBound (l : List Nat) : Prop := ∀ v ∈ l, v < 2 ^ 22

theorem keysBound_getD {l : List Nat} (h : KeysBound l) (i : Nat) : l.getD i 0 < 2 ^ 22 := by
  rw [List.getD_eq_getElem?_getD]
  cases hi : l[i]? with
  | none => simp
  | some v => exact h v (List.mem_of_getElem? hi)

/-- The shift loop (`da_shift` 108 .. `da_place` 118) of outer step `i`: `x` is inserted,
the result is `insRes x rpre post`. -/
theorem shift_loop (i : Nat) (hi1 : 1 ≤ i) (hi : i < 15) (x : Nat) (hx : x < 2 ^ 22) :
    ∀ (rpre post : List Nat) (junk : Nat) (t : MachineState),
      rpre.length + 1 + post.length = 15 → rpre.length ≤ i → KeysBound (rpre ++ post) →
      t.pc = pcOf 108 → t.getReg .x14 = BitVec.ofNat 64 (0x6E0 + 8 * rpre.length) →
      t.getReg .x9 = BitVec.ofNat 64 x → t.getReg .x8 = BitVec.ofNat 64 i →
      KeysAt t (rpre.reverse ++ junk :: post) →
      ∃ k c t', Steps image t k c t' ∧ c ≤ 7 * rpre.length + 8 ∧
        t'.pc = (if i + 1 < 15 then pcOf 105 else pcOf 119) ∧ t'.getReg .x8 = BitVec.ofNat 64 (i + 1) ∧
        KeysAt t' (insRes x rpre post) ∧ RegsEq t t' [.x8, .x13, .x14, .x17] ∧
        Frame t t' (fun a => 0x6E0 ≤ a ∧ a < 0x758)
  | [], post, junk, t, hlen, hle, hb, tpc, t14, t9, t8, tk => by
    have hs1 := symRun_sound blk108 codeAt_108 t tpc (by simp only [blk108.res, rv_simp])
    set t1 := blk108.res.toState t with ht1
    have pc1 : t1.pc = pcOf 115 := by
      simp only [ht1, blk108.res, rv_simp, t14, List.length_nil]; rfl
    have hs2 := symRun_sound blk115 codeAt_115 t1 pc1 (by
      simp only [blk115.res, rv_simp, ht1, blk108.res, t14]; decide)
    set t2 := blk115.res.toState t1 with ht2
    have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
      rw [ht1, Result.toState_getMem, show blk108.res.st.mem = [] from rfl, memEval_nil]
    have r1 : RegsEq t t1 [.x17] := by
      intro q hq; rw [ht1, Result.toState_getReg]
      cases q <;> first | exact absurd (by decide) hq | rfl
    have r2 : RegsEq t1 t2 [.x8, .x17] := by
      intro q hq; rw [ht2, Result.toState_getReg]
      cases q <;> first | exact absurd (by decide) hq | rfl
    have hm2 : ∀ a : Nat, a < 2 ^ 64 → t2.getMem (BitVec.ofNat 64 a) =
        if a = 0x6E0 + 8 * 0 then BitVec.ofNat 64 x else t.getMem (BitVec.ofNat 64 a) := by
      intro a ha
      simp only [ht2, blk115.res, rv_simp, r1.get .x14, r1.get .x9, t14, t9, List.length_nil, Nat.mul_zero,
        Nat.add_zero, m1]
      by_cases h : a = 0x6E0
      · rw [if_pos (by rw [h]), if_pos h]
      · rw [if_neg (by rw [ofNat_eq_iff]; omega), if_neg (by omega)]
    refine ⟨_, _, t2, hs1.trans hs2, by rw [show blk108.res.cycles = 2 from rfl,
      show blk115.res.cycles = 4 from rfl]; omega, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ht2, blk115.res, rv_simp, r1.get .x8, t8, ofNat_add_ofNat, ofNat_bne_ofNat]
      by_cases h : i + 1 < 15
      · rw [if_pos h, if_pos (by simp; omega)]
      · rw [if_neg h, if_neg (by simp; omega)]
    · simp only [ht2, blk115.res, rv_simp, r1.get .x8, t8, ofNat_add_ofNat]
    · have := KeysAt.set tk (by simp at hlen ⊢; omega) (by omega) hm2
      simpa [insRes] using this
    · exact (r1.trans r2).mono (by decide)
    · intro a ha hW
      rw [hm2 a ha, if_neg (by omega)]
  | y :: r, post, junk, t, hlen, hle, hb, tpc, t14, t9, t8, tk => by
    simp only [List.length_cons] at hlen hle t14
    have hy : y < 2 ^ 22 := hb y (by simp)
    have hs1 := symRun_sound blk108 codeAt_108 t tpc (by simp only [blk108.res, rv_simp])
    set t1 := blk108.res.toState t with ht1
    have pc1 : t1.pc = pcOf 110 := by
      simp only [ht1, blk108.res, rv_simp, t14, ofNat_beq_ofNat]
      rw [if_neg (by simp; omega)]
    have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
      rw [ht1, Result.toState_getMem, show blk108.res.st.mem = [] from rfl, memEval_nil]
    have r1 : RegsEq t t1 [.x17] := by
      intro q hq; rw [ht1, Result.toState_getReg]
      cases q <;> first | exact absurd (by decide) hq | rfl
    have t114 : t1.getReg .x14 = BitVec.ofNat 64 (0x6E0 + 8 * (r.length + 1)) := by rw [r1.get .x14, t14]
    have hyv : t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * r.length)) = BitVec.ofNat 64 y := by
      rw [tk r.length (by omega), List.reverse_cons, List.append_assoc, List.singleton_append,
        getD_shift]
    have hs2 := symRun_sound blk110 codeAt_110 t1 pc1 (by
      simp only [blk110.res, rv_simp, t114]
      rw [ofNat_sub_ofNat _ _ (by omega) (by omega)]
      simp only [accessValid_ofNat]; omega)
    set t2 := blk110.res.toState t1 with ht2
    have r2 : RegsEq t1 t2 [.x13] := by
      intro q hq; rw [ht2, Result.toState_getReg]
      cases q <;> first | exact absurd (by decide) hq | rfl
    have m2 : ∀ z, t2.getMem z = t1.getMem z := fun z => by
      rw [ht2, Result.toState_getMem, show blk110.res.st.mem = [] from rfl, memEval_nil]
    have x13 : t2.getReg .x13 = BitVec.ofNat 64 y := by
      simp only [ht2, blk110.res, rv_simp, t114]
      rw [ofNat_sub_ofNat _ _ (by omega) (by omega), m1, show 0x6E0 + 8 * (r.length + 1) - 8 =
        0x6E0 + 8 * r.length by omega, hyv]
    have pc2 : t2.pc = if y ≤ x then pcOf 115 else pcOf 112 := by
      simp only [ht2, blk110.res, rv_simp, t114, r1.get .x9, t9]
      rw [ofNat_sub_ofNat _ _ (by omega) (by omega), m1, show 0x6E0 + 8 * (r.length + 1) - 8 =
        0x6E0 + 8 * r.length by omega, hyv, BitVec.ult, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : x < 2 ^ 64), Nat.mod_eq_of_lt (by omega : y < 2 ^ 64)]
      by_cases h : y ≤ x
      · rw [if_pos h, if_pos (by simp; omega)]
      · rw [if_neg h, if_neg (by simp; omega)]
    have hM : (y :: r).reverse ++ junk :: post = r.reverse ++ y :: junk :: post := by simp
    by_cases hyx : y ≤ x
    · -- place
      have hs3 := symRun_sound blk115 codeAt_115 t2 (by rw [pc2, if_pos hyx]) (by
        simp only [blk115.res, rv_simp, r2.get .x14, t114]
        simp only [accessValid_ofNat]; omega)
      set t3 := blk115.res.toState t2 with ht3
      have hm3 : ∀ a : Nat, a < 2 ^ 64 → t3.getMem (BitVec.ofNat 64 a) =
          if a = 0x6E0 + 8 * (r.length + 1) then BitVec.ofNat 64 x else t.getMem (BitVec.ofNat 64 a) := by
        intro a ha
        simp only [ht3, blk115.res, rv_simp, r2.get .x14, t114, r2.get .x9, r1.get .x9, t9, m2, m1]
        by_cases h : a = 0x6E0 + 8 * (r.length + 1)
        · rw [if_pos (by rw [h]), if_pos h]
        · rw [if_neg (by rw [ofNat_eq_iff]; omega), if_neg h]
      have r3 : RegsEq t2 t3 [.x8, .x17] := by
        intro q hq; rw [ht3, Result.toState_getReg]
        cases q <;> first | exact absurd (by decide) hq | rfl
      refine ⟨_, _, t3, hs1.trans (hs2.trans hs3), by rw [show blk108.res.cycles = 2 from rfl,
        show blk110.res.cycles = 2 from rfl, show blk115.res.cycles = 4 from rfl]; omega, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [ht3, blk115.res, rv_simp, r2.get .x8, r1.get .x8, t8, ofNat_add_ofNat, ofNat_bne_ofNat]
        by_cases h : i + 1 < 15
        · rw [if_pos h, if_pos (by simp; omega)]
        · rw [if_neg h, if_neg (by simp; omega)]
      · simp only [ht3, blk115.res, rv_simp, r2.get .x8, r1.get .x8, t8, ofNat_add_ofNat]
      · rw [hM] at tk
        have := KeysAt.set tk (by simp; omega) (by omega) hm3
        rw [set_shift] at this
        unfold insRes; rw [if_neg (by omega)]
        simpa using this
      · exact ((r1.trans r2).trans r3).mono (by decide)
      · intro a ha hW
        rw [hm3 a ha, if_neg (by omega)]
    · -- shift
      have hs3 := symRun_sound blk112 codeAt_112 t2 (by rw [pc2, if_neg hyx]) (by
        simp only [blk112.res, rv_simp, r2.get .x14, t114]
        simp only [accessValid_ofNat]; omega)
      set t3 := blk112.res.toState t2 with ht3
      have hm3 : ∀ a : Nat, a < 2 ^ 64 → t3.getMem (BitVec.ofNat 64 a) =
          if a = 0x6E0 + 8 * (r.length + 1) then BitVec.ofNat 64 y else t.getMem (BitVec.ofNat 64 a) := by
        intro a ha
        simp only [ht3, blk112.res, rv_simp, r2.get .x14, t114, x13, m2, m1]
        by_cases h : a = 0x6E0 + 8 * (r.length + 1)
        · rw [if_pos (by rw [h]), if_pos h]
        · rw [if_neg (by rw [ofNat_eq_iff]; omega), if_neg h]
      have r3 : RegsEq t2 t3 [.x14] := by
        intro q hq; rw [ht3, Result.toState_getReg]
        cases q <;> first | exact absurd (by decide) hq | rfl
      have pc3 : t3.pc = pcOf 108 := by simp only [ht3, blk112.res, rv_simp]
      have x14' : t3.getReg .x14 = BitVec.ofNat 64 (0x6E0 + 8 * r.length) := by
        simp only [ht3, blk112.res, rv_simp, r2.get .x14, t114]
        rw [ofNat_sub_ofNat _ _ (by omega) (by omega)]; exact ofNat_congr (by omega)
      have tk3 : KeysAt t3 (r.reverse ++ y :: (y :: post)) := by
        rw [hM] at tk
        have := KeysAt.set tk (by simp; omega) (by omega) hm3
        rwa [set_shift] at this
      obtain ⟨k, c, t', hs', hc', pc', x8', keys', regs', fr'⟩ := shift_loop i hi1 hi x hx r (y :: post) y t3
        (by simp; omega) (by omega)
        (fun v hv => by
          simp only [List.mem_append, List.mem_cons] at hv
          exact hb v (by simp only [List.mem_append, List.mem_cons]; tauto))
        pc3 x14' (by rw [r3.get .x9, r2.get .x9, r1.get .x9, t9])
        (by rw [r3.get .x8, r2.get .x8, r1.get .x8, t8]) tk3
      refine ⟨_, _, t', hs1.trans (hs2.trans (hs3.trans hs')), by rw [show blk108.res.cycles = 2 from rfl,
        show blk110.res.cycles = 2 from rfl, show blk112.res.cycles = 3 from rfl]; simp; omega, pc', x8', ?_, ?_, ?_⟩
      · unfold insRes; rw [if_pos (by omega)]; exact keys'
      · exact (((r1.trans r2).trans r3).trans regs').mono (by decide)
      · intro a ha hW
        rw [fr' a ha hW, hm3 a ha, if_neg (by omega)]

theorem keyOf_mod (N r : Nat) (hr : r < 32) : keyOf N r % 256 = 8 * r := by
  unfold keyOf; omega

theorem keys0_nodup (N : Nat) : (keys0 N).Nodup := by
  unfold keys0
  refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
  have h1 := keyOf_mod N a (by simp at ha; omega)
  have h2 := keyOf_mod N b (by simp at hb; omega)
  rw [hab] at h1; omega

theorem length_keys0 (N : Nat) : (keys0 N).length = 15 := by simp [keys0]

theorem keysBound_keys0 (N : Nat) : KeysBound (keys0 N) := by
  intro v hv
  simp only [keys0, List.mem_map, List.mem_range] at hv
  obtain ⟨r, hr, rfl⟩ := hv
  exact keyOf_lt N r (by omega)

theorem keysBound_perm {l l' : List Nat} (h : KeysBound l) (hp : l'.Perm l) : KeysBound l' :=
  fun v hv => h v (hp.subset hv)

theorem sortN_perm (N n : Nat) (hn : n ≤ 14) : (sortN (keys0 N) n).Perm (keys0 N) :=
  (sortN_inv (keys0 N) (length_keys0 N) (keys0_nodup N) n hn).1

/-- Outer sort invariant before step `i` (`1 ≤ i ≤ 15`). -/
def SortInv (N : Nat) (t0 : MachineState) (i : Nat) (t : MachineState) : Prop :=
  1 ≤ i ∧ i ≤ 15 ∧ t.pc = (if i < 15 then pcOf 105 else pcOf 119) ∧ t.getReg .x8 = BitVec.ofNat 64 i ∧
  KeysAt t (sortN (keys0 N) (i - 1)) ∧ RegsEq t0 t anRegs ∧ Frame t0 t (fun a => 0x6E0 ≤ a ∧ a < 0x758)

theorem sort_iter (N : Nat) (t0 : MachineState) (i : Nat) (hi1 : 1 ≤ i) (hi : i < 15) (t : MachineState)
    (h : SortInv N t0 i t) : ∃ k c t', Steps image t k c t' ∧ c ≤ 109 ∧ SortInv N t0 (i + 1) t' := by
  obtain ⟨-, -, tpc, t8, tk, tregs, tframe⟩ := h
  rw [if_pos hi] at tpc
  set L := sortN (keys0 N) (i - 1) with hL
  have hlen : L.length = 15 := length_sortN _ (length_keys0 N) _ (by omega)
  have hbL : KeysBound L := keysBound_perm (keysBound_keys0 N) (sortN_perm N _ (by omega))
  have hs1 := symRun_sound blk105 codeAt_105 t tpc (by
    simp only [blk105.res, rv_simp, t8]
    bvsimp [accessValid_ofNat]; omega)
  set t1 := blk105.res.toState t with ht1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk105.res.st.mem = [] from rfl, memEval_nil]
  have r1 : RegsEq t t1 [.x9, .x14] := by
    intro q hq; rw [ht1, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have x14 : t1.getReg .x14 = BitVec.ofNat 64 (0x6E0 + 8 * (L.take i).reverse.length) := by
    simp only [ht1, blk105.res, rv_simp, t8]; bvsimp []
    simp only [List.length_reverse, List.length_take, hlen]
    exact ofNat_congr (by omega)
  have x9 : t1.getReg .x9 = BitVec.ofNat 64 (L.getD i 0) := by
    simp only [ht1, blk105.res, rv_simp, t8]; bvsimp []
    rw [show i * 8 + 1760 = 0x6E0 + 8 * i by ring, tk i hi]
  have hsplit := getD_drop_take L i (by omega)
  obtain ⟨k, c, t', hs', hc', pc', x8', keys', regs', fr'⟩ := shift_loop i hi1 hi (L.getD i 0)
    (keysBound_getD hbL i) (L.take i).reverse (L.drop (i + 1)) (L.getD i 0) t1
    (by simp [hlen]; omega) (by simp)
    (fun v hv => by
      simp only [List.mem_append, List.mem_reverse] at hv
      rcases hv with hv | hv
      · exact hbL v (List.mem_of_mem_take hv)
      · exact hbL v (List.mem_of_mem_drop hv))
    (by simp only [ht1, blk105.res, rv_simp]) x14 x9 (by rw [r1.get .x8, t8])
    (by rw [List.reverse_reverse, ← hsplit]; intro j hj; rw [m1]; exact tk j hj)
  refine ⟨_, _, t', hs1.trans hs', by rw [show blk105.res.cycles = 3 from rfl]; simp at hc'; omega,
    by omega, by omega, pc', x8', ?_, ?_, ?_⟩
  · rw [show i + 1 - 1 = (i - 1) + 1 by omega]
    show KeysAt t' (sortStep (sortN (keys0 N) (i - 1)) (i - 1 + 1))
    rw [show i - 1 + 1 = i by omega]
    exact keys'
  · exact ((tregs.trans r1).trans regs').mono (by decide)
  · intro a ha hW
    rw [fr' a ha hW, m1, tframe a ha hW]

/-! ## The pass (119 .. 136) -/

/-- The partial bit-length sum of the pass. -/
def passPart (L : List Nat) (s : Nat) : Nat :=
  ((List.range s).map fun j => blen (keyV (L.getD j 0) ^^^ keyV (L.getD (j + 1) 0))).sum

theorem passPart_succ (L : List Nat) (s : Nat) :
    passPart L (s + 1) = passPart L s + blen (keyV (L.getD s 0) ^^^ keyV (L.getD (s + 1) 0)) := by
  simp [passPart, List.range_succ]

/-- The bit-length loop (`bitlen_1`, 128 .. 130). -/
theorem bitlen_loop : ∀ (y : Nat) (acc : Nat) (t : MachineState), y ≠ 0 → y < 2 ^ 14 →
    t.pc = pcOf 128 → t.getReg .x9 = BitVec.ofNat 64 y → t.getReg .x15 = BitVec.ofNat 64 acc →
    ∃ k c t', Steps image t k c t' ∧ c = 3 * blen y ∧ t'.pc = pcOf 131 ∧
      t'.getReg .x15 = BitVec.ofNat 64 (acc + blen y) ∧ RegsEq t t' [.x9, .x15] ∧ (∀ z, t'.getMem z = t.getMem z)
  | y, acc, t, hy, hy14, tpc, t9, t15 => by
    have hs1 := symRun_sound blk128 codeAt_128 t tpc (by simp only [blk128.res, rv_simp])
    set t1 := blk128.res.toState t with ht1
    have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
      rw [ht1, Result.toState_getMem, show blk128.res.st.mem = [] from rfl, memEval_nil]
    have r1 : RegsEq t t1 [.x9, .x15] := by
      intro q hq; rw [ht1, Result.toState_getReg]
      cases q <;> first | exact absurd (by decide) hq | rfl
    have x9 : t1.getReg .x9 = BitVec.ofNat 64 (y / 2) := by
      simp only [ht1, blk128.res, rv_simp, t9]; bvsimp []
    have x15 : t1.getReg .x15 = BitVec.ofNat 64 (acc + 1) := by
      simp only [ht1, blk128.res, rv_simp, t15, ofNat_add_ofNat]
    have hb := SchedMath.bitLen_div_two hy
    have hc1 : blk128.res.cycles = 3 := rfl
    by_cases h2 : y / 2 = 0
    · refine ⟨_, _, t1, hs1, by rw [hc1, show blen y = SigGolfCandidate.Ref.bitLen y from rfl, hb, h2]; rfl, ?_, ?_, r1, m1⟩
      · simp only [ht1, blk128.res, rv_simp, t9]; bvsimp [ofNat_bne_ofNat]
        rw [if_neg (by simp; omega)]
      · rw [x15, show blen y = SigGolfCandidate.Ref.bitLen y from rfl, hb, h2]; rfl
    · have pc1 : t1.pc = pcOf 128 := by
        simp only [ht1, blk128.res, rv_simp, t9]; bvsimp [ofNat_bne_ofNat]
        rw [if_pos (by simp; omega)]
      obtain ⟨k, c, t', hs', hc', pc', x15', r', m'⟩ := bitlen_loop (y / 2) (acc + 1) t1 h2 (by omega)
        pc1 x9 x15
      refine ⟨_, _, t', hs1.trans hs', by rw [hc1, hc', show blen y = SigGolfCandidate.Ref.bitLen y from rfl, hb]; ring,
        pc', ?_, (r1.trans r').mono (by decide), fun z => by rw [m', m1]⟩
      rw [x15', show blen y = SigGolfCandidate.Ref.bitLen y from rfl, hb]; exact ofNat_congr (by simp only [blen]; omega)
  termination_by y => y
  decreasing_by omega

theorem blen_le14 (y : Nat) (hy : y < 2 ^ 14) : blen y ≤ 14 := (SchedMath.bitLen_le_iff y 14).2 hy

theorem ushr8 (k : Nat) (hk : k < 2 ^ 64) : BitVec.ofNat 64 k >>> 8 = BitVec.ofNat 64 (keyV k) := by
  rw [ofNat_ushiftRight _ _ hk]; rfl

/-- Pass invariant before pair `s`. -/
def PassInv (L : List Nat) (t0 : MachineState) (s : Nat) (t : MachineState) : Prop :=
  s ≤ 14 ∧ t.pc = (if s < 14 then pcOf 121 else pcOf 134) ∧ t.getReg .x8 = BitVec.ofNat 64 s ∧
  t.getReg .x15 = BitVec.ofNat 64 (passPart L s) ∧
  (∀ j < s, keyV (L.getD j 0) ≠ keyV (L.getD (j + 1) 0)) ∧ KeysAt t L ∧ RegsEq t0 t anRegs ∧
  (∀ z, t.getMem z = t0.getMem z)

theorem passPart_le (L : List Nat) (hb : KeysBound L) (s : Nat) : passPart L s ≤ 14 * s := by
  induction s with
  | zero => simp [passPart]
  | succ s ih =>
    rw [passPart_succ]
    have h1 : keyV (L.getD s 0) < 2 ^ 14 := by have := keysBound_getD hb s; unfold keyV; omega
    have h2 : keyV (L.getD (s + 1) 0) < 2 ^ 14 := by have := keysBound_getD hb (s + 1); unfold keyV; omega
    have := blen_le14 _ (Nat.xor_lt_two_pow h1 h2)
    omega

theorem pass_iter (L : List Nat) (hb : KeysBound L) (t0 : MachineState) (s : Nat) (hs : s < 14)
    (t : MachineState) (h : PassInv L t0 s t) :
    ∃ k c t', Steps image t k c t' ∧ c ≤ 52 ∧
      (if keyV (L.getD s 0) = keyV (L.getD (s + 1) 0) then t'.pc = pcOf 137 ∧ RegsEq t0 t' anRegs ∧
        (∀ z, t'.getMem z = t0.getMem z)
      else PassInv L t0 (s + 1) t') := by
  obtain ⟨-, tpc, t8, t15, tdist, tk, tregs, tmem⟩ := h
  rw [if_pos hs] at tpc
  have hk0 := tk s (by omega)
  have hk1 := tk (s + 1) (by omega)
  have b0 := keysBound_getD hb s
  have b1 := keysBound_getD hb (s + 1)
  have hs1 := symRun_sound blk121 codeAt_121 t tpc (by
    simp only [blk121.res, rv_simp, t8]
    bvsimp [accessValid_ofNat]; omega)
  set t1 := blk121.res.toState t with ht1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk121.res.st.mem = [] from rfl, memEval_nil]
  have r1 : RegsEq t t1 [.x3, .x9, .x13] := by
    intro q hq; rw [ht1, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have e0 : t.getMem (BitVec.ofNat 64 (s * 8 + 1760)) = BitVec.ofNat 64 (L.getD s 0) := by
    rw [show s * 8 + 1760 = 0x6E0 + 8 * s by ring, hk0]
  have e1 : t.getMem (BitVec.ofNat 64 (s * 8 + 1768)) = BitVec.ofNat 64 (L.getD (s + 1) 0) := by
    rw [show s * 8 + 1768 = 0x6E0 + 8 * (s + 1) by ring, hk1]
  have hv0 : keyV (L.getD s 0) < 2 ^ 14 := by unfold keyV; omega
  have hv1 : keyV (L.getD (s + 1) 0) < 2 ^ 14 := by unfold keyV; omega
  have hx : keyV (L.getD s 0) ^^^ keyV (L.getD (s + 1) 0) < 2 ^ 14 := Nat.xor_lt_two_pow hv0 hv1
  have x9 : t1.getReg .x9 = BitVec.ofNat 64 (keyV (L.getD s 0) ^^^ keyV (L.getD (s + 1) 0)) := by
    simp only [ht1, blk121.res, rv_simp, t8]; bvsimp []
    rw [e0, e1, ushr8 _ (by omega), ushr8 _ (by omega), ofNat_xor_ofNat _ _ (by omega) (by omega)]
  have hxz : (keyV (L.getD s 0) ^^^ keyV (L.getD (s + 1) 0) = 0) ↔ keyV (L.getD s 0) = keyV (L.getD (s + 1) 0) :=
    ⟨SchedMath.xor_eq_zero, fun h => by rw [h, Nat.xor_self]⟩
  have hc1 : blk121.res.cycles = 7 := rfl
  by_cases hdup : keyV (L.getD s 0) = keyV (L.getD (s + 1) 0)
  · simp only [if_pos hdup]
    refine ⟨_, _, t1, hs1, by rw [hc1]; omega, ?_, (tregs.trans r1).mono (by decide), fun z => by rw [m1, tmem]⟩
    simp only [ht1, blk121.res, rv_simp, t8]; bvsimp []
    rw [e0, e1, ushr8 _ (by omega), ushr8 _ (by omega), ofNat_xor_ofNat _ _ (by omega) (by omega)]
    rw [if_pos (by rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ofNat_beq_ofNat,
      Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64), hxz.mpr hdup]; rfl)]
  · simp only [if_neg hdup]
    have pc1 : t1.pc = pcOf 128 := by
      simp only [ht1, blk121.res, rv_simp, t8]; bvsimp []
      rw [e0, e1, ushr8 _ (by omega), ushr8 _ (by omega), ofNat_xor_ofNat _ _ (by omega) (by omega)]
      rw [if_neg (by rw [show (0#64 : Word) = BitVec.ofNat 64 0 from rfl, ofNat_beq_ofNat,
        Nat.mod_eq_of_lt (by omega : _ < 2 ^ 64)]; simpa only [decide_eq_true_eq, Nat.zero_mod] using
        fun h => hdup (hxz.mp h))]
    have hpp := passPart_le L hb s
    obtain ⟨k2, c2, t2, hs2, hc2, pc2, x15', r2, m2⟩ := bitlen_loop _ (passPart L s) t1
      (fun h => hdup (hxz.mp h)) hx pc1 x9 (by rw [r1.get .x15, t15])
    have hs3 := symRun_sound blk131 codeAt_131 t2 pc2 (by simp only [blk131.res, rv_simp])
    set t3 := blk131.res.toState t2 with ht3
    have r3 : RegsEq t2 t3 [.x8, .x17] := by
      intro q hq; rw [ht3, Result.toState_getReg]
      cases q <;> first | exact absurd (by decide) hq | rfl
    have m3 : ∀ z, t3.getMem z = t2.getMem z := fun z => by
      rw [ht3, Result.toState_getMem, show blk131.res.st.mem = [] from rfl, memEval_nil]
    have t28 : t2.getReg .x8 = BitVec.ofNat 64 s := by rw [r2.get .x8, r1.get .x8, t8]
    have hbl := blen_le14 _ hx
    refine ⟨_, _, t3, hs1.trans (hs2.trans hs3), by rw [hc1, hc2, show blk131.res.cycles = 3 from rfl]; omega,
      by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ht3, blk131.res, rv_simp, t28, ofNat_add_ofNat, ofNat_bne_ofNat]
      by_cases h : s + 1 < 14
      · rw [if_pos h, if_pos (by simp; omega)]
      · rw [if_neg h, if_neg (by simp; omega)]
    · simp only [ht3, blk131.res, rv_simp, t28, ofNat_add_ofNat]
    · rw [r3.get .x15, x15', passPart_succ]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
      · exact tdist j hj
      · rw [hj]; exact hdup
    · intro j hj; rw [m3, m2, m1]; exact tk j hj
    · exact (((tregs.trans r1).trans r2).trans r3).mono (by decide)
    · intro z; rw [m3, m2, m1, tmem]

theorem pass_run (L : List Nat) (hb : KeysBound L) (t0 : MachineState) : ∀ n s t, s + n = 14 →
    PassInv L t0 s t → ∃ k c t', Steps image t k c t' ∧ c ≤ 52 * n ∧
      ((∀ j, s ≤ j → j < 14 → keyV (L.getD j 0) ≠ keyV (L.getD (j + 1) 0)) → PassInv L t0 14 t') ∧
      (¬ (∀ j, s ≤ j → j < 14 → keyV (L.getD j 0) ≠ keyV (L.getD (j + 1) 0)) →
        t'.pc = pcOf 137 ∧ RegsEq t0 t' anRegs ∧ ∀ z, t'.getMem z = t0.getMem z)
  | 0, s, t, hs, h => ⟨0, 0, t, Steps.refl t, le_refl _, fun _ => by rw [show s = 14 by omega] at h; exact h,
      fun hn => absurd (fun j h1 h2 => absurd h2 (by omega)) hn⟩
  | n + 1, s, t, hs, h => by
    obtain ⟨k, c, t', hs', hc', h'⟩ := pass_iter L hb t0 s (by omega) t h
    by_cases hdup : keyV (L.getD s 0) = keyV (L.getD (s + 1) 0)
    · rw [if_pos hdup] at h'
      exact ⟨k, c, t', hs', by omega, fun hall => absurd hdup (hall s (le_refl _) (by omega)), fun _ => h'⟩
    · rw [if_neg hdup] at h'
      obtain ⟨k2, c2, t2, hs2, hc2, h2a, h2b⟩ := pass_run L hb t0 n (s + 1) t' (by omega) h'
      refine ⟨_, _, t2, hs'.trans hs2, by omega, fun hall => h2a (fun j h1 h2 => hall j (by omega) h2),
        fun hn => h2b (fun hall => hn (fun j h1 h2 => ?_))⟩
      rcases Nat.eq_or_lt_of_le h1 with h1 | h1
      · rw [← h1]; exact hdup
      · exact hall j h1 h2

/-- Cycle bound of the analysis. -/
def anCyc : Nat := 4 + 15 * 22 + 1 + 14 * 109 + 2 + 14 * 52 + 3

theorem passSum_eq (L : List Nat) : passSum L = passPart L 14 := rfl

theorem passOk_iff (L : List Nat) :
    passOk L = true ↔ ∀ j, 0 ≤ j → j < 14 → keyV (L.getD j 0) ≠ keyV (L.getD (j + 1) 0) := by
  simp [passOk, List.all_eq_true]

/-- **The digest analysis.** -/
theorem analysis_run (ans : BitVec 256) (t : MachineState) (hpc : t.pc = pcOf 78)
    (hdo : ∀ k < 4, t.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = dword ans k) :
    ∃ k c t', Steps image t k c t' ∧ c ≤ anCyc ∧
      t'.pc = (if admissibleM ans.toNat then pcOf 145 else pcOf 137) ∧
      KeysAt t' (sortKeys (keys0 ans.toNat)) ∧ t'.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22) ∧
      RegsEq t t' anRegs ∧ Frame t t' anW := by
  set N := ans.toNat with hN
  -- block 78
  have hs0 := symRun_sound blk78 codeAt_78 t hpc (by simp only [blk78.res, rv_simp])
  set t0 := blk78.res.toState t with ht0
  have hm0 : ∀ a : Nat, a < 2 ^ 64 → t0.getMem (BitVec.ofNat 64 a) =
      if a = 0x758 then BitVec.ofNat 64 (2 ^ 22) else t.getMem (BitVec.ofNat 64 a) := by
    intro a ha
    simp only [ht0, blk78.res, rv_simp, show (1880#64 : Word) = BitVec.ofNat 64 1880 from rfl, ofNat_eq_iff,
      Nat.mod_eq_of_lt ha]
    split_ifs <;> first | rfl | omega
  have r0 : RegsEq t t0 [.x4, .x8, .x16] := by
    intro q hq; rw [ht0, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have hdo0 : ∀ k < 4, t0.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = dword ans k := fun k hk => by
    rw [hm0 _ (by omega), if_neg (by omega), hdo k hk]
  -- extraction
  have e0 : ExtInv ans t0 0 t0 := ⟨by omega, by simp only [ht0, blk78.res, rv_simp] <;> rfl,
    by simp only [ht0, blk78.res, rv_simp] <;> rfl, by simp only [ht0, blk78.res, rv_simp] <;> rfl,
    fun i hi => absurd hi (by omega), RegsEq.refl _ _, Frame.refl _ _⟩
  obtain ⟨k1, c1, t1, hs1, hc1, ⟨-, pc1, -, -, keys1, regs1, fr1⟩⟩ :=
    steps_loop (image := image) (ExtInv ans t0) 22 15 (fun r hr t h => ext_iter ans t0 hdo0 r hr t h) t0 e0
  rw [if_neg (by omega)] at pc1
  -- block 104
  have hs2 := symRun_sound blk104 codeAt_104 t1 pc1 (by simp only [blk104.res, rv_simp])
  set t2 := blk104.res.toState t1 with ht2
  have m2 : ∀ z, t2.getMem z = t1.getMem z := fun z => by
    rw [ht2, Result.toState_getMem, show blk104.res.st.mem = [] from rfl, memEval_nil]
  have r2 : RegsEq t1 t2 [.x8] := by
    intro q hq; rw [ht2, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have si1 : SortInv N t2 1 t2 := by
    refine ⟨le_refl _, by omega, by simp only [ht2, blk104.res, rv_simp] <;> rfl,
      by simp only [ht2, blk104.res, rv_simp] <;> rfl, ?_, RegsEq.refl _ _, Frame.refl _ _⟩
    intro i hi
    rw [m2, keys1 i hi, show 1 - 1 = 0 from rfl]
    simp only [sortN, keys0]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]; rfl
  obtain ⟨k3, c3, t3, hs3, hc3, ⟨-, -, pc3, -, keys3, regs3, fr3⟩⟩ :=
    steps_loop (image := image) (fun j u => SortInv N t2 (j + 1) u) 109 14
      (fun j hj u h => sort_iter N t2 (j + 1) (by omega) (by omega) u h) t2 si1
  rw [if_neg (by omega)] at pc3
  -- block 119
  have hs4 := symRun_sound blk119 codeAt_119 t3 pc3 (by simp only [blk119.res, rv_simp])
  set t4 := blk119.res.toState t3 with ht4
  have m4 : ∀ z, t4.getMem z = t3.getMem z := fun z => by
    rw [ht4, Result.toState_getMem, show blk119.res.st.mem = [] from rfl, memEval_nil]
  have r4 : RegsEq t3 t4 [.x8, .x15] := by
    intro q hq; rw [ht4, Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  set L := sortKeys (keys0 N) with hL
  have hbL : KeysBound L := keysBound_perm (keysBound_keys0 N) (sortN_perm N 14 (le_refl _))
  have pi0 : PassInv L t4 0 t4 := by
    refine ⟨by omega, by simp only [ht4, blk119.res, rv_simp] <;> rfl, by simp only [ht4, blk119.res, rv_simp] <;> rfl,
      by simp only [ht4, blk119.res, rv_simp] <;> rfl, fun j hj => absurd hj (by omega), ?_,
      RegsEq.refl _ _, fun _ => rfl⟩
    intro i hi; rw [m4]; exact keys3 i hi
  obtain ⟨k5, c5, t5, hs5, hc5, h5a, h5b⟩ := pass_run L hbL t4 14 0 t4 (by omega) pi0
  -- frames and common facts
  have fr03 : Frame t t3 anW := by
    intro a ha hW
    simp only [anW] at hW
    rw [fr3 a ha (by omega), m2, fr1 a ha (by omega), hm0 a ha, if_neg (by omega)]
  have sent3 : t3.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22) := by
    rw [fr3 _ (by norm_num) (by omega), m2, fr1 _ (by norm_num) (by omega), hm0 _ (by norm_num), if_pos rfl]
  have rg3 : RegsEq t t3 anRegs := ((r0.trans regs1).trans r2 |>.trans regs3).mono (by decide)
  have hc : blk78.res.cycles = 4 ∧ blk104.res.cycles = 1 ∧ blk119.res.cycles = 2 :=
    ⟨rfl, rfl, rfl⟩
  by_cases hall : ∀ j, 0 ≤ j → j < 14 → keyV (L.getD j 0) ≠ keyV (L.getD (j + 1) 0)
  · obtain ⟨-, pc5, -, x15, -, keys5, regs5, mem5⟩ := h5a hall
    rw [if_neg (by omega)] at pc5
    have hs6 := symRun_sound blk134 codeAt_134 t5 pc5 (by simp only [blk134.res, rv_simp])
    set t6 := blk134.res.toState t5 with ht6
    have hpp := passPart_le L hbL 14
    have pc6 : t6.pc = if passPart L 14 ≤ 134 then pcOf 136 else pcOf 137 := by
      simp only [ht6, blk134.res, rv_simp, x15]
      rw [show (134#64 : Word) = BitVec.ofNat 64 134 from rfl, ofNat_slt_ofNat _ _ (by norm_num) (by omega)]
      by_cases h : passPart L 14 ≤ 134
      · rw [if_pos h, if_neg (by simp; omega)]
      · rw [if_neg h, if_pos (by simp; omega)]
    have m6 : ∀ z, t6.getMem z = t5.getMem z := fun z => by
      rw [ht6, Result.toState_getMem, show blk134.res.st.mem = [] from rfl, memEval_nil]
    have r6 : RegsEq t5 t6 [.x17] := by
      intro q hq; rw [ht6, Result.toState_getReg]
      cases q <;> first | exact absurd (by decide) hq | rfl
    have hadm : admissibleM N = decide (passPart L 14 ≤ 134) := by
      unfold admissibleM; rw [(passOk_iff L).mpr hall, passSum_eq, Bool.true_and]
    have keys6 : KeysAt t6 L := fun i hi => by rw [m6]; exact keys5 i hi
    have sent6 : t6.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22) := by
      rw [m6, mem5, m4, sent3]
    have fr6 : Frame t t6 anW := fun a ha hW => by rw [m6, mem5, m4, fr03 a ha hW]
    have rg6 : RegsEq t t6 anRegs := (((rg3.trans r4).trans regs5).trans r6).mono (by decide)
    by_cases hsum : passPart L 14 ≤ 134
    · have hs7 := symRun_sound blk136 codeAt_136 t6 (by rw [pc6, if_pos hsum]) (by simp only [blk136.res, rv_simp])
      set t7 := blk136.res.toState t6 with ht7
      have m7 : ∀ z, t7.getMem z = t6.getMem z := fun z => by
        rw [ht7, Result.toState_getMem, show blk136.res.st.mem = [] from rfl, memEval_nil]
      refine ⟨_, _, t7, hs0.trans (hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans (hs6.trans hs7)))))),
        ?_, ?_, fun i hi => by rw [m7]; exact keys6 i hi, by rw [m7, sent6],
        rg6.trans (show RegsEq t6 t7 [] by
          intro q hq; rw [ht7, Result.toState_getReg]
          cases q <;> first | exact absurd (by decide) hq | rfl) |>.mono (by decide),
        fun a ha hW => by rw [m7, fr6 a ha hW]⟩
      · rw [hc.1, hc.2.1, hc.2.2, show blk134.res.cycles = 2 from rfl, show blk136.res.cycles = 1 from rfl]
        unfold anCyc; omega
      · rw [hadm, if_pos (by simpa using hsum)]; simp only [ht7, blk136.res, rv_simp] <;> rfl
    · refine ⟨_, _, t6, hs0.trans (hs1.trans (hs2.trans (hs3.trans (hs4.trans (hs5.trans hs6))))),
        ?_, ?_, keys6, sent6, rg6, fr6⟩
      · rw [hc.1, hc.2.1, hc.2.2, show blk134.res.cycles = 2 from rfl]
        unfold anCyc; omega
      · rw [hadm, if_neg (by simpa using hsum), pc6, if_neg hsum]
  · obtain ⟨pc5, regs5, mem5⟩ := h5b hall
    have hadm : admissibleM N = false := by
      unfold admissibleM; rw [Bool.and_eq_false_iff]; left
      exact Bool.eq_false_iff.mpr (fun h => hall ((passOk_iff L).mp h))
    refine ⟨_, _, t5, hs0.trans (hs1.trans (hs2.trans (hs3.trans (hs4.trans hs5)))), ?_, ?_, ?_, ?_,
      ((rg3.trans r4).trans regs5).mono (by decide), fun a ha hW => by rw [mem5, m4, fr03 a ha hW]⟩
    · rw [hc.1, hc.2.1, hc.2.2]; unfold anCyc; omega
    · rw [hadm, pc5]; rfl
    · intro i hi; rw [mem5, m4]; exact keys3 i hi
    · rw [mem5, m4, sent3]

end SigGolfCandidate.Sign
