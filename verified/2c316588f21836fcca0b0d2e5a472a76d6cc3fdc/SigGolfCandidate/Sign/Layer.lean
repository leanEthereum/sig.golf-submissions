import SigGolfCandidate.Sign.Tree
import SigGolfCandidate.Sign.Top

/-!
# `sign`, the hypertree layers (`layer_loop`, instructions 205 .. 613)

`layers_sim` : from `layer_loop` with `KAP = n - 1` and the message `M` at `EB + 32`, the machine
refines `signLayers S idx n M`; layer `l`'s counter, chain values and path are staged at
`STG + 760 l` (counter dword, `+8`: 42 values, `+680`: path).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Buffers that stay constant during the layer phase (P slots, `S`). -/
structure Statics (S : List Byte) (t : MachineState) : Prop where
  ebP : t.readWords (BitVec.ofNat 64 0x110) 2 = [0, 0]
  pbP : t.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cbP : t.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]
  lbP : t.readWords (BitVec.ofNat 64 0x350) 2 = [0, 0]
  nbP : t.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0]

/-- Addresses of the static buffers. -/
def staticA (a : Nat) : Prop :=
  (0x110 ≤ a ∧ a < 0x120) ∨ (0x6B0 ≤ a ∧ a < 0x6E0) ∨ (0xD0 ≤ a ∧ a < 0xE0) ∨
    (0x350 ≤ a ∧ a < 0x360) ∨ (0x1D0 ≤ a ∧ a < 0x1E0)

theorem Statics.frame {S : List Byte} {s t : MachineState} {W : Nat → Prop} (h : Statics S s)
    (hf : Frame s t W) (hW : ∀ a, staticA a → ¬ W a) : Statics S t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.ebP]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.pbP]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.pbS]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.cbP]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.lbP]
  · rw [hf.readWords _ _ (by norm_num) (fun i hi => hW _ (by simp only [staticA]; omega)), h.nbP]

/-- The cache region (masked top-tree nodes), untouched by `sign`. -/
def RegionOk (cache : List Byte) (t : MachineState) : Prop :=
  ∀ l j, l < 11 → j < 2 ^ (11 - l) →
    t.readWords (BitVec.ofNat 64 (0x4B00 + cacheNodeOff l j)) 2 = wordsOf (cacheNode cache l j)

/-- Addresses of the cache region. -/
def regionA (a : Nat) : Prop := 0x4B20 ≤ a ∧ a < 0x14B00

theorem RegionOk.frame {cache : List Byte} {s t : MachineState} {W : Nat → Prop} (h : RegionOk cache s)
    (hf : Frame s t W) (hW : ∀ a, regionA a → ¬ W a) : RegionOk cache t := by
  intro l j hl hj
  have := cacheNodeOff_lt l j hl hj
  have : 32 ≤ cacheNodeOff l j := by unfold cacheNodeOff; omega
  rw [hf.readWords _ _ (by omega) (fun i hi => hW _ (by simp only [regionA]; omega)), h l j hl hj]

/-- The state at `layer_loop` for layer `lay` with message `M`. -/
structure LayHead (S cache : List Byte) (idx lay : Nat) (M : Val) (t : MachineState) : Prop where
  hlay : lay < 5
  hidx : idx < 2 ^ 34
  hM : M.length = 16
  pc : t.pc = pcOf 316
  x5 : t.getReg .x5 = 0
  x7 : t.getReg .x7 = BitVec.ofNat 64 (2 ^ 22)
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay
  x18 : t.getReg .x18 = BitVec.ofNat 64 (0x900 + 856 * lay)
  x22 : t.getReg .x22 = BitVec.ofNat 64 idx
  x26 : t.getReg .x26 = swM1
  x27 : t.getReg .x27 = swM2
  ebM : t.readWords (BitVec.ofNat 64 0x120) 2 = wordsOf M
  st : Statics S t
  region : RegionOk cache t

theorem shiftBelow_eq (lay : Nat) (h : lay < 5) :
    shiftBelow lay = if lay = 0 then 23 else if lay < 4 then 23 - 6 * lay else 0 := by
  interval_cases lay <;> decide

theorem height_eq (lay : Nat) (h : lay < 5) :
    height lay = if lay = 0 then 11 else if lay < 4 then 6 else 5 := by
  interval_cases lay <;> decide

theorem shiftBelow_add (lay : Nat) (h : lay < 5) : 4 ≤ shiftBelow lay + height lay ∧ shiftBelow lay + height lay ≤ 34 ∧
    shiftBelow lay ≤ 23 ∧ 4 ≤ height lay ∧ height lay ≤ 11 := by
  interval_cases lay <;> decide

/-- Route and header state at `enc_loop`. -/
theorem layer_header (S cache : List Byte) (idx lay : Nat) (M : Val) (t : MachineState)
    (hh : LayHead S cache idx lay M t) :
    ∃ k c t4, Steps image t k c t4 ∧ c ≤ 26 ∧ t4.pc = pcOf 346 ∧
      t4.getReg .x6 = BitVec.ofNat 64 0 ∧ t4.getReg .x9 = BitVec.ofNat 64 (height lay) ∧
      t4.getReg .x13 = BitVec.ofNat 64 ((route idx lay).1) ∧
      t4.getReg .x30 = BitVec.ofNat 64 ((route idx lay).2) ∧
      t4.getReg .x31 = BitVec.ofNat 64 ((route idx lay).2 + 2 ^ 32 * (route idx lay).1) ∧
      EncMem lay (route idx lay).2 (route idx lay).1 M t4 ∧
      RegsEq t t4 [.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ∧
      Frame t t4 (fun a => a = 0x100 ∨ a = 0x108 ∨ a = 0x138) := by
  have hl := hh.hlay
  have hidx := hh.hidx
  obtain ⟨hsh1, hsh2, hsb, hhg1, hhg2⟩ := shiftBelow_add lay hl
  -- block 263: test lay < 4
  have hs1 := symRun_sound blk316 codeAt_316 t hh.pc (by simp only [blk316.res, rv_simp])
  have r1 : RegsEq t (blk316.res.toState t) [.x3] := by
    intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have f1 : Frame t (blk316.res.toState t) (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk316.res]
  have x8' : (blk316.res.toState t).getReg .x8 = BitVec.ofNat 64 lay := by rw [r1.get .x8, hh.x8]
  have pc1 : (blk316.res.toState t).pc = if lay < 4 then pcOf 321 else pcOf 318 := by
    simp only [blk316.res, rv_simp, hh.x8]
    rw [show (4#64 : Word) = BitVec.ofNat 64 4 from rfl, ofNat_slt_ofNat _ _ (by omega) (by norm_num)]
    by_cases h : lay < 4
    · rw [if_pos h, if_pos (by simpa using h)]
    · rw [if_neg h, if_neg (by simpa using h)]
  -- the three ways to (s, h)
  obtain ⟨k2, c2, t2, hs2, hc2, pc2, x28, x9, r2, f2⟩ : ∃ k c t2, Steps image (blk316.res.toState t) k c t2 ∧
      c ≤ 9 ∧ t2.pc = pcOf 331 ∧ t2.getReg .x28 = BitVec.ofNat 64 (shiftBelow lay) ∧
      t2.getReg .x9 = BitVec.ofNat 64 (height lay) ∧ RegsEq (blk316.res.toState t) t2 [.x3, .x9, .x28] ∧
      Frame (blk316.res.toState t) t2 (fun _ => False) := by
    by_cases h4 : lay < 4
    · have hs3 := symRun_sound blk321 codeAt_321 _ (by rw [pc1, if_pos h4]) (by simp only [blk321.res, rv_simp])
      have r3 : RegsEq (blk316.res.toState t) (blk321.res.toState (blk316.res.toState t)) [] := by
        intro r hr; rw [Result.toState_getReg]
        cases r <;> first | exact absurd (by decide) hr | rfl
      have pc3 : (blk321.res.toState (blk316.res.toState t)).pc = if lay = 0 then pcOf 329 else pcOf 322 := by
        simp only [blk321.res, rv_simp, x8', ofNat_beq_ofNat]
        by_cases h : lay = 0
        · rw [if_pos h, if_pos (by simp [h])]
        · rw [if_neg h, if_neg (by rw [decide_eq_true_eq, Nat.mod_eq_of_lt (by omega)]; simpa using h)]
      have f3 : Frame (blk316.res.toState t) (blk321.res.toState (blk316.res.toState t)) (fun _ => False) := by
        apply frame_toState; intro x hx hW; simp [blk321.res]
      by_cases h0 : lay = 0
      · subst h0
        have hs4 := symRun_sound blk329 codeAt_329 _ (by rw [pc3, if_pos rfl]) (by simp only [blk329.res, rv_simp])
        refine ⟨_, _, _, hs3.trans hs4, by decide, by simp only [blk329.res, rv_simp], ?_, ?_, ?_, ?_⟩
        · simp only [blk329.res, rv_simp]; rfl
        · simp only [blk329.res, rv_simp]; rfl
        · exact (r3.trans (show RegsEq _ (blk329.res.toState _) [.x3, .x9, .x28] by
            intro r hr; rw [Result.toState_getReg]
            cases r <;> first | exact absurd (by decide) hr | rfl)).mono (by decide)
        · exact (f3.trans (by apply frame_toState; intro x hx hW; simp [blk329.res])).mono
            (by intro x hx; rcases hx with h | h <;> exact h)
      · have x8'' : (blk321.res.toState (blk316.res.toState t)).getReg .x8 = BitVec.ofNat 64 lay := by
          rw [r3.get .x8, x8']
        have hs4 := symRun_sound blk322 codeAt_322 _ (by rw [pc3, if_neg h0]) (by simp only [blk322.res, rv_simp])
        refine ⟨_, _, _, hs3.trans hs4, by decide, by simp only [blk322.res, rv_simp], ?_, ?_, ?_, ?_⟩
        · simp only [blk322.res, rv_simp, x8'']
          bvsimp []
          rw [shiftBelow_eq lay hl, if_neg h0, if_pos h4]; exact ofNat_congr (by omega)
        · simp only [blk322.res, rv_simp]; rw [height_eq lay hl, if_neg h0, if_pos h4]
        · exact (r3.trans (show RegsEq _ (blk322.res.toState _) [.x3, .x9, .x28] by
            intro r hr; rw [Result.toState_getReg]
            cases r <;> first | exact absurd (by decide) hr | rfl)).mono (by decide)
        · exact (f3.trans (by apply frame_toState; intro x hx hW; simp [blk322.res])).mono
            (by intro x hx; rcases hx with h | h <;> exact h)
    · refine ⟨_, _, _, symRun_sound blk318 codeAt_318 _ (by rw [pc1, if_neg h4])
        (by simp only [blk318.res, rv_simp]), by decide, by simp only [blk318.res, rv_simp], ?_, ?_, ?_, ?_⟩
      · simp only [blk318.res, rv_simp]
        rw [shiftBelow_eq lay hl, if_neg (by omega), if_neg h4]
      · simp only [blk318.res, rv_simp]; rw [height_eq lay hl, if_neg (by omega), if_neg h4]
      · intro r hr; rw [Result.toState_getReg]
        cases r <;> first | exact absurd (by decide) hr | rfl
      · apply frame_toState; intro x hx hW; simp [blk318.res]
  -- block 279: route, encoding tweak
  have rt2 : RegsEq t t2 ([.x3] ++ [.x3, .x9, .x28]) := r1.trans r2
  have y22 : t2.getReg .x22 = BitVec.ofNat 64 idx := by rw [rt2.get .x22, hh.x22]
  have y8 : t2.getReg .x8 = BitVec.ofNat 64 lay := by rw [rt2.get .x8, hh.x8]
  have hs3 := symRun_sound blk331 codeAt_331 t2 pc2 (by simp only [blk331.res, rv_simp])
  set t4 := blk331.res.toState t2 with ht4
  have hp1 : 1 ≤ 2 ^ height lay := Nat.one_le_two_pow
  set e := (route idx lay).1 with he
  set tau := (route idx lay).2 with htau
  have he' : e = idx / 2 ^ shiftBelow lay % 2 ^ height lay := rfl
  have htau' : tau = idx / 2 ^ (shiftBelow lay + height lay) := rfl
  have hpw : 2 ^ height lay ≤ 2048 := by
    calc 2 ^ height lay ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) hhg2
      _ = 2048 := by norm_num
  have he2048 : e < 2048 := by
    rw [he']; have := Nat.mod_lt (idx / 2 ^ shiftBelow lay) (Nat.two_pow_pos (height lay)); omega
  have htau30 : tau < 2 ^ 30 := by
    rw [htau', Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc idx < 2 ^ 34 := hidx
      _ = 2 ^ 30 * 2 ^ 4 := by norm_num
      _ ≤ 2 ^ 30 * 2 ^ (shiftBelow lay + height lay) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hsh1)
  have hdiv1 : idx / 2 ^ shiftBelow lay ≤ idx := Nat.div_le_self _ _
  have hdiv2 : idx / 2 ^ (shiftBelow lay + height lay) ≤ idx := Nat.div_le_self _ _
  have z13 : t4.getReg .x13 = BitVec.ofNat 64 e := by
    simp only [ht4, blk331.res, rv_simp, y22, x28, x9]
    bvsimp [Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
    rw [he']
  have z30 : t4.getReg .x30 = BitVec.ofNat 64 tau := by
    simp only [ht4, blk331.res, rv_simp, y22, x28, x9]
    bvsimp []
    rw [htau']
  have z31 : t4.getReg .x31 = BitVec.ofNat 64 (tau + 2 ^ 32 * e) := by
    simp only [ht4, blk331.res, rv_simp, y22, x28, x9]
    bvsimp [ofNat_eq_iff, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
    rw [htau', he']; congr 1; ring
  have f4 : Frame t2 t4 (fun a => a = 0x100 ∨ a = 0x108 ∨ a = 0x138) := by
    apply frame_toState; intro x hx hW
    simp only [blk331.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r4 : RegsEq t2 t4 [.x3, .x6, .x13, .x29, .x30, .x31] := by
    intro r hr; rw [ht4, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft4 : Frame t t4 (fun a => a = 0x100 ∨ a = 0x108 ∨ a = 0x138) :=
    (f1.trans (f2.trans f4)).mono (by intro x hx; rcases hx with h | h | h; exact h.elim; exact h.elim; exact h)
  have hc3 : blk331.res.cycles = 15 := rfl
  have hc1 : blk316.res.cycles = 2 := rfl
  refine ⟨_, _, t4, (hs1.trans (hs2.trans hs3)), by rw [hc1, hc3]; omega,
    by simp only [ht4, blk331.res, rv_simp], by simp only [ht4, blk331.res, rv_simp],
    by rw [r4.get .x9, x9], z13, z30, z31, ?_, ?_, ft4⟩
  · refine ⟨by omega, htau30, he2048, hh.hM, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ht4, blk331.res, rv_simp, y8]
      bvsimp [ofNat_eq_iff]
      unfold twWord0; congr 1
      rw [Nat.div_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (a := lay) (by omega)]; omega
    · have : t4.getMem (BitVec.ofNat 64 0x108) = t4.getReg .x31 := by
        simp (config := { decide := true }) only [ht4, blk331.res, rv_simp, ↓reduceIte]
      rw [this, z31]
    · rw [ft4.readWords _ _ (by norm_num) (by intro i hi; omega), hh.st.ebP]
    · rw [ft4.readWords _ _ (by norm_num) (by intro i hi; omega), hh.ebM]
    · simp only [ht4, blk331.res, rv_simp]; rfl
    · rw [r4.get .x5, rt2.get .x5, hh.x5]
    · rw [r4.get .x7, rt2.get .x7, hh.x7]
    · rw [r4.get .x26, rt2.get .x26, hh.x26]
    · rw [r4.get .x27, rt2.get .x27, hh.x27]
  · exact (rt2.trans r4).mono (by decide)

/-! ## `enc_ok`: counter, digits, tree setup (instructions 370 .. 507) -/

def digList (a : Word) : List Word := (a &&& 7) :: (List.range' 1 20).map (fun r => (a >>> (3 * r)) &&& 7)

-- The digit dwords written by `enc_ok` (kernel check with a variable state).
kernel_theorem blk382_dig : ∀ t : MachineState, (blk382.res.toState t).readWords (BitVec.ofNat 64 0x780) 42 =
    digList (t.getReg .x1) ++ digList (t.getReg .x2)

theorem digit_toNat (a : Word) (r : Nat) : ((a >>> (3 * r)) &&& 7).toNat = a.toNat / 2 ^ (3 * r) % 8 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact land7 _

theorem digList_ofNat (d : Nat) (hd : d < 2 ^ 64) :
    digList (BitVec.ofNat 64 d) = (digitsOfWord d).map (BitVec.ofNat 64) := by
  unfold digList digitsOfWord
  rw [show List.range 21 = 0 :: List.range' 1 20 from rfl]
  simp only [List.map_cons, List.map_map, Nat.pow_zero, Nat.div_one]
  congr 1
  · apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd,
      show (7 : Word).toNat = 7 from rfl, land7]
    have : d % 8 < 8 := Nat.mod_lt _ (by norm_num)
    omega
  · apply List.map_congr_left
    intro r hr
    simp only [Function.comp]
    apply BitVec.eq_of_toNat_eq
    rw [digit_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd, Nat.pow_mul]
    have : d / 8 ^ r % 8 < 8 := Nat.mod_lt _ (by norm_num)
    norm_num
    omega

theorem getD_append_left' {α : Type} (l1 l2 : List α) (i : Nat) (d : α) (h : i < l1.length) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' {α : Type} (l1 l2 : List α) (i : Nat) (d : α) (h : l1.length ≤ i) :
    (l1 ++ l2).getD i d = l2.getD (i - l1.length) d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem digitsOfWord_lt (d i : Nat) : (digitsOfWord d).getD i 0 < 8 := by
  unfold digitsOfWord
  by_cases h : i < 21
  · rw [getD_of_lt (by simpa using h)]; simp; exact Nat.mod_lt _ (by norm_num)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]; simp

theorem digits_lt (d0 d1 i : Nat) : (digitsOfWord d0 ++ digitsOfWord d1).getD i 0 < 8 := by
  by_cases h : i < 21
  · rw [getD_append_left' _ _ _ _ (by simp [digitsOfWord]; omega)]; exact digitsOfWord_lt _ _
  · rw [getD_append_right' _ _ _ _ (by simp [digitsOfWord]; omega)]; exact digitsOfWord_lt _ _

/-- `enc_ok` (330 .. 456): counter → stage, digits → `DIG8`, branch to the top layer or tree_build. -/
theorem enc_digits (lay c d0 d1 : Nat) (hlay : lay < 6) (hd0 : d0 < 2 ^ 63) (hd1 : d1 < 2 ^ 63)
    (t : MachineState) (tpc : t.pc = pcOf 382) (t1 : t.getReg .x1 = BitVec.ofNat 64 d0)
    (t2 : t.getReg .x2 = BitVec.ofNat 64 d1) (t6 : t.getReg .x6 = BitVec.ofNat 64 c)
    (t8 : t.getReg .x8 = BitVec.ofNat 64 lay) (t18 : t.getReg .x18 = BitVec.ofNat 64 (0x900 + 856 * lay)) :
    ∃ u, Steps image t 127 127 u ∧ u.pc = (if lay = 0 then pcOf 637 else pcOf 509) ∧
      u.readWords (BitVec.ofNat 64 0x780) 42 = (digitsOfWord d0 ++ digitsOfWord d1).map (BitVec.ofNat 64) ∧
      u.getMem (BitVec.ofNat 64 (0x900 + 856 * lay)) = BitVec.ofNat 64 c ∧
      RegsEq t u [.x3, .x14] ∧ Frame t u (fun a => a = 0x900 + 856 * lay ∨ (0x780 ≤ a ∧ a < 0x8D0)) := by
  have hs := symRun_sound blk382 codeAt_382 t tpc (by
    simp only [blk382.res, rv_simp]; bvsimp [t18, accessValid_ofNat, ne_eq, ofNat_eq_iff]; omega)
  have hc1 : blk382.res.cycles = 127 := rfl
  have hk1 : blk382.res.steps = 127 := rfl
  rw [hc1, hk1] at hs
  set u := blk382.res.toState t with hu
  refine ⟨u, hs, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hu, blk382.res, rv_simp, t8, ofNat_beq_ofNat]
    by_cases h : lay = 0
    · rw [if_pos h, if_pos (by simp [h])]
    · rw [if_neg h, if_neg (by rw [decide_eq_true_eq, Nat.mod_eq_of_lt (by omega)]; simpa using h)]
  · rw [hu, blk382_dig, t1, t2, digList_ofNat _ (by omega), digList_ofNat _ (by omega), ← List.map_append]
  · have hread := Result.toState_getMem_of_read blk382.res t (cfg := { noAlias := true })
      (k := ⟨some (.reg .x18), 0⟩) (by sym_eval) (by
        simp only [rv_simp, t18]; bvsimp [ne_eq, ofNat_eq_iff]; omega)
    rw [show (⟨some (.reg .x18), 0⟩ : Addr).eval t = BitVec.ofNat 64 (0x900 + 856 * lay) by
      simp [Addr.eval, E.eval, t18]] at hread
    rw [hu, hread]; simp [E.eval, t6]
  · intro r hr; rw [hu, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro x hx hW
    simp only [blk382.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t18, ofNat_eq_iff]
    omega

/-- Tree setup (457 .. 470): TA, the PB/CB/LB tweak words, `NCNT = 2^h`, `CB+32..48` cleared. -/
theorem tree_setup (S : List Byte) (lay tau h e d0 d1 : Nat) (hlay : lay < 6) (htau : tau < 2 ^ 30)
    (hh : 1 ≤ h ∧ h ≤ 6) (hheight : h = height lay) (he : e < 2 ^ h) (t : MachineState) (tpc : t.pc = pcOf 509)
    (hdig : t.readWords (BitVec.ofNat 64 0x780) 42 = (digitsOfWord d0 ++ digitsOfWord d1).map (BitVec.ofNat 64))
    (t5 : t.getReg .x5 = 0) (t8 : t.getReg .x8 = BitVec.ofNat 64 lay) (t9 : t.getReg .x9 = BitVec.ofNat 64 h)
    (t13 : t.getReg .x13 = BitVec.ofNat 64 e) (t18 : t.getReg .x18 = BitVec.ofNat 64 (0x900 + 856 * lay))
    (t30 : t.getReg .x30 = BitVec.ofNat 64 tau) (tst : Statics S t) :
    ∃ tt, Steps image t 13 13 tt ∧
      TreeCtx S (digitsOfWord d0 ++ digitsOfWord d1) ⟨lay, tau, h, e, 0x900 + 856 * lay⟩ tt ∧
      tt.pc = pcOf 522 ∧ tt.getReg .x20 = BitVec.ofNat 64 0 ∧
      RegsEq t tt [.x3, .x17, .x19, .x20, .x29] ∧
      Frame t tt (fun a => a = 0x6A0 ∨ a = 0xC0 ∨ a = 0x340 ∨ a = 0xE0 ∨ a = 0xE8) := by
  have hs := symRun_sound blk509 codeAt_509 t tpc (by simp only [blk509.res, rv_simp])
  have hc1 : blk509.res.cycles = 13 := rfl
  have hk1 : blk509.res.steps = 13 := rfl
  rw [hc1, hk1] at hs
  set tt := blk509.res.toState t with htt
  have f : Frame t tt (fun a => a = 0x6A0 ∨ a = 0xC0 ∨ a = 0x340 ∨ a = 0xE0 ∨ a = 0xE8) := by
    apply frame_toState; intro x hx hW
    simp only [blk509.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r : RegsEq t tt [.x3, .x17, .x19, .x20, .x29] := by
    intro r hr; rw [htt, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have hdig' : tt.readWords (BitVec.ofNat 64 0x780) 42 =
      (digitsOfWord d0 ++ digitsOfWord d1).map (BitVec.ofNat 64) := by
    rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), hdig]
  have hp1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hp32 : 2 ^ h ≤ 64 := pow_le32 _ hh.2
  refine ⟨tt, hs, ?_, by simp only [htt, blk509.res, rv_simp], by simp only [htt, blk509.res, rv_simp], r, f⟩
  refine ⟨by show lay < 7; omega, htau, hh.2, he, rfl, hheight, fun i => digits_lt d0 d1 i, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [r.get .x5, t5]
  · rw [r.get .x8, t8]
  · rw [r.get .x9, t9]
  · rw [r.get .x13, t13]
  · simp only [htt, blk509.res, rv_simp, t9]; bvsimp [Nat.one_mul]
  · rw [r.get .x18, t18]
  · simp only [htt, blk509.res, rv_simp]
  · rw [r.get .x30, t30]
  · intro i hi
    rw [getMem_of_readWords tt 42 0x780 i _ hdig' hi]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    rw [List.getD_eq_getElem?_getD]
    cases (digitsOfWord d0 ++ digitsOfWord d1)[i]? <;> rfl
  · simp only [htt, blk509.res, rv_simp, t8]
    bvsimp [ofNat_eq_iff]
    rw [lo32_replace0, ofNat_or_disjoint (lay * 65536) 1 16 (by omega) (by norm_num) (by omega)]
    simp only [truncate32_ofNat]; congr 1; ring
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.pbP]
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.pbS]
  · simp only [htt, blk509.res, rv_simp, t8]
    bvsimp [ofNat_eq_iff]
    rw [lo32_replace0, ofNat_or_disjoint (lay * 65536) 257 16 (by omega) (by norm_num) (by omega)]
    simp only [truncate32_ofNat]; congr 1; ring
  · rw [show (4 : Nat) = 2 + 2 from rfl, readWords_ofNat_add,
      f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.cbP, readWords_ofNat_two]
    simp only [htt, blk509.res, rv_simp]; rfl
  · simp only [htt, blk509.res, rv_simp, t8]
    bvsimp [ofNat_eq_iff]
    rw [ofNat_or_disjoint (lay * 65536) 513 16 (by omega) (by norm_num) (by omega)]
    unfold twWord0; congr 1
    rw [Nat.div_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (a := lay) (by omega)]; omega
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.lbP]
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.nbP]

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem signLayers_succ (S cache : List Byte) (idx lay : Nat) (M : Val) :
    signLayers S cache idx (lay + 1) M =
      searchCounter (lay + 1) (route idx (lay + 1)).2 (route idx (lay + 1)).1 M 0 cMax >>= fun r =>
        match r with
        | none => pure none
        | some (c, x) =>
          buildTree S (lay + 1) (route idx (lay + 1)).2 (height (lay + 1)) (route idx (lay + 1)).1 x >>= fun tr =>
            signLayers S cache idx lay tr.1 >>= fun r2 =>
              match r2 with
              | none => pure none
              | some rest => pure (some (rest ++ [(c, tr.2.1, tr.2.2)])) := by
  simp only [signLayers]
  rfl

theorem signTop_eq (S cache : List Byte) (idx : Nat) (M : Val) :
    signLayers S cache idx 0 M =
      searchCounter 0 (route idx 0).2 (route idx 0).1 M 0 cMax >>= fun r =>
        match r with
        | none => pure none
        | some (c, x) =>
          ((List.range (nChains / 2)).foldlM (fun (acc : List Val) k => do
              let (s0, s1) ← prf2 (prfInput S 0 (route idx 0).2 (route idx 0).1 k)
              let v0 ← chainTo 0 (route idx 0).2 (route idx 0).1 (2 * k) (x.getD (2 * k) 0) s0
              let v1 ← chainTo 0 (route idx 0).2 (route idx 0).1 (2 * k + 1) (x.getD (2 * k + 1) 0) s1
              pure (acc ++ [v0, v1])) [] >>= fun vals => topPath S cache (route idx 0).1 >>= fun path =>
                pure (vals, path)) >>= fun r => pure (some [(c, r.1, r.2)]) := by
  simp only [signLayers, signTop, bind_assoc, pure_bind]
  rfl

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- A staged layer signature (counter, 42 chain values, path) of layer `l`. -/
def StageAt (t : MachineState) (l : Nat) (ls : LayerSig) : Prop :=
  t.getMem (BitVec.ofNat 64 (0x900 + 856 * l)) = BitVec.ofNat 64 ls.1 ∧ ls.1 < 2 ^ 22 ∧
  ls.2.1.length = 42 ∧ (∀ v ∈ ls.2.1, v.length = 16) ∧ Slots t (0x900 + 856 * l + 8) ls.2.1 ∧
  ls.2.2.length = height l ∧ (∀ v ∈ ls.2.2, v.length = 16) ∧ Slots t (0x900 + 856 * l + 680) ls.2.2

theorem height_le (l : Nat) (hl : l < 6) : height l ≤ 11 := by interval_cases l <;> decide

theorem StageAt.frame {s t : MachineState} {W : Nat → Prop} {l : Nat} {ls : LayerSig}
    (h : StageAt s l ls) (hf : Frame s t W) (hl : l < 6)
    (hW : ∀ a, 0x900 + 856 * l ≤ a → a < 0x900 + 856 * (l + 1) → ¬ W a) : StageAt t l ls := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hh := height_le l hl
  refine ⟨?_, h2, h3, h4, ?_, h6, h7, ?_⟩
  · rw [hf.getMem (by omega) (hW _ (by omega) (by omega)), h1]
  · exact h5.frame hf (by omega) (fun i hi => ⟨hW _ (by omega) (by omega), hW _ (by omega) (by omega)⟩)
  · exact h8.frame hf (by omega) (fun i hi => ⟨hW _ (by omega) (by omega), hW _ (by omega) (by omega)⟩)

/-- Addresses written by layers `n .. 0`. -/
def layW (n : Nat) (a : Nat) : Prop := a < 0x900 ∨ (0x900 ≤ a ∧ a < 0x900 + 856 * (n + 1)) ∨ 0x30000 ≤ a

/-- Result of `signLayers n`. -/
def LaysPost (t0 : MachineState) (n : Nat) : Option (List LayerSig) → MachineState → Prop
  | none, t => t.pc = pcOf 381 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1
  | some lays, t => lays.length = n + 1 ∧ (∀ l (hl : l < lays.length), StageAt t l lays[l]) ∧
      t.pc = pcOf 718 ∧ t.getReg .x5 = 0 ∧ Frame t0 t (layW n)

/-- Cycle bound of one layer below the top. -/
def layCyc : Nat := 26 + ((2 ^ 22) * 40 + 2) + (127 + (13 + (treeCyc + 7)))

/-- Cycle bound of the top layer. -/
def topCyc : Nat := 26 + ((2 ^ 22) * 40 + 2) + (127 + (9 + (21 * 320 + (4 + 11 * 36))))

/-- End of a layer (instructions 565 .. 571): root → `EB+32`, next layer. -/
theorem layer_tail (lay : Nat) (hlay : lay < 6) (h1 : 1 ≤ lay) (t : MachineState) (tpc : t.pc = pcOf 630)
    (t8 : t.getReg .x8 = BitVec.ofNat 64 lay) (t18 : t.getReg .x18 = BitVec.ofNat 64 (0x900 + 856 * lay))
    (t19 : t.getReg .x19 = BitVec.ofNat 64 0xB0000) :
    ∃ t', Steps image t 7 7 t' ∧ t'.pc = pcOf 316 ∧ t'.getReg .x8 = BitVec.ofNat 64 (lay - 1) ∧
      t'.getReg .x18 = BitVec.ofNat 64 (0x900 + 856 * (lay - 1)) ∧
      t'.readWords (BitVec.ofNat 64 0x120) 2 = t.readWords (BitVec.ofNat 64 0xB0000) 2 ∧
      RegsEq t t' [.x1, .x2, .x8, .x18] ∧ Frame t t' (fun a => a = 0x120 ∨ a = 0x128) := by
  have hs := symRun_sound blk630 codeAt_630 t tpc (by
    simp only [blk630.res, rv_simp]; bvsimp [t19, accessValid_ofNat]; norm_num)
  set t' := blk630.res.toState t with ht'
  refine ⟨t', hs, by simp only [ht', blk630.res, rv_simp], ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ht', blk630.res, rv_simp, t8]; bvsimp []
  · simp only [ht', blk630.res, rv_simp, t18]; bvsimp []; exact ofNat_congr (by omega)
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht', blk630.res, rv_simp, t19]; bvsimp []; simp
  · intro r hr; rw [ht', Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro x hx hW
    simp only [blk630.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem length_cacheNode (cache : List Byte) (hc : cache.length = 131072) (l j : Nat) (hl : l < 11)
    (hj : j < 2 ^ (11 - l)) : (cacheNode cache l j).length = 16 := by
  have := cacheNodeOff_lt l j hl hj
  simp [cacheNode, slice, hc]; omega

/-- The top layer, from `layer_loop` with `LAY = 0`. -/
theorem top_layer_sim (S cache : List Byte) (hS : S.length = 32) (hcache : cache.length = 131072)
    (idx : Nat) (M : Val) (t : MachineState) (hh : LayHead S cache idx 0 M t) :
    Sim image t topCyc (signLayers S cache idx 0 M) (LaysPost t 0) := by
  have hidx := hh.hidx
  obtain ⟨k, c0, t4, hs4, hc4, pc4, x46, x49, x413, x430, x431, emem, r4, f4⟩ := layer_header S cache idx 0 M t hh
  set e := (route idx 0).1 with he
  set tau := (route idx 0).2 with htau
  have he2048 := emem.he
  have htau30 := emem.htau
  rw [signTop_eq, show cMax = 2 ^ 22 - 1 + 1 from rfl]
  have henc := encLoop_sim 0 tau e M t4 emem (2 ^ 22 - 1) 0 t4 (by norm_num)
    ⟨pc4, x46, by norm_num, RegsEq.refl _ _, Frame.refl _ _⟩
  refine (Sim.steps hs4 (Sim.bind (W₂ := 127 + (9 + (21 * 320 + (4 + 11 * 36)))) henc
    (fun r t5 h5 => ?_))).mono (by unfold topCyc; omega) (fun _ _ h => h)
  rcases r with _ | ⟨c, x⟩
  · exact (Sim.pure (Q := LaysPost t 0) (a := none) (s := t5) h5).mono (by omega) (fun _ _ h => h)
  obtain ⟨pc5, x56, hc, ⟨d0, d1, hd0, hd1, hx, hsum, x51, x52⟩, r5, f5⟩ := h5
  subst hx
  have rt5 : RegsEq t t5 ([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) := r4.trans r5
  have ft5 : Frame t t5 (fun a => (a = 0x100 ∨ a = 0x108 ∨ a = 0x138) ∨ encW a) := f4.trans f5
  obtain ⟨u, hsu, pcu, digu, cntu, ru, fu⟩ := enc_digits 0 c d0 d1 (by norm_num) hd0 hd1 t5 pc5 x51 x52 x56
    (by rw [rt5.get .x8, hh.x8]) (by rw [rt5.get .x18, hh.x18])
  rw [if_pos rfl] at pcu
  have rtu : RegsEq t u (([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) ++ [.x3, .x14]) := rt5.trans ru
  have ftu : Frame t u (fun a => ((a = 0x100 ∨ a = 0x108 ∨ a = 0x138) ∨ encW a) ∨
      (a = 0x900 + 856 * 0 ∨ (0x780 ≤ a ∧ a < 0x8D0))) := ft5.trans fu
  have tctx : TopCtx S cache (digitsOfWord d0 ++ digitsOfWord d1) tau e u := by
    refine ⟨htau30, he2048, fun i => digits_lt d0 d1 i, by rw [rtu.get .x5, hh.x5],
      by rw [ru.get .x13, r5.get .x13, x413], by rw [rtu.get .x18, hh.x18],
      by rw [ru.get .x31, r5.get .x31, x431], fun i hi => ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [getMem_of_readWords u 42 0x780 i _ digu hi]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getD_eq_getElem?_getD]
      cases (digitsOfWord d0 ++ digitsOfWord d1)[i]? <;> rfl
    · rw [ftu.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hh.st.pbP]
    · rw [ftu.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hh.st.pbS]
    · rw [ftu.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hh.st.cbP]
    · exact hh.region.frame ftu (by intro a ha; simp only [regionA] at ha; simp only [encW]; omega)
    · exact fun l j hl hj => length_cacheNode cache hcache l j hl hj
  refine Sim.steps hsu (Sim.bind (W₂ := 0) (top_sim S cache hS _ tau e u tctx pcu) (fun r t6 h6 => ?_))
  obtain ⟨hl1, hv1, hs1, hl2, hv2, hs2, pc6, x65, f6⟩ := h6
  refine Sim.pure ⟨rfl, fun l hl => ?_, pc6, x65, ?_⟩
  · simp only [List.length_singleton] at hl
    have : l = 0 := by omega
    subst this
    refine ⟨?_, hc, hl1, hv1, hs1, hl2, hv2, hs2⟩
    rw [f6.getMem (by norm_num) (by simp only [topW]; omega), cntu]; rfl
  · exact (ftu.trans f6).mono (by intro a ha; simp only [encW, topW, layW] at ha ⊢; omega)

theorem height_bounds (lay : Nat) (h1 : 1 ≤ lay) (h6 : lay < 5) : 4 ≤ height lay ∧ height lay ≤ 6 := by
  interval_cases lay <;> decide

/-- **The layers** `n .. 0` (layer 0 is the cached top tree). -/
theorem layers_sim (S cache : List Byte) (hS : S.length = 32) (hcache : cache.length = 131072)
    (idx : Nat) (hidx : idx < 2 ^ 34) :
    ∀ n, n ≤ 4 → ∀ (M : Val) (t : MachineState), LayHead S cache idx n M t →
      Sim image t (n * layCyc + topCyc) (signLayers S cache idx n M) (LaysPost t n) := by
  intro n
  induction n with
  | zero =>
    intro _ M t hh
    simpa using top_layer_sim S cache hS hcache idx M t hh
  | succ n ih =>
    intro hn M t hh
    have hl : n + 1 < 5 := by omega
    have hhb := height_bounds (n + 1) (by omega) hl
    obtain ⟨k, c0, t4, hs4, hc4, pc4, x46, x49, x413, x430, x431, emem, r4, f4⟩ :=
      layer_header S cache idx (n + 1) M t hh
    set e := (route idx (n + 1)).1 with he
    set tau := (route idx (n + 1)).2 with htau
    have he32 : e < 2 ^ height (n + 1) := Nat.mod_lt _ (Nat.two_pow_pos _)
    have htau30 := emem.htau
    rw [signLayers_succ, show cMax = 2 ^ 22 - 1 + 1 from rfl]
    have henc := encLoop_sim (n + 1) tau e M t4 emem (2 ^ 22 - 1) 0 t4 (by norm_num)
      ⟨pc4, x46, by norm_num, RegsEq.refl _ _, Frame.refl _ _⟩
    have hW : c0 + ((2 ^ 22 - 1 + 1) * 40 + 2 + (127 + (13 + (treeCyc + (7 + (n * layCyc + topCyc + 0)))))) ≤
        (n + 1) * layCyc + topCyc := by
      have hL : 26 + ((2 ^ 22) * 40 + 2) + (127 + (13 + (treeCyc + 7))) = layCyc := rfl
      rw [Nat.add_mul n 1 layCyc, Nat.one_mul]; omega
    refine (Sim.steps hs4 (Sim.bind henc (fun r t5 h5 => ?_))).mono hW (fun _ _ h => h)
    rcases r with _ | ⟨c, x⟩
    · exact (Sim.pure (Q := LaysPost t (n + 1)) (a := none) (s := t5) h5).mono (by omega)
        (fun _ _ h => h)
    · obtain ⟨pc5, x56, hc, ⟨d0, d1, hd0, hd1, hx, hsum, x51, x52⟩, r5, f5⟩ := h5
      subst hx
      have rt5 : RegsEq t t5 ([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) := r4.trans r5
      have ft5 : Frame t t5 (fun a => (a = 0x100 ∨ a = 0x108 ∨ a = 0x138) ∨ encW a) := f4.trans f5
      obtain ⟨u, hsu, pcu, digu, cntu, ru, fu⟩ := enc_digits (n + 1) c d0 d1 (by omega) hd0 hd1 t5 pc5 x51 x52 x56
        (by rw [rt5.get .x8, hh.x8]) (by rw [rt5.get .x18, hh.x18])
      rw [if_neg (by omega)] at pcu
      have rtu : RegsEq t u (([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) ++ [.x3, .x14]) :=
        rt5.trans ru
      have ftu := ft5.trans fu
      have stu : Statics S u := hh.st.frame ftu (by
        intro a ha; simp only [staticA] at ha; simp only [encW]; omega)
      obtain ⟨tt, hs6, tctx, pc6, x620, r6, f6⟩ := tree_setup S (n + 1) tau (height (n + 1)) e d0 d1 (by omega) htau30
        ⟨by omega, hhb.2⟩ rfl he32 u pcu digu (by rw [rtu.get .x5, hh.x5]) (by rw [rtu.get .x8, hh.x8])
        (by rw [ru.get .x9, r5.get .x9, x49]) (by rw [ru.get .x13, r5.get .x13, x413])
        (by rw [rtu.get .x18, hh.x18]) (by rw [ru.get .x30, r5.get .x30, x430]) stu
      refine Sim.steps hsu (Sim.steps hs6 (Sim.bind (tree_sim S hS _ ⟨n + 1, tau, height (n + 1), e,
        0x900 + 856 * (n + 1)⟩ tt tctx (show 1 ≤ height (n + 1) by omega) pc6 x620) (fun tr t7 h7 => ?_)))
      obtain ⟨pc7, hr1, hroot, hv1, hvv, hvs, hp1, hpv, hps, r7, f7⟩ := h7
      have rt7 : RegsEq t t7 ((([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) ++ [.x3, .x14]) ++
          [.x3, .x17, .x19, .x20, .x29] ++ treeRegs) := (rtu.trans r6).trans r7
      obtain ⟨t8, hs8, pc8, x88, x818, heb, r8, f8⟩ := layer_tail (n + 1) (by omega) (by omega) t7 pc7
        (by rw [rt7.get .x8, hh.x8]) (by rw [rt7.get .x18, hh.x18])
        (by rw [r7.get .x19, tctx.x19])
      have rt8 : RegsEq t t8 _ := rt7.trans r8
      have ft8' := ((ftu.trans f6).trans f7).trans f8
      have ft8 : Frame t t8 (layW (n + 1)) := ft8'.mono (by
        intro a ha
        simp only [encW, treeW, leavesW, tlevW] at ha
        simp only [layW]; omega)
      have st8 : Statics S t8 := hh.st.frame ft8' (by
        intro a ha h
        simp only [staticA] at ha; simp only [encW, treeW, leavesW, tlevW] at h; omega)
      have rg8 : RegionOk cache t8 := hh.region.frame ft8' (by
        intro a ha h
        simp only [regionA] at ha; simp only [encW, treeW, leavesW, tlevW] at h; omega)
      -- the layers below
      have hroot16 : tr.1.length = 16 := hr1
      have hih := ih (by omega) tr.1 t8 ⟨by omega, hidx, hroot16, pc8, by rw [rt8.get .x5, hh.x5],
          by rw [rt8.get .x7, hh.x7], by rw [x88]; exact ofNat_congr (by omega),
          by rw [x818]; exact ofNat_congr (by omega), by rw [rt8.get .x22, hh.x22],
          by rw [rt8.get .x26, hh.x26], by rw [rt8.get .x27, hh.x27],
          by rw [heb, hroot 0 (by simp)]; simp, st8, rg8⟩
      refine Sim.steps hs8 (Sim.bind (W₂ := 0) hih (fun r2 t9 h9 => ?_))
      rcases r2 with _ | rest
      · exact Sim.pure h9
      · obtain ⟨hlen, hstages, pc9, x95, f9⟩ := h9
        refine Sim.pure ⟨by simp [hlen], ?_, pc9, x95, ?_⟩
        · intro l hl'
          simp only [List.length_append, List.length_singleton] at hl'
          by_cases hln : l < rest.length
          · rw [List.getElem_append_left hln]; exact hstages l hln
          · have : l = n + 1 := by omega
            subst this
            rw [List.getElem_append_right (by omega)]
            simp only [hlen, Nat.sub_self, List.getElem_singleton]
            have hst7 : StageAt t7 (n + 1) (c, tr.2.1, tr.2.2) := by
              refine ⟨?_, hc, hv1, hvv, hvs, hp1, hpv, hps⟩
              rw [f7.getMem (by omega) (by simp only [treeW, leavesW, tlevW]; omega),
                f6.getMem (by omega) (by omega), cntu]
            exact (hst7.frame (f8.trans f9) (by omega) (by
              intro a h1 h2 h; rcases h with h | h
              · omega
              · simp only [layW] at h; omega))
        · exact (ft8.trans f9).mono (by
            intro a ha; simp only [layW] at ha ⊢; omega)

end SigGolfCandidate.Sign
