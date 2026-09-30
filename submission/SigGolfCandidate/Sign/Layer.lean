import SigGolfCandidate.Sign.Tree
import SigGolfCandidate.Sign.Enc

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
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

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

/-- The state at `layer_loop` for layer `lay` with message `M`. -/
structure LayHead (S : List Byte) (idx lay : Nat) (M : Val) (t : MachineState) : Prop where
  hlay : lay < 7
  hidx : idx < 2 ^ 34
  hM : M.length = 16
  pc : t.pc = pcOf 205
  x5 : t.getReg .x5 = 0
  x7 : t.getReg .x7 = BitVec.ofNat 64 (2 ^ 20)
  x8 : t.getReg .x8 = BitVec.ofNat 64 lay
  x18 : t.getReg .x18 = BitVec.ofNat 64 (0x900 + 760 * lay)
  x22 : t.getReg .x22 = BitVec.ofNat 64 idx
  ebM : t.readWords (BitVec.ofNat 64 0x120) 2 = wordsOf M
  st : Statics S t

theorem shiftBelow_eq (lay : Nat) (h : lay < 7) :
    shiftBelow lay = if lay = 6 then 0 else 29 - 5 * lay := by
  interval_cases lay <;> decide

theorem height_eq (lay : Nat) : height lay = if lay = 6 then 4 else 5 := rfl

/-- Route and header state at `enc_loop`. -/
theorem layer_header (S : List Byte) (idx lay : Nat) (M : Val) (t : MachineState)
    (hh : LayHead S idx lay M t) :
    ∃ k c t4, Steps image t k c t4 ∧ c ≤ 22 ∧ t4.pc = pcOf 230 ∧
      t4.getReg .x6 = BitVec.ofNat 64 0 ∧ t4.getReg .x9 = BitVec.ofNat 64 (height lay) ∧
      t4.getReg .x13 = BitVec.ofNat 64 ((route idx lay).1) ∧
      t4.getReg .x30 = BitVec.ofNat 64 ((route idx lay).2) ∧
      EncMem lay (route idx lay).2 (route idx lay).1 M t4 ∧
      RegsEq t t4 [.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ∧
      Frame t t4 (fun a => a = 0x100 ∨ a = 0x108 ∨ a = 0x138) := by
  have hl := hh.hlay
  have hidx := hh.hidx
  -- block 205: test lay = 6
  have hs1 := symRun_sound blk205 codeAt_205 t hh.pc (by simp only [blk205.res, rv_simp])
  have r1 : RegsEq t (blk205.res.toState t) [.x3] := by
    intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have f1 : Frame t (blk205.res.toState t) (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk205.res]
  have pc1 : (blk205.res.toState t).pc = if lay = 6 then pcOf 207 else pcOf 210 := by
    simp only [blk205.res, rv_simp, hh.x8, ofNat_bne_ofNat]
    by_cases h : lay = 6
    · rw [if_pos h, if_neg (by rw [bne_cond _ _ (by omega) (by norm_num)]; omega)]
    · rw [if_neg h, if_pos (by rw [bne_cond _ _ (by omega) (by norm_num)]; omega)]
  -- the two ways to (s, h)
  obtain ⟨k2, c2, t2, hs2, hc2, pc2, x28, x9, r2, f2⟩ : ∃ k c t2, Steps image (blk205.res.toState t) k c t2 ∧
      c ≤ 5 ∧ t2.pc = pcOf 215 ∧ t2.getReg .x28 = BitVec.ofNat 64 (shiftBelow lay) ∧
      t2.getReg .x9 = BitVec.ofNat 64 (height lay) ∧ RegsEq (blk205.res.toState t) t2 [.x3, .x9, .x28] ∧
      Frame (blk205.res.toState t) t2 (fun _ => False) := by
    by_cases h6 : lay = 6
    · subst h6
      refine ⟨_, _, _, symRun_sound blk207 codeAt_207 _ (by rw [pc1, if_pos rfl])
        (by simp only [blk207.res, rv_simp]), by decide, by simp only [blk207.res, rv_simp], ?_, ?_, ?_, ?_⟩
      · simp only [blk207.res, rv_simp]; rfl
      · simp only [blk207.res, rv_simp]; rfl
      · intro r hr; rw [Result.toState_getReg]
        cases r <;> first | exact absurd (by decide) hr | rfl
      · apply frame_toState; intro x hx hW; simp [blk207.res]
    · have x8' : (blk205.res.toState t).getReg .x8 = BitVec.ofNat 64 lay := by
        rw [r1.get .x8, hh.x8]
      refine ⟨_, _, _, symRun_sound blk210 codeAt_210 _ (by rw [pc1, if_neg h6])
        (by simp only [blk210.res, rv_simp]), by decide, by simp only [blk210.res, rv_simp], ?_, ?_, ?_, ?_⟩
      · simp only [blk210.res, rv_simp, x8']
        bvsimp []
        rw [shiftBelow_eq lay hl, if_neg h6]; congr 1; omega
      · simp only [blk210.res, rv_simp]; rw [height_eq, if_neg h6]
      · intro r hr; rw [Result.toState_getReg]
        cases r <;> first | exact absurd (by decide) hr | rfl
      · apply frame_toState; intro x hx hW; simp [blk210.res]
  -- block 215: route, encoding tweak
  have rt2 : RegsEq t t2 ([.x3] ++ [.x3, .x9, .x28]) := r1.trans r2
  have y22 : t2.getReg .x22 = BitVec.ofNat 64 idx := by rw [rt2.get .x22, hh.x22]
  have y8 : t2.getReg .x8 = BitVec.ofNat 64 lay := by rw [rt2.get .x8, hh.x8]
  have hs3 := symRun_sound blk215 codeAt_215 t2 pc2 (by simp only [blk215.res, rv_simp])
  set t4 := blk215.res.toState t2 with ht4
  have hsb : shiftBelow lay ≤ 29 := by rw [shiftBelow_eq lay hl]; split <;> omega
  have hhg : 4 ≤ height lay ∧ height lay ≤ 5 := by rw [height_eq]; split <;> omega
  have hsh : 4 ≤ shiftBelow lay + height lay := by rw [shiftBelow_eq lay hl, height_eq]; split <;> omega
  have hp1 : 1 ≤ 2 ^ height lay := Nat.one_le_two_pow
  have hp32 : 2 ^ height lay ≤ 32 := pow_le32 _ hhg.2
  set e := (route idx lay).1 with he
  set tau := (route idx lay).2 with htau
  have he' : e = idx / 2 ^ shiftBelow lay % 2 ^ height lay := rfl
  have htau' : tau = idx / 2 ^ (shiftBelow lay + height lay) := rfl
  have he32 : e < 32 := by rw [he']; have := Nat.mod_lt (idx / 2 ^ shiftBelow lay) (Nat.two_pow_pos (height lay)); omega
  have htau30 : tau < 2 ^ 30 := by
    rw [htau', Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
    calc idx < 2 ^ 34 := hidx
      _ = 2 ^ 30 * 2 ^ 4 := by norm_num
      _ ≤ 2 ^ 30 * 2 ^ (shiftBelow lay + height lay) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hsh)
  have hdiv1 : idx / 2 ^ shiftBelow lay ≤ idx := Nat.div_le_self _ _
  have hdiv2 : idx / 2 ^ (shiftBelow lay + height lay) ≤ idx := Nat.div_le_self _ _
  have z13 : t4.getReg .x13 = BitVec.ofNat 64 e := by
    simp only [ht4, blk215.res, rv_simp, y22, x28, x9]
    bvsimp [Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
    rw [he']
  have z30 : t4.getReg .x30 = BitVec.ofNat 64 tau := by
    simp only [ht4, blk215.res, rv_simp, y22, x28, x9]
    bvsimp []
    rw [htau']
  have f4 : Frame t2 t4 (fun a => a = 0x100 ∨ a = 0x108 ∨ a = 0x138) := by
    apply frame_toState; intro x hx hW
    simp only [blk215.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r4 : RegsEq t2 t4 [.x3, .x6, .x13, .x29, .x30, .x31] := by
    intro r hr; rw [ht4, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft4 : Frame t t4 (fun a => a = 0x100 ∨ a = 0x108 ∨ a = 0x138) :=
    (f1.trans (f2.trans f4)).mono (by intro x hx; rcases hx with h | h | h; exact h.elim; exact h.elim; exact h)
  have hc3 : blk215.res.cycles = 15 := rfl
  have hc1 : blk205.res.cycles = 2 := rfl
  refine ⟨_, _, t4, (hs1.trans (hs2.trans hs3)), by rw [hc1, hc3]; omega,
    by simp only [ht4, blk215.res, rv_simp], by simp only [ht4, blk215.res, rv_simp],
    by rw [r4.get .x9, x9], z13, z30, ?_, ?_, ft4⟩
  · refine ⟨hl, htau30, he32, hh.hM, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [ht4, blk215.res, rv_simp, y8]
      bvsimp [ofNat_eq_iff]
      unfold twWord0; congr 1
      rw [Nat.div_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (a := lay) (by omega)]; omega
    · simp only [ht4, blk215.res, rv_simp, y22, x28, x9]
      bvsimp [ofNat_eq_iff, Nat.one_mul, Nat.and_two_pow_sub_one_eq_mod]
      rw [htau', he']; congr 1; ring
    · rw [ft4.readWords _ _ (by norm_num) (by intro i hi; omega), hh.st.ebP]
    · rw [ft4.readWords _ _ (by norm_num) (by intro i hi; omega), hh.ebM]
    · simp only [ht4, blk215.res, rv_simp]; rfl
    · rw [r4.get .x5, rt2.get .x5, hh.x5]
    · rw [r4.get .x7, rt2.get .x7, hh.x7]
  · exact (rt2.trans r4).mono (by decide)

/-! ## `enc_ok`: counter, digits, tree setup (instructions 370 .. 507) -/

def digList (a : Word) : List Word := (a &&& 7) :: (List.range' 1 20).map (fun r => (a >>> (3 * r)) &&& 7)

-- The digit dwords written by `enc_ok` (kernel check with a variable state).
kernel_theorem blk370_dig : ∀ t : MachineState, (blk370.res.toState t).readWords (BitVec.ofNat 64 0x780) 42 =
    digList (t.getReg .x1) ++ digList (t.getReg .x2)

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

theorem enc_ok (S : List Byte) (lay tau h e c d0 d1 : Nat) (hlay : lay < 7) (htau : tau < 2 ^ 30)
    (hh : 1 ≤ h ∧ h ≤ 5) (he : e < 2 ^ h) (hc : c < 2 ^ 20) (hd0 : d0 < 2 ^ 63) (hd1 : d1 < 2 ^ 63)
    (t : MachineState) (tpc : t.pc = pcOf 370) (t1 : t.getReg .x1 = BitVec.ofNat 64 d0)
    (t2 : t.getReg .x2 = BitVec.ofNat 64 d1) (t5 : t.getReg .x5 = 0) (t6 : t.getReg .x6 = BitVec.ofNat 64 c)
    (t8 : t.getReg .x8 = BitVec.ofNat 64 lay) (t9 : t.getReg .x9 = BitVec.ofNat 64 h)
    (t13 : t.getReg .x13 = BitVec.ofNat 64 e) (t18 : t.getReg .x18 = BitVec.ofNat 64 (0x900 + 760 * lay))
    (t30 : t.getReg .x30 = BitVec.ofNat 64 tau) (tst : Statics S t) :
    ∃ tt, Steps image t 140 140 tt ∧
      TreeCtx S (digitsOfWord d0 ++ digitsOfWord d1) ⟨lay, tau, h, e, 0x900 + 760 * lay⟩ tt ∧
      tt.pc = pcOf 510 ∧ tt.getReg .x20 = BitVec.ofNat 64 0 ∧
      tt.getMem (BitVec.ofNat 64 (0x900 + 760 * lay)) = BitVec.ofNat 64 c ∧
      RegsEq t tt [.x3, .x14, .x17, .x19, .x20, .x29] ∧
      Frame t tt (fun a => a = 0x900 + 760 * lay ∨ (0x780 ≤ a ∧ a < 0x8D0) ∨ a = 0x6A0 ∨ a = 0xC0 ∨
        a = 0x340 ∨ a = 0xE0 ∨ a = 0xE8) := by
  have hs := symRun_sound blk370 codeAt_370 t tpc (by
    simp only [blk370.res, rv_simp]; bvsimp [t18, accessValid_ofNat, ne_eq, ofNat_eq_iff]; omega)
  have hc1 : blk370.res.cycles = 140 := rfl
  have hk1 : blk370.res.steps = 140 := rfl
  rw [hc1, hk1] at hs
  set tt := blk370.res.toState t with htt
  have f : Frame t tt (fun a => a = 0x900 + 760 * lay ∨ (0x780 ≤ a ∧ a < 0x8D0) ∨ a = 0x6A0 ∨
      a = 0xC0 ∨ a = 0x340 ∨ a = 0xE0 ∨ a = 0xE8) := by
    apply frame_toState; intro x hx hW
    simp only [blk370.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [t18, ofNat_eq_iff]
    omega
  have r : RegsEq t tt [.x3, .x14, .x17, .x19, .x20, .x29] := by
    intro r hr; rw [htt, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have hdig := blk370_dig t
  rw [t1, t2, digList_ofNat _ (by omega), digList_ofNat _ (by omega), ← List.map_append] at hdig
  have hp1 : 1 ≤ 2 ^ h := Nat.one_le_two_pow
  have hp32 : 2 ^ h ≤ 32 := pow_le32 _ hh.2
  refine ⟨tt, hs, ?_, by simp only [htt, blk370.res, rv_simp], by simp only [htt, blk370.res, rv_simp], ?_, r, f⟩
  · refine ⟨hlay, htau, hh.2, he, rfl, fun i => digits_lt d0 d1 i, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [r.get .x5, t5]
    · rw [r.get .x8, t8]
    · rw [r.get .x9, t9]
    · rw [r.get .x13, t13]
    · simp only [htt, blk370.res, rv_simp, t9]; bvsimp [Nat.one_mul]
    · rw [r.get .x18, t18]
    · simp only [htt, blk370.res, rv_simp]
    · rw [r.get .x30, t30]
    · intro i hi
      rw [getMem_of_readWords tt 42 0x780 i _ hdig hi]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map]
      rw [List.getD_eq_getElem?_getD]
      cases (digitsOfWord d0 ++ digitsOfWord d1)[i]? <;> rfl
    · simp only [htt, blk370.res, rv_simp, t8]
      bvsimp [ofNat_eq_iff]
      rw [lo32_replace0, ofNat_or_disjoint (lay * 65536) 1 16 (by omega) (by norm_num) (by omega)]
      simp only [truncate32_ofNat]; congr 1; ring
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.pbP]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.pbS]
    · simp only [htt, blk370.res, rv_simp, t8]
      bvsimp [ofNat_eq_iff]
      rw [lo32_replace0, ofNat_or_disjoint (lay * 65536) 257 16 (by omega) (by norm_num) (by omega)]
      simp only [truncate32_ofNat]; congr 1; ring
    · rw [show (4 : Nat) = 2 + 2 from rfl, readWords_ofNat_add,
        f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.cbP, readWords_ofNat_two]
      simp only [htt, blk370.res, rv_simp]; rfl
    · simp only [htt, blk370.res, rv_simp, t8]
      bvsimp [ofNat_eq_iff]
      rw [ofNat_or_disjoint (lay * 65536) 513 16 (by omega) (by norm_num) (by omega)]
      unfold twWord0; congr 1
      rw [Nat.div_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (a := lay) (by omega)]; omega
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.lbP]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), tst.nbP]
  · have hread := Result.toState_getMem_of_read blk370.res t (cfg := { noAlias := true })
      (k := ⟨some (.reg .x18), 0⟩) (by sym_eval) (by
        simp only [rv_simp, t18]; bvsimp [ne_eq, ofNat_eq_iff]; omega)
    rw [show (⟨some (.reg .x18), 0⟩ : Addr).eval t = BitVec.ofNat 64 (0x900 + 760 * lay) by
      simp [Addr.eval, E.eval, t18]] at hread
    rw [htt, hread]; simp [E.eval, t6]

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem signLayers_succ (S : List Byte) (idx lay : Nat) (M : Val) :
    signLayers S idx (lay + 1) M =
      searchCounter lay (route idx lay).2 (route idx lay).1 M 0 cMax >>= fun r =>
        match r with
        | none => pure none
        | some (c, x) =>
          buildTree S lay (route idx lay).2 (height lay) (route idx lay).1 x >>= fun tr =>
            signLayers S idx lay tr.1 >>= fun r2 =>
              match r2 with
              | none => pure none
              | some rest => pure (some (rest ++ [(c, tr.2.1, tr.2.2)])) := by
  simp only [signLayers]
  rfl

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- A staged layer signature (counter, 42 chain values, path) of layer `l`. -/
def StageAt (t : MachineState) (l : Nat) (ls : LayerSig) : Prop :=
  t.getMem (BitVec.ofNat 64 (0x900 + 760 * l)) = BitVec.ofNat 64 ls.1 ∧ ls.1 < 2 ^ 20 ∧
  ls.2.1.length = 42 ∧ (∀ v ∈ ls.2.1, v.length = 16) ∧ Slots t (0x900 + 760 * l + 8) ls.2.1 ∧
  ls.2.2.length = height l ∧ (∀ v ∈ ls.2.2, v.length = 16) ∧ Slots t (0x900 + 760 * l + 680) ls.2.2

theorem StageAt.frame {s t : MachineState} {W : Nat → Prop} {l : Nat} {ls : LayerSig}
    (h : StageAt s l ls) (hf : Frame s t W) (hl : l < 7)
    (hW : ∀ a, 0x900 + 760 * l ≤ a → a < 0x900 + 760 * (l + 1) → ¬ W a) : StageAt t l ls := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hh : height l ≤ 5 := by rw [height_eq]; split <;> omega
  refine ⟨?_, h2, h3, h4, ?_, h6, h7, ?_⟩
  · rw [hf.getMem (by omega) (hW _ (by omega) (by omega)), h1]
  · exact h5.frame hf (by omega) (fun i hi => ⟨hW _ (by omega) (by omega), hW _ (by omega) (by omega)⟩)
  · exact h8.frame hf (by omega) (fun i hi => ⟨hW _ (by omega) (by omega), hW _ (by omega) (by omega)⟩)

/-- Addresses written by layers `n-1 .. 0`. -/
def layW (n : Nat) (a : Nat) : Prop := a < 0x900 ∨ (0x900 ≤ a ∧ a < 0x900 + 760 * n) ∨ 0x30000 ≤ a

/-- Result of `signLayers n`. -/
def LaysPost (t0 : MachineState) (n : Nat) : Option (List LayerSig) → MachineState → Prop
  | none, t => t.pc = pcOf 369 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1
  | some lays, t => lays.length = n ∧ (∀ l (hl : l < lays.length), StageAt t l lays[l]) ∧
      t.pc = pcOf 611 ∧ t.getReg .x5 = 0 ∧ Frame t0 t (layW n)

/-- Cycle bound of one layer. -/
def layCyc : Nat := 22 + ((2 ^ 20) * 144 + 2) + (140 + (treeCyc + 7))

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- End of a layer (instructions 604 .. 610): root → `EB+32`, next layer. -/
theorem layer_tail (lay : Nat) (hlay : lay < 7) (t : MachineState) (tpc : t.pc = pcOf 604)
    (t8 : t.getReg .x8 = BitVec.ofNat 64 lay) (t18 : t.getReg .x18 = BitVec.ofNat 64 (0x900 + 760 * lay))
    (t19 : t.getReg .x19 = BitVec.ofNat 64 0x34100) :
    ∃ t', Steps image t 7 7 t' ∧
      (1 ≤ lay → t'.pc = pcOf 205 ∧ t'.getReg .x8 = BitVec.ofNat 64 (lay - 1) ∧
        t'.getReg .x18 = BitVec.ofNat 64 (0x900 + 760 * (lay - 1))) ∧
      (lay = 0 → t'.pc = pcOf 611) ∧
      t'.readWords (BitVec.ofNat 64 0x120) 2 = t.readWords (BitVec.ofNat 64 0x34100) 2 ∧
      RegsEq t t' [.x1, .x2, .x8, .x18] ∧ Frame t t' (fun a => a = 0x120 ∨ a = 0x128) := by
  have hs := symRun_sound blk604 codeAt_604 t tpc (by
    simp only [blk604.res, rv_simp]; bvsimp [t19, accessValid_ofNat]; norm_num)
  set t' := blk604.res.toState t with ht'
  refine ⟨t', hs, ?_, ?_, ?_, ?_, ?_⟩
  · intro h1
    refine ⟨?_, ?_, ?_⟩
    · simp only [ht', blk604.res, rv_simp, t8, CmpOp.eval]
      rw [ofNat_sub_ofNat lay 1 h1 (by omega), slt_zero_ofNat _ (by omega), if_pos (by simp; omega)]
    · simp only [ht', blk604.res, rv_simp, t8]; bvsimp []
    · simp only [ht', blk604.res, rv_simp, t18]; bvsimp []; exact ofNat_congr (by omega)
  · intro h0; subst h0
    simp only [ht', blk604.res, rv_simp, t8, CmpOp.eval]
    rfl
  · rw [readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht', blk604.res, rv_simp, t19]; bvsimp []; simp
  · intro r hr; rw [ht', Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  · apply frame_toState; intro x hx hW
    simp only [blk604.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem height_bounds (lay : Nat) : 4 ≤ height lay ∧ height lay ≤ 5 := by
  rw [height_eq]; split <;> omega

/-- **The layers** `n-1 .. 0`. -/
theorem layers_sim (S : List Byte) (hS : S.length = 32) (idx : Nat) (hidx : idx < 2 ^ 34) :
    ∀ n, n ≤ 7 → ∀ (M : Val) (t : MachineState),
      (n = 0 → t.pc = pcOf 611 ∧ t.getReg .x5 = 0) →
      (∀ lay, n = lay + 1 → LayHead S idx lay M t) →
      Sim image t (n * layCyc) (signLayers S idx n M) (LaysPost t n) := by
  intro n
  induction n with
  | zero =>
    intro _ M t h0 _
    obtain ⟨hpc, h5⟩ := h0 rfl
    exact Sim.pure ⟨rfl, fun l hl => absurd hl (by simp), hpc, h5, Frame.refl _ _⟩
  | succ n ih =>
    intro hn M t _ hhead
    have hh := hhead n rfl
    have hl : n < 7 := by omega
    have hhb := height_bounds n
    obtain ⟨k, c0, t4, hs4, hc4, pc4, x46, x49, x413, x430, emem, r4, f4⟩ := layer_header S idx n M t hh
    set e := (route idx n).1 with he
    set tau := (route idx n).2 with htau
    have he32 : e < 2 ^ height n := Nat.mod_lt _ (Nat.two_pow_pos _)
    have htau30 := emem.htau
    rw [signLayers_succ, show cMax = 2 ^ 20 - 1 + 1 from rfl]
    have henc := encLoop_sim n tau e M t4 emem (2 ^ 20 - 1) 0 t4 (by norm_num)
      ⟨pc4, x46, by norm_num, RegsEq.refl _ _, Frame.refl _ _⟩
    have hW : c0 + ((2 ^ 20 - 1 + 1) * 144 + 2 + (140 + (treeCyc + (7 + (n * layCyc + 0))))) ≤
        (n + 1) * layCyc := by
      have hL : 22 + ((2 ^ 20) * 144 + 2) + (140 + (treeCyc + 7)) = layCyc := rfl
      rw [Nat.add_mul n 1 layCyc, Nat.one_mul]; omega
    refine (Sim.steps hs4 (Sim.bind henc (fun r t5 h5 => ?_))).mono hW (fun _ _ h => h)
    rcases r with _ | ⟨c, x⟩
    · exact (Sim.pure (Q := LaysPost t (n + 1)) (a := none) (s := t5) h5).mono (by omega)
        (fun _ _ h => h)
    · obtain ⟨pc5, x56, hc, ⟨d0, d1, hd0, hd1, hx, hsum, x51, x52⟩, r5, f5⟩ := h5
      subst hx
      have rt5 : RegsEq t t5 ([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) := r4.trans r5
      have ft5 : Frame t t5 (fun a => (a = 0x100 ∨ a = 0x108 ∨ a = 0x138) ∨ encW a) := f4.trans f5
      have st5 : Statics S t5 := hh.st.frame ft5 (by
        intro a ha; simp only [staticA] at ha; simp only [encW]; omega)
      obtain ⟨tt, hs6, tctx, pc6, x620, cnt6, r6, f6⟩ := enc_ok S n tau (height n) e c d0 d1 hl htau30
        ⟨by omega, hhb.2⟩ he32 hc hd0 hd1 t5 pc5 x51 x52 (by rw [rt5.get .x5, hh.x5]) x56
        (by rw [rt5.get .x8, hh.x8]) (by rw [r5.get .x9, x49]) (by rw [r5.get .x13, x413])
        (by rw [rt5.get .x18, hh.x18]) (by rw [r5.get .x30, x430]) st5
      refine Sim.steps hs6 (Sim.bind (tree_sim S hS _ ⟨n, tau, height n, e, 0x900 + 760 * n⟩ tt tctx
        (show 1 ≤ height n by omega) pc6 x620) (fun tr t7 h7 => ?_))
      obtain ⟨pc7, hr1, hroot, hv1, hvv, hvs, hp1, hpv, hps, r7, f7⟩ := h7
      have rt7 : RegsEq t t7 (([.x3, .x6, .x9, .x13, .x28, .x29, .x30, .x31] ++ encRegs) ++
          [.x3, .x14, .x17, .x19, .x20, .x29] ++ treeRegs) := (rt5.trans r6).trans r7
      obtain ⟨t8, hs8, hnext, hlast, heb, r8, f8⟩ := layer_tail n hl t7 pc7
        (by rw [rt7.get .x8, hh.x8]) (by rw [rt7.get .x18, hh.x18])
        (by rw [r7.get .x19, tctx.x19])
      have rt8 : RegsEq t t8 _ := rt7.trans r8
      have ft8' := ((ft5.trans f6).trans f7).trans f8
      have ft8 : Frame t t8 (layW (n + 1)) := ft8'.mono (by
        intro a ha
        simp only [encW, treeW, leavesW, tlevW] at ha
        simp only [layW]; omega)
      have st8 : Statics S t8 := hh.st.frame ft8' (by
        intro a ha h
        simp only [staticA] at ha; simp only [encW, treeW, leavesW, tlevW] at h; omega)
      -- the layers below
      have hroot16 : tr.1.length = 16 := hr1
      have hih := ih (by omega) tr.1 t8
        (fun h0 => ⟨hlast h0, by rw [rt8.get .x5, hh.x5]⟩)
        (fun lay' hlay' => ⟨by omega, hidx, hroot16, (hnext (by omega)).1, by rw [rt8.get .x5, hh.x5],
          by rw [rt8.get .x7, hh.x7], by rw [(hnext (by omega)).2.1]; exact ofNat_congr (by omega),
          by rw [(hnext (by omega)).2.2]; exact ofNat_congr (by omega), by rw [rt8.get .x22, hh.x22],
          by rw [heb, hroot 0 (by simp)]; simp, st8⟩)
      refine Sim.steps hs8 (Sim.bind (W₂ := 0) hih (fun r2 t9 h9 => ?_))
      rcases r2 with _ | rest
      · exact Sim.pure h9
      · obtain ⟨hlen, hstages, pc9, x95, f9⟩ := h9
        refine Sim.pure ⟨by simp [hlen], ?_, pc9, x95, ?_⟩
        · intro l hl'
          simp only [List.length_append, List.length_singleton] at hl'
          by_cases hln : l < rest.length
          · rw [List.getElem_append_left hln]; exact hstages l hln
          · have : l = n := by omega
            subst this
            rw [List.getElem_append_right (by omega)]
            simp only [hlen, Nat.sub_self, List.getElem_singleton]
            have hst7 : StageAt t7 l (c, tr.2.1, tr.2.2) := by
              refine ⟨?_, hc, hv1, hvv, hvs, hp1, hpv, hps⟩
              rw [f7.getMem (by omega) (by simp only [treeW, leavesW, tlevW]; omega), cnt6]
            exact (hst7.frame (f8.trans f9) hl (by
              intro a h1 h2 h; rcases h with h | h
              · omega
              · simp only [layW] at h; omega))
        · exact (ft8.trans f9).mono (by
            intro a ha; simp only [layW] at ha ⊢; omega)

end SigGolfCandidate.Sign
