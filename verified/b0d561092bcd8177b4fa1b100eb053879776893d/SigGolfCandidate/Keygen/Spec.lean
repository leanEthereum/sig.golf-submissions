import SigGolfCandidate.Keygen.Blocks
import SigGolfCandidate.Keygen.State

/-!
# Block specifications of `keygen`

One lemma per symbolic block: steps / cycles, next pc, the registers and doublewords it writes,
and a frame for all other doublewords.
-/

namespace SigGolfCandidate.Keygen
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- Normalization of symbolic-block results. -/
macro "kgn" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp only [rv_simp, ofNat_add_ofNat, ofNat_shl', ofNat_shr', ofNat_eq_iff,
      BitVec.toNat_ofNat, accessValid_iff, MEMORY_BYTES, ne_eq, bne_iff_ne, decide_eq_true_eq,
      ↓reduceIte, Nat.reduceDiv, Nat.reduceMod, Nat.reduceEqDiff, Nat.reduceAdd, Nat.reduceMul,
      Nat.reducePow, ofNat_shl,
      $ts',*])

/-- Frame of a block for doublewords not written. -/
abbrev Frame (s t : MachineState) (keys : List Nat) : Prop :=
  ∀ A < 2 ^ 64, A ∉ keys → t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)

theorem ofNat_and1 (i : Nat) : BitVec.ofNat 64 i &&& 1#64 = BitVec.ofNat 64 (i % 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show 1 < 2 ^ 64 by norm_num), Nat.and_one_is_mod]
  omega

/-- `tb_chain_loop` head: even chains query the paired secrets, odd chains skip the query. -/
theorem spec_32 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 32)) (i : Nat)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 i) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if i % 2 = 0 then BitVec.ofNat 64 (0x1000 + 4 * 34) else BitVec.ofNat 64 (0x1000 + 4 * 40)) ∧
      (∀ r, r ≠ .x3 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_32.res.obligs s := by simp only [blk_32.res, rv_simp]
  refine ⟨_, symRun_sound blk_32 codeAt_32 s hpc hobl, ?_, ?_, ?_⟩
  · kgn [blk_32.res, h21, ofNat_and1]
    split_ifs <;> first | rfl | (exfalso; omega)
  · intro r h1; cases r <;> simp_all [blk_32.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_32.res]

/-- Paired PRF query setup: `PB+4 = i / 2`, `a0 = PB`, `a1 = 64`, `a2 = EO`. -/
theorem spec_34 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 34)) (k : Nat)
    (hk : 2 * k < 2 ^ 32) (h21 : s.getReg .x21 = BitVec.ofNat 64 (2 * k))
    (h1696 : (s.getMem (BitVec.ofNat 64 1696)).toNat % 2 ^ 32 = 1) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 39) ∧
      t.getReg .x10 = BitVec.ofNat 64 1696 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 320 ∧
      (∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 1696) = BitVec.ofNat 64 (1 + 2 ^ 32 * k) ∧
      Frame s t [1696] := by
  have hobl : blk_34.res.obligs s := by simp only [blk_34.res, rv_simp]
  refine ⟨_, symRun_sound blk_34 codeAt_34 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_34.res]
  · kgn [blk_34.res]
  · kgn [blk_34.res]
  · kgn [blk_34.res]
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_34.res, rv_simp] <;> rfl
  · kgn [blk_34.res, h21]
    rw [ofNat_shr _ _ (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [rw32_one_toNat, h1696, truncate32_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · intro A hA hne
    kgn [blk_34.res]
    simp at hne
    rw [if_neg (by omega)]

/-- The secret of chain `j` (low / high half of the paired answer at `EO`) → `CB+48`;
`a0 = CB`, `a2 = CB+48`, `s7 = 0`. -/
theorem spec_40 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 40)) (j : Nat)
    (h21 : s.getReg .x21 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 49) ∧
      t.getReg .x10 = BitVec.ofNat 64 192 ∧ t.getReg .x12 = BitVec.ofNat 64 240 ∧
      t.getReg .x23 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x10 → r ≠ .x12 → r ≠ .x23 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 240) = s.getMem (BitVec.ofNat 64 (320 + 16 * (j % 2))) ∧
      t.getMem (BitVec.ofNat 64 248) = s.getMem (BitVec.ofNat 64 (328 + 16 * (j % 2))) ∧
      Frame s t [240, 248] := by
  have hobl : blk_40.res.obligs s := by
    kgn [blk_40.res, h21, ofNat_and1]
    omega
  refine ⟨_, symRun_sound blk_40 codeAt_40 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_40.res]
  · kgn [blk_40.res]
  · kgn [blk_40.res]
  · kgn [blk_40.res]
  · intro r h1 h2 h3 h4 h5 h6; cases r <;> simp_all [blk_40.res, rv_simp] <;> rfl
  · kgn [blk_40.res, h21, ofNat_and1]
    congr 2; omega
  · kgn [blk_40.res, h21, ofNat_and1]
    congr 2; omega
  · intro A hA hne
    kgn [blk_40.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

theorem spec_0 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 0))
    (h1696 : s.getMem (BitVec.ofNat 64 1696) = 0) (h192 : s.getMem (BitVec.ofNat 64 192) = 0) :
    ∃ t, Steps image s 25 25 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 25) ∧
      t.getReg .x8 = BitVec.ofNat 64 0 ∧ t.getReg .x30 = BitVec.ofNat 64 0 ∧
      t.getReg .x9 = BitVec.ofNat 64 11 ∧ t.getReg .x19 = BitVec.ofNat 64 0x4B20 ∧
      t.getReg .x17 = BitVec.ofNat 64 2048 ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      t.getReg .x5 = s.getReg .x5 ∧
      t.getMem (BitVec.ofNat 64 1728) = s.getMem (BitVec.ofNat 64 128) ∧
      t.getMem (BitVec.ofNat 64 1736) = s.getMem (BitVec.ofNat 64 136) ∧
      t.getMem (BitVec.ofNat 64 1744) = s.getMem (BitVec.ofNat 64 144) ∧
      t.getMem (BitVec.ofNat 64 1752) = s.getMem (BitVec.ofNat 64 152) ∧
      (t.getMem (BitVec.ofNat 64 1696)).toNat % 2 ^ 32 = 1 ∧
      (t.getMem (BitVec.ofNat 64 192)).toNat % 2 ^ 32 = 257 ∧
      t.getMem (BitVec.ofNat 64 832) = BitVec.ofNat 64 513 ∧
      t.getMem (BitVec.ofNat 64 224) = 0 ∧ t.getMem (BitVec.ofNat 64 232) = 0 ∧
      Frame s t [1728, 1736, 1744, 1752, 1696, 192, 832, 224, 232] := by
  have hobl : blk_0.res.obligs s := by simp only [blk_0.res, rv_simp]
  refine ⟨_, symRun_sound blk_0 codeAt_0 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 12 (· kgn [blk_0.res] <;> rfl)
  · kgn [blk_0.res]; rw [rw32_zero_low']; rfl
  · kgn [blk_0.res]; rw [rw32_zero_low']; rfl
  · kgn [blk_0.res]
  · kgn [blk_0.res]
  · kgn [blk_0.res]
  · intro A hA hne
    kgn [blk_0.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem spec_25 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 25)) (e : Nat)
    (he : e < 2 ^ 32) (h20 : s.getReg .x20 = BitVec.ofNat 64 e)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 0) :
    ∃ t, Steps image s 7 7 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 32) ∧
      t.getReg .x21 = BitVec.ofNat 64 0 ∧ t.getReg .x24 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x3 → r ≠ .x21 → r ≠ .x24 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 1704) = BitVec.ofNat 64 (2 ^ 32 * e) ∧
      t.getMem (BitVec.ofNat 64 200) = BitVec.ofNat 64 (2 ^ 32 * e) ∧
      t.getMem (BitVec.ofNat 64 840) = BitVec.ofNat 64 (2 ^ 32 * e) ∧
      Frame s t [1704, 200, 840] := by
  have hobl : blk_25.res.obligs s := by simp only [blk_25.res, rv_simp]
  refine ⟨_, symRun_sound blk_25 codeAt_25 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 3 (· kgn [blk_25.res] <;> rfl)
  · intro r h1 h2 h3; cases r <;> simp_all [blk_25.res, rv_simp] <;> rfl
  iterate 3 (· kgn [blk_25.res, h20, h30, BitVec.or_zero]; rw [Nat.mul_comm])
  · intro A hA hne
    kgn [blk_25.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem split_p_lo (p : Nat) (hp : p < 2 ^ 27) :
    (BitVec.ofNat 64 p >>> ((3#64).toNat % 64)) <<< ((8#64).toNat % 64) = BitVec.ofNat 64 (p / 8 * 2 ^ 8) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (a := p) (by omega)]

theorem split_p_hi (p : Nat) (hp : p < 2 ^ 27) : BitVec.ofNat 64 p &&& 7#64 = BitVec.ofNat 64 (p % 8) := by
  apply BitVec.eq_of_toNat_eq
  have h7 : (7#64 : Word).toNat = 2 ^ 3 - 1 := rfl
  rw [BitVec.toNat_and, h7, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := p) (by omega),
    Nat.and_two_pow_sub_one_eq_mod]
  omega

/-- A chain step (`tb_step_loop`): split tweak position `p` (byte 4 = `p mod 8`, byte 5 = `p div 8`)
into `CB+4`, `a0 = CB`. -/
theorem spec_49 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 49)) (m p : Nat)
    (hp : p < 2 ^ 27) (h23 : s.getReg .x23 = BitVec.ofNat 64 m) (h24 : s.getReg .x24 = BitVec.ofNat 64 p)
    (h192 : (s.getMem (BitVec.ofNat 64 192)).toNat % 2 ^ 32 = 257) :
    ∃ t, Steps image s 7 7 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 56) ∧
      t.getReg .x23 = BitVec.ofNat 64 (m + 1) ∧ t.getReg .x10 = BitVec.ofNat 64 192 ∧
      (∀ r, r ≠ .x23 → r ≠ .x10 → r ≠ .x3 → r ≠ .x29 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 192) = BitVec.ofNat 64 (257 + 2 ^ 32 * (p % 8 + 256 * (p / 8))) ∧
      Frame s t [192] := by
  have hobl : blk_49.res.obligs s := by simp only [blk_49.res, rv_simp]
  refine ⟨_, symRun_sound blk_49 codeAt_49 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (kgn [blk_49.res]; done)
  · kgn [blk_49.res, h23]
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_49.res, rv_simp] <;> rfl
  · simp only [blk_49.res, rv_simp, h24, ↓reduceIte]
    rw [split_p_lo p hp, split_p_hi p hp, ofNat_or_add (p % 8) (p / 8) 8 (by omega)]
    apply BitVec.eq_of_toNat_eq
    rw [show (4 / 4 : Nat) = 1 from rfl, rw32_one_toNat, h192, truncate32_toNat, BitVec.toNat_ofNat,
      BitVec.toNat_ofNat]
    have e1 : (p / 8 * 2 ^ 8 + p % 8) % 2 ^ 64 % 2 ^ 32 = p % 8 + 256 * (p / 8) := by omega
    rw [e1, Nat.mod_eq_of_lt (a := 257 + 2 ^ 32 * (p % 8 + 256 * (p / 8))) (by omega)]
  · intro A hA hne
    kgn [blk_49.res]
    simp at hne
    rw [if_neg (by omega)]

theorem spec_57 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 57)) (m p : Nat)
    (hm : m < 2 ^ 32) (h23 : s.getReg .x23 = BitVec.ofNat 64 m) (h24 : s.getReg .x24 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if m = 7 then BitVec.ofNat 64 (0x1000 + 4 * 60) else BitVec.ofNat 64 (0x1000 + 4 * 49)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (p + 1) ∧
      (∀ r, r ≠ .x24 → r ≠ .x3 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_57.res.obligs s := by simp only [blk_57.res, rv_simp]
  refine ⟨_, symRun_sound blk_57 codeAt_57 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_57.res, h23]
    by_cases h : m = 7
    · simp [h]
    · rw [if_pos (by omega), if_neg h]
  · kgn [blk_57.res, h24]
  · intro r h1 h2; cases r <;> simp_all [blk_57.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_57.res]

theorem spec_60 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 60)) (i p : Nat)
    (hi : i < 42) (h21 : s.getReg .x21 = BitVec.ofNat 64 i) (h24 : s.getReg .x24 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 9 9 t ∧
      t.pc = (if i + 1 = 42 then BitVec.ofNat 64 (0x1000 + 4 * 69) else BitVec.ofNat 64 (0x1000 + 4 * 32)) ∧
      t.getReg .x21 = BitVec.ofNat 64 (i + 1) ∧ t.getReg .x24 = BitVec.ofNat 64 (p + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x21 → r ≠ .x24 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 (864 + 16 * i)) = s.getMem (BitVec.ofNat 64 240) ∧
      t.getMem (BitVec.ofNat 64 (864 + 16 * i + 8)) = s.getMem (BitVec.ofNat 64 248) ∧
      Frame s t [864 + 16 * i, 864 + 16 * i + 8] := by
  have hobl : blk_60.res.obligs s := by
    kgn [blk_60.res, h21]; omega
  refine ⟨_, symRun_sound blk_60 codeAt_60 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_60.res, h21]
    by_cases h : i = 41 <;> simp [h] <;> omega
  · kgn [blk_60.res, h21]
  · kgn [blk_60.res, h24]
  · intro r h1 h2 h3 h4 h5; cases r <;> simp_all [blk_60.res, rv_simp] <;> rfl
  · kgn [blk_60.res, h21]; rw [if_neg (by omega), if_pos (by omega)]
  · kgn [blk_60.res, h21]; rw [if_pos (by omega)]
  · intro A hA hne
    kgn [blk_60.res, h21]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

theorem spec_69 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 69)) (e : Nat)
    (he : e < 2048) (h20 : s.getReg .x20 = BitVec.ofNat 64 e) (h19 : s.getReg .x19 = BitVec.ofNat 64 0x4B20) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 73) ∧
      t.getReg .x10 = BitVec.ofNat 64 832 ∧ t.getReg .x11 = BitVec.ofNat 64 704 ∧
      t.getReg .x12 = BitVec.ofNat 64 (0x4B20 + 16 * e) ∧
      (∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      Frame s t [] := by
  have hobl : blk_69.res.obligs s := by simp only [blk_69.res, rv_simp]
  refine ⟨_, symRun_sound blk_69 codeAt_69 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_69.res]
  · kgn [blk_69.res]
  · kgn [blk_69.res]
  · kgn [blk_69.res, h19, h20]; omega
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_69.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_69.res]

theorem spec_74 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 74)) (e : Nat)
    (he : e < 2048) (h20 : s.getReg .x20 = BitVec.ofNat 64 e) (h17 : s.getReg .x17 = BitVec.ofNat 64 2048) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if e + 1 = 2048 then BitVec.ofNat 64 (0x1000 + 4 * 76) else BitVec.ofNat 64 (0x1000 + 4 * 25)) ∧
      t.getReg .x20 = BitVec.ofNat 64 (e + 1) ∧
      (∀ r, r ≠ .x20 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_74.res.obligs s := by simp only [blk_74.res, rv_simp]
  refine ⟨_, symRun_sound blk_74 codeAt_74 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_74.res, h20, h17]
    by_cases h : e = 2047 <;> simp [h] <;> omega
  · kgn [blk_74.res, h20]
  · intro r h1; cases r <;> simp_all [blk_74.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_74.res]

theorem spec_76 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 76)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 77) ∧
      t.getReg .x15 = BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x15 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_76.res.obligs s := by simp only [blk_76.res, rv_simp]
  refine ⟨_, symRun_sound blk_76 codeAt_76 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_76.res]
  · kgn [blk_76.res]
  · intro r h1; cases r <;> simp_all [blk_76.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_76.res]

/-- Level head (`tb_level_loop`): node tweak word0, `NB+8`, destination base `s9 = s3 + 16 a7`,
`a7 /= 2`, `a6 = 0`. -/
theorem spec_77 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 77)) (c B : Nat)
    (hc : c < 2 ^ 32) (hB : B < 2 ^ 32)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 0) (h30 : s.getReg .x30 = BitVec.ofNat 64 0)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c) (h19 : s.getReg .x19 = BitVec.ofNat 64 B) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 85) ∧
      t.getReg .x17 = BitVec.ofNat 64 (c / 2) ∧ t.getReg .x16 = BitVec.ofNat 64 0 ∧
      t.getReg .x25 = BitVec.ofNat 64 (B + 16 * c) ∧
      (∀ r, r ≠ .x3 → r ≠ .x29 → r ≠ .x17 → r ≠ .x16 → r ≠ .x25 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 448) = BitVec.ofNat 64 769 ∧
      (t.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = 0 ∧
      Frame s t [448, 456] := by
  have hobl : blk_77.res.obligs s := by simp only [blk_77.res, rv_simp]
  refine ⟨_, symRun_sound blk_77 codeAt_77 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_77.res]
  · kgn [blk_77.res, h17]; rw [ofNat_shr _ _ (by omega)]; rfl
  · kgn [blk_77.res]
  · kgn [blk_77.res, h17, h19]; congr 1; omega
  · intro r h1 h2 h3 h4 h5; cases r <;> simp_all [blk_77.res, rv_simp] <;> rfl
  · kgn [blk_77.res, h8]; rfl
  · kgn [blk_77.res, h30]; rw [rw32_zero_low']; rfl
  · intro A hA hne
    kgn [blk_77.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

/-- Node inputs (`tb_node_loop`): `NB+12 = j`, children `s3 + 32 j .. + 32` → `NB+32 ..`,
`a2 = s9 + 16 j`. -/
theorem spec_85 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 85)) (j c B D : Nat)
    (hj : j < 2 ^ 11) (hc : c ≤ 2 ^ 11) (hB : B + 32 * j + 32 ≤ 2 ^ 24) (hB8 : B % 8 = 0) (hB0 : 512 ≤ B)
    (hD : D + 16 * j + 32 ≤ 2 ^ 24)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 j) (h17 : s.getReg .x17 = BitVec.ofNat 64 c)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 B) (h25 : s.getReg .x25 = BitVec.ofNat 64 D)
    (h456 : (s.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = 0) :
    ∃ t, Steps image s 16 16 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 101) ∧
      t.getReg .x10 = BitVec.ofNat 64 448 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (D + 16 * j) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 456) = BitVec.ofNat 64 (2 ^ 32 * (c + j)) ∧
      t.getMem (BitVec.ofNat 64 480) = s.getMem (BitVec.ofNat 64 (B + 32 * j)) ∧
      t.getMem (BitVec.ofNat 64 488) = s.getMem (BitVec.ofNat 64 (B + 32 * j + 8)) ∧
      t.getMem (BitVec.ofNat 64 496) = s.getMem (BitVec.ofNat 64 (B + 32 * j + 16)) ∧
      t.getMem (BitVec.ofNat 64 504) = s.getMem (BitVec.ofNat 64 (B + 32 * j + 24)) ∧
      Frame s t [456, 480, 488, 496, 504] := by
  have hobl : blk_85.res.obligs s := by
    kgn [blk_85.res, h16, h19]; omega
  refine ⟨_, symRun_sound blk_85 codeAt_85 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_85.res]
  · kgn [blk_85.res]
  · kgn [blk_85.res]
  · kgn [blk_85.res, h16, h25]; omega
  · intro r h1 h2 h3 h4 h5 h6; cases r <;> simp_all [blk_85.res, rv_simp] <;> rfl
  · kgn [blk_85.res, h16, h17]
    apply BitVec.eq_of_toNat_eq
    rw [rw32_one_toNat', truncate32_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [show (4294967296 : Nat) = 2 ^ 32 by norm_num, h456]
    omega
  iterate 4 (· kgn [blk_85.res, h16, h19]; congr 2; ring)
  · intro A hA hne
    kgn [blk_85.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem spec_102 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 102)) (j c : Nat)
    (hj : j + 1 < 2 ^ 64) (hc : c < 2 ^ 64) (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if j + 1 = c then BitVec.ofNat 64 (0x1000 + 4 * 104) else BitVec.ofNat 64 (0x1000 + 4 * 85)) ∧
      t.getReg .x16 = BitVec.ofNat 64 (j + 1) ∧
      (∀ r, r ≠ .x16 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_102.res.obligs s := by simp only [blk_102.res, rv_simp]
  refine ⟨_, symRun_sound blk_102 codeAt_102 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_102.res, h16, h17]
    by_cases h : j + 1 = c
    · simp [h]
    · rw [if_pos (by omega), if_neg h]
  · kgn [blk_102.res, h16]
  · intro r h1; cases r <;> simp_all [blk_102.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_102.res]

/-- Level tail: `s3 = s9`, `a5 += 1`, loop while `a5 ≤ 11`. -/
theorem spec_104 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 104)) (lam : Nat)
    (hl : lam < 12) (h15 : s.getReg .x15 = BitVec.ofNat 64 lam) (h9 : s.getReg .x9 = BitVec.ofNat 64 11) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if lam + 1 ≤ 11 then BitVec.ofNat 64 (0x1000 + 4 * 77) else BitVec.ofNat 64 (0x1000 + 4 * 107)) ∧
      t.getReg .x15 = BitVec.ofNat 64 (lam + 1) ∧ t.getReg .x19 = s.getReg .x25 ∧
      (∀ r, r ≠ .x15 → r ≠ .x19 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_104.res.obligs s := by simp only [blk_104.res, rv_simp]
  refine ⟨_, symRun_sound blk_104 codeAt_104 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_104.res, h15, h9]
    rw [ofNat_slt 11 (lam + 1) (by omega) (by omega)]
    by_cases h : lam + 1 ≤ 11
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · kgn [blk_104.res, h15]
  · kgn [blk_104.res]
  · intro r h1 h2; cases r <;> simp_all [blk_104.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_104.res]

/-- Root → public key (`160`, `168`), then zero the 32 bytes at `s3`. -/
theorem spec_107 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 107))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 0x14B00) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 115) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 160) = s.getMem (BitVec.ofNat 64 0x14B00) ∧
      t.getMem (BitVec.ofNat 64 168) = s.getMem (BitVec.ofNat 64 0x14B08) ∧
      t.getMem (BitVec.ofNat 64 0x14B00) = 0 ∧ t.getMem (BitVec.ofNat 64 0x14B08) = 0 ∧
      t.getMem (BitVec.ofNat 64 0x14B10) = 0 ∧ t.getMem (BitVec.ofNat 64 0x14B18) = 0 ∧
      Frame s t [160, 168, 0x14B00, 0x14B08, 0x14B10, 0x14B18] := by
  have hobl : blk_107.res.obligs s := by kgn [blk_107.res, h19]; norm_num
  refine ⟨_, symRun_sound blk_107 codeAt_107 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_107.res]
  · intro r h1 h2; cases r <;> simp_all [blk_107.res, rv_simp] <;> rfl
  iterate 6 (· kgn [blk_107.res, h19] <;> rfl)
  · intro A hA hne
    kgn [blk_107.res, h19]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

theorem spec_115 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 115)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 118) ∧
      t.getReg .x20 = BitVec.ofNat 64 0x4B20 ∧ t.getReg .x15 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x20 → r ≠ .x15 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_115.res.obligs s := by simp only [blk_115.res, rv_simp]
  refine ⟨_, symRun_sound blk_115 codeAt_115 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_115.res]
  · kgn [blk_115.res]
  · kgn [blk_115.res]
  · intro r h1 h2; cases r <;> simp_all [blk_115.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_115.res]

/-- Mask level head: `a7 = 2^(11 - l)`, `a6 = 0`. -/
theorem spec_118 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 118)) (l : Nat)
    (hl : l < 11) (h15 : s.getReg .x15 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 123) ∧
      t.getReg .x17 = BitVec.ofNat 64 (2 ^ (11 - l)) ∧ t.getReg .x16 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x3 → r ≠ .x29 → r ≠ .x17 → r ≠ .x16 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_118.res.obligs s := by simp only [blk_118.res, rv_simp]
  refine ⟨_, symRun_sound blk_118 codeAt_118 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_118.res]
  · kgn [blk_118.res, h15]
    interval_cases l <;> rfl
  · kgn [blk_118.res]
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_118.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_118.res]

/-- Mask query setup: `PB = tw_mask(l, j)`, `a0 = PB`, `a1 = 64`, `a2 = EO`. -/
theorem spec_123 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 123)) (l j : Nat)
    (hl : l < 11) (hj : j < 2 ^ 11) (h15 : s.getReg .x15 = BitVec.ofNat 64 l)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 132) ∧
      t.getReg .x10 = BitVec.ofNat 64 1696 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 320 ∧
      (∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 1696) = BitVec.ofNat 64 (3329 + 2 ^ 32 * l) ∧
      t.getMem (BitVec.ofNat 64 1704) = BitVec.ofNat 64 (2 ^ 32 * j) ∧
      Frame s t [1696, 1704] := by
  have hobl : blk_123.res.obligs s := by simp only [blk_123.res, rv_simp]
  refine ⟨_, symRun_sound blk_123 codeAt_123 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_123.res]
  · kgn [blk_123.res]
  · kgn [blk_123.res]
  · kgn [blk_123.res]
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_123.res, rv_simp] <;> rfl
  · kgn [blk_123.res, h15]
    congr 1; ring
  · kgn [blk_123.res, h16]
    congr 1; ring
  · intro A hA hne
    kgn [blk_123.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

/-- Mask the node at `s4` with the answer at `EO`, advance. -/
theorem spec_133 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 133)) (A j c : Nat)
    (hA : A + 16 < 2 ^ 24) (hA8 : A % 8 = 0) (hA0 : 336 ≤ A) (hj : j + 1 < 2 ^ 64) (hc : c < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 A) (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 11 11 t ∧
      t.pc = (if j + 1 = c then BitVec.ofNat 64 (0x1000 + 4 * 144) else BitVec.ofNat 64 (0x1000 + 4 * 123)) ∧
      t.getReg .x20 = BitVec.ofNat 64 (A + 16) ∧ t.getReg .x16 = BitVec.ofNat 64 (j + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x20 → r ≠ .x16 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) ^^^ s.getMem (BitVec.ofNat 64 320) ∧
      t.getMem (BitVec.ofNat 64 (A + 8)) = s.getMem (BitVec.ofNat 64 (A + 8)) ^^^ s.getMem (BitVec.ofNat 64 328) ∧
      Frame s t [A, A + 8] := by
  have hobl : blk_133.res.obligs s := by kgn [blk_133.res, h20]; omega
  refine ⟨_, symRun_sound blk_133 codeAt_133 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_133.res, h16, h17]
    by_cases h : j + 1 = c
    · simp [h]
    · rw [if_pos (by rw [Nat.mod_eq_of_lt (show j + 1 < 18446744073709551616 from hj),
        Nat.mod_eq_of_lt (show c < 18446744073709551616 from hc)]; exact h), if_neg h]
  · kgn [blk_133.res, h20]
  · kgn [blk_133.res, h16]
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_133.res, rv_simp] <;> rfl
  · kgn [blk_133.res, h20]
    rw [if_neg (by omega), if_pos (by omega)]
  · kgn [blk_133.res, h20]
  · intro A' hA' hne
    kgn [blk_133.res, h20]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

theorem spec_144 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 144)) (l : Nat)
    (hl : l < 11) (h15 : s.getReg .x15 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if l + 1 = 11 then BitVec.ofNat 64 (0x1000 + 4 * 147) else BitVec.ofNat 64 (0x1000 + 4 * 118)) ∧
      t.getReg .x15 = BitVec.ofNat 64 (l + 1) ∧
      (∀ r, r ≠ .x15 → r ≠ .x3 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_144.res.obligs s := by simp only [blk_144.res, rv_simp]
  refine ⟨_, symRun_sound blk_144 codeAt_144 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_144.res, h15]
    by_cases h : l = 10
    · subst h; rfl
    · rw [if_pos (by omega), if_neg h]
  · kgn [blk_144.res, h15]
  · intro r h1 h2; cases r <;> simp_all [blk_144.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_144.res]

/-- MAC input in place: `tw_mac` word0 at `CACHE-32`, `S` at `CACHE`, zeros after the region;
`a0 = CACHE-32`, `a1 = 65600`, `a2 = CACHE`. -/
theorem spec_147 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 147)) :
    ∃ t, Steps image s 24 24 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 171) ∧
      t.getReg .x10 = BitVec.ofNat 64 0x4AE0 ∧ t.getReg .x11 = BitVec.ofNat 64 65600 ∧
      t.getReg .x12 = BitVec.ofNat 64 0x4B00 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x29 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 0x4AE0) = BitVec.ofNat 64 3585 ∧
      t.getMem (BitVec.ofNat 64 0x4B00) = s.getMem (BitVec.ofNat 64 128) ∧
      t.getMem (BitVec.ofNat 64 0x4B08) = s.getMem (BitVec.ofNat 64 136) ∧
      t.getMem (BitVec.ofNat 64 0x4B10) = s.getMem (BitVec.ofNat 64 144) ∧
      t.getMem (BitVec.ofNat 64 0x4B18) = s.getMem (BitVec.ofNat 64 152) ∧
      t.getMem (BitVec.ofNat 64 0x14B00) = 0 ∧ t.getMem (BitVec.ofNat 64 0x14B08) = 0 ∧
      t.getMem (BitVec.ofNat 64 0x14B10) = 0 ∧ t.getMem (BitVec.ofNat 64 0x14B18) = 0 ∧
      Frame s t [0x4AE0, 0x4B00, 0x4B08, 0x4B10, 0x4B18, 0x14B00, 0x14B08, 0x14B10, 0x14B18] := by
  have hobl : blk_147.res.obligs s := by simp only [blk_147.res, rv_simp]
  refine ⟨_, symRun_sound blk_147 codeAt_147 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  iterate 4 (· kgn [blk_147.res])
  · intro r h1 h2 h3 h4 h5 h6; cases r <;> simp_all [blk_147.res, rv_simp] <;> rfl
  iterate 9 (· kgn [blk_147.res] <;> rfl)
  · intro A hA hne
    kgn [blk_147.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem spec_172 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 172)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 174) ∧
      t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 0 ∧ Frame s t [] := by
  have hobl : blk_172.res.obligs s := by simp only [blk_172.res, rv_simp]
  refine ⟨_, symRun_sound blk_172 codeAt_172 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_172.res]
  · kgn [blk_172.res]
  · kgn [blk_172.res]
  · intro A _ _; kgn [blk_172.res]

end SigGolfCandidate.Keygen
