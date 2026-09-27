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

theorem spec_30 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 30)) (i : Nat)
    (hi : i < 2 ^ 32) (h21 : s.getReg .x21 = BitVec.ofNat 64 i)
    (h1696 : (s.getMem (BitVec.ofNat 64 1696)).toNat % 2 ^ 32 = 1) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 34) ∧
      t.getReg .x10 = BitVec.ofNat 64 1696 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 224 ∧
      (∀ r, r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 1696) = BitVec.ofNat 64 (1 + 2 ^ 32 * i) ∧
      Frame s t [1696] := by
  have hobl : blk_30.res.obligs s := by simp only [blk_30.res, rv_simp]
  refine ⟨_, symRun_sound blk_30 codeAt_30 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_30.res]
  · kgn [blk_30.res]
  · kgn [blk_30.res]
  · kgn [blk_30.res]
  · intro r h1 h2 h3; cases r <;> simp_all [blk_30.res, rv_simp] <;> rfl
  · kgn [blk_30.res, h21]
    apply BitVec.eq_of_toNat_eq
    rw [rw32_one_toNat, h1696, truncate32_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · intro A hA hne
    kgn [blk_30.res]
    simp at hne
    rw [if_neg (by omega)]

theorem spec_0 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 0))
    (h1696 : s.getMem (BitVec.ofNat 64 1696) = 0) (h192 : s.getMem (BitVec.ofNat 64 192) = 0) :
    ∃ t, Steps image s 23 23 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 23) ∧
      t.getReg .x8 = BitVec.ofNat 64 0 ∧ t.getReg .x30 = BitVec.ofNat 64 0 ∧
      t.getReg .x9 = BitVec.ofNat 64 5 ∧ t.getReg .x19 = BitVec.ofNat 64 0x34100 ∧
      t.getReg .x17 = BitVec.ofNat 64 32 ∧ t.getReg .x20 = BitVec.ofNat 64 0 ∧
      t.getReg .x5 = s.getReg .x5 ∧
      t.getMem (BitVec.ofNat 64 1728) = s.getMem (BitVec.ofNat 64 128) ∧
      t.getMem (BitVec.ofNat 64 1736) = s.getMem (BitVec.ofNat 64 136) ∧
      t.getMem (BitVec.ofNat 64 1744) = s.getMem (BitVec.ofNat 64 144) ∧
      t.getMem (BitVec.ofNat 64 1752) = s.getMem (BitVec.ofNat 64 152) ∧
      (t.getMem (BitVec.ofNat 64 1696)).toNat % 2 ^ 32 = 1 ∧
      (t.getMem (BitVec.ofNat 64 192)).toNat % 2 ^ 32 = 257 ∧
      t.getMem (BitVec.ofNat 64 832) = BitVec.ofNat 64 513 ∧
      Frame s t [1728, 1736, 1744, 1752, 1696, 192, 832] := by
  have hobl : blk_0.res.obligs s := by simp only [blk_0.res, rv_simp]
  refine ⟨_, symRun_sound blk_0 codeAt_0 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  iterate 12 (· kgn [blk_0.res] <;> rfl)
  · kgn [blk_0.res]; rw [rw32_zero_low']; rfl
  · kgn [blk_0.res]; rw [rw32_zero_low']; rfl
  · kgn [blk_0.res]
  · intro A hA hne
    kgn [blk_0.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega)]

theorem spec_23 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 23)) (e : Nat)
    (he : e < 2 ^ 32) (h20 : s.getReg .x20 = BitVec.ofNat 64 e)
    (h30 : s.getReg .x30 = BitVec.ofNat 64 0) :
    ∃ t, Steps image s 7 7 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 30) ∧
      t.getReg .x21 = BitVec.ofNat 64 0 ∧ t.getReg .x24 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x3 → r ≠ .x21 → r ≠ .x24 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 1704) = BitVec.ofNat 64 (2 ^ 32 * e) ∧
      t.getMem (BitVec.ofNat 64 200) = BitVec.ofNat 64 (2 ^ 32 * e) ∧
      t.getMem (BitVec.ofNat 64 840) = BitVec.ofNat 64 (2 ^ 32 * e) ∧
      Frame s t [1704, 200, 840] := by
  have hobl : blk_23.res.obligs s := by simp only [blk_23.res, rv_simp]
  refine ⟨_, symRun_sound blk_23 codeAt_23 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  iterate 3 (· kgn [blk_23.res] <;> rfl)
  · intro r h1 h2 h3; cases r <;> simp_all [blk_23.res, rv_simp] <;> rfl
  iterate 3 (· kgn [blk_23.res, h20, h30, BitVec.or_zero]; rw [Nat.mul_comm])
  · intro A hA hne
    kgn [blk_23.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem spec_35 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 35)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 38) ∧
      t.getReg .x23 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x23 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 240) = 0 ∧ t.getMem (BitVec.ofNat 64 248) = 0 ∧
      Frame s t [240, 248] := by
  have hobl : blk_35.res.obligs s := by simp only [blk_35.res, rv_simp]
  refine ⟨_, symRun_sound blk_35 codeAt_35 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (kgn [blk_35.res]; done)
  · intro r h1; cases r <;> simp_all [blk_35.res, rv_simp] <;> rfl
  · intro A hA hne
    kgn [blk_35.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

theorem spec_38 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 38)) (m p : Nat)
    (hp : p < 2 ^ 32) (h23 : s.getReg .x23 = BitVec.ofNat 64 m) (h24 : s.getReg .x24 = BitVec.ofNat 64 p)
    (h192 : (s.getMem (BitVec.ofNat 64 192)).toNat % 2 ^ 32 = 257) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 42) ∧
      t.getReg .x23 = BitVec.ofNat 64 (m + 1) ∧ t.getReg .x10 = BitVec.ofNat 64 192 ∧
      t.getReg .x12 = BitVec.ofNat 64 224 ∧
      (∀ r, r ≠ .x23 → r ≠ .x10 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 192) = BitVec.ofNat 64 (257 + 2 ^ 32 * p) ∧
      Frame s t [192] := by
  have hobl : blk_38.res.obligs s := by simp only [blk_38.res, rv_simp]
  refine ⟨_, symRun_sound blk_38 codeAt_38 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (kgn [blk_38.res]; done)
  · kgn [blk_38.res, h23]
  · intro r h1 h2 h3; cases r <;> simp_all [blk_38.res, rv_simp] <;> rfl
  · kgn [blk_38.res, h24]
    apply BitVec.eq_of_toNat_eq
    rw [rw32_one_toNat, h192, truncate32_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · intro A hA hne
    kgn [blk_38.res]
    simp at hne
    rw [if_neg (by omega)]

theorem spec_43 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 43)) (m p : Nat)
    (hm : m < 2 ^ 32) (h23 : s.getReg .x23 = BitVec.ofNat 64 m) (h24 : s.getReg .x24 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 5 5 t ∧
      t.pc = (if m = 7 then BitVec.ofNat 64 (0x1000 + 4 * 48) else BitVec.ofNat 64 (0x1000 + 4 * 38)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (p + 1) ∧
      (∀ r, r ≠ .x24 → r ≠ .x3 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 240) = 0 ∧ t.getMem (BitVec.ofNat 64 248) = 0 ∧
      Frame s t [240, 248] := by
  have hobl : blk_43.res.obligs s := by simp only [blk_43.res, rv_simp]
  refine ⟨_, symRun_sound blk_43 codeAt_43 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (kgn [blk_43.res]; done)
  · kgn [blk_43.res, h23]
    by_cases h : m = 7
    · simp [h]
    · rw [if_pos (by omega), if_neg h]
  · kgn [blk_43.res, h24]
  · intro r h1 h2; cases r <;> simp_all [blk_43.res, rv_simp] <;> rfl
  · intro A hA hne
    kgn [blk_43.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

theorem spec_48 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 48)) (i p : Nat)
    (hi : i < 42) (h21 : s.getReg .x21 = BitVec.ofNat 64 i) (h24 : s.getReg .x24 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 9 9 t ∧
      t.pc = (if i + 1 = 42 then BitVec.ofNat 64 (0x1000 + 4 * 57) else BitVec.ofNat 64 (0x1000 + 4 * 30)) ∧
      t.getReg .x21 = BitVec.ofNat 64 (i + 1) ∧ t.getReg .x24 = BitVec.ofNat 64 (p + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x21 → r ≠ .x24 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 (864 + 16 * i)) = s.getMem (BitVec.ofNat 64 224) ∧
      t.getMem (BitVec.ofNat 64 (864 + 16 * i + 8)) = s.getMem (BitVec.ofNat 64 232) ∧
      Frame s t [864 + 16 * i, 864 + 16 * i + 8] := by
  have hobl : blk_48.res.obligs s := by
    kgn [blk_48.res, h21]; omega
  refine ⟨_, symRun_sound blk_48 codeAt_48 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_48.res, h21]
    by_cases h : i = 41 <;> simp [h] <;> omega
  · kgn [blk_48.res, h21]
  · kgn [blk_48.res, h24]
  · intro r h1 h2 h3 h4 h5; cases r <;> simp_all [blk_48.res, rv_simp] <;> rfl
  · kgn [blk_48.res, h21]; rw [if_neg (by omega), if_pos (by omega)]
  · kgn [blk_48.res, h21]; rw [if_pos (by omega)]
  · intro A hA hne
    kgn [blk_48.res, h21]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

theorem spec_57 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 57)) (e : Nat)
    (he : e < 32) (h20 : s.getReg .x20 = BitVec.ofNat 64 e) (h19 : s.getReg .x19 = BitVec.ofNat 64 0x34100) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 61) ∧
      t.getReg .x10 = BitVec.ofNat 64 832 ∧ t.getReg .x11 = BitVec.ofNat 64 704 ∧
      t.getReg .x12 = BitVec.ofNat 64 (0x34100 + 16 * e) ∧
      (∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      Frame s t [] := by
  have hobl : blk_57.res.obligs s := by simp only [blk_57.res, rv_simp]
  refine ⟨_, symRun_sound blk_57 codeAt_57 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_57.res]
  · kgn [blk_57.res]
  · kgn [blk_57.res]
  · kgn [blk_57.res, h19, h20]; omega
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_57.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_57.res]

theorem spec_62 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 62)) (e : Nat)
    (he : e < 32) (h20 : s.getReg .x20 = BitVec.ofNat 64 e) (h17 : s.getReg .x17 = BitVec.ofNat 64 32) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if e + 1 = 32 then BitVec.ofNat 64 (0x1000 + 4 * 64) else BitVec.ofNat 64 (0x1000 + 4 * 23)) ∧
      t.getReg .x20 = BitVec.ofNat 64 (e + 1) ∧
      (∀ r, r ≠ .x20 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_62.res.obligs s := by simp only [blk_62.res, rv_simp]
  refine ⟨_, symRun_sound blk_62 codeAt_62 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_62.res, h20, h17]
    by_cases h : e = 31 <;> simp [h] <;> omega
  · kgn [blk_62.res, h20]
  · intro r h1; cases r <;> simp_all [blk_62.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_62.res]

theorem spec_64 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 64)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 65) ∧
      t.getReg .x15 = BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x15 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_64.res.obligs s := by simp only [blk_64.res, rv_simp]
  refine ⟨_, symRun_sound blk_64 codeAt_64 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_64.res]
  · kgn [blk_64.res]
  · intro r h1; cases r <;> simp_all [blk_64.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_64.res]

theorem spec_65 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 65)) (lam c : Nat)
    (hl : lam < 2 ^ 32) (hc : c < 2 ^ 64) (h15 : s.getReg .x15 = BitVec.ofNat 64 lam)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 0) (h30 : s.getReg .x30 = BitVec.ofNat 64 0)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 73) ∧
      t.getReg .x17 = BitVec.ofNat 64 (c / 2) ∧ t.getReg .x16 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x3 → r ≠ .x29 → r ≠ .x17 → r ≠ .x16 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 448) = BitVec.ofNat 64 (769 + 2 ^ 32 * lam) ∧
      (t.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = 0 ∧
      Frame s t [448, 456] := by
  have hobl : blk_65.res.obligs s := by simp only [blk_65.res, rv_simp]
  refine ⟨_, symRun_sound blk_65 codeAt_65 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_65.res]
  · kgn [blk_65.res, h17]; rw [ofNat_shr _ _ hc]; rfl
  · kgn [blk_65.res]
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_65.res, rv_simp] <;> rfl
  · kgn [blk_65.res, h15, h8, BitVec.or_zero]
    rw [show (4294967296 : Nat) = 2 ^ 32 by norm_num, ofNat_or_add 769 lam 32 (by norm_num)]
    congr 1; omega
  · kgn [blk_65.res, h30]; rw [rw32_zero_low']; rfl
  · intro A hA hne
    kgn [blk_65.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

theorem spec_73 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 73)) (j : Nat)
    (hj : j < 16) (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 0x34100)
    (h456 : (s.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = 0) :
    ∃ t, Steps image s 15 15 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 88) ∧
      t.getReg .x10 = BitVec.ofNat 64 448 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (0x34100 + 16 * j) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 456) = BitVec.ofNat 64 (2 ^ 32 * j) ∧
      t.getMem (BitVec.ofNat 64 480) = s.getMem (BitVec.ofNat 64 (0x34100 + 32 * j)) ∧
      t.getMem (BitVec.ofNat 64 488) = s.getMem (BitVec.ofNat 64 (0x34100 + 32 * j + 8)) ∧
      t.getMem (BitVec.ofNat 64 496) = s.getMem (BitVec.ofNat 64 (0x34100 + 32 * j + 16)) ∧
      t.getMem (BitVec.ofNat 64 504) = s.getMem (BitVec.ofNat 64 (0x34100 + 32 * j + 24)) ∧
      Frame s t [456, 480, 488, 496, 504] := by
  have hobl : blk_73.res.obligs s := by
    kgn [blk_73.res, h16, h19]; omega
  refine ⟨_, symRun_sound blk_73 codeAt_73 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_73.res]
  · kgn [blk_73.res]
  · kgn [blk_73.res]
  · kgn [blk_73.res, h16, h19]; omega
  · intro r h1 h2 h3 h4 h5; cases r <;> simp_all [blk_73.res, rv_simp] <;> rfl
  · kgn [blk_73.res, h16]
    apply BitVec.eq_of_toNat_eq
    rw [rw32_one_toNat', truncate32_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [show (4294967296 : Nat) = 2 ^ 32 by norm_num, h456]
    omega
  iterate 4 (· kgn [blk_73.res, h16, h19]; rw [show ∀ x y : Nat, x = y → s.getMem (BitVec.ofNat 64 x) =
      s.getMem (BitVec.ofNat 64 y) from fun _ _ h => h ▸ rfl]; omega)
  · intro A hA hne
    kgn [blk_73.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem spec_89 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 89)) (j c : Nat)
    (hj : j + 1 < 2 ^ 64) (hc : c < 2 ^ 64) (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if j + 1 = c then BitVec.ofNat 64 (0x1000 + 4 * 91) else BitVec.ofNat 64 (0x1000 + 4 * 73)) ∧
      t.getReg .x16 = BitVec.ofNat 64 (j + 1) ∧
      (∀ r, r ≠ .x16 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_89.res.obligs s := by simp only [blk_89.res, rv_simp]
  refine ⟨_, symRun_sound blk_89 codeAt_89 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_89.res, h16, h17]
    by_cases h : j + 1 = c
    · simp [h]
    · rw [if_pos (by omega), if_neg h]
  · kgn [blk_89.res, h16]
  · intro r h1; cases r <;> simp_all [blk_89.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_89.res]

theorem spec_91 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 91)) (lam : Nat)
    (hl : lam < 6) (h15 : s.getReg .x15 = BitVec.ofNat 64 lam) (h9 : s.getReg .x9 = BitVec.ofNat 64 5) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if lam + 1 ≤ 5 then BitVec.ofNat 64 (0x1000 + 4 * 65) else BitVec.ofNat 64 (0x1000 + 4 * 93)) ∧
      t.getReg .x15 = BitVec.ofNat 64 (lam + 1) ∧
      (∀ r, r ≠ .x15 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_91.res.obligs s := by simp only [blk_91.res, rv_simp]
  refine ⟨_, symRun_sound blk_91 codeAt_91 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_91.res, h15, h9]
    rw [ofNat_slt 5 (lam + 1) (by omega) (by omega)]
    by_cases h : lam + 1 ≤ 5
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · kgn [blk_91.res, h15]
  · intro r h1; cases r <;> simp_all [blk_91.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_91.res]

theorem spec_93 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 93)) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 101) ∧
      t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 0 ∧
      t.getMem (BitVec.ofNat 64 160) = s.getMem (BitVec.ofNat 64 0x34100) ∧
      t.getMem (BitVec.ofNat 64 168) = s.getMem (BitVec.ofNat 64 0x34108) ∧
      Frame s t [160, 168] := by
  have hobl : blk_93.res.obligs s := by simp only [blk_93.res, rv_simp]
  refine ⟨_, symRun_sound blk_93 codeAt_93 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_93.res]
  · kgn [blk_93.res]
  · kgn [blk_93.res]
  · kgn [blk_93.res]
  · kgn [blk_93.res]
  · intro A hA hne
    kgn [blk_93.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

end SigGolfCandidate.Keygen
