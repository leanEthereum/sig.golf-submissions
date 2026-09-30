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
      t.getReg .x9 = BitVec.ofNat 64 11 ∧ t.getReg .x19 = BitVec.ofNat 64 0x44C0 ∧
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

theorem spec_49 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 49)) (m p : Nat)
    (hp : p < 2 ^ 32) (h23 : s.getReg .x23 = BitVec.ofNat 64 m) (h24 : s.getReg .x24 = BitVec.ofNat 64 p)
    (h192 : (s.getMem (BitVec.ofNat 64 192)).toNat % 2 ^ 32 = 257) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 52) ∧
      t.getReg .x23 = BitVec.ofNat 64 (m + 1) ∧ t.getReg .x10 = BitVec.ofNat 64 192 ∧
      (∀ r, r ≠ .x23 → r ≠ .x10 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 192) = BitVec.ofNat 64 (257 + 2 ^ 32 * p) ∧
      Frame s t [192] := by
  have hobl : blk_49.res.obligs s := by simp only [blk_49.res, rv_simp]
  refine ⟨_, symRun_sound blk_49 codeAt_49 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals try (kgn [blk_49.res]; done)
  · kgn [blk_49.res, h23]
  · intro r h1 h2; cases r <;> simp_all [blk_49.res, rv_simp] <;> rfl
  · kgn [blk_49.res, h24]
    apply BitVec.eq_of_toNat_eq
    rw [rw32_one_toNat, h192, truncate32_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    omega
  · intro A hA hne
    kgn [blk_49.res]
    simp at hne
    rw [if_neg (by omega)]

theorem spec_53 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 53)) (m p : Nat)
    (hm : m < 2 ^ 32) (h23 : s.getReg .x23 = BitVec.ofNat 64 m) (h24 : s.getReg .x24 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if m = 7 then BitVec.ofNat 64 (0x1000 + 4 * 56) else BitVec.ofNat 64 (0x1000 + 4 * 49)) ∧
      t.getReg .x24 = BitVec.ofNat 64 (p + 1) ∧
      (∀ r, r ≠ .x24 → r ≠ .x3 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_53.res.obligs s := by simp only [blk_53.res, rv_simp]
  refine ⟨_, symRun_sound blk_53 codeAt_53 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_53.res, h23]
    by_cases h : m = 7
    · simp [h]
    · rw [if_pos (by omega), if_neg h]
  · kgn [blk_53.res, h24]
  · intro r h1 h2; cases r <;> simp_all [blk_53.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_53.res]

theorem spec_56 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 56)) (i p : Nat)
    (hi : i < 42) (h21 : s.getReg .x21 = BitVec.ofNat 64 i) (h24 : s.getReg .x24 = BitVec.ofNat 64 p) :
    ∃ t, Steps image s 9 9 t ∧
      t.pc = (if i + 1 = 42 then BitVec.ofNat 64 (0x1000 + 4 * 65) else BitVec.ofNat 64 (0x1000 + 4 * 32)) ∧
      t.getReg .x21 = BitVec.ofNat 64 (i + 1) ∧ t.getReg .x24 = BitVec.ofNat 64 (p + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x3 → r ≠ .x21 → r ≠ .x24 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 (864 + 16 * i)) = s.getMem (BitVec.ofNat 64 240) ∧
      t.getMem (BitVec.ofNat 64 (864 + 16 * i + 8)) = s.getMem (BitVec.ofNat 64 248) ∧
      Frame s t [864 + 16 * i, 864 + 16 * i + 8] := by
  have hobl : blk_56.res.obligs s := by
    kgn [blk_56.res, h21]; omega
  refine ⟨_, symRun_sound blk_56 codeAt_56 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_56.res, h21]
    by_cases h : i = 41 <;> simp [h] <;> omega
  · kgn [blk_56.res, h21]
  · kgn [blk_56.res, h24]
  · intro r h1 h2 h3 h4 h5; cases r <;> simp_all [blk_56.res, rv_simp] <;> rfl
  · kgn [blk_56.res, h21]; rw [if_neg (by omega), if_pos (by omega)]
  · kgn [blk_56.res, h21]; rw [if_pos (by omega)]
  · intro A hA hne
    kgn [blk_56.res, h21]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

theorem spec_65 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 65)) (e : Nat)
    (he : e < 2048) (h20 : s.getReg .x20 = BitVec.ofNat 64 e) (h19 : s.getReg .x19 = BitVec.ofNat 64 0x44C0) :
    ∃ t, Steps image s 4 4 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 69) ∧
      t.getReg .x10 = BitVec.ofNat 64 832 ∧ t.getReg .x11 = BitVec.ofNat 64 704 ∧
      t.getReg .x12 = BitVec.ofNat 64 (0x44C0 + 16 * e) ∧
      (∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      Frame s t [] := by
  have hobl : blk_65.res.obligs s := by simp only [blk_65.res, rv_simp]
  refine ⟨_, symRun_sound blk_65 codeAt_65 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_65.res]
  · kgn [blk_65.res]
  · kgn [blk_65.res]
  · kgn [blk_65.res, h19, h20]; omega
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_65.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_65.res]

theorem spec_70 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 70)) (e : Nat)
    (he : e < 2048) (h20 : s.getReg .x20 = BitVec.ofNat 64 e) (h17 : s.getReg .x17 = BitVec.ofNat 64 2048) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if e + 1 = 2048 then BitVec.ofNat 64 (0x1000 + 4 * 72) else BitVec.ofNat 64 (0x1000 + 4 * 25)) ∧
      t.getReg .x20 = BitVec.ofNat 64 (e + 1) ∧
      (∀ r, r ≠ .x20 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_70.res.obligs s := by simp only [blk_70.res, rv_simp]
  refine ⟨_, symRun_sound blk_70 codeAt_70 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_70.res, h20, h17]
    by_cases h : e = 2047 <;> simp [h] <;> omega
  · kgn [blk_70.res, h20]
  · intro r h1; cases r <;> simp_all [blk_70.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_70.res]

theorem spec_72 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 72)) :
    ∃ t, Steps image s 1 1 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 73) ∧
      t.getReg .x15 = BitVec.ofNat 64 1 ∧
      (∀ r, r ≠ .x15 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_72.res.obligs s := by simp only [blk_72.res, rv_simp]
  refine ⟨_, symRun_sound blk_72 codeAt_72 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_72.res]
  · kgn [blk_72.res]
  · intro r h1; cases r <;> simp_all [blk_72.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_72.res]

/-- Level head (`tb_level_loop`): node tweak word0, `NB+8`, destination base `s9 = s3 + 16 a7`,
`a7 /= 2`, `a6 = 0`. -/
theorem spec_73 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 73)) (lam c B : Nat)
    (hl : lam < 2 ^ 32) (hc : c < 2 ^ 32) (hB : B < 2 ^ 32) (h15 : s.getReg .x15 = BitVec.ofNat 64 lam)
    (h8 : s.getReg .x8 = BitVec.ofNat 64 0) (h30 : s.getReg .x30 = BitVec.ofNat 64 0)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c) (h19 : s.getReg .x19 = BitVec.ofNat 64 B) :
    ∃ t, Steps image s 10 10 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 83) ∧
      t.getReg .x17 = BitVec.ofNat 64 (c / 2) ∧ t.getReg .x16 = BitVec.ofNat 64 0 ∧
      t.getReg .x25 = BitVec.ofNat 64 (B + 16 * c) ∧
      (∀ r, r ≠ .x3 → r ≠ .x29 → r ≠ .x17 → r ≠ .x16 → r ≠ .x25 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 448) = BitVec.ofNat 64 (769 + 2 ^ 32 * lam) ∧
      (t.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = 0 ∧
      Frame s t [448, 456] := by
  have hobl : blk_73.res.obligs s := by simp only [blk_73.res, rv_simp]
  refine ⟨_, symRun_sound blk_73 codeAt_73 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_73.res]
  · kgn [blk_73.res, h17]; rw [ofNat_shr _ _ (by omega)]; rfl
  · kgn [blk_73.res]
  · kgn [blk_73.res, h17, h19]; congr 1; omega
  · intro r h1 h2 h3 h4 h5; cases r <;> simp_all [blk_73.res, rv_simp] <;> rfl
  · kgn [blk_73.res, h15, h8, BitVec.or_zero]
    rw [show (4294967296 : Nat) = 2 ^ 32 by norm_num, ofNat_or_add 769 lam 32 (by norm_num)]
    congr 1; omega
  · kgn [blk_73.res, h30]; rw [rw32_zero_low']; rfl
  · intro A hA hne
    kgn [blk_73.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

/-- Node inputs (`tb_node_loop`): `NB+12 = j`, children `s3 + 32 j .. + 32` → `NB+32 ..`,
`a2 = s9 + 16 j`. -/
theorem spec_83 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 83)) (j B D : Nat)
    (hj : j < 2 ^ 11) (hB : B + 32 * j + 32 ≤ 2 ^ 24) (hB8 : B % 8 = 0) (hB0 : 512 ≤ B)
    (hD : D + 16 * j + 32 ≤ 2 ^ 24)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h19 : s.getReg .x19 = BitVec.ofNat 64 B) (h25 : s.getReg .x25 = BitVec.ofNat 64 D)
    (h456 : (s.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = 0) :
    ∃ t, Steps image s 15 15 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 98) ∧
      t.getReg .x10 = BitVec.ofNat 64 448 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 (D + 16 * j) ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 456) = BitVec.ofNat 64 (2 ^ 32 * j) ∧
      t.getMem (BitVec.ofNat 64 480) = s.getMem (BitVec.ofNat 64 (B + 32 * j)) ∧
      t.getMem (BitVec.ofNat 64 488) = s.getMem (BitVec.ofNat 64 (B + 32 * j + 8)) ∧
      t.getMem (BitVec.ofNat 64 496) = s.getMem (BitVec.ofNat 64 (B + 32 * j + 16)) ∧
      t.getMem (BitVec.ofNat 64 504) = s.getMem (BitVec.ofNat 64 (B + 32 * j + 24)) ∧
      Frame s t [456, 480, 488, 496, 504] := by
  have hobl : blk_83.res.obligs s := by
    kgn [blk_83.res, h16, h19]; omega
  refine ⟨_, symRun_sound blk_83 codeAt_83 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_83.res]
  · kgn [blk_83.res]
  · kgn [blk_83.res]
  · kgn [blk_83.res, h16, h25]; omega
  · intro r h1 h2 h3 h4 h5; cases r <;> simp_all [blk_83.res, rv_simp] <;> rfl
  · kgn [blk_83.res, h16]
    apply BitVec.eq_of_toNat_eq
    rw [rw32_one_toNat', truncate32_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
    rw [show (4294967296 : Nat) = 2 ^ 32 by norm_num, h456]
    omega
  iterate 4 (· kgn [blk_83.res, h16, h19]; congr 2; ring)
  · intro A hA hne
    kgn [blk_83.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem spec_99 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 99)) (j c : Nat)
    (hj : j + 1 < 2 ^ 64) (hc : c < 2 ^ 64) (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 2 2 t ∧
      t.pc = (if j + 1 = c then BitVec.ofNat 64 (0x1000 + 4 * 101) else BitVec.ofNat 64 (0x1000 + 4 * 83)) ∧
      t.getReg .x16 = BitVec.ofNat 64 (j + 1) ∧
      (∀ r, r ≠ .x16 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_99.res.obligs s := by simp only [blk_99.res, rv_simp]
  refine ⟨_, symRun_sound blk_99 codeAt_99 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_99.res, h16, h17]
    by_cases h : j + 1 = c
    · simp [h]
    · rw [if_pos (by omega), if_neg h]
  · kgn [blk_99.res, h16]
  · intro r h1; cases r <;> simp_all [blk_99.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_99.res]

/-- Level tail: `s3 = s9`, `a5 += 1`, loop while `a5 ≤ 11`. -/
theorem spec_101 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 101)) (lam : Nat)
    (hl : lam < 12) (h15 : s.getReg .x15 = BitVec.ofNat 64 lam) (h9 : s.getReg .x9 = BitVec.ofNat 64 11) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if lam + 1 ≤ 11 then BitVec.ofNat 64 (0x1000 + 4 * 73) else BitVec.ofNat 64 (0x1000 + 4 * 104)) ∧
      t.getReg .x15 = BitVec.ofNat 64 (lam + 1) ∧ t.getReg .x19 = s.getReg .x25 ∧
      (∀ r, r ≠ .x15 → r ≠ .x19 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_101.res.obligs s := by simp only [blk_101.res, rv_simp]
  refine ⟨_, symRun_sound blk_101 codeAt_101 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_101.res, h15, h9]
    rw [ofNat_slt 11 (lam + 1) (by omega) (by omega)]
    by_cases h : lam + 1 ≤ 11
    · rw [if_pos h, if_pos (by simp; omega)]
    · rw [if_neg h, if_neg (by simp; omega)]
  · kgn [blk_101.res, h15]
  · kgn [blk_101.res]
  · intro r h1 h2; cases r <;> simp_all [blk_101.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_101.res]

/-- Root → public key (`160`, `168`), then zero the 32 bytes at `s3`. -/
theorem spec_104 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 104))
    (h19 : s.getReg .x19 = BitVec.ofNat 64 0x144A0) :
    ∃ t, Steps image s 8 8 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 112) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 160) = s.getMem (BitVec.ofNat 64 0x144A0) ∧
      t.getMem (BitVec.ofNat 64 168) = s.getMem (BitVec.ofNat 64 0x144A8) ∧
      t.getMem (BitVec.ofNat 64 0x144A0) = 0 ∧ t.getMem (BitVec.ofNat 64 0x144A8) = 0 ∧
      t.getMem (BitVec.ofNat 64 0x144B0) = 0 ∧ t.getMem (BitVec.ofNat 64 0x144B8) = 0 ∧
      Frame s t [160, 168, 0x144A0, 0x144A8, 0x144B0, 0x144B8] := by
  have hobl : blk_104.res.obligs s := by kgn [blk_104.res, h19]; norm_num
  refine ⟨_, symRun_sound blk_104 codeAt_104 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_104.res]
  · intro r h1 h2; cases r <;> simp_all [blk_104.res, rv_simp] <;> rfl
  iterate 6 (· kgn [blk_104.res, h19] <;> rfl)
  · intro A hA hne
    kgn [blk_104.res, h19]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]

theorem spec_112 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 112)) :
    ∃ t, Steps image s 3 3 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 115) ∧
      t.getReg .x20 = BitVec.ofNat 64 0x44C0 ∧ t.getReg .x15 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x20 → r ≠ .x15 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_112.res.obligs s := by simp only [blk_112.res, rv_simp]
  refine ⟨_, symRun_sound blk_112 codeAt_112 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_112.res]
  · kgn [blk_112.res]
  · kgn [blk_112.res]
  · intro r h1 h2; cases r <;> simp_all [blk_112.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_112.res]

/-- Mask level head: `a7 = 2^(11 - l)`, `a6 = 0`. -/
theorem spec_115 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 115)) (l : Nat)
    (hl : l < 11) (h15 : s.getReg .x15 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 5 5 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 120) ∧
      t.getReg .x17 = BitVec.ofNat 64 (2 ^ (11 - l)) ∧ t.getReg .x16 = BitVec.ofNat 64 0 ∧
      (∀ r, r ≠ .x3 → r ≠ .x29 → r ≠ .x17 → r ≠ .x16 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_115.res.obligs s := by simp only [blk_115.res, rv_simp]
  refine ⟨_, symRun_sound blk_115 codeAt_115 s hpc hobl, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_115.res]
  · kgn [blk_115.res, h15]
    interval_cases l <;> rfl
  · kgn [blk_115.res]
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_115.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_115.res]

/-- Mask query setup: `PB = tw_mask(l, j)`, `a0 = PB`, `a1 = 64`, `a2 = EO`. -/
theorem spec_120 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 120)) (l j : Nat)
    (hl : l < 11) (hj : j < 2 ^ 11) (h15 : s.getReg .x15 = BitVec.ofNat 64 l)
    (h16 : s.getReg .x16 = BitVec.ofNat 64 j) :
    ∃ t, Steps image s 9 9 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 129) ∧
      t.getReg .x10 = BitVec.ofNat 64 1696 ∧ t.getReg .x11 = BitVec.ofNat 64 64 ∧
      t.getReg .x12 = BitVec.ofNat 64 320 ∧
      (∀ r, r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 1696) = BitVec.ofNat 64 (3329 + 2 ^ 32 * l) ∧
      t.getMem (BitVec.ofNat 64 1704) = BitVec.ofNat 64 (2 ^ 32 * j) ∧
      Frame s t [1696, 1704] := by
  have hobl : blk_120.res.obligs s := by simp only [blk_120.res, rv_simp]
  refine ⟨_, symRun_sound blk_120 codeAt_120 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_120.res]
  · kgn [blk_120.res]
  · kgn [blk_120.res]
  · kgn [blk_120.res]
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_120.res, rv_simp] <;> rfl
  · kgn [blk_120.res, h15]
    congr 1; ring
  · kgn [blk_120.res, h16]
    congr 1; ring
  · intro A hA hne
    kgn [blk_120.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

/-- Mask the node at `s4` with the answer at `EO`, advance. -/
theorem spec_130 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 130)) (A j c : Nat)
    (hA : A + 16 < 2 ^ 24) (hA8 : A % 8 = 0) (hA0 : 336 ≤ A) (hj : j + 1 < 2 ^ 64) (hc : c < 2 ^ 64)
    (h20 : s.getReg .x20 = BitVec.ofNat 64 A) (h16 : s.getReg .x16 = BitVec.ofNat 64 j)
    (h17 : s.getReg .x17 = BitVec.ofNat 64 c) :
    ∃ t, Steps image s 11 11 t ∧
      t.pc = (if j + 1 = c then BitVec.ofNat 64 (0x1000 + 4 * 141) else BitVec.ofNat 64 (0x1000 + 4 * 120)) ∧
      t.getReg .x20 = BitVec.ofNat 64 (A + 16) ∧ t.getReg .x16 = BitVec.ofNat 64 (j + 1) ∧
      (∀ r, r ≠ .x1 → r ≠ .x2 → r ≠ .x20 → r ≠ .x16 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) ^^^ s.getMem (BitVec.ofNat 64 320) ∧
      t.getMem (BitVec.ofNat 64 (A + 8)) = s.getMem (BitVec.ofNat 64 (A + 8)) ^^^ s.getMem (BitVec.ofNat 64 328) ∧
      Frame s t [A, A + 8] := by
  have hobl : blk_130.res.obligs s := by kgn [blk_130.res, h20]; omega
  refine ⟨_, symRun_sound blk_130 codeAt_130 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · kgn [blk_130.res, h16, h17]
    by_cases h : j + 1 = c
    · simp [h]
    · rw [if_pos (by rw [Nat.mod_eq_of_lt (show j + 1 < 18446744073709551616 from hj),
        Nat.mod_eq_of_lt (show c < 18446744073709551616 from hc)]; exact h), if_neg h]
  · kgn [blk_130.res, h20]
  · kgn [blk_130.res, h16]
  · intro r h1 h2 h3 h4; cases r <;> simp_all [blk_130.res, rv_simp] <;> rfl
  · kgn [blk_130.res, h20]
    rw [if_neg (by omega), if_pos (by omega)]
  · kgn [blk_130.res, h20]
  · intro A' hA' hne
    kgn [blk_130.res, h20]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega)]

theorem spec_141 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 141)) (l : Nat)
    (hl : l < 11) (h15 : s.getReg .x15 = BitVec.ofNat 64 l) :
    ∃ t, Steps image s 3 3 t ∧
      t.pc = (if l + 1 = 11 then BitVec.ofNat 64 (0x1000 + 4 * 144) else BitVec.ofNat 64 (0x1000 + 4 * 115)) ∧
      t.getReg .x15 = BitVec.ofNat 64 (l + 1) ∧
      (∀ r, r ≠ .x15 → r ≠ .x3 → t.getReg r = s.getReg r) ∧ Frame s t [] := by
  have hobl : blk_141.res.obligs s := by simp only [blk_141.res, rv_simp]
  refine ⟨_, symRun_sound blk_141 codeAt_141 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_141.res, h15]
    by_cases h : l = 10
    · subst h; rfl
    · rw [if_pos (by omega), if_neg h]
  · kgn [blk_141.res, h15]
  · intro r h1 h2; cases r <;> simp_all [blk_141.res, rv_simp] <;> rfl
  · intro A _ _; kgn [blk_141.res]

/-- MAC input in place: `tw_mac` word0 at `CACHE-32`, `S` at `CACHE`, zeros after the region;
`a0 = CACHE-32`, `a1 = 65600`, `a2 = CACHE`. -/
theorem spec_144 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 144)) :
    ∃ t, Steps image s 24 24 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 168) ∧
      t.getReg .x10 = BitVec.ofNat 64 0x4480 ∧ t.getReg .x11 = BitVec.ofNat 64 65600 ∧
      t.getReg .x12 = BitVec.ofNat 64 0x44A0 ∧
      (∀ r, r ≠ .x1 → r ≠ .x3 → r ≠ .x10 → r ≠ .x11 → r ≠ .x12 → r ≠ .x29 → t.getReg r = s.getReg r) ∧
      t.getMem (BitVec.ofNat 64 0x4480) = BitVec.ofNat 64 3585 ∧
      t.getMem (BitVec.ofNat 64 0x44A0) = s.getMem (BitVec.ofNat 64 128) ∧
      t.getMem (BitVec.ofNat 64 0x44A8) = s.getMem (BitVec.ofNat 64 136) ∧
      t.getMem (BitVec.ofNat 64 0x44B0) = s.getMem (BitVec.ofNat 64 144) ∧
      t.getMem (BitVec.ofNat 64 0x44B8) = s.getMem (BitVec.ofNat 64 152) ∧
      t.getMem (BitVec.ofNat 64 0x144A0) = 0 ∧ t.getMem (BitVec.ofNat 64 0x144A8) = 0 ∧
      t.getMem (BitVec.ofNat 64 0x144B0) = 0 ∧ t.getMem (BitVec.ofNat 64 0x144B8) = 0 ∧
      Frame s t [0x4480, 0x44A0, 0x44A8, 0x44B0, 0x44B8, 0x144A0, 0x144A8, 0x144B0, 0x144B8] := by
  have hobl : blk_144.res.obligs s := by simp only [blk_144.res, rv_simp]
  refine ⟨_, symRun_sound blk_144 codeAt_144 s hpc hobl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  iterate 4 (· kgn [blk_144.res])
  · intro r h1 h2 h3 h4 h5 h6; cases r <;> simp_all [blk_144.res, rv_simp] <;> rfl
  iterate 9 (· kgn [blk_144.res] <;> rfl)
  · intro A hA hne
    kgn [blk_144.res]
    simp at hne
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem spec_169 (s : MachineState) (hpc : s.pc = BitVec.ofNat 64 (0x1000 + 4 * 169)) :
    ∃ t, Steps image s 2 2 t ∧ t.pc = BitVec.ofNat 64 (0x1000 + 4 * 171) ∧
      t.getReg .x5 = BitVec.ofNat 64 1 ∧ t.getReg .x10 = BitVec.ofNat 64 0 ∧ Frame s t [] := by
  have hobl : blk_169.res.obligs s := by simp only [blk_169.res, rv_simp]
  refine ⟨_, symRun_sound blk_169 codeAt_169 s hpc hobl, ?_, ?_, ?_, ?_⟩
  · kgn [blk_169.res]
  · kgn [blk_169.res]
  · kgn [blk_169.res]
  · intro A _ _; kgn [blk_169.res]

end SigGolfCandidate.Keygen
