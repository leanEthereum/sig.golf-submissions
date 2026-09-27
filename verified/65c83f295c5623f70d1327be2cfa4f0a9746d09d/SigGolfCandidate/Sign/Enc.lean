import SigGolfCandidate.Sign.Blocks
import SigGolfCandidate.Sign.Inv

/-!
# `sign`, the counter search of a layer (`enc_loop`, instructions 230 .. 369)

`encLoop_sim` : from `enc_loop` with counter `c`, the machine refines
`searchCounter lay tau e M c (2^20 - c)`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem slice_valOfWords_0 (w0 w1 : Word) : slice (valOfWords w0 w1) 0 8 = bytesOfWord w0 := by
  simp [slice, valOfWords]

theorem slice_valOfWords_8 (w0 w1 : Word) : slice (valOfWords w0 w1) 8 8 = bytesOfWord w1 := by
  simp [slice, valOfWords, List.drop_append_of_le_length]

/-- `decodeDigits` of a hash answer, in terms of its first two dwords. -/
theorem decodeDigits_answer (a : BitVec 256) :
    decodeDigits (answerBytes 16 a) =
      if (a.extractLsb' 0 64).toNat < 2 ^ 63 ∧ (a.extractLsb' 64 64).toNat < 2 ^ 63 then
        (if (digitsOfWord (a.extractLsb' 0 64).toNat ++ digitsOfWord (a.extractLsb' 64 64).toNat).sum
            = 170 then
          some (digitsOfWord (a.extractLsb' 0 64).toNat ++ digitsOfWord (a.extractLsb' 64 64).toNat)
        else none)
      else none := by
  rw [answerBytes_16]
  unfold decodeDigits
  rw [slice_valOfWords_0, slice_valOfWords_8, leNat_bytesOfWord, leNat_bytesOfWord]
  rfl

theorem slt_zero_ofNat (d : Nat) (hd : d < 2 ^ 64) :
    BitVec.slt (BitVec.ofNat 64 d) (BitVec.ofNat 64 0) = decide (2 ^ 63 ≤ d) := by
  rw [show BitVec.ofNat 64 0 = 0#64 from rfl, BitVec.slt_zero_eq_msb, BitVec.msb_eq_decide]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]

theorem land7 (n : Nat) : n &&& 7 = n % 8 := Nat.and_two_pow_sub_one_eq_mod n 3

theorem ofNat_sub170_bne (X : Nat) (hX : X < 2 ^ 64) :
    (BitVec.ofNat 64 X - BitVec.ofNat 64 170 != BitVec.ofNat 64 0) = !decide (X = 170) := by
  by_cases h : X = 170
  · subst h; rfl
  · have : BitVec.ofNat 64 X - BitVec.ofNat 64 170 ≠ BitVec.ofNat 64 0 := by
      intro h'
      have := congrArg BitVec.toNat h'
      simp [BitVec.toNat_sub] at this; omega
    simp [this, h]

/-! ## The digit sum of the encoding check -/

/-- `acc + Σ_{i<k} (a >>> 3(r+i)) &&& 7`, accumulated left to right as the machine does. -/
def dsumAcc (acc a : Word) : Nat → Nat → Word
  | _, 0 => acc
  | r, k + 1 => dsumAcc (acc + ((a >>> (3 * r)) &&& 7)) a (r + 1) k

/-- The machine's digit sum of `(d0, d1)`. -/
def dsum2 (a b : Word) : Word := dsumAcc (dsumAcc (a &&& 7) a 1 20) b 0 21

-- The final pc of the digit-sum block (`bne t3, x0` after `addi t3, t3, -170`).
kernel_theorem blk239_pc_raw : ∀ t : MachineState, (blk239.res.toState t).pc =
    if (dsum2 (t.getReg .x1) (t.getReg .x2) + 18446744073709551446#64 != 0#64) = true then
      pcOf 365 else pcOf 364

theorem digit_toNat (a : Word) (r : Nat) : ((a >>> (3 * r)) &&& 7).toNat = a.toNat / 2 ^ (3 * r) % 8 := by
  rw [BitVec.toNat_and, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  exact land7 _

theorem dsumAcc_toNat (a : Word) : ∀ (k : Nat) (acc : Word) (r : Nat), acc.toNat + 7 * k < 2 ^ 64 →
    (dsumAcc acc a r k).toNat =
      acc.toNat + ((List.range k).map (fun i => a.toNat / 2 ^ (3 * (r + i)) % 8)).sum := by
  intro k
  induction k with
  | zero => intro acc r _; simp [dsumAcc]
  | succ k ih =>
    intro acc r h
    have hd : a.toNat / 2 ^ (3 * r) % 8 < 8 := Nat.mod_lt _ (by norm_num)
    rw [dsumAcc, ih _ _ (by rw [BitVec.toNat_add, digit_toNat, Nat.mod_eq_of_lt (by omega)]; omega),
      BitVec.toNat_add, digit_toNat, Nat.mod_eq_of_lt (by omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, List.sum_cons, Nat.add_zero]
    have : (fun i => a.toNat / 2 ^ (3 * (r + 1 + i)) % 8) =
        ((fun i => a.toNat / 2 ^ (3 * (r + i)) % 8) ∘ Nat.succ) := by
      funext i; simp only [Function.comp, Nat.succ_eq_add_one]; congr 3; ring
    rw [this]; ring

theorem digitsOfWord_sum (d : Nat) :
    (digitsOfWord d).sum = ((List.range 21).map (fun i => d / 2 ^ (3 * (0 + i)) % 8)).sum := by
  unfold digitsOfWord
  have : ∀ i, d / 8 ^ i % 8 = d / 2 ^ (3 * (0 + i)) % 8 := fun i => by simp [Nat.pow_mul]
  simp only [this]

theorem sum_le_7 (d r k : Nat) : ((List.range k).map (fun i => d / 2 ^ (3 * (r + i)) % 8)).sum ≤ 7 * k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    have := Nat.mod_lt (d / 2 ^ (3 * (r + k))) (by norm_num : 8 > 0)
    omega

theorem dsum2_toNat (d0 d1 : Nat) (h0 : d0 < 2 ^ 64) (h1 : d1 < 2 ^ 64) :
    (dsum2 (BitVec.ofNat 64 d0) (BitVec.ofNat 64 d1)).toNat =
      (digitsOfWord d0 ++ digitsOfWord d1).sum := by
  have e0 : (BitVec.ofNat 64 d0).toNat = d0 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h0]
  have e1 : (BitVec.ofNat 64 d1).toNat = d1 := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h1]
  have hs1 := sum_le_7 d0 1 20
  have hs2 := sum_le_7 d0 0 21
  have hs3 := sum_le_7 d1 0 21
  have ha : ((BitVec.ofNat 64 d0) &&& 7).toNat = d0 % 8 := by
    have := digit_toNat (BitVec.ofNat 64 d0) 0
    simp only [Nat.mul_zero, BitVec.ushiftRight_zero, Nat.pow_zero, Nat.div_one] at this
    rw [this, e0]
  have hd8 : d0 % 8 < 8 := Nat.mod_lt _ (by norm_num)
  unfold dsum2
  have i1 : (dsumAcc (BitVec.ofNat 64 d0 &&& 7) (BitVec.ofNat 64 d0) 1 20).toNat =
      d0 % 8 + ((List.range 20).map (fun i => d0 / 2 ^ (3 * (1 + i)) % 8)).sum := by
    rw [dsumAcc_toNat _ _ _ _ (by rw [ha]; omega), ha, e0]
  rw [dsumAcc_toNat _ _ _ _ (by rw [i1]; omega), i1, e1, List.sum_append, digitsOfWord_sum,
    digitsOfWord_sum, List.range_succ_eq_map (n := 20)]
  simp only [List.map_cons, List.map_map, List.sum_cons, Nat.zero_add, Nat.mul_zero, Nat.pow_zero,
    Nat.div_one]
  have : (fun i => d0 / 2 ^ (3 * (1 + i)) % 8) = ((fun i => d0 / 2 ^ (3 * i) % 8) ∘ Nat.succ) := by
    funext i; simp only [Function.comp, Nat.succ_eq_add_one]; congr 3; ring
  rw [this]

/-- The encoding check of the machine decides `decodeDigits`' digit-sum condition. -/
theorem blk239_pc (t : MachineState) (d0 d1 : Nat) (h0 : d0 < 2 ^ 63) (h1 : d1 < 2 ^ 63)
    (t1 : t.getReg .x1 = BitVec.ofNat 64 d0) (t2 : t.getReg .x2 = BitVec.ofNat 64 d1) :
    (blk239.res.toState t).pc =
      if (digitsOfWord d0 ++ digitsOfWord d1).sum = 170 then pcOf 364 else pcOf 365 := by
  rw [blk239_pc_raw, t1, t2]
  have hs := dsum2_toNat d0 d1 (by omega) (by omega)
  have hle : (digitsOfWord d0 ++ digitsOfWord d1).sum ≤ 294 := by
    rw [List.sum_append, digitsOfWord_sum, digitsOfWord_sum]
    have := sum_le_7 d0 0 21; have := sum_le_7 d1 0 21; omega
  generalize dsum2 (BitVec.ofNat 64 d0) (BitVec.ofNat 64 d1) = w at hs
  have hw : w = BitVec.ofNat 64 ((digitsOfWord d0 ++ digitsOfWord d1).sum) := by
    apply BitVec.eq_of_toNat_eq; rw [hs, BitVec.toNat_ofNat]; omega
  subst hw
  generalize (digitsOfWord d0 ++ digitsOfWord d1).sum = X at hle ⊢
  by_cases hX : X = 170
  · subst hX
    rw [if_pos rfl, if_neg]
    rw [ofNat_add_ofNat, bne_iff_ne, ne_eq, not_not, show (0#64 : Word) = BitVec.ofNat 64 0 from rfl,
      ofNat_eq_iff]
    norm_num
  · rw [if_neg hX, if_pos]
    rw [ofNat_add_ofNat, bne_iff_ne, ne_eq, show (0#64 : Word) = BitVec.ofNat 64 0 from rfl,
      ofNat_eq_iff]
    omega

/-! ## The search loop -/

/-- Facts at the start of the counter search. -/
structure EncMem (lay tau e : Nat) (M : Val) (u : MachineState) : Prop where
  hlay : lay < 7
  htau : tau < 2 ^ 30
  he : e < 32
  hM : M.length = 16
  eb0 : u.getMem (BitVec.ofNat 64 0x100) = twWord0 4 lay tau 0
  eb8 : u.getMem (BitVec.ofNat 64 0x108) = BitVec.ofNat 64 (tau + 2 ^ 32 * e)
  ebP : u.readWords (BitVec.ofNat 64 0x110) 2 = [0, 0]
  ebM : u.readWords (BitVec.ofNat 64 0x120) 2 = wordsOf M
  eb56 : u.getMem (BitVec.ofNat 64 0x138) = 0
  x5 : u.getReg .x5 = 0
  x7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20)

def encW (a : Nat) : Prop := a = 0x130 ∨ (0x140 ≤ a ∧ a < 0x160)

def encRegs : List Reg := [.x1, .x2, .x3, .x6, .x10, .x11, .x12, .x28]

def EncInv (u : MachineState) (c : Nat) (t : MachineState) : Prop :=
  t.pc = pcOf 230 ∧ t.getReg .x6 = BitVec.ofNat 64 c ∧ c < 2 ^ 20 ∧ RegsEq u t encRegs ∧ Frame u t encW

def EncPost (u : MachineState) : Option (Nat × List Nat) → MachineState → Prop
  | none, t => t.pc = pcOf 369 ∧ t.getReg .x5 = 1 ∧ t.getReg .x10 = 1
  | some (c, x), t => t.pc = pcOf 370 ∧ t.getReg .x6 = BitVec.ofNat 64 c ∧ c < 2 ^ 20 ∧
      (∃ d0 d1, d0 < 2 ^ 63 ∧ d1 < 2 ^ 63 ∧ x = digitsOfWord d0 ++ digitsOfWord d1 ∧ x.sum = 170 ∧
        t.getReg .x1 = BitVec.ofNat 64 d0 ∧ t.getReg .x2 = BitVec.ofNat 64 d1) ∧
      RegsEq u t encRegs ∧ Frame u t encW

theorem searchCounter_succ (lay tau e : Nat) (M : Val) (c f : Nat) :
    searchCounter lay tau e M c (f + 1) = (hash16 (encInput lay tau e M c) >>= fun d =>
      match decodeDigits d with
      | some x => pure (some (c, x))
      | none => searchCounter lay tau e M (c + 1) f) := rfl

theorem encTrial (lay tau e : Nat) (M : Val) (u : MachineState) (hmem : EncMem lay tau e M u)
    (c : Nat) (t : MachineState) (hinv : EncInv u c t) (rest : OracleComp HashSpec (Option (Nat × List Nat)))
    (Wr : Nat)
    (hrest : ∀ t', t'.pc = pcOf 365 → t'.getReg .x6 = BitVec.ofNat 64 c → RegsEq u t' encRegs →
      Frame u t' encW → Sim image t' Wr rest (EncPost u)) :
    Sim image t (142 + Wr) (hash16 (encInput lay tau e M c) >>= fun d =>
      match decodeDigits d with
      | some x => pure (some (c, x))
      | none => rest) (EncPost u) := by
  obtain ⟨tpc, t6, hc, tregs, tframe⟩ := hinv
  have hl := hmem.hlay
  have htau := hmem.htau
  have he := hmem.he
  -- block 230
  have hs1 := symRun_sound blk230 codeAt_230 t tpc (by simp only [blk230.res, rv_simp])
  have hc1 : blk230.res.cycles = 4 := rfl
  rw [hc1] at hs1
  set t1 := blk230.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x130) := by
    apply frame_toState; intro x hx hW
    simp only [blk230.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x10, .x11, .x12] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk230 codeAt_230 t (by simp only [blk230.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x100 := by simp only [ht1, blk230.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht1, blk230.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht1, blk230.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tregs.get .x5, hmem.x5]
  have pc1 : t1.pc = pcOf 234 := by simp only [ht1, blk230.res, rv_simp]
  have hq : hashInput t1 = pad64 (encInput lay tau e M c) := by
    obtain ⟨hn, hw⟩ := words_encInput lay tau e M hmem.hM c
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 2 + 1 + 1 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add,
      readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, readWords_ofNat_one, readWords_ofNat_one,
      f1.getMem (a := 0x100) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x100) (by norm_num) (by simp only [encW]; omega),
      hmem.eb0, f1.getMem (a := 0x108) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x108) (by norm_num) (by simp only [encW]; omega), hmem.eb8,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hmem.ebP,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [encW]; omega), hmem.ebM,
      f1.getMem (a := 0x138) (by norm_num) (by norm_num),
      tframe.getMem (a := 0x138) (by norm_num) (by simp only [encW]; omega), hmem.eb56]
    simp only [ht1, blk230.res, rv_simp, t6]
    simp only [twWords_eq, List.cons_append, List.nil_append, List.append_assoc, List.cons.injEq,
      true_and, and_true]
    refine ⟨?_, ?_⟩
    · congr 1; rw [Nat.mod_eq_of_lt (by omega : tau < 2 ^ 32), Nat.mod_eq_of_lt (by omega : e < 2 ^ 32)]
    · rw [if_pos trivial, Nat.mod_eq_of_lt (by omega : c < 2 ^ 32)]
  have hb : (pad64 (encInput lay tau e M c)).blocks = 1 :=
    congrArg (· + 1) (words_encInput lay tau e M hmem.hM c).1
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 130 + Wr) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fun a => ?_))).mono (by rw [hb]; omega) (fun _ _ h => h)
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 235 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have w0 : t2.getMem (BitVec.ofNat 64 0x140) = a.extractLsb' 0 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x140 x12 (by norm_num) (by norm_num)]; simp
  have w1 : t2.getMem (BitVec.ofNat 64 0x148) = a.extractLsb' 64 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x148 x12 (by norm_num) (by norm_num)]; simp
  set d0 := (a.extractLsb' 0 64).toNat with hd0
  set d1 := (a.extractLsb' 64 64).toNat with hd1
  have hd0' : a.extractLsb' 0 64 = BitVec.ofNat 64 d0 := by rw [hd0, BitVec.ofNat_toNat]; rfl
  have hd1' : a.extractLsb' 64 64 = BitVec.ofNat 64 d1 := by rw [hd1, BitVec.ofNat_toNat]; rfl
  have hd0l : d0 < 2 ^ 64 := BitVec.isLt _
  have hd1l : d1 < 2 ^ 64 := BitVec.isLt _
  rw [decodeDigits_answer]
  -- block 235: load the encoding, test bit 63 of d0
  have hs3 := symRun_sound blk235 codeAt_235 t2 pc2 (by simp only [blk235.res, rv_simp])
  have hc3 : blk235.res.cycles = 3 := rfl
  rw [hc3] at hs3
  set t3 := blk235.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk235.res]
  have r3 : RegsEq t2 t3 [.x1, .x2] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have y1 : t3.getReg .x1 = BitVec.ofNat 64 d0 := by
    simp only [ht3, blk235.res, rv_simp]; rw [w0, hd0']
  have y2 : t3.getReg .x2 = BitVec.ofNat 64 d1 := by
    simp only [ht3, blk235.res, rv_simp]; rw [w1, hd1']
  have fu3 : Frame u t3 encW := (((tframe.trans f1).trans f2).trans f3).mono (by
    intro x hx; simp only [encW] at hx ⊢; rcases hx with ((h | h) | h) | h
    · exact h
    · omega
    · omega
    · exact h.elim)
  have ru3 : RegsEq u t3 encRegs := ((((tregs.trans r1).trans (regsEq_writeHash _ _ [])).trans r3)).mono
    (by decide)
  have x36 : t3.getReg .x6 = BitVec.ofNat 64 c := by
    rw [r3.get .x6, ht2, writeHash_getReg, r1.get .x6, t6]
  have pc3 : t3.pc = if 2 ^ 63 ≤ d0 then pcOf 365 else pcOf 238 := by
    simp only [ht3, blk235.res, rv_simp, CmpOp.eval, w0, hd0', slt_zero_ofNat _ hd0l]
    by_cases h : 2 ^ 63 ≤ d0
    · rw [if_pos h, if_pos (by simpa using h)]
    · rw [if_neg h, if_neg (by simpa using h)]
  by_cases h0 : d0 < 2 ^ 63
  · have hs4 := symRun_sound blk238 codeAt_238 t3 (by rw [pc3, if_neg (by omega)])
      (by simp only [blk238.res, rv_simp])
    have hc4 : blk238.res.cycles = 1 := rfl
    rw [hc4] at hs4
    set t4 := blk238.res.toState t3 with ht4
    have f4 : Frame t3 t4 (fun _ => False) := by
      apply frame_toState; intro x hx hW; simp [blk238.res]
    have r4 : RegsEq t3 t4 [] := by
      intro r hr; rw [ht4, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    have fu4 : Frame u t4 encW := (fu3.trans f4).mono (by
      intro x hx; rcases hx with h | h; exact h; exact h.elim)
    have ru4 : RegsEq u t4 encRegs := (ru3.trans r4).mono (by decide)
    have pc4 : t4.pc = if 2 ^ 63 ≤ d1 then pcOf 365 else pcOf 239 := by
      simp only [ht4, blk238.res, rv_simp, CmpOp.eval, y2, slt_zero_ofNat _ hd1l]
      by_cases h : 2 ^ 63 ≤ d1
      · rw [if_pos h, if_pos (by simpa using h)]
      · rw [if_neg h, if_neg (by simpa using h)]
    by_cases h1 : d1 < 2 ^ 63
    · have hs5 := symRun_sound blk239 codeAt_239 t4 (by rw [pc4, if_neg (by omega)])
        (by simp only [blk239.res, rv_simp])
      have hc5 : blk239.res.cycles = 125 := rfl
      rw [hc5] at hs5
      set t5 := blk239.res.toState t4 with ht5
      have f5 : Frame t4 t5 (fun _ => False) := by
        apply frame_toState; intro x hx hW; simp [blk239.res]
      have r5 : RegsEq t4 t5 [.x3, .x28] := by
        intro r hr; rw [ht5, Result.toState_getReg]
        cases r <;> first | exact absurd (by decide) hr | rfl
      have fu5 : Frame u t5 encW := (fu4.trans f5).mono (by
        intro x hx; rcases hx with h | h; exact h; exact h.elim)
      have ru5 : RegsEq u t5 encRegs := (ru4.trans r5).mono (by decide)
      have pc5 := blk239_pc t4 d0 d1 h0 h1 (by rw [r4.get .x1, y1]) (by rw [r4.get .x2, y2])
      rw [if_pos ⟨h0, h1⟩]
      by_cases hsum : (digitsOfWord d0 ++ digitsOfWord d1).sum = 170
      · rw [if_pos hsum]
        have hs6 := symRun_sound blk364 codeAt_364 t5 (by rw [pc5, if_pos hsum])
          (by simp only [blk364.res, rv_simp])
        have hc6 : blk364.res.cycles = 1 := rfl
        rw [hc6] at hs6
        set t6 := blk364.res.toState t5 with ht6
        have f6 : Frame t5 t6 (fun _ => False) := by
          apply frame_toState; intro x hx hW; simp [blk364.res]
        have r6 : RegsEq t5 t6 [] := by
          intro r hr; rw [ht6, Result.toState_getReg]
          cases r <;> first | exact absurd (by decide) hr | rfl
        refine (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 (Sim.pure_steps hs6 ?_)))).mono
          (by omega) (fun _ _ h => h)
        refine ⟨by simp only [ht6, blk364.res, rv_simp], ?_, hc, ⟨d0, d1, h0, h1, rfl, hsum, ?_, ?_⟩,
          (ru5.trans r6).mono (by decide), (fu5.trans f6).mono (by
            intro x hx; rcases hx with h | h; exact h; exact h.elim)⟩
        · rw [r6.get .x6, r5.get .x6, r4.get .x6, x36]
        · rw [r6.get .x1, r5.get .x1, r4.get .x1, y1]
        · rw [r6.get .x2, r5.get .x2, r4.get .x2, y2]
      · rw [if_neg hsum]
        exact (Sim.steps hs3 (Sim.steps hs4 (Sim.steps hs5 (hrest t5 (by rw [pc5, if_neg hsum])
          (by rw [r5.get .x6, r4.get .x6, x36]) ru5 fu5)))).mono (by omega) (fun _ _ h => h)
    · rw [if_neg (by omega)]
      exact (Sim.steps hs3 (Sim.steps hs4 (hrest t4 (by rw [pc4, if_pos (by omega)])
        (by rw [r4.get .x6, x36]) ru4 fu4))).mono (by omega) (fun _ _ h => h)
  · rw [if_neg (by omega)]
    exact (Sim.steps hs3 (hrest t3 (by rw [pc3, if_pos (by omega)]) x36 ru3 fu3)).mono (by omega)
      (fun _ _ h => h)

/-- After a failing trial (instruction 365): `c += 1`, back to the loop or fail. -/
theorem encNext (u : MachineState) (hx7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20)) (c : Nat)
    (hc : c < 2 ^ 20) (t : MachineState) (tpc : t.pc = pcOf 365) (t6 : t.getReg .x6 = BitVec.ofNat 64 c)
    (tregs : RegsEq u t encRegs) (tframe : Frame u t encW) :
    ∃ t', Steps image t 2 2 t' ∧ (c + 1 < 2 ^ 20 → EncInv u (c + 1) t') ∧
      (c + 1 = 2 ^ 20 → t'.pc = pcOf 367) := by
  have hs := symRun_sound blk365 codeAt_365 t tpc (by simp only [blk365.res, rv_simp])
  have r1 : RegsEq t (blk365.res.toState t) [.x6] := by
    intro r hr; rw [Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have t7 : t.getReg .x7 = BitVec.ofNat 64 (2 ^ 20) := by rw [tregs.get .x7, hx7]
  refine ⟨_, hs, ?_, ?_⟩
  · intro h
    refine ⟨?_, ?_, h, (tregs.trans r1).mono (by decide), ?_⟩
    · simp only [blk365.res, rv_simp, t6, t7, ofNat_add_ofNat, ofNat_bne_ofNat]
      rw [if_pos (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]
    · simp only [blk365.res, rv_simp, t6, ofNat_add_ofNat]
    · intro x hx hW
      rw [Result.toState_getMem, show blk365.res.st.mem = [] from rfl, memEval_nil]; exact tframe x hx hW
  · intro h
    simp only [blk365.res, rv_simp, t6, t7, ofNat_add_ofNat, ofNat_bne_ofNat]
    rw [if_neg (by rw [bne_cond _ _ (by omega) (by omega)]; omega)]

/-- **Counter search** of a layer, from counter `c` with `fuel + 1` trials left. -/
theorem encLoop_sim (lay tau e : Nat) (M : Val) (u : MachineState) (hmem : EncMem lay tau e M u) :
    ∀ fuel c t, c + (fuel + 1) = 2 ^ 20 → EncInv u c t →
      Sim image t ((fuel + 1) * 144 + 2) (searchCounter lay tau e M c (fuel + 1)) (EncPost u) := by
  intro fuel
  induction fuel with
  | zero =>
    intro c t hc hinv
    rw [searchCounter_succ]
    refine (encTrial lay tau e M u hmem c t hinv _ 4 ?_).mono (by omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe
    obtain ⟨t'', hs, -, hfail⟩ := encNext u hmem.x7 c (by omega) t' tpc t6 tregs tframe
    have hs67 := symRun_sound blk367 codeAt_367 t'' (hfail (by omega)) (by simp only [blk367.res, rv_simp])
    have hc67 : blk367.res.cycles = 2 := rfl
    rw [hc67] at hs67
    have := Sim.steps hs (Sim.pure_steps (a := (none : Option (Nat × List Nat))) (Q := EncPost u) hs67
      ⟨by simp only [blk367.res, rv_simp], by simp only [blk367.res, rv_simp],
       by simp only [blk367.res, rv_simp]⟩)
    simpa [searchCounter] using this
  | succ f ih =>
    intro c t hc hinv
    rw [searchCounter_succ]
    refine (encTrial lay tau e M u hmem c t hinv _ (2 + ((f + 1) * 144 + 2)) ?_).mono
      (by ring_nf; omega) (fun _ _ h => h)
    intro t' tpc t6 tregs tframe
    obtain ⟨t'', hs, hinv', -⟩ := encNext u hmem.x7 c (by omega) t' tpc t6 tregs tframe
    exact Sim.steps hs (ih (c + 1) t'' (by omega) (hinv' (by omega)))

end SigGolfCandidate.Sign
