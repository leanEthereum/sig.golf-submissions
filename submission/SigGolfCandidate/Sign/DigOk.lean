import SigGolfCandidate.Sign.Fors

/-!
# `sign`: `dig_ok` (instructions 46 .. 111)

`digok_run` : after an admissible digest, `rho` goes to the signature, `idx` to `s6`, the `u_k` to
`US`, and the FORS tweak words are set up (`ForsCtx`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- The `u_k` dwords as the machine computes them from the digest dwords. -/
def ukList (w0 w1 w2 : Word) : List Word :=
  [(w0 >>> 34) &&& 1023, (w0 >>> 44) &&& 1023, w0 >>> 54, w1 &&& 1023, (w1 >>> 10) &&& 1023,
   (w1 >>> 20) &&& 1023, (w1 >>> 30) &&& 1023, (w1 >>> 40) &&& 1023, (w1 >>> 50) &&& 1023,
   ((w2 &&& 63) <<< 4) + (w1 >>> 60), (w2 >>> 6) &&& 1023, (w2 >>> 16) &&& 1023,
   (w2 >>> 26) &&& 1023, (w2 >>> 36) &&& 1023]

-- Memory effect of `dig_ok` (kernel-checked with a variable state).
kernel_theorem blk90_us : ∀ t : MachineState,
    (blk90.res.toState t).readWords (BitVec.ofNat 64 0x710) 14 =
      ukList (t.getMem (BitVec.ofNat 64 0x160)) (t.getMem (BitVec.ofNat 64 0x168))
        (t.getMem (BitVec.ofNat 64 0x170))
kernel_theorem blk90_sig : ∀ t : MachineState,
    (blk90.res.toState t).readWords (BitVec.ofNat 64 0x2650) 2 = t.readWords (BitVec.ofNat 64 0x30) 2

theorem ukList_eq (A : Nat) (hA : A < 2 ^ 256) :
    ukList (BitVec.ofNat 64 (A % 2 ^ 64)) (BitVec.ofNat 64 (A / 2 ^ 64 % 2 ^ 64))
      (BitVec.ofNat 64 (A / 2 ^ 128 % 2 ^ 64)) =
      (List.range 14).map (fun k => BitVec.ofNat 64 (uOf (A % 2 ^ 184) k)) := by
  simp only [ukList, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.cons.injEq, and_true]
  simp only [uOf, totalH, ftsA]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_add,
      BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, Nat.reducePow, Nat.reduceMul,
      Nat.reduceAdd, show (1023 : Word).toNat = 1023 from rfl, show (63 : Word).toNat = 63 from rfl]
    first
      | omega
      | (rw [show (1023 : Nat) = 2 ^ 10 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega)
      | (rw [show (63 : Nat) = 2 ^ 6 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]; omega)

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def digokW (a : Nat) : Prop :=
  a = 0x2650 ∨ a = 0x2658 ∨ (0x710 ≤ a ∧ a < 0x780) ∨ a = 0x6A8 ∨ a = 0xC8 ∨ a = 0x1C8 ∨ a = 0x228 ∨
    a = 0x6A0 ∨ a = 0xC0

def digokRegs : List Reg := [.x1, .x2, .x3, .x4, .x8, .x14, .x18, .x19, .x22, .x28, .x29]

theorem idxExpr_eq (A : Nat) :
    (BitVec.ofNat 64 (A % 18446744073709551616) <<< 30) >>> 30 = BitVec.ofNat 64 (A % 17179869184) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem digok_run (S : List Byte) (rho : Val) (ans : BitVec 256) (t : MachineState)
    (tpc : t.pc = pcOf 90) (t5 : t.getReg .x5 = 0)
    (hd : t.readWords (BitVec.ofNat 64 0x160) 3 =
      [ans.extractLsb' 0 64, ans.extractLsb' 64 64, ans.extractLsb' 128 64])
    (hpbP : t.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0])
    (hpbS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S)
    (hcbP : t.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0])
    (hnbP : t.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0])
    (hcbZ : t.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]) :
    ∃ tF, Steps image t 66 66 tF ∧ ForsCtx S (idxOf (ans.toNat % 2 ^ 184)) (ans.toNat % 2 ^ 184) tF ∧
      tF.pc = pcOf 156 ∧ tF.getReg .x8 = BitVec.ofNat 64 0 ∧
      tF.getReg .x18 = BitVec.ofNat 64 0x2650 ∧
      tF.getReg .x22 = BitVec.ofNat 64 (idxOf (ans.toNat % 2 ^ 184)) ∧
      tF.readWords (BitVec.ofNat 64 0x2650) 2 = t.readWords (BitVec.ofNat 64 0x30) 2 ∧
      lo32 (tF.getMem (BitVec.ofNat 64 0x228)) = BitVec.ofNat 32 (idxOf (ans.toNat % 2 ^ 184)) ∧
      hi32 (tF.getMem (BitVec.ofNat 64 0x228)) = hi32 (t.getMem (BitVec.ofNat 64 0x228)) ∧
      RegsEq t tF digokRegs ∧ Frame t tF digokW := by
  set A := ans.toNat with hA
  have hAl : A < 2 ^ 256 := ans.isLt
  have e0 : ans.extractLsb' 0 64 = BitVec.ofNat 64 (A % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq; simp [hA]
  have e1 : ans.extractLsb' 64 64 = BitVec.ofNat 64 (A / 2 ^ 64 % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq; simp [hA, Nat.shiftRight_eq_div_pow]
  have e2 : ans.extractLsb' 128 64 = BitVec.ofNat 64 (A / 2 ^ 128 % 2 ^ 64) := by
    apply BitVec.eq_of_toNat_eq; simp [hA, Nat.shiftRight_eq_div_pow]
  have m160 : t.getMem (BitVec.ofNat 64 0x160) = BitVec.ofNat 64 (A % 2 ^ 64) := by
    have := getMem_of_readWords t 3 0x160 0 _ hd (by norm_num); simpa [e0] using this
  have m168 : t.getMem (BitVec.ofNat 64 0x168) = BitVec.ofNat 64 (A / 2 ^ 64 % 2 ^ 64) := by
    have := getMem_of_readWords t 3 0x160 1 _ hd (by norm_num); simpa [e1] using this
  have m170 : t.getMem (BitVec.ofNat 64 0x170) = BitVec.ofNat 64 (A / 2 ^ 128 % 2 ^ 64) := by
    have := getMem_of_readWords t 3 0x160 2 _ hd (by norm_num); simpa [e2] using this
  have hidx : idxOf (A % 2 ^ 184) = A % 2 ^ 34 := by unfold idxOf totalH; omega
  have hidx' : idxOf (A % 24519928653854221733733552434404946937899825954937634816) = A % 17179869184 := by
    unfold idxOf totalH; omega
  have hs := symRun_sound blk90 codeAt_90 t tpc (by simp only [blk90.res, rv_simp])
  have hc : blk90.res.cycles = 66 := rfl
  have hk : blk90.res.steps = 66 := rfl
  rw [hc, hk] at hs
  set tF := blk90.res.toState t with htF
  have f : Frame t tF digokW := by
    apply frame_toState; intro x hx hW
    simp only [blk90.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    simp only [digokW] at hW
    omega
  have r : RegsEq t tF digokRegs := by
    intro r hr; rw [htF, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have x22 : tF.getReg .x22 = BitVec.ofNat 64 (A % 2 ^ 34) := by
    simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      idxExpr_eq]
  have hus := blk90_us t
  rw [m160, m168, m170, ukList_eq A hAl] at hus
  refine ⟨tF, hs, ?_, by simp only [htF, blk90.res, rv_simp], by simp only [htF, blk90.res, rv_simp],
    by simp only [htF, blk90.res, rv_simp], by rw [x22, hidx], blk90_sig t, ?_, ?_, r, f⟩
  · refine ⟨by rw [r.get .x5, t5], ?_, by simp only [htF, blk90.res, rv_simp], ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
        idxExpr_eq]
      unfold fwVal; simp only [Nat.reducePow, hidx']
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_add, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
        Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq, show (2049 : Word).toNat = 2049 from rfl]
      omega
    · intro k hk
      rw [getMem_of_readWords tF 14 0x710 k _ hus hk]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk]; rfl
    · simp only [htF, blk90.res, rv_simp]; simp
    · simp only [htF, blk90.res, rv_simp]; simp
    · simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
        idxExpr_eq]
      simp only [if_true, ite_true, lo32_replace0, truncate32_ofNat, hidx', Nat.zero_div, ofNat_eq_iff,
        Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, if_false, ite_false]
    · simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
        idxExpr_eq]
      simp only [if_true, ite_true, lo32_replace0, truncate32_ofNat, hidx', Nat.zero_div, ofNat_eq_iff,
        Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, if_false, ite_false]
    · simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
        idxExpr_eq]
      simp only [if_true, ite_true, lo32_replace0, truncate32_ofNat, hidx', Nat.zero_div, ofNat_eq_iff,
        Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, if_false, ite_false]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hpbP]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hpbS]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hcbP]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hnbP]
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hcbZ]
  · simp only [htF, blk90.res, rv_simp, m160, BitVec.toNat_ofNat, Nat.reduceMod, Nat.reducePow,
      idxExpr_eq]
    simp only [if_true, ite_true, lo32_replace0, truncate32_ofNat, hidx', Nat.zero_div, ofNat_eq_iff,
        Nat.reducePow, Nat.reduceMod, Nat.reduceEqDiff, if_false, ite_false]
  · simp only [htF, blk90.res, rv_simp]; simp

end SigGolfCandidate.Sign
