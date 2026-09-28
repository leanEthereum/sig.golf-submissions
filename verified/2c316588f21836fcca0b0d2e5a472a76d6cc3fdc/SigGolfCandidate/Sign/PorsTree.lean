import SigGolfCandidate.Sign.Sched
import SigGolfCandidate.Sign.Digest

/-!
# `sign`: `dig_ok` and the whole PORS tree (instructions 145 .. 237)

* `digok_run` : after an admissible digest (145), `rho` goes to the signature, `idx` to `x22`,
  the PB/CB/NB tweak headers (tags 8, 9, 10) are written and the leaf loop is set up (179).
* `porsTree_sim` : from 179, the machine refines `buildPorsTree S idx`: the levels in memory
  (`LevelsAt`-like facts at `lvBase l`), the secrets of the sorted opened leaves at `SIG + 16`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def digokW (a : Nat) : Prop :=
  a = 0x3300 ∨ a = 0x3308 ∨ a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ a = 0x1C0 ∨ a = 0x1C8

def digokRegs : List Reg := [.x1, .x2, .x3, .x9, .x13, .x17, .x18, .x19, .x20, .x22, .x29]

theorem idxExpr_eq' (A : Nat) :
    (BitVec.ofNat 64 A <<< ((30#64 : Word).toNat % 64)) >>> ((30#64 : Word).toNat % 64) =
      BitVec.ofNat 64 (A % 17179869184) := by
  rw [show (30#64 : Word).toNat % 64 = 30 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq]
  omega

theorem hdr_eq (c tag idx : Nat) (hc : c = 1 + 256 * tag) (htag : tag < 256) (hidx : idx < 2 ^ 34) :
    BitVec.ofNat 64 c ||| BitVec.ofNat 64 idx >>> ((32#64 : Word).toNat % 64) <<< ((24#64 : Word).toNat % 64) =
      twWord0 tag 0 idx 0 := by
  subst hc
  rw [show (32#64 : Word).toNat % 64 = 32 from rfl, show (24#64 : Word).toNat % 64 = 24 from rfl,
    ofNat_ushiftRight _ _ (by omega), ofNat_shiftLeft,
    ofNat_or_disjoint' (idx / 2 ^ 32 * 2 ^ 24) (1 + 256 * tag) 24 (by omega) (by omega) (by omega)]
  unfold twWord0
  congr 1
  omega

theorem blk145_mem (t : MachineState) (N ix : Nat) (hidx34 : ix < 2 ^ 34)
    (m160 : t.getMem (BitVec.ofNat 64 0x160) = BitVec.ofNat 64 (N % 2 ^ 64))
    (hidxE : (BitVec.ofNat 64 (N % 2 ^ 64) <<< ((30#64 : Word).toNat % 64)) >>> ((30#64 : Word).toNat % 64) =
      BitVec.ofNat 64 ix) :
    ∀ a : Nat, a < 2 ^ 64 → (blk145.res.toState t).getMem (BitVec.ofNat 64 a) =
      if a = 456 then replaceWord32 (t.getMem (BitVec.ofNat 64 456)) 0 (BitVec.ofNat 32 ix)
      else if a = 448 then twWord0 10 0 ix 0
      else if a = 200 then replaceWord32 (t.getMem (BitVec.ofNat 64 200)) 0 (BitVec.ofNat 32 ix)
      else if a = 192 then twWord0 9 0 ix 0
      else if a = 1704 then replaceWord32 (t.getMem (BitVec.ofNat 64 1704)) 0 (BitVec.ofNat 32 ix)
      else if a = 1696 then twWord0 8 0 ix 0
      else if a = 13064 then t.getMem (BitVec.ofNat 64 56)
      else if a = 13056 then t.getMem (BitVec.ofNat 64 48)
      else t.getMem (BitVec.ofNat 64 a) := by
  intro a ha
  simp only [blk145.res, rv_simp]
  rw [m160, hidxE, show (2561#64 : Word) = BitVec.ofNat 64 2561 from rfl,
    show (2305#64 : Word) = BitVec.ofNat 64 2305 from rfl, show (2049#64 : Word) = BitVec.ofNat 64 2049 from rfl,
    hdr_eq 2561 10 _ rfl (by norm_num) hidx34, hdr_eq 2305 9 _ rfl (by norm_num) hidx34,
    hdr_eq 2049 8 _ rfl (by norm_num) hidx34, truncate32_ofNat, Nat.zero_div]
  simp only [ofNat_eq_iff]
  rw [Nat.mod_eq_of_lt ha]
  simp only [Nat.reducePow, Nat.reduceMod]

theorem digok_run (S : List Byte) (rho : Val) (ans : BitVec 256) (L : List Nat) (t : MachineState)
    (tpc : t.pc = pcOf 145) (t5 : t.getReg .x5 = 0)
    (hdo : ∀ k < 4, t.getMem (BitVec.ofNat 64 (0x160 + 8 * k)) = dword ans k)
    (hlen : L.length = 15) (hsort : (L.map keyV).Pairwise (· < ·)) (hlt : ∀ v ∈ L.map keyV, v < 2 ^ 14)
    (hbound : KeysBound L) (hkeys : KeysAt t L) (hsent : t.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22))
    (hpbP : t.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0])
    (hpbS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S)
    (hcbP : t.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0])
    (hnbP : t.readWords (BitVec.ofNat 64 0x1D0) 2 = [0, 0])
    (hcbZ : t.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]) :
    ∃ tF, Steps image t 34 34 tF ∧ PLeafCtx S (idxOf ans.toNat) L tF ∧ PLevCtx (idxOf ans.toNat) tF ∧
      tF.pc = pcOf 179 ∧ tF.getReg .x9 = BitVec.ofNat 64 0 ∧ CapInv (L.map keyV) 0 [] tF 0 ∧
      tF.getReg .x22 = BitVec.ofNat 64 (idxOf ans.toNat) ∧
      tF.readWords (BitVec.ofNat 64 0x3300) 2 = t.readWords (BitVec.ofNat 64 0x30) 2 ∧
      RegsEq t tF digokRegs ∧ Frame t tF digokW := by
  set N := ans.toNat with hN
  have hNl : N < 2 ^ 256 := ans.isLt
  have m160 : t.getMem (BitVec.ofNat 64 0x160) = BitVec.ofNat 64 (N % 2 ^ 64) := by
    rw [show (0x160 : Nat) = 0x160 + 8 * 0 from rfl, hdo 0 (by norm_num)]
    apply BitVec.eq_of_toNat_eq; rw [dword_toNat]; simp [hN]
  have hidx : idxOf N = N % 2 ^ 34 := by unfold idxOf totalH; rfl
  have hidx34 : idxOf N < 2 ^ 34 := by rw [hidx]; omega
  have hidxE : (BitVec.ofNat 64 (N % 2 ^ 64) <<< ((30#64 : Word).toNat % 64)) >>> ((30#64 : Word).toNat % 64) =
      BitVec.ofNat 64 (idxOf N) := by
    rw [idxExpr_eq', hidx]; congr 1; omega
  have hs := symRun_sound blk145 codeAt_145 t tpc (by simp only [blk145.res, rv_simp])
  have hc : blk145.res.cycles = 34 := rfl
  have hk : blk145.res.steps = 34 := rfl
  rw [hc, hk] at hs
  set tF := blk145.res.toState t with htF
  have f : Frame t tF digokW := by
    apply frame_toState; intro x hx hW
    simp only [blk145.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    simp only [digokW] at hW
    omega
  have r : RegsEq t tF digokRegs := by
    intro r hr; rw [htF, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have x22 : tF.getReg .x22 = BitVec.ofNat 64 (idxOf N) := by
    simp only [htF, blk145.res, rv_simp, m160, hidxE]
  have memF := blk145_mem t N (idxOf N) hidx34 m160 hidxE
  have lo : ∀ a, a = 456 ∨ a = 200 ∨ a = 1704 → lo32 (tF.getMem (BitVec.ofNat 64 a)) = BitVec.ofNat 32 (idxOf N) := by
    intro a ha
    rcases ha with rfl | rfl | rfl <;> (rw [memF _ (by norm_num)]; simp)
  have hw : ∀ a n, a + 8 * n < 2 ^ 64 → (∀ i < n, ¬ digokW (a + 8 * i)) →
      tF.readWords (BitVec.ofNat 64 a) n = t.readWords (BitVec.ofNat 64 a) n :=
    fun a n h1 h2 => f.readWords a n h1 h2
  refine ⟨tF, hs, ⟨hidx34, hlen, hsort, hlt, hbound, fun i hi => ?_, ?_, ?_, lo 1704 (by simp), ?_, ?_, ?_,
    lo 200 (by simp), ?_, ?_, by rw [r.get .x5, t5], by simp only [htF, blk145.res, rv_simp] <;> rfl,
    by simp only [htF, blk145.res, rv_simp] <;> rfl⟩,
    ⟨by rw [r.get .x5, t5], ?_, lo 456 (by simp), ?_⟩,
    by simp only [htF, blk145.res, rv_simp], by simp only [htF, blk145.res, rv_simp] <;> rfl,
    ⟨by omega, fun q hq => absurd hq (by omega), fun _ => by simp, fun q hq => absurd hq (by omega),
      by simp only [htF, blk145.res, rv_simp] <;> rfl, by simp only [htF, blk145.res, rv_simp] <;> rfl, ?_⟩,
    x22, ?_, r, f⟩
  · rw [f.getMem (by omega) (by simp only [digokW]; omega)]; exact hkeys i hi
  · rw [f.getMem (by norm_num) (by simp only [digokW]; omega)]; exact hsent
  · rw [memF _ (by norm_num)]; simp
  · rw [hw _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hpbP]
  · rw [hw _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hpbS]
  · rw [memF _ (by norm_num)]; simp
  · rw [hw _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hcbP]
  · rw [hw _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hcbZ]
  · rw [memF _ (by norm_num)]; simp
  · rw [hw _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), hnbP]
  · simp only [htF, blk145.res, rv_simp]
    rw [hkeys 0 (by norm_num), show (8#64 : Word).toNat % 64 = 8 from rfl,
      ushr8 _ (by have := keysBound_getD hbound 0; omega)]
    unfold vsAt; rw [if_pos (by norm_num), vs_getD]
  · rw [readWords_ofNat_two, readWords_ofNat_two, memF _ (by norm_num), memF _ (by norm_num)]
    simp

end SigGolfCandidate.Sign
