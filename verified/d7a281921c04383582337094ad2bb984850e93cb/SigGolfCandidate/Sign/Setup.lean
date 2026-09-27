import SigGolfCandidate.Sign.Digest
import SigGolfCandidate.Sign.Init

/-!
# `sign`: setup (instructions 0 .. 26)

`setup_run` : from the initial state, 27 steps reach `dig_loop` with the digest-search buffers
initialized (`DigMem`), `LIM = 2^20`, `CNT = 0`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

-- Memory effect of the setup block (kernel-checked with a variable state).
kernel_theorem blk0_pbS : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x6C0) 4 = t.readWords (BitVec.ofNat 64 0x80) 4
kernel_theorem blk0_rbS : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x640) 4 = t.readWords (BitVec.ofNat 64 0x80) 4
kernel_theorem blk0_rbM : ∀ t : MachineState,
    (blk0.res.toState t).readWords (BitVec.ofNat 64 0x660) 4 = t.readWords (BitVec.ofNat 64 0x40) 4
kernel_theorem blk0_db0 : ∀ t : MachineState,
    (blk0.res.toState t).getMem (BitVec.ofNat 64 0) = BitVec.ofNat 64 0xC01
theorem blk0_rb0 (t : MachineState) :
    lo32 ((blk0.res.toState t).getMem (BitVec.ofNat 64 0x620)) = BitVec.ofNat 32 0x701 := by
  simp only [blk0.res, rv_simp]; rw [if_neg (by decide)]
  simp only [if_true, ite_true, Nat.zero_div, lo32_replace0]; rfl

/-- Addresses written by the setup block. -/
def setupW (a : Nat) : Prop :=
  a = 0 ∨ a = 0x620 ∨ (0x640 ≤ a ∧ a < 0x680) ∨ (0x6C0 ≤ a ∧ a < 0x6E0)

theorem setup_run (sk : SecretKey) (cache : Cache) (m : Message) :
    ∃ u, Steps image (s0 sk cache m) 27 27 u ∧ DigMem (toList sk) (toList m) u ∧
      u.getReg .x5 = 0 ∧ u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20) ∧ DigInv u 0 u ∧
      u.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf (toList sk) ∧
      Frame (s0 sk cache m) u setupW := by
  set t := s0 sk cache m with ht
  have hs := symRun_sound blk0 codeAt_0 t (s0_pc sk cache m) (by simp only [blk0.res, rv_simp])
  set u := blk0.res.toState t with hu
  have f : Frame t u setupW := by
    apply frame_toState; intro x hx hW
    simp only [blk0.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    simp only [setupW] at hW
    omega
  have z : ∀ a, a % 8 = 0 → a + 8 < 2 ^ 64 → ¬ setupW a →
      (a + 8 ≤ 0x40 ∨ (0x60 ≤ a ∧ a + 8 ≤ 0x80) ∨ (0xA0 ≤ a ∧ a + 8 ≤ 0x44A0) ∨ 0x244A0 ≤ a) →
      u.getMem (BitVec.ofNat 64 a) = 0 := by
    intro a h8 ha hW hout
    rw [f.getMem (by omega) hW, s0_zero sk cache m a h8 ha hout]
  have hzw : ∀ a n, a % 8 = 0 → a + 8 * n + 8 < 2 ^ 64 → (∀ i < n, ¬ setupW (a + 8 * i)) →
      (∀ i < n, a + 8 * i + 8 ≤ 0x40 ∨ (0x60 ≤ a + 8 * i ∧ a + 8 * i + 8 ≤ 0x80) ∨
        (0xA0 ≤ a + 8 * i ∧ a + 8 * i + 8 ≤ 0x44A0) ∨ 0x244A0 ≤ a + 8 * i) →
      u.readWords (BitVec.ofNat 64 a) n = List.replicate n 0 := by
    intro a n h8 hb hW hout
    induction n generalizing a with
    | zero => rfl
    | succ n ih =>
      rw [readWords_ofNat_succ, z a h8 (by omega) (by simpa using hW 0 (by omega))
        (by simpa using hout 0 (by omega)), ih (a + 8) (by omega) (by omega)
        (fun i hi => by rw [show a + 8 + 8 * i = a + 8 * (i + 1) by ring]; exact hW _ (by omega))
        (fun i hi => by rw [show a + 8 + 8 * i = a + 8 * (i + 1) by ring]; exact hout _ (by omega))]
      rfl
  have hk : blk0.res.cycles = 27 := rfl
  have hk' : blk0.res.steps = 27 := rfl
  rw [hk, hk'] at hs
  have x5 : u.getReg .x5 = 0 := by
    simp only [hu, blk0.res, rv_simp]; exact s0_getReg sk cache m .x5 (by decide)
  have x7 : u.getReg .x7 = BitVec.ofNat 64 (2 ^ 20) := by simp only [hu, blk0.res, rv_simp]; rfl
  refine ⟨u, hs, ?_, x5, x7, ?_, ?_, f⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hu, blk0_rbS, s0_readWords_sk]
    · rw [hu, blk0_rbM, s0_readWords_msg]
    · exact hzw 0x680 4 (by norm_num) (by norm_num) (by intro i hi; simp only [setupW]; omega)
        (by intro i hi; omega)
    · exact hzw 0x628 3 (by norm_num) (by norm_num) (by intro i hi; simp only [setupW]; omega)
        (by intro i hi; omega)
    · rw [hu, blk0_rb0]
    · rw [readWords_ofNat_succ, hu, blk0_db0, ← hu,
        hzw 8 3 (by norm_num) (by norm_num) (by intro i hi; simp only [setupW]; omega)
          (by intro i hi; omega)]
      rfl
    · rw [f.readWords _ _ (by norm_num) (by intro i hi; simp only [setupW]; omega), s0_readWords_msg]
    · exact hzw 0x60 4 (by norm_num) (by norm_num) (by intro i hi; simp only [setupW]; omega)
        (by intro i hi; omega)
  · refine ⟨by simp only [hu, blk0.res, rv_simp], by simp only [hu, blk0.res, rv_simp], by norm_num,
      RegsEq.refl _ _, Frame.refl _ _, rfl⟩
  · rw [hu, blk0_pbS, s0_readWords_sk]

end SigGolfCandidate.Sign
