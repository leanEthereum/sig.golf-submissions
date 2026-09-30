import SigGolfCandidate.Verify.LayerGood

/-! # All seven layers -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

theorem layer_pc_link (lay : Nat) (h1 : 1 ≤ lay) (h7 : lay < 7) :
    foldPc (layFoldPc lay) (layH lay - 1) + 9 + 1 = layerPc (lay - 1) := by
  interval_cases lay <;> decide

theorem foldEnd_layerIn (wl pk : List Byte) (lay idx : Nat) (h1 : 1 ≤ lay) (h7 : lay < 7)
    (u : MachineState) (hu : FoldEndL ⟨wl, pk, lay, idx⟩ u) (a : BitVec 256) :
    LayerIn ⟨wl, pk, lay - 1, idx⟩ (answerBytes 16 a) (writeHash u a) := by
  obtain ⟨s0, ⟨hG, hK, hF, hpc, -, -⟩, h22, hF0, hF8⟩ := hu
  have hdst : (layFC ⟨wl, pk, lay, idx⟩).dst = 0x120 := by simp [layFC]; omega
  have h12 : u.getReg .x12 = BitVec.ofNat 64 0x120 := by
    rw [← hdst]
    exact hK (.x12, _) (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))))
  refine ⟨Glob_writeHash hG a _ h12 (by decide), ?_, ?_, ?_, ?_, by simp, ?_, ?_, ?_⟩
  · intro p hp; rw [writeHash_getReg]; exact hK p (List.mem_append_left _ hp)
  · rw [writeHash_getReg, hF.1 .x22 (by simp [keepRegs])]; exact h22
  · rw [writeHash_at0 _ a _ h12 (by omega)]; exact (vw0_answer a).symm
  · rw [show (0x128 : Nat) = 0x120 + 8 from rfl, writeHash_at8 _ a _ h12 (by omega)]
    exact (vw1_answer a).symm
  · rw [writeHash_frame _ a _ _ h12 (by omega) (by omega) (by omega), hF.2 _ (by omega) (by omega)]
    exact hF0
  · rw [writeHash_frame _ a _ _ h12 (by omega) (by omega) (by omega), hF.2 _ (by omega) (by omega)]
    exact hF8
  · rw [writeHash_pc, hpc, pcOf_add4]
    simp only [layFC]
    rw [layer_pc_link lay h1 h7]

end SigGolfCandidate.Verify
