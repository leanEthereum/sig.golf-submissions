import SigGolfCandidate.Expand.Cover2

/-!
# `expand`: every witness byte is written by the copy that reads its `witnessSrc`

Kernel check over all `7080` witness positions (`Cover0..2`, `Ref.witnessSrc` evaluated by the
kernel).
-/

namespace SigGolfCandidate.Expand
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Mem

theorem coverOk_of_lt (i : Nat) (hi : i < 7080) : coverOk i = true := by
  by_cases h1 : i < 2360
  · exact List.all_eq_true.mp cover_check0 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  by_cases h2 : i < 4720
  · exact List.all_eq_true.mp cover_check1 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)
  · exact List.all_eq_true.mp cover_check2 i (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

/-- Every witness byte is the destination of exactly the copy that reads its `witnessSrc`. -/
theorem copies_cover (i : Nat) (hi : i < 7080) :
    ∃ c ∈ copies, c.2.1 ≤ 0x800 + i ∧ 0x800 + i < c.2.1 + 4 * c.2.2 ∧
      0x800 + i - c.2.1 + c.1 = 0x2650 + Ref.witnessSrc i := by
  obtain ⟨c, hc, h'⟩ := List.any_eq_true.mp (coverOk_of_lt i hi)
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h'
  exact ⟨c, hc, h'.1.1, h'.1.2, h'.2⟩

end SigGolfCandidate.Expand
