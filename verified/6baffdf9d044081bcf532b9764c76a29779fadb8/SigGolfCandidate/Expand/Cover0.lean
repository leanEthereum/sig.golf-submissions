-- Kernel check of the witness permutation, positions 0 .. 2359 (one file per chunk:
-- kernel memory accumulates within a file; chunks are import-chained).
import SigGolfCandidate.Expand.Stages

namespace SigGolfCandidate.Expand
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Mem

/-- Some copy covers witness byte `i` and reads its `witnessSrc`. -/
def coverOk (i : Nat) : Bool := copies.any (fun c =>
  decide (c.2.1 ≤ 0x800 + i) && decide (0x800 + i < c.2.1 + 4 * c.2.2) &&
    (0x800 + i - c.2.1 + c.1 == 0x2650 + Ref.witnessSrc i))

theorem cover_check0 : (List.range' 0 2360).all coverOk = true := by
  decide +kernel

end SigGolfCandidate.Expand
