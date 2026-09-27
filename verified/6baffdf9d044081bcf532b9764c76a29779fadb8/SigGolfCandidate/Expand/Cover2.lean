-- Kernel check of the witness permutation, positions 4720 .. 7079 (one file per chunk:
-- kernel memory accumulates within a file; chunks are import-chained).
import SigGolfCandidate.Expand.Cover1

namespace SigGolfCandidate.Expand

theorem cover_check2 : (List.range' 4720 2360).all coverOk = true := by
  decide +kernel

end SigGolfCandidate.Expand
