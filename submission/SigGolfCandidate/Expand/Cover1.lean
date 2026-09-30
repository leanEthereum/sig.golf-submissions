-- Kernel check of the witness permutation, positions 2360 .. 4719 (one file per chunk:
-- kernel memory accumulates within a file; chunks are import-chained).
import SigGolfCandidate.Expand.Cover0

namespace SigGolfCandidate.Expand

theorem cover_check1 : (List.range' 2360 2360).all coverOk = true := by
  decide +kernel

end SigGolfCandidate.Expand
