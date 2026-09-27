import SigGolfCandidate.Verify.FoldRuns

namespace SigGolfCandidate.Verify

def layFoldOk (lay : Nat) : Bool :=
  foldCheck false 704 (4 - lay) 0 (heightL lay) (0x800 + (layBody lay + 672))
    (if lay = 0 then 0x180 else 0x120)

end SigGolfCandidate.Verify
