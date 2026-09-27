import SigGolfCandidate.Verify.FoldRuns

namespace SigGolfCandidate.Verify

def forsFoldOk (k : Nat) : Bool :=
  foldCheck (forsFoldTab.getD k 0) 10 (0x800 + 32 + 176 * k) (0x240 + 16 * k)

def layFoldOk (lay : Nat) : Bool :=
  foldCheck (layFoldTab.getD lay 0) (if lay = 6 then 4 else 5) (0x800 + (2480 + 752 * lay + 672))
    (if lay = 0 then 0x180 else 0x120)

end SigGolfCandidate.Verify
