/-!
# Iteration parameters

The only numbers that change between optimization iterations of the submission: the proved
bound on verify's RISC-V cycles (every run, in particular every accepting run) and the claimed
`C = verifyCycleBound + ⌈W / 256⌉`.
-/

namespace SigGolfCandidate.Final

/-- Proved upper bound on the cycles of every verify run. -/
def verifyCycleBound : Nat := 11592

/-- The witness charge `⌈6404 / 256⌉`. -/
def witnessCharge : Nat := 26

/-- The claimed verification cost `C`. -/
def claimedC : Nat := verifyCycleBound + witnessCharge

end SigGolfCandidate.Final
