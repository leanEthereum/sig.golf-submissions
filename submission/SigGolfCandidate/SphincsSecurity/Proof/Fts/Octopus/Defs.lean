import Mathlib.Data.List.Sort

/-!
# PORS+FP admissibility: definitions

Computable definitions mirroring `work/py-pors/ref.py` (`bitlen`, `octopus_size`, `admissible`,
`split_digest`) and the Ref layer (`SigGolfCandidate.Ref.bitLen`, `octopusSize`, `sortLeaves`,
`leafOf`, `leavesOf`, `admissible`, same bodies), plus the truncated list DP that the kernel
evaluates (`step`, `rowsAgree`).
-/

namespace SphincsSecurity.Octopus

/-- Python's `int.bit_length`. -/
def bitLen (x : Nat) : Nat := if x = 0 then 0 else Nat.log2 x + 1

/-- `sum_{s ≥ 1} bitlen(vs[s-1] xor vs[s])`. -/
def xorSum (vs : List Nat) : Nat := (List.zipWith (fun a b => bitLen (a ^^^ b)) vs vs.tail).sum

/-- Octopus size in a tree of height `H`: `H + sum - 2 (|vs| - 1)`, written as
`H + 2 + sum - 2 |vs|` (as in the Ref layer). -/
def octH (H : Nat) (vs : List Nat) : Nat := H + 2 + xorSum vs - 2 * vs.length

/-- `ref.octopus_size` (height 14), literally the Ref layer's body. -/
def octopusSize (vs : List Nat) : Nat :=
  14 + 2 + (List.zipWith (fun a b => bitLen (a ^^^ b)) vs vs.tail).sum - 2 * vs.length

theorem octopusSize_eq (vs : List Nat) : octopusSize vs = octH 14 vs := rfl

/-- `sorted(v)`. -/
def sortLeaves (v : List Nat) : List Nat := v.insertionSort (· ≤ ·)

/-- Leaf index `r` of a digest `N`: `N / 2^(34 + 14 r) mod 2^14`. -/
def leafOf (N r : Nat) : Nat := N / 2 ^ (34 + 14 * r) % 2 ^ 14

/-- The 15 leaf indices of a digest. -/
def leavesOf (N : Nat) : List Nat := (List.range 15).map (leafOf N)

/-- The signer's admissibility test on a digest (`ref.admissible`). -/
def admissible (N : Nat) : Bool :=
  decide (leavesOf N).Nodup && decide (octopusSize (sortLeaves (leavesOf N)) ≤ 120)

/-- The exact number of admissible 15-subsets of `[0, 2^14)` (`admit.py`). -/
def Nadm : Nat := 1447671288676927167101817092258542719267237511168

/-! ## The packed DP (kernel-evaluated)

The generating polynomial `Q_H = sum_{S ≠ ∅} X^|S| y^oc(S)` (`Split.lean`) satisfies
`Q_0 = X` and `Q_{H+1} = 2 y Q_H + Q_H^2`. With `y = 2^B` every coefficient of `X^j` is one
natural number (the octopus-size distribution packed in base `2^B`); modulo `M = y^121` only the
octopus sizes `≤ 120` survive, and modulo `y - 1` the packed digits add up. `pstep` is one level
on the rows `j = 0..K`, reduced modulo `M`. -/

/-- One level: row `j` of `2 y Q + Q^2`, modulo `M`. -/
def pstep (K y M : Nat) (T : List Nat) : List Nat :=
  (List.range (K + 1)).map fun j =>
    (2 * y * T.getD j 0 + ((List.range (j + 1)).map fun i => T.getD i 0 * T.getD (j - i) 0).sum) % M

/-- `k` levels. -/
def piter (K y M : Nat) : Nat → List Nat → List Nat
  | 0, T => T
  | k + 1, T => piter K y M k (pstep K y M T)

/-- Digit width of the packing. -/
def pB : Nat := 224

/-- The packed count: row 15 after 14 levels, digits summed (mod `2^B - 1`). -/
def packedCount : Nat := ((piter 15 (2 ^ pB) (2 ^ (pB * 121)) 14 [0, 1]).getD 15 0) % (2 ^ pB - 1)

/-- Kernel evaluation (about 1 s). -/
theorem packedCount_eq : packedCount = Nadm := by decide +kernel

end SphincsSecurity.Octopus
