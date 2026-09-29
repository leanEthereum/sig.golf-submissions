import SigGolfCandidate.SphincsSecurity.Scheme
import Mathlib.Tactic.IrreducibleDef

/-!
# Few-time signature parameters

The oracle calls of an honest few-time key and opening, and the constants the few-time analysis hands to the rest of the proof. They are sealed: the rest of the proof carries them symbolically, and only the few-time closers and the closing arithmetic use their values.
-/

namespace SphincsSecurity.Concrete

open ENNReal

/-- The signer's PORS tree, built once: its `2^14` leaves and `2^14 - 1` nodes. -/
irreducible_def ftsOpenHashCost : Nat := 2 ^ (ftsTreeHeight + 1) - 1

/-- A PORS public key (the tree root): every leaf and node of the tree. -/
irreducible_def ftsKeyHashCost : Nat := 2 ^ (ftsTreeHeight + 1) - 1

theorem two_pow_ftsTreeHeight_le_ftsOpenHashCost : 2 ^ ftsTreeHeight ≤ ftsOpenHashCost := by
  rw [ftsOpenHashCost_def]
  decide

theorem ftsOpenHashCost_le_digestAttemptLimit : ftsOpenHashCost ≤ digestAttemptLimit := by
  rw [ftsOpenHashCost_def]
  decide

/-- The length of the uniform proposal word that both budget routes price certificates against. -/
irreducible_def fixedProposalLength : Nat := 6455033870

/-- How far a proposal-word prefix may run ahead of its expected length before the monitor stops. -/
irreducible_def proposalPrefixSlack : Nat := 2 ^ 23

/-- Per query, the expected excess of the full certificate price over the price of one fresh digest. -/
noncomputable irreducible_def fullCertificateExcessRate : ENNReal := 1 / 2 ^ 144

/-- Per query, the average price of a near certificate that omits one given digest slot. -/
noncomputable irreducible_def nearCertificatePrice : ENNReal := ((1241 : ENNReal) / 15) / (2 ^ 128 : Nat)

/-- The probability that a proposal-word prefix ever runs past its slack. -/
noncomputable irreducible_def proposalPrefixExceptionBound : ENNReal := (2 ^ 700 : ENNReal)⁻¹

end SphincsSecurity.Concrete
