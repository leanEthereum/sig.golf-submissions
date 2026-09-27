import SigGolfCandidate.Final.Completeness
import SigGolfCandidate.Budget.Bridge

/-!
# The certificate

`certificate_of : Pending → SigGolf.Certificate submission 18388`: every organizer requirement,
from the pending sign / verify / abstract-security statements (`Pending.lean`).

| field | proof |
|---|---|
| `admissible` | `submission_admissible` (kernel `decide`) |
| `termination` | keygen / expand exact (`keygen_runWith`, `expand_runWith`), sign / verify pending |
| `completeness` | `submission_complete` (this directory) |
| `compressionBounds` | `Budget.submission_compressionBounds_of_counts` |
| `security` | `Equiv.submission_secure` (with `signatureLimit = 2^32 = LIFETIME`) |
| `verificationBound` | `honest_success_verify` + `VerifyCyclesStatement` (`18357 + 31`) |
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Final
open SigGolf

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.submission SigGolf.Output SigGolf.Input

/-- **Termination**: keygen and expand are exact; sign and verify are pending. -/
theorem submission_terminates (hS : SignTerminationStatement) (hV : VerifyTerminationStatement) :
    submission.Terminates := by
  intro hash phase input
  cases phase with
  | keygen =>
    show (submission.runWith hash .keygen input).finished = true ∧
      (submission.runWith hash .keygen input).cycles < CYCLE_LIMIT
    rw [Keygen.keygen_runWith]
    exact ⟨rfl, show (196282 : Nat) < 2 ^ 32 by norm_num⟩
  | sign =>
    obtain ⟨sk, cache, m⟩ := input
    exact hS hash sk cache m
  | expand =>
    obtain ⟨m, pk, σ⟩ := input
    show (submission.runWith hash .expand (m, pk, σ)).finished = true ∧
      (submission.runWith hash .expand (m, pk, σ)).cycles < CYCLE_LIMIT
    rw [Expand.expand_runWith]
    exact ⟨rfl, show (11711 : Nat) < 2 ^ 32 by norm_num⟩
  | verify =>
    obtain ⟨m, pk, w⟩ := input
    exact hV hash m pk w

theorem witnessCycles_eq : witnessCycles submission.sizes.witness = 31 := by
  rw [submission_sizes]
  rfl

/-- **Verification bound** `18388 = 18357 + ⌈7756 / 256⌉`. -/
theorem submission_verificationBound (hC : VerifyCyclesStatement) :
    submission.VerificationBound 18388 := by
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨⟨m', pk, w⟩, hacc, hcyc⟩ := honest_success_verify submission hash sk m h
  rw [hcyc, witnessCycles_eq]
  have := hC hash m' pk w hacc
  omega

/-- **Compression bounds**, from the sign refinement (keygen and expand proved). -/
theorem submission_compressionBounds (hS : SignRefinementStatement) :
    submission.CompressionBounds := by
  refine Budget.submission_compressionBounds_of_counts (fun sk cache m => ⟨id, ?_⟩) ?_
  · exact (hS sk cache m).trans (id_map _).symm
  · rintro ⟨m, pk, σ⟩
    refine ⟨Unit, (), fun _ => some (Ref.expandRef σ), ?_⟩
    rw [Expand.expand_run, map_pure, Sign.countBoth_pure, map_pure]

/-- The abstract signing budget covers the organizer lifetime (both `2^32`). -/
theorem lifetime_le : LIFETIME ≤ SphincsSecurity.signatureLimit := le_refl _

/-- **Security**, from (A) and the sign / verify refinements. -/
theorem submission_secure (hS : SignRefinementStatement) (hV : VerifyRefinementStatement)
    (hA : EventSecurityStatement) : submission.Secure :=
  Equiv.submission_secure (eventSecurity_of hA) lifetime_le (refinements hS hV)

/-- **The competition certificate**, from the pending component statements. -/
theorem certificate_of (P : Pending) : Certificate submission 18388 where
  admissible := submission_admissible
  termination := submission_terminates P.signTermination P.verifyTermination
  completeness := submission_complete P.signRefinement P.verifyRefinement
  compressionBounds := submission_compressionBounds P.signRefinement
  security := submission_secure P.signRefinement P.verifyRefinement P.eventSecurity
  verificationBound := submission_verificationBound P.verifyCycles

end SigGolfCandidate.Final
