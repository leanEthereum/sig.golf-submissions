import SigGolfCandidate.Final.Completeness
import SigGolfCandidate.Budget.Bridge

/-!
# The certificate

`certificate_of : Pending → SigGolf.Certificate submission claimedC`: every organizer requirement,
from the pending sign / verify / abstract-security statements (`Pending.lean`).

| field | proof |
|---|---|
| `admissible` | `submission_admissible` (kernel `decide`) |
| `termination` | expand exact (`expand_runWith`), keygen / sign / verify pending |
| `completeness` | `submission_complete` (this directory) |
| `compressionBounds` | `Budget.submission_compressionBounds_of_counts'` |
| `security` | `Equiv.submission_secure` |
| `verificationBound` | `honest_success_verify` + `VerifyCyclesStatement` (`verifyCycleBound + witnessCharge`) |
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Final
open SigGolf

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.submission SigGolf.Output SigGolf.Input

/-- **Termination**: expand is exact; keygen, sign and verify are pending. -/
theorem submission_terminates (hK : KeygenTerminationStatement) (hS : SignTerminationStatement)
    (hV : VerifyTerminationStatement) : submission.Terminates := by
  intro hash phase input
  cases phase with
  | keygen => exact hK hash input
  | sign =>
    obtain ⟨sk, cache, m⟩ := input
    exact hS hash sk cache m
  | expand =>
    obtain ⟨m, pk, σ⟩ := input
    show (submission.runWith hash .expand (m, pk, σ)).finished = true ∧
      (submission.runWith hash .expand (m, pk, σ)).cycles < CYCLE_LIMIT
    rw [Expand.expand_runWith]
    exact ⟨rfl, by show _ < 2 ^ 32; norm_num⟩
  | verify =>
    obtain ⟨m, pk, w⟩ := input
    exact hV hash m pk w

theorem witnessCycles_eq : witnessCycles submission.sizes.witness = witnessCharge := by
  rw [submission_sizes]
  rfl

/-- **Verification bound** `claimedC = verifyCycleBound + ⌈W / 256⌉`. -/
theorem submission_verificationBound (hC : VerifyCyclesStatement) :
    submission.VerificationBound claimedC := by
  intro hash sk m
  dsimp only
  intro h
  obtain ⟨⟨m', pk, w⟩, hacc, hcyc⟩ := honest_success_verify submission hash sk m h
  rw [hcyc, witnessCycles_eq]
  have := hC hash m' pk w hacc
  unfold claimedC
  omega

/-- **Compression bounds**, from the keygen and sign refinements (expand proved). -/
theorem submission_compressionBounds (hK : KeygenRefinementStatement)
    (hS : SignRefinementStatement) : submission.CompressionBounds := by
  refine Budget.submission_compressionBounds_of_counts' (fun sk => ⟨some, hK sk⟩)
    (fun sk cache m => ⟨id, ?_⟩) ?_
  · exact (hS sk cache m).trans (id_map _).symm
  · rintro ⟨m, pk, σ⟩
    refine ⟨Unit, (), fun _ => some (Ref.expandRef σ), ?_⟩
    rw [Expand.expand_run, map_pure, Sign.countBoth_pure, map_pure]

/-- **Security**, from (A) and the keygen / sign / verify refinements. -/
theorem submission_secure (hK : KeygenRefinementStatement) (hS : SignRefinementStatement)
    (hV : VerifyRefinementStatement) (hA : EventSecurityStatement) : submission.Secure :=
  Equiv.submission_secure (eventSecurity_of hA) (refinements hK hS hV)

/-- **The competition certificate**, from the pending component statements. -/
theorem certificate_of (P : Pending) : Certificate submission claimedC where
  admissible := submission_admissible
  termination := submission_terminates P.keygenTermination P.signTermination P.verifyTermination
  completeness := submission_complete P.keygenRefinement P.signRefinement P.verifyRefinement
  compressionBounds := submission_compressionBounds P.keygenRefinement P.signRefinement
  security := submission_secure P.keygenRefinement P.signRefinement P.verifyRefinement P.eventSecurity
  verificationBound := submission_verificationBound P.verifyCycles

end SigGolfCandidate.Final
