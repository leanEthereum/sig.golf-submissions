import SigGolfCandidate.Final.Main
import SigGolfCandidate.Keygen.Main
import SigGolfCandidate.Sign.Main
import SigGolfCandidate.Verify.Main
import SigGolfCandidate.SphincsSecurity

/-!
# Discharging the pending component statements

Each pending statement of `Pending.lean` is one of the component theorems.
-/

namespace SigGolfCandidate.Final
open SigGolfCandidate.Legacy

set_option allowUnsafeReducibility true in
attribute [local reducible] SigGolfCandidate.submission SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

theorem keygenRefinement : KeygenRefinementStatement := fun sk =>
  Keygen.keygen_run_counts sk

theorem keygenTermination : KeygenTerminationStatement := fun hash sk => by
  rw [Keygen.keygen_runWith]
  exact ⟨rfl, by show _ < 2 ^ 32; norm_num⟩

theorem signRefinement : SignRefinementStatement := fun sk cache m =>
  Sign.sign_refines sk cache m

theorem signTermination : SignTerminationStatement := fun hash sk cache m =>
  Sign.sign_terminates hash sk cache m

theorem verifyRefinement : VerifyRefinementStatement := fun m pk w =>
  Verify.verify_refines m pk w

theorem verifyTermination : VerifyTerminationStatement := fun hash m pk w =>
  ⟨(Verify.verify_terminates hash (m, pk, w)).1, (Verify.verify_terminates hash (m, pk, w)).2.2⟩

theorem verifyCycles : VerifyCyclesStatement := fun hash m pk w h =>
  Verify.verify_accept_cycles hash (m, pk, w) (by
    cases hv : (submission.runWith hash .verify (m, pk, w)).value with
    | none => simp [hv] at h
    | some u => cases u; rfl)

theorem eventSecurity : EventSecurityStatement := fun q hq adversary =>
  SphincsSecurity.security127_event q hq adversary

/-- The competition certificate for `SigGolfCandidate.submission` with `C = claimedC`. -/
theorem certificate : SigGolfCandidate.Legacy.Certificate submission claimedC :=
  certificate_of ⟨keygenRefinement, keygenTermination, signRefinement, signTermination,
    verifyRefinement, verifyTermination, verifyCycles, eventSecurity⟩

end SigGolfCandidate.Final
