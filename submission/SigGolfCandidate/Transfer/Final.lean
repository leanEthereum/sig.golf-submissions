import SigGolfCandidate.Transfer.Statements
import SigGolfCandidate.Transfer.Security
import SigGolfCandidate.Final.Discharge

/-!
# The certificate under the current contract

`submissionNew` is the submission as a value of the current contract's `SigGolf.Submission`:
the same sizes, layout and four images (`Transfer.currentOf`), computable. Its legacy view is
exactly `SigGolfCandidate.submission`, whose legacy certificate is `Final.certificate`; the
statements transfer through `Transfer.Statements` and `Transfer.Security`.
-/

namespace SigGolfCandidate
open Transfer

/-- The submission under the current contract. -/
def submissionNew : SigGolf.Submission := currentOf submission

theorem legacyOf_submissionNew : legacyOf submissionNew = submission :=
  legacyOf_currentOf submission

/-- The legacy certificate, restated for the legacy view of `submissionNew`. -/
theorem legacyCertificate : Legacy.Certificate (legacyOf submissionNew) Final.claimedC := by
  rw [legacyOf_submissionNew]
  exact Final.certificate

theorem submissionNew_runAgrees : RunAgrees submissionNew :=
  runAgrees_of_admissible submissionNew legacyCertificate.admissible

theorem certificateNew : SigGolf.Certificate submissionNew Final.claimedC where
  admission := admission_of_legacy submissionNew legacyCertificate.admissible
  completeness :=
    completeness_of_legacy submissionNew submissionNew_runAgrees legacyCertificate.completeness
  compressionBudgets := compressionBudgets_of_legacy submissionNew submissionNew_runAgrees
    legacyCertificate.compressionBounds
  verificationCycles := verificationCycles_of_legacy submissionNew submissionNew_runAgrees _
    legacyCertificate.verificationBound
  security := security_of_legacy submissionNew submissionNew_runAgrees legacyCertificate.security
  termination :=
    termination_of_legacy submissionNew submissionNew_runAgrees legacyCertificate.termination

end SigGolfCandidate
