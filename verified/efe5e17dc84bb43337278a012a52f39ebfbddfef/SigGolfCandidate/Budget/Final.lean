import SigGolfCandidate.Budget.Bridge
import SigGolfCandidate.Keygen.Main
import SigGolfCandidate.Sign.Main
import SigGolfCandidate.Expand.Main

/-!
# Budget: the compression bounds of the submission

Keygen, sign and expand are discharged by their bytecode refinements
(`Keygen.keygen_run_counts`, `Sign.sign_refines`, `Expand.expand_refines_counts`: the expand
image refines `expandRef`, one compression, the digest query): `submission_compressionBounds`.
The forms with the expand refinement as a hypothesis are kept (`_of_counts`, `_of_expand`).
-/

namespace SigGolfCandidate.Budget
open SigGolfCandidate.Legacy SigGolfCandidate.Ref OracleComp

theorem submission_keygenRefinesCounts (sk : SecretKey) :
    RefinesCounts submission .keygen sk (keygenRef sk) :=
  ⟨some, Keygen.keygen_run_counts sk⟩

set_option maxRecDepth 100000 in
theorem submission_signRefinesCounts (sk : SecretKey) (cache : Cache) (m : Message) :
    RefinesCounts submission .sign (sk, cache, m) (signRef sk cache m) :=
  ⟨id, (Sign.sign_refines sk cache m).trans (id_map _).symm⟩

/-- **Compression bounds** of `SigGolfCandidate.submission`, given the expand refinement in the
`RefinesCounts` form. -/
theorem submission_compressionBounds_of_counts
    (hE : ∀ m pk (sig : Bytes 6100), RefinesCounts submission .expand (m, pk, sig) (expandRef m pk sig)) :
    submission.CompressionBounds :=
  submission_compressionBounds_of_counts' submission_keygenRefinesCounts
    submission_signRefinesCounts hE

/-- **Compression bounds** of `SigGolfCandidate.submission`, given the expand refinement in the
form of `Sign.sign_refines`. -/
theorem submission_compressionBounds_of_expand
    (hE : ∀ m pk (sig : Bytes 6100),
      (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .expand (m, pk, sig) =
        Sign.countBoth (expandRef m pk sig)) :
    submission.CompressionBounds :=
  submission_compressionBounds_of_counts fun m pk sig => ⟨id, (hE m pk sig).trans (id_map _).symm⟩

theorem submission_expandRefinesCounts (m : Message) (pk : PublicKey) (sig : Bytes 6100) :
    RefinesCounts submission .expand (m, pk, sig) (expandRef m pk sig) :=
  ⟨id, Expand.expand_refines_counts m pk sig⟩

/-- **Compression bounds** of `SigGolfCandidate.submission` (the organizer's
`Submission.CompressionBounds`), with no hypotheses. -/
theorem submission_compressionBounds : submission.CompressionBounds :=
  submission_compressionBounds_of_counts submission_expandRefinesCounts

end SigGolfCandidate.Budget
