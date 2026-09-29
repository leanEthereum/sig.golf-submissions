import SigGolfCandidate.Hypertree.PreludeCertificate
namespace SigGolf.Challenge
noncomputable def submission : SigGolf.Submission :=
  SigGolfCandidate.Hypertree.Signing.Prelude.preludeSubmission
theorem signature_bytes : submission.sizes.signature = 119632 := by rfl
theorem witness_bytes : submission.sizes.witness = 119632 := by rfl
theorem layout_offsets : submission.layout =
  { message := 0, secretKey := 32, publicKey := 64, cache := 96,
    signature := 131168, witness := 250800 } := by rfl
theorem certificate : SigGolf.Certificate submission 1591711 :=
  SigGolfCandidate.Hypertree.PreludeCandidate.certificate
end SigGolf.Challenge
