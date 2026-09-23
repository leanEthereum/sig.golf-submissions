import SigGolfCandidate.Hypertree.TightCertificate

namespace SigGolf.Challenge

noncomputable def submission : SigGolf.Submission := SigGolfCandidate.Hypertree.submission

theorem signature_bytes : submission.sizes.signature = 119632 := by rfl

theorem witness_bytes : submission.sizes.witness = 119632 := by rfl

theorem certificate : SigGolf.Certificate submission 5847036 :=
  SigGolfCandidate.Hypertree.TightCandidate.certificate

end SigGolf.Challenge
