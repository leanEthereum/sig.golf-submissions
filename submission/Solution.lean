import SigGolfCandidate.Hypertree.ChecksumCertificate

namespace SigGolf.Challenge

noncomputable def submission : SigGolf.Submission := SigGolfCandidate.Hypertree.submission

theorem signature_bytes : submission.sizes.signature = 119632 := by rfl

theorem witness_bytes : submission.sizes.witness = 119632 := by rfl

theorem certificate : SigGolf.Certificate submission 5617758 :=
  SigGolfCandidate.Hypertree.ChecksumCandidate.certificate

end SigGolf.Challenge
