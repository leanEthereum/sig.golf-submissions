import SigGolf
import SigGolfCandidate.Final.Discharge

/-!
# sig.golf solution: a SPHINCS+ variant

`S = W = 6404` bytes, `C = 11618` cycles. Layout (bytes): message 64, secret key 128,
public key 160, cache 17568, signature 9808, witness 2048.

The certificate is `SigGolfCandidate.Final.certificate`: the four RISC-V images are proved to refine
a byte-level reference (`SigGolfCandidate.Ref`), which is proved equal to the abstract SPHINCS+
scheme (`SigGolfCandidate.SphincsSecurity`) up to zero-padding of oracle inputs; the abstract
scheme's 127-bit event-form security, per-seed completeness and correctness are transported to the
organizer's game through `SigGolfCandidate.Bridge`.
-/

namespace SigGolf.Challenge

noncomputable def submission : SigGolf.Submission := SigGolfCandidate.submission

theorem signature_bytes : submission.sizes.signature = 6404 := rfl

theorem witness_bytes : submission.sizes.witness = 6404 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 17568, signature := 9808, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 11618 :=
  SigGolfCandidate.Final.certificate

end SigGolf.Challenge
