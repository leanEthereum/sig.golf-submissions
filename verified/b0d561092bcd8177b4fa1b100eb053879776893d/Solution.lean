import SigGolf
import SigGolfCandidate.Final.Discharge

/-!
# sig.golf solution: SPHINCS+ with PORS+FP (forced-pruning single-tree few-time signature)

`S = 6100` bytes, `W = 6348` bytes, `K = 131072` bytes (cache), `C = 11907` cycles (verify bound
`11882` plus the witness charge `⌈6348 / 256⌉ = 25`). Layout (bytes): message 64, secret key 128,
public key 160, cache 19200, signature 13056, witness 2048.

The certificate is `SigGolfCandidate.Final.certificate`: the four RISC-V images are proved to refine
a byte-level reference (`SigGolfCandidate.Ref`), which is proved equal to the abstract SPHINCS+
scheme with PORS+FP (`SigGolfCandidate.SphincsSecurity`) up to the oracle input format; the abstract
scheme's 127-bit event-form security, per-seed completeness and correctness are transported to the
organizer's game through `SigGolfCandidate.Bridge`.
-/

namespace SigGolf.Challenge

noncomputable def submission : SigGolf.Submission := SigGolfCandidate.submission

theorem signature_bytes : submission.sizes.signature = 6100 := rfl

theorem witness_bytes : submission.sizes.witness = 6348 := rfl

theorem cache_bytes : submission.sizes.cache = 131072 := rfl

theorem layout_offsets : submission.layout =
  { message := 64, secretKey := 128, publicKey := 160,
    cache := 19200, signature := 13056, witness := 2048 } := rfl

theorem certificate : SigGolf.Certificate submission 11907 :=
  SigGolfCandidate.Final.certificate

end SigGolf.Challenge
