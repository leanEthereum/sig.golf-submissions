import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingSelectionCache
namespace SphincsSecurity.Concrete

/-- Every encoding input at any position, message and 32-bit counter. The signer only tries
counters below `C_max`, and the verifier rejects the others before hashing, but the set is taken over
every counter a signature can carry. -/
noncomputable def canonicalEncodingInputs (parameter : PublicParameter) : Finset HashInput :=
  Finset.univ.biUnion fun position : EncodingPosition =>
    (Finset.univ : Finset (Digest × Fin (2 ^ counterBits))).image fun pair =>
      encodingRetryInput parameter position pair.1 pair.2.val

attribute [local irreducible] canonicalEncodingInputs

theorem encodingRetryInput_mem_canonicalEncodingInputs_wide (parameter : PublicParameter)
    (position : EncodingPosition) (message : Digest) (counter : Fin (2 ^ counterBits)) :
    encodingRetryInput parameter position message counter.val ∈ canonicalEncodingInputs parameter := by
  classical
  rw [canonicalEncodingInputs, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  refine ⟨position, ?_⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact ⟨(message, counter), rfl⟩

theorem encodingRetryInput_mem_canonicalEncodingInputs (parameter : PublicParameter) (position : EncodingPosition)
    (message : Digest) (counter : Fin encodingAttemptLimit) :
    encodingRetryInput parameter position message counter.val ∈ canonicalEncodingInputs parameter :=
  encodingRetryInput_mem_canonicalEncodingInputs_wide parameter position message
    ⟨counter.val, lt_of_lt_of_le counter.isLt (by decide)⟩

end SphincsSecurity.Concrete
