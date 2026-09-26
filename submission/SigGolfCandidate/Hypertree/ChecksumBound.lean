import SigGolfCandidate.Hypertree.TightCertificate

/-!
If q is the checksum, the 43 message chains take q remaining hashes and
its three checksum chains take 21 minus the sum of q's base-8 digits.
For q ≤ 301 the combined work is at most 308 hashes, rather than the
independent-chain bound 46 × 7 = 322. The argument below is symbolic
natural-number arithmetic; it does not enumerate digests or oracles.
-/

namespace SigGolfCandidate.Hypertree.ChecksumVerifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying KeygenVerifyCount
set_option maxRecDepth 4096

/-- The first 43 remaining chain lengths are exactly the WOTS checksum. -/
theorem chainPrefix_message (message : Reference.Digest) :
    chainPrefix message 43 = Reference.checksum message := by
  unfold chainPrefix Reference.checksum
  rw [← Fin.sum_univ_eq_sum_range]
  have terms : (∑ i : Fin 43,
      (7 - (Reference.digit message ⟨i.val % 46, Nat.mod_lt _ (by decide)⟩).val)) =
      ∑ i : Fin 43, (7 - Reference.messageDigit message i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp [Reference.digit, Reference.messageDigit, Nat.mod_eq_of_lt (by omega : i.val < 46), i.isLt]
  rw [terms, Finset.sum_tsub_distrib]
  · simp
  · intro i _
    unfold Reference.messageDigit
    omega

/-- The checksum prevents all 46 chain lengths from attaining their individual maxima. -/
theorem chainPrefix_bound (message : Reference.Digest) : chainPrefix message 46 ≤ 308 := by
  have bound : Reference.checksum message ≤ 301 := Nat.sub_le _ _
  rw [chainPrefix_succ message 45 (by decide),
    chainPrefix_succ message 44 (by decide),
    chainPrefix_succ message 43 (by decide), chainPrefix_message]
  norm_num [Reference.digit]
  omega

end SigGolfCandidate.Hypertree.ChecksumVerifying
