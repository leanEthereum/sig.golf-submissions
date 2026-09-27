import SigGolfCandidate.SphincsSecurity.Statement
import SigGolfCandidate.SphincsSecurity.Completeness
import SigGolfCandidate.SphincsSecurity.Completeness.Assembly
import SigGolfCandidate.SphincsSecurity.Proof.Event.Assembly

namespace SphincsSecurity

/-- The event form of the 127-bit claim, for every adversary and with no query bound: the probability of
forging with at most `q` hash calls in the whole experiment is at most `q / 2^127`. -/
theorem security127_event : ∀ q : ℕ, 1 ≤ q → ∀ adversary : Security.Adversary,
    Pr[fun result => result.1 = true ∧ result.2 ≤ q | Security.experiment adversary] ≤ (q : ENNReal) / 2 ^ 127 := by
  intro q hq adversary
  have h := Security.security127_event q hq adversary
  have hcast : ((2 ^ 127 : Nat) : ENNReal) = (2 : ENNReal) ^ 127 := by norm_num
  rwa [hcast] at h

/-- The SPHINCS scheme has 127 bits of classical security (SUF-CMA in the ROM), as a consequence of the
event form. -/
theorem sphincs_has_127_bits_of_classical_security : SphincsSecurityStatement :=
  Security.hasClassicalSecurityBits_of_event 127 Security.security127_event

/-- A signature the SPHINCS signer produces verifies, under every hash function. -/
theorem sphincs_is_correct : SphincsCorrectnessStatement :=
  Completeness.correct

/-- One SPHINCS key signs every message successfully except with probability at most `2⁻²⁵⁶`. -/
theorem sphincs_is_complete : SphincsCompletenessStatement :=
  Completeness.complete

/-- Every master seed signs every message successfully except with probability at most `2⁻²⁵⁶`,
summed over all messages; the only randomness is the random oracle. -/
theorem sphincs_is_complete_for_every_seed : SphincsSeededCompletenessStatement :=
  Completeness.complete_seeded

/-! The build fails if the axiom footprint ever grows beyond Lean's three standard axioms, so a `sorry` or `native_decide` anywhere in the proof cannot go unnoticed. -/

/-- info: 'SphincsSecurity.security127_event' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms security127_event

/-- info: 'SphincsSecurity.sphincs_has_127_bits_of_classical_security' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincs_has_127_bits_of_classical_security

/-- info: 'SphincsSecurity.sphincs_is_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincs_is_correct

/-- info: 'SphincsSecurity.sphincs_is_complete' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincs_is_complete

/-- info: 'SphincsSecurity.sphincs_is_complete_for_every_seed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sphincs_is_complete_for_every_seed

end SphincsSecurity
