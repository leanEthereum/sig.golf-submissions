import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.DerivationTable
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.AlgorithmErasure

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

open Concrete
variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

def tableDigestLoop (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (message : Message) : Nat → Nat → m (Option (Randomness × Index × (IndexGroup → FtsLeaf)))
  | 0, _ => pure none
  | attempts + 1, trial => do
      let randomness := truncateHash (randomizers (message, BitVec.ofNat 32 trial))
      match ← Concrete.signAttempt secretKey message randomness with
      | some (index, leaves) => return some (randomness, index, leaves)
      | none => tableDigestLoop randomizers secretKey message attempts (trial + 1)

/-- The deterministic signer from tables: the randomizers from `randomizers`, then the table signer
after the digest loop. -/
def tableSign (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (message : Message) : OracleComp HashSpec (Option Signature) := do
  match ← tableDigestLoop randomizers secretKey message digestAttemptLimit 0 with
  | none => return none
  | some (randomness, index, leaves) => Concrete.signAfterDigest secretKey randomness index leaves

noncomputable def tableScheme (randomizers : RandomizerOutputs) : Scheme SphincsSecurity.SecretKey where
  keygen := Concrete.scheme.keygen
  sign := fun sk message => liftM (tableSign randomizers sk message : OracleComp HashSpec _)
  verify := Concrete.scheme.verify

theorem erases_deterministicDigestLoop (known : QueryCache HashSpec) (parameter : PublicParameter)
    (seed : MasterSeed) (root : Digest) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (hknown : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (message : Message) (attempts trial : Nat) :
    Erases known (signDigestLoop ⟨seed, parameter, root⟩ message attempts trial : OracleComp HashSpec _)
      (tableDigestLoop randomizers (tableKey parameter root outputs) message attempts trial) := by
  induction attempts generalizing trial with
  | zero => exact .pure _
  | succ attempts ih =>
      unfold signDigestLoop tableDigestLoop deriveRandomizer Concrete.oracleHash
      simp only [bind_assoc, pure_bind]
      apply Erases.skip _ _ (hknown (message, BitVec.ofNat 32 trial))
      change Erases known (Concrete.signAttempt (tableKey parameter root outputs) message
        (truncateHash (randomizers (message, BitVec.ofNat 32 trial))) >>= _)
          (Concrete.signAttempt (tableKey parameter root outputs) message
            (truncateHash (randomizers (message, BitVec.ofNat 32 trial))) >>= _)
      apply (Erases.refl known _).bind
      intro attempt
      cases attempt with
      | none => exact ih _
      | some result => exact .pure _

theorem erases_deterministicSign (known : QueryCache HashSpec) (parameter : PublicParameter)
    (seed : MasterSeed) (root : Digest) (outputs : SecretOutputs) (randomizers : RandomizerOutputs)
    (hsecrets : ∀ position, known (secretInputs parameter seed position) = some (outputs position))
    (hrandomizers : ∀ position, known (randomizerInputs parameter seed position) = some (randomizers position))
    (message : Message) :
    Erases known (sign ⟨seed, parameter, root⟩ message : OracleComp HashSpec _)
      (tableSign randomizers (tableKey parameter root outputs) message) := by
  unfold sign tableSign
  apply (erases_deterministicDigestLoop known parameter seed root outputs randomizers hrandomizers message _ _).bind
  intro attempt
  rcases attempt with _ | ⟨randomness, index, leaves⟩
  · exact .pure _
  · exact erases_signFrom_table known parameter seed outputs hsecrets root index randomness leaves

end SphincsSecurity.Seeded
