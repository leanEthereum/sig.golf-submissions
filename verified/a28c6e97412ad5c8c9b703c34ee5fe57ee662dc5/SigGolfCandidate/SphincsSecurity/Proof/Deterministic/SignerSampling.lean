import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.TrialSampling

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {State : Type}

attribute [local irreducible] tableDigestLoop Concrete.signDigestLoop

/-- What either signer does after its digest loop. -/
def signatureAfterTrial (secretKey : SphincsSecurity.SecretKey) (attempt : TrialResult) : OracleComp HashSpec (Option Signature) :=
  match attempt with
  | none => pure none
  | some (randomness, index, leaves) => Concrete.signAfterDigest secretKey randomness index leaves

theorem tableSign_eq_finish (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey) (message : Message) :
    (tableSign randomizers secretKey message : OracleComp HashSpec (Option Signature)) =
      (tableDigestLoop randomizers secretKey message digestAttemptLimit 0 >>= signatureAfterTrial secretKey) := by
  unfold tableSign
  apply bind_congr
  intro attempt
  rcases attempt with _ | ⟨randomness, index, leaves⟩ <;> rfl

theorem sign_eq_finish (secretKey : SphincsSecurity.SecretKey) (message : Message) :
    Concrete.sign secretKey message = (Concrete.signDigestLoop digestAttemptLimit secretKey message >>= fun attempt =>
      (liftM (signatureAfterTrial secretKey attempt) : OracleComp OracleWorld (Option Signature))) := by
  rw [Concrete.sign_eq]
  apply bind_congr
  intro attempt
  rcases attempt with _ | ⟨randomness, index, leaves⟩
  · simp only [signatureAfterTrial, liftM_pure]
  · rfl

attribute [local irreducible] signatureAfterTrial

theorem evalDist_tableSign (hash : QueryImpl HashSpec (StateT State ProbComp))
    (secretKey : SphincsSecurity.SecretKey) (message : Message) (state : State) :
    𝒮[do
      let tape ← sampleTrialTape
      (simulateQ (worldHandler hash) (liftM (tableSign (fun position => tape position.2)
        secretKey message : OracleComp HashSpec (Option Signature)) : OracleComp OracleWorld (Option Signature))).run state] =
      𝒮[(simulateQ (worldHandler hash) (Concrete.sign secretKey message)).run state] := by
  simp_rw [tableSign_eq_finish, sign_eq_finish, liftM_bind, simulateQ_bind, StateT.run_bind]
  have h := evalDist_tableDigestLoop hash secretKey message digestAttemptLimit 0 (by decide) state
  have heq := congrArg (fun distribution => distribution >>= fun result : TrialResult × State =>
    𝒮[(simulateQ (worldHandler hash) (liftM (signatureAfterTrial secretKey result.1) :
      OracleComp OracleWorld (Option Signature))).run result.2]) h
  simpa only [evalSPMF_bind, bind_assoc] using heq

end SphincsSecurity.Seeded
