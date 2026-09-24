import SigGolfCandidate.Hypertree.SignExecution
import SigGolfCandidate.Hypertree.SignWire

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying SignatureEncoding
set_option maxRecDepth 4096

/-- Exact official signer output for arbitrary secret keys, caches, messages, and oracles. -/
theorem sign_run_refines (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    ∃ cycles, cycles≤16922843 ∧ submission.runWith hash .sign (secretKey,cache,message)=
      ⟨some ((signCompact hash secretKey message).wire (signCompact_valid hash secretKey message)),
        true,cycles,117508,121008⟩ := by
  obtain ⟨initial,final,instructions,cycles,loaded,execution,ib,cb,stored,randomizer⟩ :=
    sign_execution hash secretKey cache message
  have run := runWith_of_executes submission hash .sign (secretKey,cache,message) initial instructions
    ⟨.success,final,cycles,117508,121008⟩ loaded execution (by unfold CYCLE_LIMIT; omega)
  have output := SignWire.read_sign hash final secretKey message randomizer stored
  refine ⟨cycles,cb,?_⟩
  rw [run]
  change (⟨some (readBuffer final 0x20060 signatureBytes),true,cycles,117508,121008⟩ :
    RunResult (Bytes signatureBytes)) = _
  rw [output]
  rfl

/-- Universal actual signer termination and exact hash-resource accounting. -/
theorem sign_run_bound (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    let result := submission.runWith hash .sign (secretKey,cache,message)
    result.finished=true ∧ result.cycles≤16922843 ∧ result.cycles<CYCLE_LIMIT ∧
      result.hashCalls=117508 ∧ result.hashCompressions=121008 ∧ result.hashCompressions≤BUDGET_SIGN := by
  obtain ⟨cycles,bound,run⟩ := sign_run_refines hash secretKey cache message
  dsimp only
  rw [run]
  dsimp only
  exact ⟨rfl,bound,by unfold CYCLE_LIMIT; omega,rfl,rfl,by decide⟩

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_run_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_run_refines
end SigGolfCandidate.Hypertree.Signing
