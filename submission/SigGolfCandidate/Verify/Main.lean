import SigGolfCandidate.Verify.Top

/-!
# Main results for the verify image

* `verify_refines`: the verify program refines `verifyRef` (value and number of hash calls),
  as an equality of oracle computations.
* `verify_terminates`: for every fixed oracle and input, the run finishes within `cycleBound`
  (= 11547) cycles (in particular `< CYCLE_LIMIT`).
* `verify_accept_cycles`: accepting runs take at most `cycleBound` cycles.
-/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

theorem init_exists (input : SigGolf.Input submission.sizes .verify) :
    ∃ s, initialState submission .verify input = some s := by
  unfold initialState
  simp only [submission_admissible.2 .verify, if_true]
  exact ⟨_, rfl⟩

theorem verify_good (input : SigGolf.Input submission.sizes .verify) (s : MachineState)
    (hs : initialState submission .verify input = some s) :
    Good s fuelBound cycleBound (cc (verifyRef input.1 input.2.1 input.2.2) Kb) := by
  obtain ⟨m, pk, w⟩ := input
  exact main_good _ _ _ (length_toList m) (length_toList pk) (length_toList w) s (init_ok m pk w s hs)

theorem cc_Kb {α : Type} (oa : OracleComp HashSpec Bool) :
    cc oa Kb = countCalls oa := by
  simp only [cc, Kb, map_pure, Nat.add_zero]
  exact bind_pure _

theorem verify_refines (m : Message) (pk : PublicKey) (w : Bytes 6404) :
    (fun r => (r.value, r.hashCalls)) <$> submission.run .verify (m, pk, w) =
      (fun p => (if p.1 then some () else none, p.2)) <$> countCalls (verifyRef m pk w) := by
  obtain ⟨s, hs⟩ := init_exists (m, pk, w)
  have hg := (verify_good (m, pk, w) s hs CYCLE_LIMIT (by unfold CYCLE_LIMIT fuelBound; norm_num)).1
  rw [cc_Kb (α := Unit)] at hg
  rw [run_eq submission .verify _ s hs, image_eq, Functor.map_map, ← hg, Functor.map_map]
  refine congrArg (fun f => f <$> Riscv.execute CYCLE_LIMIT image s) ?_
  funext e
  simp only [toRunResult, obs]
  by_cases h : e.exit = .success
  · simp only [h, decide_true, if_true]; rfl
  · simp only [h, decide_false, if_false, Bool.false_eq_true]; rfl

theorem verify_terminates (hash : Hash) (input : SigGolf.Input submission.sizes .verify) :
    (submission.runWith hash .verify input).finished = true ∧
      (submission.runWith hash .verify input).cycles ≤ cycleBound ∧
      (submission.runWith hash .verify input).cycles < CYCLE_LIMIT := by
  obtain ⟨s, hs⟩ := init_exists input
  have hg := (verify_good input s hs CYCLE_LIMIT (by unfold CYCLE_LIMIT fuelBound; norm_num)).2 hash
  rw [runWith_eq submission hash .verify input s hs, image_eq]
  simp only [toRunResult]
  refine ⟨?_, hg.2, lt_of_le_of_lt hg.2 (by unfold CYCLE_LIMIT cycleBound; norm_num)⟩
  simpa using hg.1

theorem verify_accept_cycles (hash : Hash) (input : SigGolf.Input submission.sizes .verify)
    (_h : (submission.runWith hash .verify input).value = some ()) :
    (submission.runWith hash .verify input).cycles ≤ cycleBound :=
  (verify_terminates hash input).2.1

end SigGolfCandidate.Verify
