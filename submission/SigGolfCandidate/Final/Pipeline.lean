import SigGolfCandidate.Submission

/-!
# The honest pipeline, projected

`success_honest_eq`: the success bit of one honest pipeline only depends on the phase outputs.
`honest_success_verify`: under a fixed oracle, a successful pipeline ends with an accepting verify
run and is charged its cycles plus the witness charge.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Final
open SigGolf

variable (sub : Submission)

/-- The success bit of the honest pipeline, from the phase outputs only. -/
def successPipe (sk : SecretKey) (m : Message) : OracleComp HashSpec Bool := do
  match (← (fun r => r.value) <$> sub.run .keygen sk) with
  | none => pure false
  | some (pk, cache) =>
    match (← (fun r => r.value) <$> sub.run .sign (sk, cache, m)) with
    | none => pure false
    | some σ =>
      match (← (fun r => r.value) <$> sub.run .expand (m, pk, σ)) with
      | none => pure false
      | some w => (fun r => r.value.isSome) <$> sub.run .verify (m, pk, w)

theorem success_honest_eq (sk : SecretKey) (m : Message) :
    HonestResult.success <$> sub.honest sk m = successPipe sub sk m := by
  unfold Submission.honest successPipe
  simp only [map_bind, bind_map_left]
  refine bind_congr fun k => ?_
  rcases k.value with _ | ⟨pk, cache⟩
  · simp
  simp only [map_bind]
  refine bind_congr fun s => ?_
  rcases s.value with _ | σ
  · simp
  simp only [map_bind]
  refine bind_congr fun e => ?_
  rcases e.value with _ | w
  · simp
  simp


/-- Under a fixed oracle, a successful honest pipeline ends with an accepting verify run, and its
scored cycles are that run's cycles plus the witness charge. -/
theorem honest_success_verify (hash : Hash) (sk : SecretKey) (m : Message)
    (h : (evalWithAnswerFn hash (sub.honest sk m)).success = true) :
    ∃ input : Input sub.sizes .verify,
      (sub.runWith hash .verify input).value.isSome = true ∧
      (evalWithAnswerFn hash (sub.honest sk m)).verificationCycles =
        (sub.runWith hash .verify input).cycles + witnessCycles sub.sizes.witness := by
  unfold Submission.honest at h ⊢
  simp only [evalWithAnswerFn_bind] at h ⊢
  generalize evalWithAnswerFn hash (sub.run .keygen sk) = k at h ⊢
  rcases hk : k.value with _ | ⟨pk, cache⟩
  · simp [hk] at h
  simp only [hk, evalWithAnswerFn_bind] at h ⊢
  generalize evalWithAnswerFn hash (sub.run .sign (sk, cache, m)) = s at h ⊢
  rcases hs : s.value with _ | σ
  · simp [hs] at h
  simp only [hs, evalWithAnswerFn_bind] at h ⊢
  generalize he : evalWithAnswerFn hash (sub.run .expand (m, pk, σ)) = e at h ⊢
  rcases he' : e.value with _ | w
  · simp [he'] at h
  simp only [he', evalWithAnswerFn_bind, evalWithAnswerFn_pure] at h ⊢
  exact ⟨(m, pk, w), h, rfl⟩

end SigGolfCandidate.Final
