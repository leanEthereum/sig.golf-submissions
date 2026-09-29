import SigGolfCandidate.Transfer.Basic
import VCVio.EvalDist.Expectation

/-!
# Transfer of the non-security statements

Given run agreement (`RunAgrees`, which holds for every submission whose legacy view is
admissible), each legacy statement of the submission's legacy view implies the corresponding
current statement: admission, termination, completeness, compression budgets and verification
cycles. Security is transferred in `SigGolfCandidate.Transfer.Security`.
-/

namespace SigGolfCandidate.Transfer
open OracleComp OracleSpec OracleComp.EvalDist

/-- A legacy honest record as a current one. -/
def honestOf (result : Legacy.HonestResult) : SigGolf.HonestResult :=
  ⟨result.success, fun program => result.costs (phaseOf program), result.verificationCycles⟩

theorem honest_eq (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (secretKey : SigGolf.SecretKey) (message : SigGolf.Message) :
    submission.honest secretKey message =
      honestOf <$> (legacyOf submission).honest secretKey message := by
  unfold SigGolf.Submission.honest Legacy.Submission.honest
  dsimp only
  rw [hrun SigGolf.Program.keygen secretKey, bind_map_left, map_bind]
  congr 1; funext keygen
  rcases keygen with ⟨_ | ⟨pk, cache⟩, _, _, _, _⟩
  · simp only [resultOf, Option.map_none, map_pure]
    congr 1
    simp only [honestOf, SigGolf.HonestResult.mk.injEq, true_and, and_true]
    funext program; cases program <;> rfl
  dsimp only [resultOf, Option.map, outputOf]
  rw [hrun SigGolf.Program.sign (secretKey, cache, message), bind_map_left, map_bind]
  congr 1; funext sign
  rcases sign with ⟨_ | signature, _, _, _, _⟩
  · simp only [resultOf, Option.map_none, map_pure]
    congr 1
    simp only [honestOf, SigGolf.HonestResult.mk.injEq, true_and, and_true]
    funext program; cases program <;> rfl
  dsimp only [resultOf, Option.map, outputOf]
  rw [hrun SigGolf.Program.expand (message, pk, signature), bind_map_left, map_bind]
  congr 1; funext expand
  rcases expand with ⟨_ | witness, _, _, _, _⟩
  · simp only [resultOf, Option.map_none, map_pure]
    congr 1
    simp only [honestOf, SigGolf.HonestResult.mk.injEq, true_and, and_true]
    funext program; cases program <;> rfl
  dsimp only [resultOf, Option.map, outputOf]
  rw [hrun SigGolf.Program.verify (message, pk, witness), bind_map_left, map_bind]
  congr 1; funext verify
  simp only [resultOf, map_pure, Option.isSome_map]
  congr 1
  simp only [honestOf, SigGolf.HonestResult.mk.injEq]
  refine ⟨rfl, ?_, rfl⟩
  funext program; cases program <;> rfl

theorem evalWithAnswerFn_honest (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (hash : SigGolf.Hash) (secretKey : SigGolf.SecretKey) (message : SigGolf.Message) :
    evalWithAnswerFn hash (submission.honest secretKey message) =
      honestOf (evalWithAnswerFn hash ((legacyOf submission).honest secretKey message)) := by
  rw [honest_eq submission hrun, evalWithAnswerFn_map]

theorem withRandomOracle_map {α β : Type} (f : α → β) (program : OracleComp SigGolf.HashSpec α) :
    SigGolf.withRandomOracle (f <$> program) = f <$> SigGolf.withRandomOracle program := by
  simp [SigGolf.withRandomOracle, simulateQ_map]

theorem withRandomOracle_eq {α : Type} (program : OracleComp SigGolf.HashSpec α) :
    SigGolf.withRandomOracle program = Legacy.withRandomOracle program := rfl

/-! ### Verification cycles -/

theorem verificationCycles_of_legacy (submission : SigGolf.Submission)
    (hrun : RunAgrees submission) (C : Nat) (hbound : (legacyOf submission).VerificationBound C) :
    submission.VerificationCycles C := by
  intro hash secretKey message
  dsimp only
  rw [evalWithAnswerFn_honest submission hrun]
  exact hbound hash secretKey message

/-! ### Termination -/

theorem termination_of_legacy (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (hterm : (legacyOf submission).Terminates) : submission.Termination := by
  intro hash program input
  rw [evalWithAnswerFn_run submission hrun]
  exact (hterm hash (phaseOf program) (inputOf program input)).2

/-! ### Compression budgets -/

theorem two_rpow_eq (x : ℝ) : (2 : ENNReal) ^ x = ENNReal.ofReal (Real.rpow 2 x) := by
  rw [Real.rpow_eq_pow, ← ENNReal.ofReal_rpow_of_pos (by norm_num)]
  simp

theorem compressionBudgets_of_legacy (submission : SigGolf.Submission)
    (hrun : RunAgrees submission) (hbounds : (legacyOf submission).CompressionBounds) :
    submission.CompressionBudgets := by
  intro secretKey program budget hbudget
  have hphase : phaseOf program ∈ Legacy.Phase.budgeted ∧
      (phaseOf program).budget = budget := by
    cases program <;> simp_all [SigGolf.Program.budget, Legacy.Phase.budget, Legacy.Phase.budgeted,
      phaseOf, SigGolf.BUDGET_KEYGEN, SigGolf.BUDGET_SIGN, SigGolf.BUDGET_EXPAND,
      Legacy.BUDGET_KEYGEN, Legacy.BUDGET_SIGN, Legacy.BUDGET_EXPAND]
  have hlegacy := hbounds secretKey (phaseOf program) hphase.1
  have hworkload : (do
        let message ← ($ᵗ SigGolf.Message : ProbComp SigGolf.Message)
        SigGolf.withRandomOracle (submission.honest secretKey message)) =
      honestOf <$> (legacyOf submission).honestWorkload secretKey := by
    unfold Legacy.Submission.honestWorkload
    simp only [honest_eq submission hrun, withRandomOracle_map, map_bind]
    rfl
  rw [hworkload, expectedValue_map]
  refine le_of_eq_of_le ?_ hlegacy
  congr 1
  funext result
  simp only [honestOf, two_rpow_eq, hphase.2]

/-! ### Completeness -/

theorem forIn_eq_foldlM (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (secretKey : SigGolf.SecretKey) (messages : List SigGolf.Message) (summary : Legacy.HonestSummary) :
    forIn messages summary.allSucceed (fun message (allSucceeded : Bool) => do
        let result ← submission.honest secretKey message
        pure (ForInStep.yield (allSucceeded && result.success))) =
      (fun summary => summary.allSucceed) <$>
        messages.foldlM (fun summary message => do
          let result ← (legacyOf submission).honest secretKey message
          return (⟨summary.allSucceed && result.success,
            fun phase => max (summary.maxCosts phase) (result.costs phase)⟩ :
              Legacy.HonestSummary)) summary := by
  induction messages generalizing summary with
  | nil => simp
  | cons message messages ih =>
      simp only [List.forIn_cons, List.foldlM_cons, honest_eq submission hrun, bind_assoc,
        map_bind, bind_map_left, pure_bind]
      congr 1
      funext result
      have ih' := ih ⟨summary.allSucceed && result.success,
        fun phase => max (summary.maxCosts phase) (result.costs phase)⟩
      simp only [honest_eq submission hrun, bind_map_left] at ih'
      exact ih'

theorem everyMessageSucceeds_eq (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (secretKey : SigGolf.SecretKey) :
    submission.everyMessageSucceeds secretKey =
      (fun summary => summary.allSucceed) <$> (legacyOf submission).allMessages secretKey := by
  unfold SigGolf.Submission.everyMessageSucceeds Legacy.Submission.allMessages
  have := forIn_eq_foldlM submission hrun secretKey (Finset.univ : Finset SigGolf.Message).toList {}
  simp only at this ⊢
  rw [← this]
  simp

theorem completeness_of_legacy (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (hcomplete : (legacyOf submission).Complete) : submission.Completeness := by
  intro secretKey
  rw [everyMessageSucceeds_eq submission hrun, withRandomOracle_map,
    ← probEvent_eq_eq_probOutput, probEvent_map]
  exact hcomplete secretKey

/-! ### Admission -/

theorem buffersDisjoint_iff (buffers : List (Nat × Nat)) :
    Legacy.Riscv.buffersDisjoint buffers = true ↔ buffers.Pairwise SigGolf.Riscv.DisjointBuffers := by
  induction buffers with
  | nil => simp [Legacy.Riscv.buffersDisjoint]
  | cons first rest ih =>
      simp only [Legacy.Riscv.buffersDisjoint, Bool.and_eq_true, List.all_eq_true,
        decide_eq_true_eq, List.pairwise_cons, ih]
      rfl

theorem admission_of_legacy (submission : SigGolf.Submission)
    (hadmissible : (legacyOf submission).Admissible) : submission.Admission := by
  obtain ⟨⟨_, hS, hW, hK⟩, himages⟩ := hadmissible
  refine ⟨⟨hS, hW, hK⟩, fun program => ?_⟩
  have h := himages (phaseOf program)
  simp only [programOf_phaseOf] at h
  obtain ⟨hsize, hall, hdisjoint⟩ := h
  refine ⟨hsize, ?_, (buffersDisjoint_iff _).1 hdisjoint⟩
  intro buffer hbuffer
  exact of_decide_eq_true (List.all_eq_true.1 hall buffer hbuffer)

end SigGolfCandidate.Transfer
