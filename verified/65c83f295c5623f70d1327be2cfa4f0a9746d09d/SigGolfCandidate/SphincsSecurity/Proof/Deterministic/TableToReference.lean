import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.RequestSampling
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.ReferenceSource
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.MemoTable
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.CostState

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

variable {State : Type}

attribute [local irreducible] tableSign

theorem evalDist_tableGameAfterSecrets_memo (hash : QueryImpl HashSpec (StateT State ProbComp))
    (adversary : Adversary) (outputs : SecretOutputs) (state : State) :
    𝒮[do
      let randomizers ← sampleRandomizerOutputs
      (simulateQ (worldHandler hash) (tableGameAfterSecrets (memoAdversary adversary) outputs randomizers)).run state] =
      𝒮[(simulateQ (worldHandler hash) (Concrete.gameAfterSecrets (memoAdversary adversary)
        0 (tableOts outputs) (tableFts outputs))).run state] := by
  unfold tableGameAfterSecrets Concrete.gameAfterSecrets
  simp only [simulateQ_bind, StateT.run_bind]
  rw [evalSPMF_bind_bind_swap]
  apply evalSPMF_bind_congr'
  intro result
  change _ = 𝒮[(simulateQ (worldHandler hash) (gameRest Concrete.scheme (memoAdversary adversary)
    ⟨result.1, 0⟩ (tableKey 0 result.1 outputs))).run result.2]
  have hleft (randomizers) := runSigning_sourceGame randomizers (tableKey 0 result.1 outputs)
    ⟨result.1, 0⟩ (memoAdversary adversary)
  simp_rw [← hleft]
  rw [← runWorldSigning_sourceGame, simulateQ_runWorldSigning]
  exact evalDist_tableRequests hash (tableKey 0 result.1 outputs)
    (sourceGame ⟨result.1, 0⟩ (memoAdversary adversary))
    (freshRequests_sourceGame_memo _ _) result.2

theorem hashQueryBound_reference_afterSecrets (adversary : Adversary) (outputs : SecretOutputs) (q : Nat)
    (hbound : ∀ randomizers, HashQueryBound
      (tableGameAfterSecrets (memoAdversary adversary) outputs randomizers) ∅ q) :
    HashQueryBound (Concrete.gameAfterSecrets (memoAdversary adversary)
      0 (tableOts outputs) (tableFts outputs)) ∅ q := by
  rw [hashQueryBound_iff_costState]
  intro result hresult
  rw [← mem_support_iff_of_evalSPMF_eq (evalDist_tableGameAfterSecrets_memo costHash adversary
    outputs (∅, 0)), mem_support_bind_iff] at hresult
  obtain ⟨randomizers, _, hresult⟩ := hresult
  exact (hashQueryBound_iff_costState _ ∅ q).1 (hbound randomizers) result hresult

theorem referenceBudget_from_table (adversary : Adversary) (q : Nat)
    (hbound : HasTableBudget (memoAdversary adversary) q) :
    HasHashQueryBound Concrete.scheme (memoAdversary adversary) q := by
  rw [hasHashQueryBound_iff, Concrete.gameCore_eq_secrets]
  have htail (parameter : PublicParameter) (hparameter : parameter ∈ support Concrete.sampleParameter)
      (ots : OtsSecrets) (fts : FtsSecrets) :
      HashQueryBound (Concrete.gameAfterSecrets (memoAdversary adversary) parameter ots fts) ∅ q := by
    rw [sampleParameter_eq_zero, support_pure, Set.mem_singleton_iff] at hparameter
    subst parameter
    let high : Secrets := (fun _ _ _ _ => 0, fun _ _ _ => 0)
    have h := hashQueryBound_reference_afterSecrets adversary
      (secretHalves.symm ((ots, fts), high)) q (hbound _)
    simpa only [tableOts_from_halves, tableFts_from_halves] using h
  intro result hresult
  simp only [countHashQueries_bind, countHashQueries_lift_prob, simulateQ_bind,
    simulateQ_map, StateT.run'_eq, StateT.run_bind, StateT.run_map,
    romImpl, QueryImpl.simulateQ_add_liftM_left, unifFwdImpl.simulateQ_run,
    bind_map_left, map_bind, Nat.zero_add, bind_pure_comp, Functor.map_map,
    support_bind, Set.mem_iUnion, support_map] at hresult
  obtain ⟨parameter, hparameter, ots, _, fts, _, record, hrecord, rfl⟩ := hresult
  apply htail parameter hparameter ots fts record.1
  rw [StateT.run'_eq, support_map]
  exact ⟨record, hrecord, rfl⟩

end SphincsSecurity.Seeded
