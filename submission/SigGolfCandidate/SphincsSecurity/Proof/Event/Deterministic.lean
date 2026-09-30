import SigGolfCandidate.SphincsSecurity.Proof.Event.CachedErasure
import SigGolfCandidate.SphincsSecurity.Proof.Event.Boundary
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.ReferenceDistribution
/-!
# The deterministic seeded scheme, in event form

The comparison between the deterministic seeded scheme and the independent scheme of the ideal proof,
with the budget event carried along: every step either keeps the joint law of the verdict and the hash
count, or couples two runs so that the count can only go down.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

open DeterministicSigning

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

theorem probEvent_bind_le_of {α β : Type} {mx : ProbComp α} {my oc : α → ProbComp β} {p q : β → Prop}
    (h : ∀ x, Pr[p | my x] ≤ Pr[q | oc x]) : Pr[p | mx >>= my] ≤ Pr[q | mx >>= oc] := by
  simp only [probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)

theorem probEvent_of_evalSPMF_eq {α : Type} {left right : ProbComp α} (h : 𝒮[left] = 𝒮[right]) (event : α → Prop) :
    Pr[event | left] = Pr[event | right] :=
  probEvent_congr' (fun _ _ => Iff.rfl) h

theorem countHashQueries_run'_support {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (result : α × Nat) (hresult : result ∈ support ((simulateQ romImpl (countHashQueries computation)).run' cache)) :
    result.1 ∈ support ((simulateQ romImpl computation).run' cache) := by
  rw [StateT.run'_eq, support_map] at hresult ⊢
  obtain ⟨full, hfull, rfl⟩ := hresult
  refine ⟨(full.1.1, full.2), ?_, rfl⟩
  rw [← countHashQueries_run_forget, support_map]
  exact ⟨full, hfull, rfl⟩

/-- Memoizing the signing requests keeps every downward-closed budget event. -/
theorem probEvent_runSigning_memoize_counted {Request Answer : Type} [Fintype Request] [DecidableEq Request] {α : Type}
    (sign : Request → OracleComp HashSpec Answer)
    (computation : OracleComp (OracleWorld + (Request →ₒ Answer)) α) (cache : QueryCache HashSpec)
    (event : α → Nat → Prop) (hmono : ∀ value count count', count' ≤ count → event value count → event value count') :
    Pr[fun result => event result.1 result.2 | (simulateQ romImpl (countHashQueries (runSigning sign computation))).run' cache] ≤
      Pr[fun result => event result.1 result.2 |
        (simulateQ romImpl (countHashQueries (runSigning sign (memoize computation ∅)))).run' cache] := by
  let preparation : OracleComp OracleWorld (Request → Answer) := liftM (prepareSigning sign)
  rw [probEvent_of_evalSPMF_eq (evalDist_presample_computation _ preparation cache),
    probEvent_of_evalSPMF_eq (evalDist_presample_computation (countHashQueries (runSigning sign (memoize computation ∅)))
      preparation cache), probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro prepared
  by_cases hprepared : prepared ∈ support ((simulateQ romImpl preparation).run cache)
  · apply mul_le_mul' le_rfl
    have hrun : simulateQ romImpl preparation = simulateQ randomOracle (prepareSigning sign) :=
      QueryImpl.simulateQ_add_liftM_right _ _ _
    rw [hrun] at hprepared
    have hknown := resolves_prepareSigning sign cache prepared hprepared
    exact (erases_memoize prepared.2 sign prepared.1 hknown computation ∅
      (fun request answer h => by simp at h)).probEvent_counted_le prepared.2 le_rfl event hmono
  · rw [probOutput_eq_zero_of_not_mem_support hprepared, zero_mul, zero_mul]

theorem probEvent_sourceGame_memo_counted (sign : Message → OracleComp HashSpec (Option Signature))
    (publicKey : PublicKey) (adversary : Adversary) (cache : QueryCache HashSpec) (budget : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ budget |
      (simulateQ romImpl (countHashQueries (runSigning sign (sourceGame publicKey adversary)))).run' cache] ≤
    Pr[fun result => result.1 = true ∧ result.2 ≤ budget |
      (simulateQ romImpl (countHashQueries (runSigning sign (sourceGame publicKey (memoAdversary adversary))))).run' cache] := by
  refine (probEvent_runSigning_memoize_counted sign (sourceGame publicKey adversary) cache
    (fun value count => value = true ∧ count ≤ budget) (fun _ _ _ hle h => ⟨h.1, hle.trans h.2⟩)).trans ?_
  have hmap (f : Bool × Bool → Bool) :
      (simulateQ romImpl (countHashQueries (runSigning sign (f <$> transcriptReduction publicKey adversary)))).run' cache =
        (fun result => (f result.1, result.2)) <$>
          (simulateQ romImpl (countHashQueries (runSigning sign (transcriptReduction publicKey adversary)))).run' cache := by
    rw [runSigning, simulateQ_map, ← runSigning, countHashQueries_map, simulateQ_map, StateT.run'_eq, StateT.run'_eq,
      StateT.run_map, Functor.map_map, Functor.map_map]
  rw [← fst_transcriptReduction, ← snd_transcriptReduction, hmap, hmap, probEvent_map, probEvent_map]
  apply probEvent_mono
  intro result hresult hwin
  refine ⟨?_, hwin.2⟩
  have hsupp := countHashQueries_run'_support _ cache result hresult
  have hsource := evaluateSource_support sign (transcriptReduction publicKey adversary) cache hsupp
  exact transcriptReduction_win publicKey adversary result.1 hsource hwin.1

theorem countHashQueries_run'_bind {α β : Type} (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (countHashQueries (first >>= next))).run' cache =
      (simulateQ romImpl (countHashQueries first)).run cache >>= fun head =>
        (fun result => (result.1, head.1.2 + result.2)) <$>
          (simulateQ romImpl (countHashQueries (next head.1.1))).run' head.2 := by
  rw [countHashQueries_bind, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  apply bind_congr
  intro head
  simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

theorem probEvent_counted_bind_le {α β : Type} (first : OracleComp OracleWorld α)
    (left right : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) (event : β → Prop) (budget : Nat)
    (hnext : ∀ value cache budget,
      Pr[fun result => event result.1 ∧ result.2 ≤ budget | (simulateQ romImpl (countHashQueries (left value))).run' cache] ≤
        Pr[fun result => event result.1 ∧ result.2 ≤ budget | (simulateQ romImpl (countHashQueries (right value))).run' cache]) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget | (simulateQ romImpl (countHashQueries (first >>= left))).run' cache] ≤
      Pr[fun result => event result.1 ∧ result.2 ≤ budget | (simulateQ romImpl (countHashQueries (first >>= right))).run' cache] := by
  rw [countHashQueries_run'_bind, countHashQueries_run'_bind, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  apply ENNReal.tsum_le_tsum
  intro head
  apply mul_le_mul' le_rfl
  have hshift (next : α → OracleComp OracleWorld β) :
      Pr[fun result => event result.1 ∧ result.2 ≤ budget | (fun result => (result.1, head.1.2 + result.2)) <$>
        (simulateQ romImpl (countHashQueries (next head.1.1))).run' head.2] =
      if head.1.2 ≤ budget then
        Pr[fun result => event result.1 ∧ result.2 ≤ budget - head.1.2 |
          (simulateQ romImpl (countHashQueries (next head.1.1))).run' head.2]
      else 0 := by
    rw [probEvent_map]
    split_ifs with hle
    · apply probEvent_ext
      intro result _
      simp only [Function.comp_apply]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩
    · apply probEvent_eq_zero
      intro result _ hresult
      simp only [Function.comp_apply] at hresult
      omega
  rw [hshift left, hshift right]
  split_ifs
  · exact hnext _ _ _
  · exact le_rfl

theorem probEvent_tableGameAfterSecrets_memo_counted (adversary : Adversary) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (cache : QueryCache HashSpec) (budget : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ budget |
      (simulateQ romImpl (countHashQueries (tableGameAfterSecrets adversary outputs randomizers))).run' cache] ≤
    Pr[fun result => result.1 = true ∧ result.2 ≤ budget |
      (simulateQ romImpl (countHashQueries (tableGameAfterSecrets (memoAdversary adversary) outputs randomizers))).run' cache] := by
  unfold tableGameAfterSecrets
  refine probEvent_counted_bind_le _ _ _ cache (fun value => value = true) budget ?_
  intro root cache budget
  rw [← runSigning_sourceGame, ← runSigning_sourceGame]
  exact probEvent_sourceGame_memo_counted _ _ _ _ _

theorem romRun_count_of_costWorld {α : Type} (computation : OracleComp OracleWorld α) :
    (fun result => (result.1, result.2.2)) <$> (simulateQ (worldHandler costHash) computation).run (∅, 0) =
      (simulateQ romImpl (countHashQueries computation)).run' ∅ := by
  rw [run_costWorld, Functor.map_map, StateT.run'_eq]
  simp only [Nat.zero_add]

theorem evalDist_independentTable_memo_counted (adversary : Adversary) :
    𝒮[do
      let outputs ← sampleSecretOutputs
      let randomizers ← sampleRandomizerOutputs
      (simulateQ romImpl (countHashQueries (tableGameAfterSecrets (memoAdversary adversary) outputs randomizers))).run' ∅] =
    𝒮[(simulateQ romImpl (countHashQueries (gameCore Concrete.scheme (memoAdversary adversary)))).run' ∅] := by
  rw [gameCore_independent_eq, Concrete.romRun_countHashQueries_lift_bind]
  have hsecrets := evalDist_secrets_continuation fun secret =>
    (simulateQ romImpl (countHashQueries (Concrete.gameAfterSecrets (memoAdversary adversary) 0 secret.1 secret.2))).run' ∅
  rw [← hsecrets, evalSPMF_bind, evalSPMF_bind]
  apply congrArg (𝒮[sampleSecretOutputs] >>= ·)
  funext outputs
  have h := congrArg (fun law => (fun result => (result.1, result.2.2)) <$> law)
    (evalDist_tableGameAfterSecrets_memo costHash adversary outputs (∅, 0))
  simp only [evalSPMF_map, evalSPMF_bind, map_bind] at h
  simp only [← evalSPMF_map, romRun_count_of_costWorld] at h
  rw [evalSPMF_bind]
  exact h

end SphincsSecurity.Seeded
