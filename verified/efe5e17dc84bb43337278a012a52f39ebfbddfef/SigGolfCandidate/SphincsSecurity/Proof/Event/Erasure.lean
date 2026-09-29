import SigGolfCandidate.SphincsSecurity.Proof.Seeded.GameErasure
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.AdaptiveSeedGuessing
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryCapAccounting
/-!
# Erasure keeps the budget event

An erasure removes queries whose answers are already known. The two computations have the same
outputs along a coupled run, and the erased one makes no more hash calls, so any event that is
downward closed in the hash count is at least as likely for the erased computation.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem countHashQueries_run'_query_bind {α : Type} (input : OracleWorld.Domain)
    (next : OracleWorld.Range input → OracleComp OracleWorld α) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (countHashQueries (liftM (OracleWorld.query input) >>= next))).run' cache =
      ((romImpl input).run cache >>= fun step =>
        (fun result => (result.1, (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0) + result.2)) <$>
          (simulateQ romImpl (countHashQueries (next step.1))).run' step.2) := by
  rw [countHashQueries_query_bind, run'_query_bind]
  apply bind_congr
  intro step
  simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]
  rfl

theorem Erases.probEvent_counted_le {α : Type} {known : QueryCache HashSpec}
    {left right : OracleComp OracleWorld α} (h : Erases (worldKnown known) left right)
    (cache : QueryCache HashSpec) (hcache : known ≤ cache) (event : α → Nat → Prop)
    (hmono : ∀ value count count', count' ≤ count → event value count → event value count') :
    Pr[fun result => event result.1 result.2 | (simulateQ romImpl (countHashQueries left)).run' cache] ≤
      Pr[fun result => event result.1 result.2 | (simulateQ romImpl (countHashQueries right)).run' cache] := by
  induction h generalizing cache event with
  | pure value => exact le_rfl
  | query input left right _ ih =>
      rw [countHashQueries_run'_query_bind, countHashQueries_run'_query_bind, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
      apply ENNReal.tsum_le_tsum
      intro step
      by_cases hstep : step ∈ support ((romImpl input).run cache)
      · apply mul_le_mul' le_rfl
        rw [probEvent_map, probEvent_map]
        exact ih step.1 step.2 (romImpl_preserves_known known cache hcache input step hstep) _
          (fun value count count' hle h => hmono value _ _ (Nat.add_le_add_left hle _) h)
      · rw [probOutput_eq_zero_of_not_mem_support hstep, zero_mul, zero_mul]
  | skip input answer hknown next right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          rw [countHashQueries_run'_query_bind]
          change Pr[_ | (randomOracle (spec := HashSpec) input).run cache >>= _] ≤ _
          rw [QueryImpl.withCaching_run_some _ hc, pure_bind, probEvent_map]
          refine le_trans ?_ (ih cache hcache event hmono)
          apply probEvent_mono
          intro result _ hresult
          exact hmono _ _ _ (Nat.le_add_left _ _) hresult
  | cached input answer hknown left right _ ih =>
      cases input with
      | inl input => simp [worldKnown] at hknown
      | inr input =>
          have hc : cache input = some answer := hcache hknown
          rw [countHashQueries_run'_query_bind, countHashQueries_run'_query_bind]
          change Pr[_ | (randomOracle (spec := HashSpec) input).run cache >>= _] ≤
            Pr[_ | (randomOracle (spec := HashSpec) input).run cache >>= _]
          rw [QueryImpl.withCaching_run_some _ hc, pure_bind, pure_bind, probEvent_map, probEvent_map]
          exact ih cache hcache _ (fun value count count' hle h => hmono value _ _ (Nat.add_le_add_left hle _) h)
  | trans _ _ first second => exact (first cache hcache event hmono).trans (second cache hcache event hmono)


open scoped Classical in
theorem romRun_cap_event {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget | (simulateQ romImpl (countHashQueries computation)).run' cache] =
      Pr[fun outcome => ∃ result, outcome = some result ∧ event result.1 |
        (simulateQ romImpl (QueryCap.run (fun input : OracleWorld.Domain => input matches .inr _) computation budget)).run' cache] := by
  induction computation using OracleComp.inductionOn generalizing cache budget with
  | pure value =>
      simp only [countHashQueries_pure, QueryCap.run_pure, simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure]
      rw [probEvent_pure, probEvent_pure]
      simp
  | query_bind input next ih =>
      rw [countHashQueries_run'_query_bind, QueryCap.run_query_bind]
      cases input with
      | inl sample =>
          simp only [Bool.false_eq_true, if_false, zero_add, Prod.mk.eta, id_map']
          rw [run'_query_bind, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
          exact tsum_congr fun step => congrArg _ (ih step.1 step.2 budget)
      | inr hash =>
          simp only [if_true]
          cases budget with
          | zero =>
              rw [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, probEvent_pure]
              simp only [reduceCtorEq, false_and, exists_false, if_false]
              apply probEvent_eq_zero
              intro result hresult hev
              rw [mem_support_bind_iff] at hresult
              obtain ⟨step, _, hr⟩ := hresult
              rw [support_map] at hr
              obtain ⟨inner, _, rfl⟩ := hr
              have := hev.2
              simp at this
          | succ remaining =>
              rw [run'_query_bind, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
              refine tsum_congr fun step => congrArg _ ?_
              rw [probEvent_map, ← ih step.1 step.2 remaining]
              apply probEvent_ext
              intro result _
              simp only [Function.comp_apply]
              constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by omega⟩

theorem hashQueryBound_cap {α : Type} (computation : OracleComp OracleWorld α) (cache : QueryCache HashSpec) (budget : Nat) :
    HashQueryBound (QueryCap.run (fun input : OracleWorld.Domain => input matches .inr _) computation budget) cache budget := by
  intro result hresult
  apply QueryCap.counted_le_of_queryBound (fun input : OracleWorld.Domain => input matches .inr _) _ budget
    (QueryCap.run_queryBound _ computation budget) result
  exact support_simulateQ_run'_subset _ _ _ hresult

open scoped Classical in
theorem probEvent_random_cache_change_event {α : Type} (computation : OracleComp OracleWorld α)
    (initial : MasterSeed → QueryCache HashSpec) (cache : QueryCache HashSpec)
    (hagree : ∀ seed, AgreeOutside (fun input => SeedHit input seed) (initial seed) cache)
    (budget : Nat) (event : α → Prop) :
    Pr[fun result => event result.1 ∧ result.2 ≤ budget | sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (countHashQueries computation)).run' (initial seed)] ≤
      Pr[fun result => event result.1 ∧ result.2 ≤ budget | (simulateQ romImpl (countHashQueries computation)).run' cache] +
        budget / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  have hleft : Pr[fun result => event result.1 ∧ result.2 ≤ budget | sampleMasterSeed >>= fun seed =>
      (simulateQ romImpl (countHashQueries computation)).run' (initial seed)] =
      Pr[fun outcome => ∃ result, outcome = some result ∧ event result.1 | sampleMasterSeed >>= fun seed =>
        (simulateQ romImpl (QueryCap.run (fun input : OracleWorld.Domain => input matches .inr _) computation budget)).run'
          (initial seed)] := by
    rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
    exact tsum_congr fun seed => congrArg _ (romRun_cap_event computation _ budget event)
  rw [hleft, romRun_cap_event computation cache budget event]
  exact probEvent_random_cache_change_le _ initial cache hagree budget (hashQueryBound_cap computation cache budget) _

end SphincsSecurity.Seeded
