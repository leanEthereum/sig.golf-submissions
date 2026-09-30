import SigGolfCandidate.SphincsSecurity.Proof.Event.Erasure
import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.GameExpansion
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Presampling

/-!
# Erasing the seed from the experiment, in event form

The experiment samples the master seed and derives everything from it: the one-time and few-time
secrets, the randomizers, the cache's masks and its MAC. Presampling every derivation into the random
oracle's cache and erasing the derivation queries turns the experiment after the seed into the cached
table game, which saves at least key generation's first query. The table game does not depend on the
seed, so replacing the derivation cache by the empty one costs one 256-bit seed guess per hash query.
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096

private theorem probEvent_bind_le_of' {α β : Type} {mx : ProbComp α} {my oc : α → ProbComp β} {p q : β → Prop}
    (h : ∀ x, Pr[p | my x] ≤ Pr[q | oc x]) : Pr[p | mx >>= my] ≤ Pr[q | mx >>= oc] := by
  simp only [probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl (h x)

private theorem probEvent_of_evalSPMF_eq' {α : Type} {left right : ProbComp α} (h : 𝒮[left] = 𝒮[right])
    (event : α → Prop) : Pr[event | left] = Pr[event | right] :=
  probEvent_congr' (fun _ _ => Iff.rfl) h

private theorem romRun_countHashQueries_lift_bind' {α β : Type} (sample : ProbComp α)
    (next : α → OracleComp OracleWorld β) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (countHashQueries ((liftM sample : OracleComp OracleWorld α) >>= next))).run' cache =
      sample >>= fun value => (simulateQ romImpl (countHashQueries (next value))).run' cache := by
  rw [countHashQueries_bind, countHashQueries_lift_prob, bind_map_left]
  simp only [zero_add, Prod.mk.eta, bind_pure]
  exact Concrete.simulateQ_romImpl_liftM_bind_run' sample _ cache

section FirstQuery

variable {known : QueryCache HashSpec} {seed : MasterSeed} {outputs : SecretOutputs}
  {randomizers : RandomizerOutputs} {masks : MaskOutputs} {macs : MacOutputs}
  (hsecrets : ∀ position, known (secretInputs 0 seed position) = some (outputs position))
  (hrandomizers : ∀ position, known (randomizerInputs 0 seed position) = some (randomizers position))
  (hmasks : ∀ position, known (maskInputs 0 seed position) = some (masks position))
  (hmacs : ∀ region, known (macInputs 0 seed region) = some (macs region))

include hsecrets hrandomizers hmasks hmacs

/-- The erased game saves at least the first query of key generation. -/
theorem probEvent_deterministicAfterSeed_erased (adversary : Security.Adversary) (cache : QueryCache HashSpec)
    (hcache : known ≤ cache) (event : Bool → Prop) (q : Nat) :
    Pr[fun result => event result.1 ∧ result.2 ≤ q |
      (simulateQ romImpl (countHashQueries (deterministicGameAfterSeed adversary seed))).run' cache] ≤
    Pr[fun result => event result.1 ∧ result.2 ≤ q - 1 |
      (simulateQ romImpl (countHashQueries
        (cachedTableGameAfterSecrets adversary outputs randomizers masks macs))).run' cache] := by
  rw [deterministicAfterSeed_first_query, countHashQueries_run'_query_bind]
  have hc : cache (secretInputs 0 seed firstSecretPosition) = some (outputs firstSecretPosition) :=
    hcache (hsecrets _)
  change Pr[_ | (randomOracle (spec := HashSpec) _).run cache >>= _] ≤ _
  rw [QueryImpl.withCaching_run_some _ hc, pure_bind, probEvent_map]
  have h := (erases_deterministicGameAfterSeed_first hsecrets hrandomizers hmasks hmacs adversary).probEvent_counted_le
    cache hcache (fun value count => event value ∧ 1 + count ≤ q)
    (fun value count count' hle h => ⟨h.1, by have := h.2; omega⟩)
  refine le_trans (le_of_eq ?_) (h.trans ?_)
  · rfl
  · apply probEvent_mono
    intro result _ hresult
    exact ⟨hresult.1, by have := hresult.2; omega⟩

end FirstQuery

private theorem presample_step {α β : Type} (computation : OracleComp OracleWorld α)
    (preparation : OracleComp HashSpec β) (cache : QueryCache HashSpec) (sample : ProbComp β)
    (cacheOf : β → QueryCache HashSpec)
    (hprepared : 𝒮[(simulateQ randomOracle preparation).run cache] =
      𝒮[(fun value => (value, cacheOf value)) <$> sample]) :
    𝒮[(simulateQ romImpl computation).run' cache] =
      𝒮[sample >>= fun value => (simulateQ romImpl computation).run' (cacheOf value)] := by
  rw [evalDist_presample_computation _ (liftM preparation : OracleComp OracleWorld β) cache,
    show simulateQ romImpl (liftM preparation : OracleComp OracleWorld β) = simulateQ randomOracle preparation
      from QueryImpl.simulateQ_add_liftM_right _ _ _,
    evalSPMF_bind, hprepared, ← evalSPMF_bind, bind_map_left]

attribute [local irreducible] deterministicGameAfterSeed cachedTableGameAfterSecrets derivationCache
  signingDerivationCache maskedDerivationCache cachedDerivationCache in
/-- Presampling every derivation and erasing it: the experiment after the seed, counted. -/
theorem probEvent_deterministicAfterSeed_le_cachedTable (adversary : Security.Adversary) (seed : MasterSeed)
    (event : Bool → Prop) (q : Nat) :
    Pr[fun result => event result.1 ∧ result.2 ≤ q |
      (simulateQ romImpl (countHashQueries (deterministicGameAfterSeed adversary seed))).run' ∅] ≤
    Pr[fun result => event result.1 ∧ result.2 ≤ q - 1 | do
      let outputs ← sampleSecretOutputs
      let randomizers ← sampleRandomizerOutputs
      let masks ← sampleMaskOutputs
      let macs ← sampleMacOutputs
      (simulateQ romImpl (countHashQueries
        (cachedTableGameAfterSecrets adversary outputs randomizers masks macs))).run'
        (cachedDerivationCache seed outputs randomizers masks macs)] := by
  rw [probEvent_of_evalSPMF_eq' (presample_step _ (prepareSecrets seed) ∅ sampleSecretOutputs _
    (evalDist_prepareSecrets seed))]
  apply probEvent_bind_le_of'
  intro outputs
  rw [probEvent_of_evalSPMF_eq' (presample_step _ (prepareRandomizers seed) _ sampleRandomizerOutputs _
    (evalDist_prepareRandomizers seed outputs))]
  apply probEvent_bind_le_of'
  intro randomizers
  rw [probEvent_of_evalSPMF_eq' (presample_step _ (prepareMasks seed) _ sampleMaskOutputs _
    (evalDist_prepareMasks seed outputs randomizers))]
  apply probEvent_bind_le_of'
  intro masks
  rw [probEvent_of_evalSPMF_eq' (presample_step _ (prepareMacs seed) _ sampleMacOutputs _
    (evalDist_prepareMacs seed outputs randomizers masks))]
  apply probEvent_bind_le_of'
  intro macs
  exact probEvent_deterministicAfterSeed_erased
    (cachedDerivationCache_secret seed outputs randomizers masks macs)
    (cachedDerivationCache_randomizer seed outputs randomizers masks macs)
    (cachedDerivationCache_mask seed outputs randomizers masks macs)
    (cachedDerivationCache_mac seed outputs randomizers masks macs) adversary _ le_rfl event q

theorem experiment_eq_counted (adversary : Security.Adversary) :
    Security.experiment adversary =
      (simulateQ romImpl (countHashQueries (Security.gameCore adversary))).run' ∅ := by
  rw [simulateQ_countHashQueries]
  rfl

attribute [local irreducible] deterministicGameAfterSeed cachedTableGameAfterSecrets derivationCache
  signingDerivationCache maskedDerivationCache cachedDerivationCache sampleMasterSeed sampleSecretOutputs
  sampleRandomizerOutputs sampleMaskOutputs sampleMacOutputs in
/-- **The seed erased from the experiment.** The experiment's budget event is at most the cached table
game's, at one query less, plus one 256-bit seed guess per remaining query. -/
theorem experiment_event_le_cachedTable (adversary : Security.Adversary) (q : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ q | Security.experiment adversary] ≤
      Pr[fun result => result.1 = true ∧ result.2 ≤ q - 1 | do
        let outputs ← sampleSecretOutputs
        let randomizers ← sampleRandomizerOutputs
        let masks ← sampleMaskOutputs
        let macs ← sampleMacOutputs
        (simulateQ romImpl (countHashQueries
          (cachedTableGameAfterSecrets adversary outputs randomizers masks macs))).run' ∅] +
        ((q - 1 : Nat) : ℝ≥0∞) / ((2 ^ 256 : Nat) : ℝ≥0∞) := by
  rw [experiment_eq_counted, gameCore_deterministic_eq, romRun_countHashQueries_lift_bind']
  calc
    _ ≤ Pr[fun result => result.1 = true ∧ result.2 ≤ q - 1 | do
          let seed ← sampleMasterSeed
          let outputs ← sampleSecretOutputs
          let randomizers ← sampleRandomizerOutputs
          let masks ← sampleMaskOutputs
          let macs ← sampleMacOutputs
          (simulateQ romImpl (countHashQueries
            (cachedTableGameAfterSecrets adversary outputs randomizers masks macs))).run'
            (cachedDerivationCache seed outputs randomizers masks macs)] := by
      apply probEvent_bind_le_of'
      intro seed
      exact probEvent_deterministicAfterSeed_le_cachedTable adversary seed (fun b => b = true) q
    _ = Pr[fun result => result.1 = true ∧ result.2 ≤ q - 1 | do
          let outputs ← sampleSecretOutputs
          let randomizers ← sampleRandomizerOutputs
          let masks ← sampleMaskOutputs
          let macs ← sampleMacOutputs
          let seed ← sampleMasterSeed
          (simulateQ romImpl (countHashQueries
            (cachedTableGameAfterSecrets adversary outputs randomizers masks macs))).run'
            (cachedDerivationCache seed outputs randomizers masks macs)] := by
      apply probEvent_of_evalSPMF_eq'
      rw [evalSPMF_bind_bind_swap]
      apply evalSPMF_bind_congr'
      intro outputs
      rw [evalSPMF_bind_bind_swap]
      apply evalSPMF_bind_congr'
      intro randomizers
      rw [evalSPMF_bind_bind_swap]
      apply evalSPMF_bind_congr'
      intro masks
      rw [evalSPMF_bind_bind_swap]
    _ ≤ _ := by
      apply probEvent_bind_congr_le_add
      intro outputs _
      apply probEvent_bind_congr_le_add
      intro randomizers _
      apply probEvent_bind_congr_le_add
      intro masks _
      apply probEvent_bind_congr_le_add
      intro macs _
      exact probEvent_random_cache_change_event _
        (fun seed => cachedDerivationCache seed outputs randomizers masks macs) ∅
        (fun seed => cachedDerivationCache_agreeOutside seed _ _ _ _) (q - 1) (· = true)

end SphincsSecurity.Seeded
