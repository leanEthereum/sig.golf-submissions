import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.Capped
import SigGolfCandidate.SphincsSecurity.Proof.Reference.SigningBoundaryHashCost
import SigGolfCandidate.SphincsSecurity.Proof.Reference.DirectQueryBudget
import SigGolfCandidate.SphincsSecurity.Proof.Reference.FixedHashBoundary
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.FrontierRandomOracle
/-!
# The capped adversary keeps every run within budget

Fix the hash function. A run of the adversary whose hash calls stay within the budget never reaches
the cap of `visAdversary`, because every query costs at least its visible charge. So the
expectation of any functional that vanishes above the budget is at most the corresponding
expectation for the capped adversary.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

/-- The adversary phase of the game: forward the world, sign with the logged signer. -/
noncomputable def advPhase (sk : SecretKey) {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    OracleComp OracleWorld (α × QueryLog SigningSpec) :=
  (simulateQ (forwardOracles + signingOracle scheme sk) computation).run

/-- One step of the adversary phase. -/
noncomputable def advStep (sk : SecretKey) (input : (OracleWorld + SigningSpec).Domain) :
    OracleComp OracleWorld ((OracleWorld + SigningSpec).Range input × QueryLog SigningSpec) :=
  ((forwardOracles + signingOracle scheme sk) input).run

theorem advPhase_pure (sk : SecretKey) {α : Type} (value : α) :
    advPhase sk (pure value : OracleComp (OracleWorld + SigningSpec) α) = pure (value, []) := rfl

theorem advPhase_bind (sk : SecretKey) {α β : Type} (first : OracleComp (OracleWorld + SigningSpec) α)
    (next : α → OracleComp (OracleWorld + SigningSpec) β) :
    advPhase sk (first >>= next) =
      advPhase sk first >>= fun result => Prod.map id (result.2 ++ ·) <$> advPhase sk (next result.1) := by
  simp only [advPhase, simulateQ_bind]
  rfl

theorem advPhase_query_bind (sk : SecretKey) {α : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) :
    advPhase sk (liftM ((OracleWorld + SigningSpec).query input) >>= next) =
      advStep sk input >>= fun result => Prod.map id (result.2 ++ ·) <$> advPhase sk (next result.1) := by
  rw [advPhase_bind]
  simp only [advPhase, advStep, simulateQ_spec_query]

theorem advPhase_map (sk : SecretKey) {α β : Type} (computation : OracleComp (OracleWorld + SigningSpec) α)
    (g : α → β) : advPhase sk (g <$> computation) = Prod.map g id <$> advPhase sk computation := by
  simp only [advPhase, simulateQ_map]
  rfl

/-! ### Fixed-hash runs through a total cache -/

/-- The cache that already holds every answer of `f`. -/
def totalCache (f : QueryImpl HashSpec Id) : QueryCache HashSpec := fun input => some (f input)

theorem fixedBoundaryRun_eq_totalCache (parameter : PublicParameter) (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp OracleWorld α) :
    fixedBoundaryRun parameter f computation = Prod.fst <$> boundaryRun parameter computation (totalCache f) := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [fixedBoundaryRun_bind, boundaryRun_bind, boundaryRun_query]
      cases input with
      | inl input =>
          change (simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter))
            (liftM (OracleWorld.query (.inl input)))).run >>= _ = _
          rw [simulateQ_spec_query]
          simp only [QueryImpl.withTrace_apply, fixedHashWorld, map_bind, bind_map_left, ih, Functor.map_map]
          simp [romImpl, WriterT.run_bind, WriterT.run_tell, map_eq_bind_pure_comp]
          rfl
      | inr input =>
          have hcache : totalCache f input = some (f input) := rfl
          change (simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter))
            (liftM (OracleWorld.query (.inr input)))).run >>= _ = _
          rw [simulateQ_spec_query]
          change _ = Prod.fst <$> ((fun result => ((result.1, signingBoundaryTrace parameter (.inr input) result.1), result.2)) <$>
            (randomOracle (spec := HashSpec) input).run (totalCache f) >>= _)
          rw [QueryImpl.withCaching_run_some _ hcache]
          simp only [QueryImpl.withTrace_apply, fixedHashWorld, map_pure, pure_bind, Functor.map_map, ih]
          simp [WriterT.run_bind, WriterT.run_tell, map_eq_bind_pure_comp]

theorem fixedBoundaryRun_atLeast (parameter : PublicParameter) (f : QueryImpl HashSpec Id) {α : Type}
    {computation : OracleComp OracleWorld α} {cost : Nat} (h : BoundaryHashAtLeast parameter computation cost)
    (result : α × SigningBoundaryTrace) (hresult : result ∈ support (fixedBoundaryRun parameter f computation)) :
    cost ≤ result.2.hashCalls := by
  rw [fixedBoundaryRun_eq_totalCache, support_map] at hresult
  obtain ⟨source, hsource, rfl⟩ := hresult
  exact h _ source hsource


theorem advStep_world (sk : SecretKey) (input : HashInput) :
    advStep sk (.inl (.inr input)) = (fun answer => (answer, [])) <$> oracleHash input := rfl

theorem advStep_sign (sk : SecretKey) (message : Message) :
    advStep sk (.inr message) = (fun answer => (answer, [⟨message, answer⟩])) <$> sign sk message := by
  simp only [advStep, QueryImpl.add_apply_inr, signingOracle, QueryImpl.withLogging_apply, WriterT.run_bind', WriterT.run_monadLift',
    WriterT.run_tell]
  simp [scheme, map_eq_bind_pure_comp]

/-- Every query costs at least its visible charge. -/
theorem advStep_cost (sk : SecretKey) (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (input : (OracleWorld + SigningSpec).Domain) (result : _)
    (hresult : result ∈ support (fixedBoundaryRun parameter f (advStep sk input))) :
    visWeight input ≤ result.2.hashCalls := by
  rcases input with (input | input) | message
  · exact Nat.zero_le _
  · rw [advStep_world, fixedBoundaryRun_map, support_map] at hresult
    obtain ⟨source, hsource, rfl⟩ := hresult
    exact fixedBoundaryRun_atLeast parameter f (boundaryHashAtLeast_hash parameter input) source hsource
  · rw [advStep_sign, fixedBoundaryRun_map, support_map] at hresult
    obtain ⟨source, hsource, rfl⟩ := hresult
    exact fixed_sign_charge parameter f sk message source hsource


/-- Keep the value of a functional on the runs the cap did not stop. -/
def capLift {α : Type} (φ : (α × QueryLog SigningSpec) × SigningBoundaryTrace → ℝ≥0∞) :
    (Option α × QueryLog SigningSpec) × SigningBoundaryTrace → ℝ≥0∞
  | ((some value, log), trace) => φ ((value, log), trace)
  | ((none, _), _) => 0

private theorem inner_expectation (parameter : PublicParameter) (f : QueryImpl HashSpec Id) {α β : Type}
    (step : α × SigningBoundaryTrace) (log : QueryLog SigningSpec)
    (computation : OracleComp OracleWorld (β × QueryLog SigningSpec)) (φ : (β × QueryLog SigningSpec) × SigningBoundaryTrace → ℝ≥0∞) :
    ∑' x, Pr[= x | (fun final => (final.1, step.2 * final.2)) <$>
        fixedBoundaryRun parameter f (Prod.map id (log ++ ·) <$> computation)] * φ x =
      ∑' x, Pr[= x | fixedBoundaryRun parameter f computation] * φ ((x.1.1, log ++ x.1.2), step.2 * x.2) := by
  rw [fixedBoundaryRun_map, tsum_probOutput_map_mul, tsum_probOutput_map_mul]
  rfl

theorem fixed_cap_domination (sk : SecretKey) (parameter : PublicParameter) (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : Nat)
    (φ : (α × QueryLog SigningSpec) × SigningBoundaryTrace → ℝ≥0∞)
    (hφ : ∀ x, budget < x.2.hashCalls → φ x = 0) :
    ∑' x, Pr[= x | fixedBoundaryRun parameter f (advPhase sk computation)] * φ x ≤
      ∑' y, Pr[= y | fixedBoundaryRun parameter f (advPhase sk (weightCap computation budget))] * capLift φ y := by
  induction computation using OracleComp.inductionOn generalizing budget φ with
  | pure value =>
      rw [weightCap_pure, advPhase_pure, advPhase_pure, fixedBoundaryRun_pure, fixedBoundaryRun_pure,
        tsum_probOutput_pure_mul, tsum_probOutput_pure_mul]
      exact le_rfl
  | query_bind input next ih =>
      rw [advPhase_query_bind, fixedBoundaryRun_bind, tsum_probOutput_bind_mul, weightCap_query_bind]
      split_ifs with hweight
      · rw [advPhase_query_bind, fixedBoundaryRun_bind, tsum_probOutput_bind_mul]
        apply ENNReal.tsum_le_tsum
        intro step
        by_cases hstep : step ∈ support (fixedBoundaryRun parameter f (advStep sk input))
        · apply mul_le_mul' le_rfl
          have hcost := advStep_cost sk parameter f input step hstep
          rw [inner_expectation, inner_expectation]
          refine le_of_le_of_eq (ih step.1.1 (budget - visWeight input)
            (fun x => φ ((x.1.1, step.1.2 ++ x.1.2), step.2 * x.2)) ?_) ?_
          · intro x hx
            apply hφ
            rw [SigningBoundaryTrace.hashCalls_mul]
            omega
          · apply tsum_congr
            intro y
            rcases y with ⟨⟨_ | value, log⟩, trace⟩ <;> rfl
        · rw [probOutput_eq_zero_of_not_mem_support hstep, zero_mul, zero_mul]
      · refine le_trans (le_of_eq ?_) zero_le
        apply ENNReal.tsum_eq_zero.mpr
        intro step
        by_cases hstep : step ∈ support (fixedBoundaryRun parameter f (advStep sk input))
        · have hcost := advStep_cost sk parameter f input step hstep
          rw [inner_expectation]
          apply mul_eq_zero_of_right
          apply ENNReal.tsum_eq_zero.mpr
          intro x
          rw [hφ _ (by rw [SigningBoundaryTrace.hashCalls_mul]; omega), mul_zero]
        · rw [probOutput_eq_zero_of_not_mem_support hstep, zero_mul]


/-! ### The whole game with a fixed hash function -/

/-- Verification and the verdict after the adversary phase. -/
noncomputable def finishGame (pk : PublicKey) (result : Forgery × QueryLog SigningSpec) : OracleComp OracleWorld Bool := do
  let verified ← scheme.verify pk result.1.message result.1.signature
  return decide (SigningTranscript.Valid result.2 ∧ ¬SigningTranscript.Contains result.2 result.1) && verified

theorem gameRest_eq_advPhase (adversary : Adversary) (pk : PublicKey) (sk : SecretKey) :
    Seeded.gameRest scheme adversary pk sk = advPhase sk (adversary.main pk) >>= finishGame pk := by
  simp only [Seeded.gameRest, advPhase]
  congr 1

theorem advPhase_visAdversary (adversary : Adversary) (budget : Nat) (pk : PublicKey) (sk : SecretKey) :
    advPhase sk ((visAdversary adversary budget).main pk) =
      advPhase sk (QueryCap.counted (NonmessageQuery pk.parameter) (weightCap (adversary.main pk) (budget - keygenHashCost - 1))) >>=
        fun result => Prod.map id (result.2 ++ ·) <$>
          ((fun _ => (result.1.1.getD dummyForgery, [])) <$> oracleHash (markerInput pk.parameter result.1.2)) := by
  simp only [visAdversary]
  rw [advPhase_bind]
  congr 1


theorem fixedBoundaryRun_oracleHash (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (input : HashInput) :
    fixedBoundaryRun parameter f (oracleHash input : OracleComp OracleWorld HashOutput) =
      pure (f input, signingBoundaryTrace parameter (.inr input) (f input)) := by
  change (simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter))
    (liftM (OracleWorld.query (.inr input)))).run = _
  rw [simulateQ_spec_query]
  rfl

theorem fixed_gameRest_coupling (adversary : Adversary) (q : Nat) (parameter : PublicParameter)
    (f : QueryImpl HashSpec Id) (pk : PublicKey) (sk : SecretKey) :
    Pr[fun result => result.1 = true ∧ keygenHashCost + result.2.hashCalls ≤ q |
        fixedBoundaryRun parameter f (Seeded.gameRest scheme adversary pk sk)] ≤
      Pr[fun result => result.1 = true ∧ keygenHashCost + result.2.hashCalls ≤ q + 1 |
        fixedBoundaryRun parameter f (Seeded.gameRest scheme (visAdversary adversary (q + 1)) pk sk)] := by
  let φ : (Forgery × QueryLog SigningSpec) × SigningBoundaryTrace → ℝ≥0∞ := fun x =>
    Pr[fun final => final.1 = true ∧ keygenHashCost + (x.2 * final.2).hashCalls ≤ q |
      fixedBoundaryRun parameter f (finishGame pk x.1)]
  have hφ : ∀ x, q - keygenHashCost < x.2.hashCalls → φ x = 0 := by
    intro x hx
    apply probEvent_eq_zero
    intro final _ hfinal
    rw [SigningBoundaryTrace.hashCalls_mul] at hfinal
    omega
  have hleft : Pr[fun result => result.1 = true ∧ keygenHashCost + result.2.hashCalls ≤ q |
      fixedBoundaryRun parameter f (Seeded.gameRest scheme adversary pk sk)] =
      ∑' x, Pr[= x | fixedBoundaryRun parameter f (advPhase sk (adversary.main pk))] * φ x := by
    rw [gameRest_eq_advPhase, fixedBoundaryRun_bind, probEvent_bind_eq_tsum]
    simp only [probEvent_map, Function.comp_def, φ]
  have hdom := fixed_cap_domination sk parameter f (adversary.main pk) (q - keygenHashCost) φ hφ
  have hbudget : q + 1 - keygenHashCost - 1 = q - keygenHashCost := by omega
  rw [hleft]
  refine hdom.trans ?_
  rw [gameRest_eq_advPhase, advPhase_visAdversary, hbudget, bind_assoc, fixedBoundaryRun_bind, probEvent_bind_eq_tsum]
  have hforget : weightCap (adversary.main pk) (q - keygenHashCost) =
      Prod.fst <$> QueryCap.counted (NonmessageQuery pk.parameter) (weightCap (adversary.main pk) (q - keygenHashCost)) :=
    (QueryCap.counted_forget _ _).symm
  have hcounted : ∑' y, Pr[= y | fixedBoundaryRun parameter f (advPhase sk (weightCap (adversary.main pk) (q - keygenHashCost)))] *
        capLift φ y =
      ∑' z, Pr[= z | fixedBoundaryRun parameter f (advPhase sk
        (QueryCap.counted (NonmessageQuery pk.parameter) (weightCap (adversary.main pk) (q - keygenHashCost))))] *
        capLift φ (Prod.map (Prod.map Prod.fst id) id z) := by
    conv_lhs => rw [hforget, advPhase_map, fixedBoundaryRun_map, tsum_probOutput_map_mul]
  rw [hcounted]
  apply ENNReal.tsum_le_tsum
  intro z
  apply mul_le_mul' le_rfl
  rcases z with ⟨⟨⟨_ | forgery, count⟩, log⟩, trace⟩
  · exact zero_le
  · simp only [Prod.map, id, capLift, φ]
    rw [Functor.map_map, bind_map_left, fixedBoundaryRun_bind, fixedBoundaryRun_oracleHash, pure_bind, probEvent_map,
      probEvent_map]
    simp only [Option.getD_some, Prod.map, id, List.append_nil]
    apply le_of_eq
    congr 1
    funext final
    simp only [Function.comp_apply, SigningBoundaryTrace.hashCalls_mul, signingBoundaryTrace_hashCalls_eq]
    apply propext
    constructor <;> intro h <;> exact ⟨h.1, by simp at h ⊢; omega⟩


private theorem probEvent_bind_le_bind {α β : Type} (first : ProbComp α) (left right : α → ProbComp β)
    (p q : β → Prop) (h : ∀ value, Pr[p | left value] ≤ Pr[q | right value]) :
    Pr[p | first >>= left] ≤ Pr[q | first >>= right] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun value => mul_le_mul' le_rfl (h value)

theorem fixed_gameAfterSecrets (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (f : QueryImpl HashSpec Id) :
    fixedBoundaryRun parameter f (gameAfterSecrets adversary parameter otsSecret ftsSecret) =
      let top := evalWithAnswerFn f (keygenTable parameter (otsSecret topLayer rootTree))
      (fun final => (final.1, (FreeMonoid.of none) ^ keygenHashCost * final.2)) <$>
        fixedBoundaryRun parameter f (Seeded.gameRest scheme adversary ⟨top (layerHeight topLayer) 0, parameter⟩
          ⟨parameter, top (layerHeight topLayer) 0, otsSecret, ftsSecret, top⟩) := by
  rw [gameAfterSecrets, fixedBoundaryRun_bind, fixedBoundaryRun_lift_hash, boundaryEval_keygen, pure_bind]
  rfl

theorem fixed_boundaryGameCore (adversary : Adversary) (f : QueryImpl HashSpec Id) :
    simulateQ (fixedHashWorld f) (boundaryGameCore adversary) = (do
      let parameter ← sampleParameter
      let otsSecret ← sampleOtsSecrets
      let ftsSecret ← sampleFtsSecrets
      fixedBoundaryRun parameter f (gameAfterSecrets adversary parameter otsSecret ftsSecret)) := by
  rw [boundaryGameCore]
  simp only [simulateQ_bind, simulateQ_fixedHashWorld_lift_prob]
  apply bind_congr
  intro parameter
  apply bind_congr
  intro otsSecret
  apply bind_congr
  intro ftsSecret
  rw [← fixedBoundaryRun_eq_boundaryComputation]

theorem fixed_boundaryGameCore_coupling (adversary : Adversary) (q : Nat) (f : QueryImpl HashSpec Id) :
    Pr[fun result => result.1 = true ∧ result.2.hashCalls ≤ q | simulateQ (fixedHashWorld f) (boundaryGameCore adversary)] ≤
      Pr[fun result => result.1 = true ∧ result.2.hashCalls ≤ q + 1 |
        simulateQ (fixedHashWorld f) (boundaryGameCore (visAdversary adversary (q + 1)))] := by
  rw [fixed_boundaryGameCore, fixed_boundaryGameCore]
  refine probEvent_bind_le_bind _ _ _ _ _ fun parameter => ?_
  refine probEvent_bind_le_bind _ _ _ _ _ fun otsSecret => ?_
  refine probEvent_bind_le_bind _ _ _ _ _ fun ftsSecret => ?_
  rw [fixed_gameAfterSecrets, fixed_gameAfterSecrets]
  dsimp only
  rw [probEvent_map, probEvent_map]
  simp only [Function.comp_def, SigningBoundaryTrace.hashCalls_mul, SigningBoundaryTrace.hashCalls_pow_none]
  exact fixed_gameRest_coupling adversary q parameter f _ _

/-- **The coupling.** Every run within budget `q` is a run of the capped adversary within `q + 1`. -/
theorem forgeEventAdvantage_le_visAdversary (adversary : Adversary) (q : Nat) :
    forgeEventAdvantage scheme adversary q ≤ forgeEventAdvantage scheme (visAdversary adversary (q + 1)) (q + 1) := by
  classical
  rw [forgeEventAdvantage_eq_boundary, forgeEventAdvantage_eq_boundary]
  let inputs := hashInputs (boundaryGameCore adversary) ∪ hashInputs (boundaryGameCore (visAdversary adversary (q + 1)))
  let _ : SampleableType (inputs → HashOutput) := SampleableType.ofFintype _
  have hleft := evalDist_romRun_eq_finiteHash (boundaryGameCore adversary) inputs Finset.subset_union_left ∅
  have hright := evalDist_romRun_eq_finiteHash (boundaryGameCore (visAdversary adversary (q + 1))) inputs
    Finset.subset_union_right ∅
  rw [probEvent_def, hleft, probEvent_def, hright, ← probEvent_def, ← probEvent_def]
  refine probEvent_bind_le_bind _ _ _ _ _ fun table => ?_
  exact fixed_boundaryGameCore_coupling adversary q _

end SphincsSecurity.Concrete.EventSmall
