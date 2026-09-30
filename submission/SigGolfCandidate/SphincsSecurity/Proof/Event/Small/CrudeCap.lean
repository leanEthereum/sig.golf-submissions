import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.SignCost
/-!
# A crude hash budget for the capped adversary

Every hash query of the capped adversary costs one call and every signing request at most
`signRatio` times its charge, so with the verifier and key generation the whole experiment makes at
most `signRatio * budget` hash calls.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem advStep_cost_le (sk : SecretKey) (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (input : (OracleWorld + SigningSpec).Domain) (result : _)
    (hresult : result ∈ support (fixedBoundaryRun parameter f (advStep sk input))) :
    result.2.hashCalls ≤ signRatio * visWeight input := by
  rcases input with (input | input) | message
  · have hstep : advStep sk (.inl (.inl input)) =
        (fun answer => (answer, [])) <$> (liftM (liftM (unifSpec.query input) : ProbComp _) : OracleComp OracleWorld _) := rfl
    rw [hstep, fixedBoundaryRun_map, support_map] at hresult
    obtain ⟨source, hsource, rfl⟩ := hresult
    have h := fixed_lift_prob_hashCalls parameter f _ source hsource
    simp only [Prod.map_snd, id, h]
    exact Nat.zero_le _
  · rw [advStep_world, fixedBoundaryRun_map, fixedBoundaryRun_oracleHash, map_pure, support_pure,
      Set.mem_singleton_iff] at hresult
    subst result
    simp only [Prod.map_snd, id, signingBoundaryTrace_hashCalls_eq, visWeight, signRatio]
    decide
  · rw [advStep_sign, fixedBoundaryRun_map, support_map] at hresult
    obtain ⟨source, hsource, rfl⟩ := hresult
    exact (fixed_sign_cost parameter f sk message source hsource).trans signHashBound_le

theorem fixed_advPhase_cost (sk : SecretKey) (parameter : PublicParameter) (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : Nat) (hbudget : WeightBound computation budget)
    (result : _) (hresult : result ∈ support (fixedBoundaryRun parameter f (advPhase sk computation))) :
    result.2.hashCalls ≤ signRatio * budget := by
  induction computation using OracleComp.inductionOn generalizing budget result with
  | pure value =>
      rw [advPhase_pure, fixedBoundaryRun_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Nat.zero_le _
  | query_bind input next ih =>
      rw [weightBound_query_bind_iff] at hbudget
      rw [advPhase_query_bind, fixedBoundaryRun_bind, mem_support_bind_iff] at hresult
      obtain ⟨step, hstep, hresult⟩ := hresult
      rw [fixedBoundaryRun_map, support_map] at hresult
      obtain ⟨tail, htail, rfl⟩ := hresult
      rw [support_map] at htail
      obtain ⟨last, hlast, rfl⟩ := htail
      have hfirst := advStep_cost_le sk parameter f input step hstep
      have hrest := ih step.1.1 (budget - visWeight input) (hbudget.2 step.1.1) last hlast
      simp only [SigningBoundaryTrace.hashCalls_mul, Prod.map_snd, id]
      have h1 := hbudget.1
      calc step.2.hashCalls + last.2.hashCalls ≤ signRatio * visWeight input + signRatio * (budget - visWeight input) :=
            Nat.add_le_add hfirst hrest
        _ = signRatio * budget := by rw [← Nat.mul_add]; congr 1; omega

theorem fixed_finishGame_cost (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (pk : PublicKey)
    (outcome : Forgery × QueryLog SigningSpec) (result : Bool × SigningBoundaryTrace)
    (hresult : result ∈ support (fixedBoundaryRun parameter f (finishGame pk outcome))) :
    result.2.hashCalls ≤ verifyHashBound := by
  rw [finishGame, fixedBoundaryRun_bind, mem_support_bind_iff] at hresult
  obtain ⟨checked, hchecked, hresult⟩ := hresult
  rw [fixedBoundaryRun_pure, map_pure, support_pure, Set.mem_singleton_iff] at hresult
  subst result
  change checked ∈ support (fixedBoundaryRun parameter f (liftM (verify pk outcome.1.message outcome.1.signature :
    OracleComp HashSpec Bool))) at hchecked
  rw [fixedBoundaryRun_lift_hash, support_pure, Set.mem_singleton_iff] at hchecked
  subst checked
  simp only [SigningBoundaryTrace.hashCalls_mul]
  exact (evenBound_boundaryEval parameter f (evenBound_verify _ _ _)).trans_eq (by rfl)


theorem fixed_visAdversary_cost (adversary : Adversary) (budget : Nat) (hbudget : keygenHashCost + 1 ≤ budget)
    (f : QueryImpl HashSpec Id) (result : Bool × SigningBoundaryTrace)
    (hresult : result ∈ support (simulateQ (fixedHashWorld f) (boundaryGameCore (visAdversary adversary budget)))) :
    result.2.hashCalls ≤ signRatio * budget := by
  rw [fixed_boundaryGameCore] at hresult
  simp only [mem_support_bind_iff] at hresult
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, hresult⟩ := hresult
  rw [fixed_gameAfterSecrets] at hresult
  dsimp only at hresult
  rw [support_map] at hresult
  obtain ⟨final, hfinal, rfl⟩ := hresult
  rw [gameRest_eq_advPhase, fixedBoundaryRun_bind, mem_support_bind_iff] at hfinal
  obtain ⟨adv, hadv, hfinal⟩ := hfinal
  rw [support_map] at hfinal
  obtain ⟨fin, hfin, rfl⟩ := hfinal
  have hA := fixed_advPhase_cost _ parameter f _ _ (visAdversary_weightBound adversary budget _ hbudget) adv hadv
  have hV := fixed_finishGame_cost parameter f _ adv.1 fin hfin
  have hK := verifyHashBound_lt_keygen
  have hR : 1 ≤ signRatio := by decide
  simp only [SigningBoundaryTrace.hashCalls_mul, SigningBoundaryTrace.hashCalls_pow_none]
  have hmul : signRatio * (budget - keygenHashCost) + signRatio * keygenHashCost = signRatio * budget := by
    rw [← Nat.mul_add]; congr 1; omega
  have hk : keygenHashCost ≤ signRatio * keygenHashCost := Nat.le_mul_of_pos_left _ hR
  have hsplit : keygenHashCost + verifyHashBound ≤ signRatio * keygenHashCost := by
    have : 2 * keygenHashCost ≤ signRatio * keygenHashCost := Nat.mul_le_mul_right _ (by decide)
    omega
  omega

/-- The capped adversary makes at most `signRatio * budget` hash calls in the whole experiment. -/
theorem hasHashQueryBound_visAdversary (adversary : Adversary) (budget : Nat) (hbudget : keygenHashCost + 1 ≤ budget) :
    HasHashQueryBound scheme (visAdversary adversary budget) (signRatio * budget) := by
  classical
  intro result hresult
  rw [countedGame_eq_boundaryGameCore, support_map] at hresult
  obtain ⟨run, hrun, rfl⟩ := hresult
  let inputs := hashInputs (boundaryGameCore (visAdversary adversary budget))
  let _ : SampleableType (inputs → HashOutput) := SampleableType.ofFintype _
  have heq := evalDist_romRun_eq_finiteHash (boundaryGameCore (visAdversary adversary budget)) inputs
    (Finset.Subset.refl _) ∅
  have hs : run ∈ support (do
      let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
      simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs table)) (boundaryGameCore (visAdversary adversary budget))) := by
    rw [mem_support_iff, probOutput_def, ← heq, ← probOutput_def, ← mem_support_iff]
    exact hrun
  rw [mem_support_bind_iff] at hs
  obtain ⟨table, _, hs⟩ := hs
  exact fixed_visAdversary_cost adversary budget hbudget _ run hs

end SphincsSecurity.Concrete.EventSmall
