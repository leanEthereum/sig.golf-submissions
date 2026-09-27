import SigGolfCandidate.SphincsSecurity.Proof.Event.Boundary
import SigGolfCandidate.SphincsSecurity.Proof.Reference.FixedHashBoundary
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.FrontierSigningEvaluation
/-!
# The least cost of one signing request

With the hash function fixed, every signing request makes at least `signCharge` hash calls: either
its digest loop fails after `digestAttemptLimit` trials, or it builds the forest and then, for every
layer below the top one, either finds a counter and builds the layer's tree or fails after
`encodingAttemptLimit` trials. The capped adversary charges `signCharge` per request.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem fixedBoundaryRun_lift_prob (parameter : PublicParameter) (f : QueryImpl HashSpec Id) {α : Type}
    (computation : ProbComp α) :
    fixedBoundaryRun parameter f (liftM computation : OracleComp OracleWorld α) = (fun value => (value, 1)) <$> computation := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [liftM_bind, fixedBoundaryRun_bind]
      have hq : fixedBoundaryRun parameter f (liftM (liftM (unifSpec.query input) : ProbComp _) : OracleComp OracleWorld _) =
          (fun value => (value, 1)) <$> (liftM (unifSpec.query input) : ProbComp _) := by
        change (simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter))
          (liftM (OracleWorld.query (.inl input)))).run = _
        rw [simulateQ_spec_query]
        simp [fixedHashWorld, WriterT.run_bind, WriterT.run_tell, signingBoundaryTrace]
      rw [hq, bind_map_left]
      simp only [ih, Functor.map_map, mul_one, map_bind]

theorem fixed_lift_prob_hashCalls (parameter : PublicParameter) (f : QueryImpl HashSpec Id) {α : Type}
    (computation : ProbComp α) (result : α × SigningBoundaryTrace)
    (hresult : result ∈ support (fixedBoundaryRun parameter f (liftM computation : OracleComp OracleWorld α))) :
    result.2.hashCalls = 0 := by
  rw [fixedBoundaryRun_lift_prob, support_map] at hresult
  obtain ⟨_, _, rfl⟩ := hresult
  rfl

theorem boundaryEval_hashCalls_parameter (parameter other : PublicParameter) (f : QueryImpl HashSpec Id) {α : Type}
    (computation : OracleComp HashSpec α) :
    (boundaryEval parameter f computation).2.hashCalls = (boundaryEval other f computation).2.hashCalls := by
  induction computation using OracleComp.inductionOn with
  | pure value => rfl
  | query_bind input next ih =>
      rw [boundaryEval_bind, boundaryEval_bind, boundaryEval_hash_query, boundaryEval_hash_query,
        SigningBoundaryTrace.hashCalls_mul, SigningBoundaryTrace.hashCalls_mul, signingBoundaryTrace_hashCalls_eq,
        signingBoundaryTrace_hashCalls_eq, ih]

/-- The trees of the layers below `remaining` other than the top one. -/
def lowerTreesFrom : Nat → Nat
  | 0 => 0
  | remaining + 1 =>
      (if h : remaining < numLayers then (if remaining = 0 then 0 else treeNodeHashCost (layerHeight ⟨remaining, h⟩))
        else 0) + lowerTreesFrom remaining

/-- The trees a completed signature builds below the top layer. -/
def lowerTreesCost : Nat := lowerTreesFrom numLayers

/-- The least cost of a signing request. -/
def signCharge : Nat := ftsOpenHashCost + lowerTreesCost

theorem lowerTreesCost_eq : lowerTreesCost = 66300 := by
  simp only [lowerTreesCost, lowerTreesFrom, numLayers, treeNodeHashCost_def, oneTimeKeyHashCost_def]
  decide

theorem signCharge_eq : signCharge = 99067 := by
  rw [signCharge, lowerTreesCost_eq, ftsOpenHashCost_def]
  decide

theorem ftsOpenHashCost_le_signCharge : ftsOpenHashCost ≤ signCharge := Nat.le_add_right _ _

theorem signCharge_le_encodingAttemptLimit : lowerTreesCost ≤ encodingAttemptLimit := by
  rw [lowerTreesCost_eq, encodingAttemptLimit]
  norm_num

theorem signCharge_le_digestAttemptLimit : signCharge ≤ digestAttemptLimit := by
  rw [signCharge_eq, digestAttemptLimit]
  norm_num

theorem referenceEncodingSearch_none_cost (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (attempts counter : Nat)
    (hnone : (referenceEncodingSearch parameter f lay tree leaf message attempts counter).1 = none) :
    (referenceEncodingSearch parameter f lay tree leaf message attempts counter).2 = attempts := by
  induction attempts generalizing counter with
  | zero => rfl
  | succ attempts ih =>
      rw [referenceEncodingSearch] at hnone ⊢
      split at hnone
      · simp at hnone
      · dsimp only at hnone ⊢
        have := ih (counter + 1) hnone
        omega

theorem lowerTreesFrom_mono {low high : Nat} (h : low ≤ high) : lowerTreesFrom low ≤ lowerTreesFrom high := by
  induction h with
  | refl => exact le_rfl
  | step _ ih =>
      rw [lowerTreesFrom]
      omega

theorem lowerTreesFrom_le {remaining : Nat} (h : remaining ≤ numLayers) : lowerTreesFrom remaining ≤ lowerTreesCost :=
  lowerTreesFrom_mono h

theorem layersHashCostFrom_ge (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index) (remaining : Nat)
    (hremaining : remaining ≤ numLayers) :
    lowerTreesFrom remaining ≤ layersHashCostFrom (specLayerCost key f index) remaining := by
  induction remaining with
  | zero => exact Nat.zero_le _
  | succ remaining ih =>
      have hlayer : remaining < numLayers := by omega
      rw [layersHashCostFrom, dif_pos hlayer, lowerTreesFrom, dif_pos hlayer]
      have ih := ih (by omega)
      rw [specLayerCost]
      dsimp only
      cases hsearch : (referenceEncodingSearch key.parameter f ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩)
          (leafIndexAt index ⟨remaining, hlayer⟩) (evalWithAnswerFn f (layerMessage key index ⟨remaining, hlayer⟩))
          encodingAttemptLimit 0).1 with
      | none =>
          have hcost := referenceEncodingSearch_none_cost _ _ _ _ _ _ _ _ hsearch
          simp only [hcost, Option.elim_none, Nat.add_zero, Option.isSome_none, Bool.false_eq_true, if_false]
          have h1 := lowerTreesFrom_le hremaining
          rw [lowerTreesFrom, dif_pos hlayer] at h1
          have h2 := signCharge_le_encodingAttemptLimit
          omega
      | some result =>
          simp only [Option.elim_some, Option.isSome_some, if_true]
          by_cases h0 : remaining = 0
          · subst h0
            simp only [if_true]
            omega
          · have htop : (⟨remaining, hlayer⟩ : Layer) ≠ topLayer := fun h => h0 (congrArg Fin.val h)
            simp only [h0, htop, if_false]
            omega

theorem boundaryEval_signAttempt_hashCalls (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (key : SecretKey)
    (message : Message) (randomness : Randomness) :
    (boundaryEval parameter f (signAttempt key message randomness :
      OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))).2.hashCalls = 1 := by
  have h : (signAttempt key message randomness : OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) =
      liftM (HashSpec.query (tweakableHashInput key.parameter .message
        (messageDigestPayload key.root message randomness))) >>= fun output =>
          (if Admissible (truncateMessageDigest output) then
            pure (some (digestIndex (truncateMessageDigest output), digestLeaves (truncateMessageDigest output)))
          else pure none) := by
    simp only [signAttempt, messageDigest, oracleHash, bind_assoc, pure_bind]
    rfl
  have hpure : ∀ (c : Prop) [Decidable c] (a b : Option (Index × (IndexGroup → FtsLeaf))),
      (boundaryEval parameter f (if c then (pure a : OracleComp HashSpec _) else pure b)).2.hashCalls = 0 := by
    intro c _ a b
    split <;> rfl
  rw [h, boundaryEval_bind, boundaryEval_hash_query, SigningBoundaryTrace.hashCalls_mul,
    signingBoundaryTrace_hashCalls_eq, hpure]
  rfl

theorem fixed_signDigestLoop_none_cost (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (attempts : Nat)
    (key : SecretKey) (message : Message) (result : _)
    (hresult : result ∈ support (fixedBoundaryRun parameter f (signDigestLoop attempts key message)))
    (hnone : result.1 = none) : attempts ≤ result.2.hashCalls := by
  induction attempts generalizing result with
  | zero => exact Nat.zero_le _
  | succ attempts ih =>
      rw [signDigestLoop, fixedBoundaryRun_bind, mem_support_bind_iff] at hresult
      obtain ⟨sample, hsample, hresult⟩ := hresult
      rw [fixedBoundaryRun_bind, support_map] at hresult
      obtain ⟨last, hlast, rfl⟩ := hresult
      rw [mem_support_bind_iff] at hlast
      obtain ⟨attempt, hattempt, hlast⟩ := hlast
      rw [support_map] at hlast
      obtain ⟨tail, htail, rfl⟩ := hlast
      rw [fixedBoundaryRun_lift_hash, support_pure, Set.mem_singleton_iff] at hattempt
      have ha : attempt.2.hashCalls = 1 := by
        rw [hattempt]
        exact boundaryEval_signAttempt_hashCalls parameter f key message sample.1
      split at htail
      · rw [fixedBoundaryRun_pure, support_pure, Set.mem_singleton_iff] at htail
        subst tail
        simp at hnone
      · have ht := ih tail htail hnone
        simp only [SigningBoundaryTrace.hashCalls_mul]
        omega

/-- **Every signing request costs at least `signCharge` hash calls.** -/
theorem fixed_sign_charge (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (key : SecretKey) (message : Message)
    (result : Option Signature × SigningBoundaryTrace)
    (hresult : result ∈ support (fixedBoundaryRun parameter f (sign key message))) :
    signCharge ≤ result.2.hashCalls := by
  rw [sign_eq, fixedBoundaryRun_bind, mem_support_bind_iff] at hresult
  obtain ⟨loop, hloop, hresult⟩ := hresult
  rw [support_map] at hresult
  obtain ⟨tail, htail, rfl⟩ := hresult
  simp only [SigningBoundaryTrace.hashCalls_mul]
  split at htail
  · rename_i hnone
    have hl := fixed_signDigestLoop_none_cost parameter f digestAttemptLimit key message loop hloop hnone
    have := signCharge_le_digestAttemptLimit
    omega
  · rename_i randomness index leaves _
    rw [fixedBoundaryRun_lift_hash, support_pure, Set.mem_singleton_iff] at htail
    subst tail
    rw [boundaryEval_hashCalls_parameter parameter key.parameter, boundaryEval_signAfterDigest,
      SigningBoundaryTrace.hashCalls_pow_none]
    have := layersHashCostFrom_ge key f index numLayers le_rfl
    rw [sequenceLayersHashCost, signCharge, lowerTreesCost]
    omega

end SphincsSecurity.Concrete.EventSmall
