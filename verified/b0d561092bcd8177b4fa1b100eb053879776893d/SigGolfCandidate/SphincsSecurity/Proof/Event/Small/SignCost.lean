import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.VerifyCost
import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.Coupling
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.FrontierSigningEvaluation
/-!
# An upper bound on one signing request

With the hash function fixed, a signing request makes at most `signHashBound` hash calls: the digest
loop at most `digestAttemptLimit`, the forest `ftsOpenHashCost`, and each layer at most
`encodingAttemptLimit` counter trials and one tree (the top layer: its chain steps, which are fewer).
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false

theorem evenBound_boundaryEval (parameter : PublicParameter) (f : QueryImpl HashSpec Id) {α : Type}
    {computation : OracleComp HashSpec α} {budget : Nat} (h : EvenBound computation budget) :
    (boundaryEval parameter f computation).2.hashCalls ≤ budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => exact Nat.zero_le _
  | query_bind input next ih =>
      rw [evenBound_query_bind_iff] at h
      have heval : evalWithAnswerFn f (liftM (HashSpec.query input) : OracleComp HashSpec HashOutput) = f input := rfl
      rw [boundaryEval_bind, boundaryEval_hash_query, SigningBoundaryTrace.hashCalls_mul,
        signingBoundaryTrace_hashCalls_eq, heval]
      have := ih (f input) (h.2 (f input))
      have hpos := h.1.2
      change 1 + _ ≤ budget
      omega

theorem evenBound_messageDigest (parameter : PublicParameter) (root : Digest) (message : Message) (randomness : Randomness) :
    EvenBound (messageDigest parameter root message randomness : OracleComp HashSpec MessageDigest) 1 := by
  change EvenBound (liftM (HashSpec.query (tweakableHashInput parameter .message
    (messageDigestPayload root message randomness))) >>= fun output => pure (truncateMessageDigest output)) 1
  rw [evenBound_query_bind_iff, length_tweakableHashInput]
  refine ⟨⟨?_, by decide⟩, fun _ => trivial⟩
  simp only [messageDigestPayload, List.length_append, bytesLE, List.length_ofFn]
  decide

theorem evenBound_signAttempt (key : SecretKey) (message : Message) (randomness : Randomness) :
    EvenBound (signAttempt key message randomness : OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf)))) 1 := by
  rw [signAttempt]
  refine (evenBound_bind (evenBound_messageDigest _ _ _ _) fun digest => ?_ : EvenBound _ (1 + 0))
  split <;> exact evenBound_pure _ _

theorem fixed_signDigestLoop_cost (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (attempts : Nat)
    (key : SecretKey) (message : Message) (result : _)
    (hresult : result ∈ support (fixedBoundaryRun parameter f (signDigestLoop attempts key message))) :
    result.2.hashCalls ≤ attempts := by
  induction attempts generalizing result with
  | zero =>
      rw [signDigestLoop, fixedBoundaryRun_pure, support_pure, Set.mem_singleton_iff] at hresult
      subst result
      exact Nat.zero_le _
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
      have hs := fixed_lift_prob_hashCalls parameter f _ sample hsample
      have ha : attempt.2.hashCalls ≤ 1 := by
        rw [hattempt]
        exact evenBound_boundaryEval parameter f (evenBound_signAttempt key message sample.1)
      have ht : tail.2.hashCalls ≤ attempts := by
        split at htail
        · rw [fixedBoundaryRun_pure, support_pure, Set.mem_singleton_iff] at htail
          subst tail
          exact Nat.zero_le _
        · exact ih tail htail
      simp only [SigningBoundaryTrace.hashCalls_mul]
      omega


theorem referenceEncodingSearch_cost_le (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (lay : Layer)
    (tree : TreeIndex) (leaf : LeafIndex) (message : Digest) (attempts counter : Nat) :
    (referenceEncodingSearch parameter f lay tree leaf message attempts counter).2 ≤ attempts := by
  induction attempts generalizing counter with
  | zero => exact Nat.zero_le _
  | succ attempts ih =>
      rw [referenceEncodingSearch]
      split
      · exact Nat.le_add_left _ _
      · have := ih (counter + 1)
        dsimp only
        omega

theorem treeNodeHashCost_mono {low high : Nat} (h : low ≤ high) : treeNodeHashCost low ≤ treeNodeHashCost high := by
  rw [treeNodeHashCost_def, treeNodeHashCost_def]
  have := Nat.pow_le_pow_right (show 0 < 2 by decide) h
  have := Nat.mul_le_mul_left (oneTimeKeyHashCost + 2) this
  omega

theorem signingSteps_le (word : Encoding) : OtsCode.signingSteps word ≤ numChains * (chainLength - 1) := by
  unfold OtsCode.signingSteps
  calc
    _ ≤ ∑ _index : ChainIndex, (chainLength - 1) :=
      Finset.sum_le_sum fun index _ => Nat.le_sub_one_of_lt (word index).isLt
    _ = _ := by simp

theorem specLayerCost_le (key : SecretKey) (f : QueryImpl HashSpec Id) (index : Index) (lay : Layer) :
    (specLayerCost key f index lay).2 ≤ encodingAttemptLimit + treeNodeHashCost maxLayerHeight := by
  rw [specLayerCost]
  dsimp only
  have hsearch := referenceEncodingSearch_cost_le key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
    (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0
  have htree : treeNodeHashCost (layerHeight lay) ≤ treeNodeHashCost maxLayerHeight :=
    treeNodeHashCost_mono (layerHeight_le lay)
  have hsteps : numChains * (chainLength - 1) ≤ treeNodeHashCost maxLayerHeight := by
    rw [treeNodeHashCost_def, oneTimeKeyHashCost_def]
    decide
  cases (referenceEncodingSearch key.parameter f lay (treeIndexAt index lay) (leafIndexAt index lay)
      (evalWithAnswerFn f (layerMessage key index lay)) encodingAttemptLimit 0).1 with
  | none => simp only [Option.elim_none]; omega
  | some result =>
      simp only [Option.elim_some]
      split
      · have := signingSteps_le result.2
        omega
      · omega

theorem layersHashCostFrom_le {α : Type} (layers : Layer → Option α × Nat) (bound : Nat)
    (h : ∀ lay, (layers lay).2 ≤ bound) (remaining : Nat) :
    layersHashCostFrom layers remaining ≤ remaining * bound := by
  induction remaining with
  | zero => exact Nat.zero_le _
  | succ remaining ih =>
      rw [layersHashCostFrom]
      split
      · rename_i hlayer
        have := h ⟨remaining, hlayer⟩
        split <;> rw [Nat.succ_mul] <;> omega
      · exact Nat.zero_le _

/-- A bound on the hash calls of one signing request. -/
def signHashBound : Nat :=
  digestAttemptLimit + (ftsOpenHashCost + numLayers * (encodingAttemptLimit + treeNodeHashCost maxLayerHeight))

theorem fixed_sign_cost (parameter : PublicParameter) (f : QueryImpl HashSpec Id) (key : SecretKey) (message : Message)
    (result : Option Signature × SigningBoundaryTrace)
    (hresult : result ∈ support (fixedBoundaryRun parameter f (sign key message))) :
    result.2.hashCalls ≤ signHashBound := by
  rw [sign_eq, fixedBoundaryRun_bind, mem_support_bind_iff] at hresult
  obtain ⟨loop, hloop, hresult⟩ := hresult
  rw [support_map] at hresult
  obtain ⟨tail, htail, rfl⟩ := hresult
  have hl := fixed_signDigestLoop_cost parameter f digestAttemptLimit key message loop hloop
  have ht : tail.2.hashCalls ≤ ftsOpenHashCost + numLayers * (encodingAttemptLimit + treeNodeHashCost maxLayerHeight) := by
    split at htail
    · rw [fixedBoundaryRun_pure, support_pure, Set.mem_singleton_iff] at htail
      subst tail
      exact Nat.zero_le _
    · rename_i randomness index leaves _
      rw [fixedBoundaryRun_lift_hash, support_pure, Set.mem_singleton_iff] at htail
      subst tail
      rw [boundaryEval_hashCalls_parameter parameter key.parameter, boundaryEval_signAfterDigest,
        SigningBoundaryTrace.hashCalls_pow_none]
      have := layersHashCostFrom_le (specLayerCost key f index) _ (specLayerCost_le key f index) numLayers
      rw [sequenceLayersHashCost]
      omega
  simp only [SigningBoundaryTrace.hashCalls_mul, signHashBound]
  omega


theorem ftsOpenHashCost_eq : ftsOpenHashCost = 32767 := by
  rw [ftsOpenHashCost_def]
  decide

theorem keygenHashCost_eq : keygenHashCost = 606207 := by
  rw [keygenHashCost_def, treeNodeHashCost_def, oneTimeKeyHashCost_def]
  decide

theorem signHashBound_eq : signHashBound = 25083898 := by
  rw [signHashBound, ftsOpenHashCost_eq, treeNodeHashCost_def, oneTimeKeyHashCost_def]
  decide

/-- The ratio between the largest and the least cost of a signing request, rounded up. -/
def signRatio : Nat := 254

theorem signHashBound_le : signHashBound ≤ signRatio * signCharge := by
  rw [signHashBound_eq, signCharge_eq, signRatio]
  norm_num

theorem verifyHashBound_lt_keygen : verifyHashBound + 1 ≤ keygenHashCost := by
  rw [verifyHashBound_eq, keygenHashCost_eq]
  norm_num

end SphincsSecurity.Concrete.EventSmall
