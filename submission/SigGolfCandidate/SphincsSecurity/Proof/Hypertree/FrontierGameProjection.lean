import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Reference.BoundarySimulation
import SigGolfCandidate.SphincsSecurity.Proof.Reference.DirectQueryBudget
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] boundaryEval frontierTreeNode

theorem simulateQ_eq_fixedBoundaryRun {α : Type} (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (computation : OracleComp OracleWorld α) :
    simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace parameter)) computation =
      WriterT.mk (fixedBoundaryRun parameter f computation) := rfl

/-! ### The game reads the key's table only on the cached region -/

theorem signDigestLoop_congr_key (attempts : Nat) (key key' : SecretKey)
    (hparameter : key.parameter = key'.parameter) (hroot : key.root = key'.root) (message : Message) :
    signDigestLoop attempts key message = signDigestLoop attempts key' message := by
  induction attempts with
  | zero => rw [signDigestLoop, signDigestLoop]
  | succ attempts ih =>
      have hattempt : (fun randomness => (signAttempt key message randomness :
          OracleComp HashSpec (Option (Index × (IndexGroup → FtsLeaf))))) =
          fun randomness => signAttempt key' message randomness := by
        funext randomness
        unfold signAttempt
        rw [hparameter, hroot]
      rw [signDigestLoop, signDigestLoop]
      simp only [ih]
      exact congrArg (fun attempt => (liftM sampleRandomness : OracleComp OracleWorld Randomness) >>= fun randomness =>
        (liftM (attempt randomness) : OracleComp OracleWorld _) >>= fun result => match result with
          | some (index, leaves) => pure (some (randomness, index, leaves))
          | none => signDigestLoop attempts key' message) hattempt

/-- Two keys that differ only off the cached region of their tables sign alike. -/
theorem sign_congr_top (key key' : SecretKey) (hparameter : key.parameter = key'.parameter)
    (hroot : key.root = key'.root) (hots : key.otsSecret = key'.otsSecret) (hfts : key.ftsSecret = key'.ftsSecret)
    (htop : TopRegionEq (m := OracleComp HashSpec) (fun level nodeIdx => pure (key.top level nodeIdx))
      (fun level nodeIdx => pure (key'.top level nodeIdx))) (message : Message) :
    sign key message = sign key' message := by
  rw [sign_eq, sign_eq, signDigestLoop_congr_key digestAttemptLimit key key' hparameter hroot message]
  congr 1
  funext selected
  rcases selected with _ | ⟨randomness, index, leaves⟩
  · rfl
  · simp only [signAfterDigest_congr_top key key' hparameter hots hfts htop]

theorem gameRest_congr_top (adversary : Adversary) (publicKey : PublicKey) (key key' : SecretKey)
    (hparameter : key.parameter = key'.parameter)
    (hroot : key.root = key'.root) (hots : key.otsSecret = key'.otsSecret) (hfts : key.ftsSecret = key'.ftsSecret)
    (htop : TopRegionEq (m := OracleComp HashSpec) (fun level nodeIdx => pure (key.top level nodeIdx))
      (fun level nodeIdx => pure (key'.top level nodeIdx))) :
    gameRest scheme adversary publicKey key = gameRest scheme adversary publicKey key' := by
  have hsign : scheme.sign key = scheme.sign key' :=
    funext (sign_congr_top key key' hparameter hroot hots hfts htop)
  unfold gameRest signingOracle
  rw [hsign]

/-- A key up to its table off the cached region: parameter, root, secrets, and the table on the cached
levels (a superset of the region). Finitely many, unlike keys. -/
abbrev KeyCode :=
  PublicParameter × Digest × (Layer → TreeIndex → LeafIndex → ChainIndex → Digest) ×
    (Index → FtsTree → FtsLeaf → Digest) × (Fin maxLayerHeight → Fin (2 ^ maxLayerHeight) → Digest)

def KeyCode.key (code : KeyCode) : SecretKey :=
  ⟨code.1, code.2.1, code.2.2.1, code.2.2.2.1, fun level nodeIdx =>
    if h : level < maxLayerHeight ∧ nodeIdx < 2 ^ maxLayerHeight then code.2.2.2.2 ⟨level, h.1⟩ ⟨nodeIdx, h.2⟩
    else 0⟩

def keyCode (key : SecretKey) : KeyCode :=
  (key.parameter, key.root, key.otsSecret, key.ftsSecret, fun level nodeIdx => key.top level.val nodeIdx.val)

theorem keyCode_top (key : SecretKey) :
    TopRegionEq (m := OracleComp HashSpec) (fun level nodeIdx => pure ((keyCode key).key.top level nodeIdx))
      (fun level nodeIdx => pure (key.top level nodeIdx)) := by
  intro level hlevel nodeIdx hnodeIdx
  have hnode : nodeIdx < 2 ^ maxLayerHeight :=
    Nat.lt_of_lt_of_le hnodeIdx (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  simp only [KeyCode.key, keyCode, dif_pos (And.intro hlevel hnode)]

noncomputable instance keyCodeFintype : Fintype KeyCode := by
  classical
  infer_instance

attribute [irreducible] keyCodeFintype

theorem gameRest_keyCode (adversary : Adversary) (key : SecretKey) :
    gameRest scheme adversary ⟨(keyCode key).key.root, (keyCode key).key.parameter⟩ (keyCode key).key =
      gameRest scheme adversary ⟨key.root, key.parameter⟩ key :=
  gameRest_congr_top adversary _ _ _ rfl rfl rfl rfl (keyCode_top key)

noncomputable def frontierAdversaryImpl (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) :
    QueryImpl (OracleWorld + SigningSpec) (WriterT SigningBoundaryTrace ProbComp)
  | .inl input => (fixedHashWorld f).withTrace (signingBoundaryTrace parameter) input
  | .inr message => WriterT.mk (frontierSigningRun parameter root f ftsSecret words frontier message)

theorem simulateQ_expandedAdversaryImpl_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (htop : KeyTopHonest f key)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (input : (OracleWorld + SigningSpec).Domain) :
    simulateQ ((fixedHashWorld f).withTrace (signingBoundaryTrace key.parameter)) (expandedAdversaryImpl key input) =
      frontierAdversaryImpl key.parameter key.root f key.ftsSecret words frontier input := by
  cases input with
  | inl input => exact simulateQ_spec_query (impl := (fixedHashWorld f).withTrace (signingBoundaryTrace key.parameter)) input
  | inr message =>
      rw [show expandedAdversaryImpl key (.inr message) = sign key message from rfl,
        simulateQ_eq_fixedBoundaryRun]
      unfold frontierAdversaryImpl
      exact congrArg (fun result : ProbComp (Option Signature × SigningBoundaryTrace) =>
        (WriterT.mk result : WriterT SigningBoundaryTrace ProbComp (Option Signature)))
        (fixedBoundaryRun_sign_frontier key f words frontier hfrontier htop hwords message)

noncomputable def frontierAdversaryRun {α : Type} (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    ProbComp ((α × QueryLog SigningSpec) × SigningBoundaryTrace) :=
  ((simulateQ ((frontierAdversaryImpl parameter root f ftsSecret words frontier).withTraceAppend signingLogFragment)
    computation).run).run

theorem fixedBoundaryRun_adversary_frontier {α : Type} (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (htop : KeyTopHonest f key)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (computation : OracleComp (OracleWorld + SigningSpec) α) :
    fixedBoundaryRun key.parameter f
        (simulateQ (forwardOracles + signingOracle scheme key) computation).run =
      frontierAdversaryRun key.parameter key.root f key.ftsSecret words frontier computation := by
  rw [forwardOracles_add_signingOracle_eq_withTraceAppend]
  unfold fixedBoundaryRun frontierAdversaryRun
  congr 1
  apply simulateQ_writerAppend_compose
  intro input
  simp only [QueryImpl.withTraceAppend_apply]
  simp [simulateQ_expandedAdversaryImpl_frontier key f words frontier hfrontier htop hwords input]

noncomputable def frontierGameRest (parameter : PublicParameter) (root : Digest)
    (f : QueryImpl HashSpec Id) (ftsSecret : Index → FtsTree → FtsLeaf → Digest)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) (adversary : Adversary) :
    ProbComp (Bool × SigningBoundaryTrace) := do
  let result ← frontierAdversaryRun parameter root f ftsSecret words frontier
    (adversary.main ⟨root, parameter⟩)
  let checked := boundaryEval parameter f (verify ⟨root, parameter⟩ result.1.1.message result.1.1.signature)
  pure (decide (SigningTranscript.Valid result.1.2 ∧ ¬SigningTranscript.Contains result.1.2 result.1.1) && checked.1,
    result.2 * checked.2)

theorem fixedBoundaryRun_gameRest_frontier (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) (htop : KeyTopHonest f key)
    (hwords : ∀ index lay, FrontierReferenceWord key.parameter f key.ftsSecret words frontier index lay)
    (adversary : Adversary) :
    fixedBoundaryRun key.parameter f (gameRest scheme adversary ⟨key.root, key.parameter⟩ key) =
      frontierGameRest key.parameter key.root f key.ftsSecret words frontier adversary := by
  rw [gameRest, fixedBoundaryRun_bind, fixedBoundaryRun_adversary_frontier key f words frontier hfrontier htop hwords]
  unfold frontierGameRest
  apply bind_congr
  rintro ⟨⟨forgery, log⟩, trace⟩
  rw [fixedBoundaryRun_bind]
  change (fun final => (final.1, trace * final.2)) <$>
    (fixedBoundaryRun key.parameter f (liftM (verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature)) >>=
      fun checked => (fun final => (final.1, checked.2 * final.2)) <$>
        fixedBoundaryRun key.parameter f (pure
          (decide (SigningTranscript.Valid log ∧ ¬SigningTranscript.Contains log forgery) && checked.1))) = _
  rw [fixedBoundaryRun_lift_hash, pure_bind, fixedBoundaryRun_pure]
  simp only [map_pure, mul_one]

noncomputable def frontierRoot (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues) : Digest :=
  evalWithAnswerFn f (frontierTreeNode parameter topLayer rootTree (words topLayer rootTree)
    (frontier topLayer rootTree) (layerHeight topLayer) 0)

theorem frontierRoot_eq (key : SecretKey) (f : QueryImpl HashSpec Id)
    (words : OtsReferenceWords) (frontier : OtsFrontierValues)
    (hfrontier : IsSigningFrontier key f words frontier) :
    frontierRoot key.parameter f words frontier =
      evalWithAnswerFn f (treeRoot key.parameter topLayer rootTree (key.otsSecret topLayer rootTree)) :=
  eval_frontierTreeNode key.parameter f topLayer rootTree (key.otsSecret topLayer rootTree)
    (words topLayer rootTree) (frontier topLayer rootTree) (hfrontier topLayer rootTree) _ _

noncomputable def frontierGame (parameter : PublicParameter) (f : QueryImpl HashSpec Id)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (words : OtsReferenceWords)
    (frontier : OtsFrontierValues) (adversary : Adversary) : ProbComp (Bool × SigningBoundaryTrace) :=
  (fun result => (result.1, (FreeMonoid.of none) ^ keygenHashCost * result.2)) <$>
    frontierGameRest parameter (frontierRoot parameter f words frontier) f ftsSecret words frontier adversary

theorem fixedBoundaryRun_gameAfterSecrets_canonical (adversary : Adversary) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (ftsSecret : Index → FtsTree → FtsLeaf → Digest) (f : QueryImpl HashSpec Id) (dummy : OtsReferenceWords) :
    let root := evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
    let key : SecretKey := ⟨parameter, root, otsSecret, ftsSecret, honestTop f parameter (otsSecret topLayer rootTree)⟩
    let words := canonicalReferenceWords key f dummy
    fixedBoundaryRun parameter f (gameAfterSecrets adversary parameter otsSecret ftsSecret) =
      frontierGame parameter f ftsSecret words (canonicalFrontierValues key f words) adversary := by
  dsimp only
  let root := evalWithAnswerFn f (treeRoot parameter topLayer rootTree (otsSecret topLayer rootTree))
  let top := honestTop f parameter (otsSecret topLayer rootTree)
  let key : SecretKey := ⟨parameter, root, otsSecret, ftsSecret, top⟩
  let words := canonicalReferenceWords key f dummy
  let frontier := canonicalFrontierValues key f words
  have hfrontier := isSigningFrontier_canonical key f words
  have htop : KeyTopHonest f key := keyTopHonest_of_eq f key rfl
  change fixedBoundaryRun parameter f (gameAfterSecrets adversary parameter otsSecret ftsSecret) =
    frontierGame parameter f ftsSecret words frontier adversary
  have hroot := frontierRoot_eq key f words frontier hfrontier
  change frontierRoot parameter f words frontier = root at hroot
  have htopRoot : top (layerHeight topLayer) 0 = root := honestTop_root f parameter (otsSecret topLayer rootTree)
  rw [gameAfterSecrets, fixedBoundaryRun_bind, fixedBoundaryRun_lift_hash]
  have htree : boundaryEval parameter f (keygenTable parameter (otsSecret topLayer rootTree)) =
      (top, (FreeMonoid.of none) ^ keygenHashCost) := by
    exact boundaryEval_keygen parameter f (otsSecret topLayer rootTree)
  rw [htree, pure_bind]
  dsimp only
  rw [htopRoot, fixedBoundaryRun_gameRest_frontier key f words frontier hfrontier htop
    (frontierReferenceWord_canonical key f dummy)]
  rw [frontierGame, hroot]

end SphincsSecurity.Concrete
