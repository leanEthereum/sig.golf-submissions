import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.Capped
/-!
# The verifier's hash calls

Verification makes at most `verifyHashBound` hash queries, and every query it makes has even length:
all its inputs are tweakable-hash inputs with even payloads. The marker of the capped adversary has
odd length, so the verifier never queries it.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec

/-- At most `budget` queries, each of even length. -/
def EvenBound {α : Type} (computation : OracleComp HashSpec α) (budget : Nat) : Prop :=
  computation.IsQueryBound budget (fun input remaining => Even input.length ∧ 0 < remaining)
    (fun _ remaining => remaining - 1)

theorem evenBound_pure {α : Type} (value : α) (budget : Nat) :
    EvenBound (pure value : OracleComp HashSpec α) budget := trivial

theorem evenBound_query_bind_iff {α : Type} (input : HashInput) (next : HashOutput → OracleComp HashSpec α) (budget : Nat) :
    EvenBound (liftM (HashSpec.query input) >>= next) budget ↔
      (Even input.length ∧ 0 < budget) ∧ ∀ answer, EvenBound (next answer) (budget - 1) :=
  Iff.rfl

theorem EvenBound.mono {α : Type} {computation : OracleComp HashSpec α} {budget budget' : Nat}
    (h : EvenBound computation budget) (hle : budget ≤ budget') : EvenBound computation budget' := by
  induction computation using OracleComp.inductionOn generalizing budget budget' with
  | pure value => trivial
  | query_bind input next ih =>
      rw [evenBound_query_bind_iff] at h ⊢
      exact ⟨⟨h.1.1, by omega⟩, fun answer => ih answer (h.2 answer) (by omega)⟩

theorem evenBound_bind {α β : Type} {first : OracleComp HashSpec α} {next : α → OracleComp HashSpec β}
    {budget budget' : Nat} (hfirst : EvenBound first budget) (hnext : ∀ value, EvenBound (next value) budget') :
    EvenBound (first >>= next) (budget + budget') := by
  induction first using OracleComp.inductionOn generalizing budget with
  | pure value => exact (hnext value).mono (Nat.le_add_left _ _)
  | query_bind input continuation ih =>
      rw [evenBound_query_bind_iff] at hfirst
      rw [bind_assoc, evenBound_query_bind_iff]
      refine ⟨⟨hfirst.1.1, by omega⟩, fun answer => ?_⟩
      exact (ih answer (hfirst.2 answer)).mono (by omega)

theorem evenBound_map {α β : Type} {computation : OracleComp HashSpec α} (g : α → β) {budget : Nat}
    (h : EvenBound computation budget) : EvenBound (g <$> computation) budget := by
  rw [map_eq_bind_pure_comp]
  exact (evenBound_bind h (fun value => evenBound_pure (g value) 0) : EvenBound _ (budget + 0))

theorem length_tweakableHashInput (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput) :
    (tweakableHashInput parameter domain payload).length = 32 + payload.length := by
  simp only [tweakableHashInput, tweakBytes, fieldBytes, bytesLE, List.length_append, List.length_ofFn,
    List.length_singleton]

theorem evenBound_tweakableHash (parameter : PublicParameter) (domain : HashDomain) (payload : HashInput)
    (hpayload : Even payload.length) :
    EvenBound (tweakableHash parameter domain payload : OracleComp HashSpec Digest) 1 := by
  change EvenBound (liftM (HashSpec.query (tweakableHashInput parameter domain payload)) >>= fun output =>
    pure (truncateHash output)) 1
  rw [evenBound_query_bind_iff, length_tweakableHashInput]
  exact ⟨⟨by rw [Nat.even_add]; exact iff_of_true (by decide) hpayload, by decide⟩, fun _ => trivial⟩

theorem even_length_bytesLE (count : Nat) (value : BitVec (8 * count)) (hcount : Even count) :
    Even (bytesLE count value).length := by
  simpa only [bytesLE, List.length_ofFn] using hcount

theorem evenBound_sequenceFin {α : Type} {n : Nat} (computation : Fin n → OracleComp HashSpec α) (budget : Nat)
    (h : ∀ index, EvenBound (computation index) budget) :
    EvenBound (sequenceFin computation) (n * budget) := by
  induction n with
  | zero => exact evenBound_pure _ _
  | succ n ih =>
      rw [sequenceFin]
      have htail := ih (fun index => computation index.succ) (fun index => h index.succ)
      have h' := evenBound_bind (h 0) (fun head =>
        (evenBound_bind htail (fun tail => evenBound_pure (Fin.cases head tail : Fin (n + 1) → α) 0) :
          EvenBound _ (n * budget + 0)))
      refine h'.mono ?_
      rw [Nat.succ_mul]
      omega

theorem evenBound_chainWalk (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chainIdx : ChainIndex) (start steps : Nat) (value : Digest) :
    EvenBound (chainWalk parameter lay tree leaf chainIdx start steps value : OracleComp HashSpec Digest) steps := by
  induction steps with
  | zero => exact evenBound_pure _ _
  | succ steps ih =>
      rw [chainWalk]
      refine evenBound_bind ih fun previous => ?_
      split
      · exact evenBound_tweakableHash _ _ _ (even_length_bytesLE 16 previous (by decide))
      · exact (evenBound_pure _ _)


theorem length_bytesLE (count : Nat) (value : BitVec (8 * count)) : (bytesLE count value).length = count :=
  List.length_ofFn

theorem length_flatMap_bytes (values : List (BitVec (8 * 16))) :
    (values.flatMap (bytesLE 16)).length = 16 * values.length := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      rw [List.flatMap_cons, List.length_append, ih, length_bytesLE, List.length_cons]
      ring

theorem even_length_flatMap_bytes {n : Nat} (values : Fin n → Digest) :
    Even ((List.ofFn values).flatMap (bytesLE 16)).length := by
  show Even (List.flatMap (bytesLE 16) (List.ofFn (α := BitVec (8 * 16)) values)).length
  rw [length_flatMap_bytes]
  exact ⟨8 * (List.ofFn (α := BitVec (8 * 16)) values).length, by ring⟩

theorem evenBound_otsLeaf (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (counter : Counter) (values : ChainIndex → Digest) :
    EvenBound (otsLeaf parameter lay tree leaf message counter values : OracleComp HashSpec (Option Digest))
      (1 + (numChains * (chainLength - 1) + 1)) := by
  rw [otsLeaf]
  refine evenBound_bind (budget := 1) ?_ fun encoded => ?_
  · rw [encode]
    refine (evenBound_bind (evenBound_tweakableHash _ _ _ ?_) (fun _ => evenBound_pure _ 0) : EvenBound _ (1 + 0))
    simp only [List.length_append, bytesLE, List.length_ofFn]
    decide
  · cases encoded with
    | none => exact evenBound_pure _ _
    | some encoding =>
        refine evenBound_bind (evenBound_sequenceFin _ (chainLength - 1) fun chainIdx => ?_) fun endpoints => ?_
        · exact (evenBound_chainWalk _ _ _ _ _ _ _ _).mono (by omega)
        · exact (evenBound_bind (evenBound_tweakableHash _ _ _ (even_length_flatMap_bytes _))
            (fun _ => evenBound_pure _ 0) : EvenBound _ (1 + 0))


theorem even_length_nodePayload (left right : Digest) : Even (nodePayload left right).length := by
  simp only [nodePayload, List.length_append, bytesLE, List.length_ofFn]
  decide

theorem evenBound_treeFold (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (path : Nat → Digest) (levels : Nat) (value : Digest) :
    EvenBound (treeFold parameter lay tree leaf path levels value : OracleComp HashSpec Digest) levels := by
  induction levels with
  | zero => exact evenBound_pure _ _
  | succ levels ih =>
      rw [treeFold]
      refine evenBound_bind ih fun current => ?_
      split
      · exact evenBound_tweakableHash _ _ _ (even_length_nodePayload _ _)
      · exact evenBound_tweakableHash _ _ _ (even_length_nodePayload _ _)

/-- The hash queries of one verified layer. -/
def layerVerifyBound : Nat := 1 + (numChains * (chainLength - 1) + 1) + maxLayerHeight

theorem evenBound_verifyLayers (parameter : PublicParameter) (index : Index) (signature : Signature)
    (remaining : Nat) (message : Digest) :
    EvenBound (verifyLayers parameter index signature remaining message : OracleComp HashSpec (Option Digest))
      (remaining * layerVerifyBound) := by
  induction remaining generalizing message with
  | zero => exact evenBound_pure _ _
  | succ remaining ih =>
      rw [verifyLayers]
      split
      · rename_i hlayer
        refine (evenBound_bind (evenBound_otsLeaf _ _ _ _ _ _ _) fun leafValue => ?_ :
          EvenBound _ (1 + (numChains * (chainLength - 1) + 1) + (maxLayerHeight + remaining * layerVerifyBound))).mono ?_
        · cases leafValue with
          | none => exact evenBound_pure _ _
          | some value =>
              refine evenBound_bind ((evenBound_treeFold _ _ _ _ _ _ _).mono ?_) fun root => ih root
              exact layerHeight_le _
        · rw [Nat.succ_mul, layerVerifyBound]
          omega
      · exact evenBound_pure _ _

theorem even_length_foldPayload (right : Bool) (sibling current : Digest) :
    Even (foldPayload right sibling current).length := by
  unfold foldPayload
  cases right
  · exact even_length_nodePayload _ _
  · exact even_length_nodePayload _ _

theorem evenBound_foldSegment (parameter : PublicParameter) (index : Index) (segment : Segment)
    (remaining position : Nat) (current : Digest) (heap : Nat) :
    EvenBound (foldSegment parameter index segment remaining position current heap :
      OracleComp HashSpec (Digest × Nat)) remaining := by
  induction remaining generalizing position current heap with
  | zero => exact evenBound_pure _ _
  | succ remaining ih =>
      rw [foldSegment]
      exact (evenBound_bind (evenBound_tweakableHash _ _ _ (even_length_foldPayload _ _ _))
        fun parent => ih _ _ _).mono (by omega)

/-- The hash queries of one segment: the pending hash and at most `14` folds. -/
def segmentVerifyBound : Nat := 1 + ftsTreeHeight

theorem evenBound_recoverSegments (parameter : PublicParameter) (index : Index)
    (segments : Fin ftsSegments → Segment) (fuel : Nat) : ∀ (pending : PendingHash) (state : RecoverState),
    EvenBound (recoverSegments parameter index segments fuel pending state :
      OracleComp HashSpec (Option RecoverState)) (fuel * segmentVerifyBound) := by
  induction fuel with
  | zero => intro pending state; exact evenBound_pure _ _
  | succ fuel ih =>
      intro pending state
      rw [recoverSegments]
      split
      · rename_i hsegment
        dsimp only
        split
        · exact evenBound_pure _ _
        · rename_i hfolds
          split
          · exact evenBound_pure _ _
          cases pending <;>
          · refine (evenBound_bind (budget := 1) ?_ fun start => evenBound_bind
              ((evenBound_foldSegment parameter index _ _ 0 start state.heap).mono (Nat.le_of_not_lt hfolds))
              fun folded => ?_ : EvenBound _ (1 + (ftsTreeHeight + fuel * segmentVerifyBound))).mono ?_
            · first
                | exact evenBound_tweakableHash _ _ _ (even_length_bytesLE 16 _ (by decide))
                | exact evenBound_tweakableHash _ _ _ (even_length_nodePayload _ _)
            · split <;> (try split) <;> (try split) <;> first | exact evenBound_pure _ _ | exact ih _ _
            · rw [Nat.succ_mul, segmentVerifyBound]
              omega
      · exact evenBound_pure _ _

/-- The hash queries of one opened leaf: at most `29` segments. -/
def leafVerifyBound : Nat := ftsSegments * segmentVerifyBound

theorem evenBound_recoverLeaves (parameter : PublicParameter) (index : Index) (values : SlotCode → Nat)
    (fts : FtsSignature) (remaining position previous : Nat) (state : RecoverState) :
    EvenBound (recoverLeaves parameter index values fts remaining position previous state :
      OracleComp HashSpec (Option RecoverState)) (remaining * leafVerifyBound) := by
  induction remaining generalizing position previous state with
  | zero => exact evenBound_pure _ _
  | succ remaining ih =>
      rw [recoverLeaves]
      split
      · dsimp only
        split
        · exact evenBound_pure _ _
        · split
          · exact evenBound_pure _ _
          · refine (evenBound_bind (evenBound_recoverSegments _ _ _ _ _ _) fun result => ?_ :
              EvenBound _ (ftsSegments * segmentVerifyBound + remaining * leafVerifyBound)).mono ?_
            · cases result with
              | none => exact evenBound_pure _ _
              | some state' => exact ih _ _ _
            · rw [Nat.succ_mul, leafVerifyBound]
              omega
      · exact evenBound_pure _ _

/-- The hash queries of the PORS stack machine: `15` leaves of at most `29` segments each (a crude bound;
the segments of all leaves together are at most `29`). -/
def ftsVerifyBound : Nat := ftsOpenings * leafVerifyBound

theorem evenBound_ftsRecover (parameter : PublicParameter) (index : Index) (values : SlotCode → Nat)
    (fts : FtsSignature) :
    EvenBound (ftsRecover parameter index values fts : OracleComp HashSpec (Option Digest)) ftsVerifyBound := by
  rw [ftsRecover]
  refine (evenBound_bind (evenBound_recoverLeaves _ _ _ _ _ _ _ _) fun result => ?_ :
    EvenBound _ (ftsOpenings * leafVerifyBound + 0)).mono (by rw [ftsVerifyBound]; omega)
  cases result with
  | none => exact evenBound_pure _ _
  | some state =>
      dsimp only
      split <;> exact evenBound_pure _ _

/-- The hash queries of one verification. -/
def verifyHashBound : Nat :=
  1 + (ftsVerifyBound + numLayers * layerVerifyBound)

theorem evenBound_verify (publicKey : PublicKey) (message : Message) (signature : Signature) :
    EvenBound (verify publicKey message signature : OracleComp HashSpec Bool) verifyHashBound := by
  rw [verify]
  split
  · rw [verifyCore]
    have hdigest : EvenBound (messageDigest publicKey.parameter publicKey.root message signature.randomness :
        OracleComp HashSpec MessageDigest) 1 := by
      change EvenBound (liftM (HashSpec.query (tweakableHashInput publicKey.parameter .message
        (messageDigestPayload publicKey.root message signature.randomness))) >>= fun output =>
          pure (truncateMessageDigest output)) 1
      rw [evenBound_query_bind_iff, length_tweakableHashInput]
      refine ⟨⟨?_, by decide⟩, fun _ => trivial⟩
      simp only [messageDigestPayload, List.length_append, bytesLE, List.length_ofFn]
      decide
    refine evenBound_bind hdigest fun digest => ?_
    refine evenBound_bind (evenBound_ftsRecover _ _ _ _) fun key => ?_
    cases key with
    | none => exact (evenBound_pure _ _)
    | some key =>
        refine (evenBound_bind (evenBound_verifyLayers _ _ _ _ _) fun root => ?_ :
          EvenBound _ (numLayers * layerVerifyBound + 0))
        cases root <;> exact evenBound_pure _ _
  · exact evenBound_pure _ _

theorem verifyHashBound_eq : verifyHashBound = 8061 := by
  simp only [verifyHashBound, ftsVerifyBound, leafVerifyBound, segmentVerifyBound, layerVerifyBound]
  decide

end SphincsSecurity.Concrete.EventSmall
