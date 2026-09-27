import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Reference.BoundaryHashEvaluation
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundaryHashAtLeast signDigestLoop

theorem boundaryHashAtLeast_lift_sequenceFin {α : Type} {n : Nat} (parameter : PublicParameter)
    (computation : Fin n → OracleComp HashSpec α) (cost : Fin n → Nat)
    (hcost : ∀ i, BoundaryHashAtLeast parameter (liftM (computation i)) (cost i)) :
    BoundaryHashAtLeast parameter (liftM (sequenceFin computation)) (∑ i, cost i) := by
  induction n with
  | zero =>
      rw [Fin.sum_univ_zero]
      exact boundaryHashAtLeast_zero _ _
  | succ n ih =>
      rw [sequenceFin, liftM_bind, Fin.sum_univ_succ]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (hcost 0)
      intro head
      rw [liftM_bind, ← Nat.add_zero (∑ i : Fin n, cost i.succ)]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _ _ (fun i => hcost i.succ))
      intro tail
      exact boundaryHashAtLeast_zero _ _

theorem boundaryHashAtLeast_ftsNode (traceParameter parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    BoundaryHashAtLeast traceParameter
      (liftM (ftsNode parameter index tree secret level nodeIdx : OracleComp HashSpec Digest))
      (2 ^ (level + 1) - 1) := by
  induction level generalizing nodeIdx with
  | zero =>
      rw [ftsNode_zero_eq]
      exact boundaryHashAtLeast_tweakableHash traceParameter parameter
        (.ftsLeaf index tree (ftsLeafOfNat nodeIdx)) (digestBytes (secret (ftsLeafOfNat nodeIdx)))
  | succ level ih =>
      rw [ftsNode_succ_eq, liftM_bind]
      have hpower : 0 < 2 ^ (level + 1) := by positivity
      have hcost : 2 ^ (level + 1 + 1) - 1 = (2 ^ (level + 1) - 1) + ((2 ^ (level + 1) - 1) + 1) := by
        rw [pow_succ]
        omega
      rw [hcost]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _)
      intro left
      rw [liftM_bind]
      apply boundaryHashAtLeast_bind _ _ _ _ _ (ih _)
      intro right
      exact boundaryHashAtLeast_tweakableHash _ _ _ _

theorem boundaryHashAtLeast_buildLevels (traceParameter : PublicParameter)
    (hashNode : Nat → Nat → Digest → Digest → OracleComp HashSpec Digest)
    (hhash : ∀ level nodeIdx left right,
      BoundaryHashAtLeast traceParameter (liftM (hashNode level nodeIdx left right)) 1)
    (height : Nat) (leaves : Nat → Digest) (levels : Nat) :
    BoundaryHashAtLeast traceParameter (liftM (buildLevels hashNode height leaves levels))
      (levelsHashCost height levels) := by
  induction levels with
  | zero => exact boundaryHashAtLeast_zero _ _
  | succ levels ih =>
      rw [buildLevels, liftM_bind, levelsHashCost]
      apply boundaryHashAtLeast_bind _ _ _ _ _ ih
      intro table
      rw [buildLevel, liftM_bind, liftM_bind]
      rw [bind_assoc]
      refine BoundaryHashAtLeast.mono (a := 2 ^ (height - (levels + 1)) + 0) ?_ (by omega)
      apply boundaryHashAtLeast_bind _ _ _ _ 0
      · have h := boundaryHashAtLeast_lift_sequenceFin traceParameter
          (fun nodeIdx : Fin (2 ^ (height - (levels + 1))) =>
            hashNode (levels + 1) nodeIdx.val (table levels (2 * nodeIdx.val)) (table levels (2 * nodeIdx.val + 1)))
          (fun _ => 1) (fun _ => hhash _ _ _ _)
        simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] using h
      · intro _
        exact boundaryHashAtLeast_zero _ _

theorem boundaryHashAtLeast_buildFtsTree (traceParameter parameter : PublicParameter) (index : Index)
    (tree : FtsTree) (secret : FtsLeaf → Digest) (leaf : FtsLeaf) :
    BoundaryHashAtLeast traceParameter
      (liftM (buildFtsTree parameter index tree (fun leaf => pure (secret leaf)) leaf :
        OracleComp HashSpec _)) (2 ^ (ftsTreeHeight + 1) - 1) := by
  have hcost : 2 ^ (ftsTreeHeight + 1) - 1 = 2 ^ ftsTreeHeight + (levelsHashCost ftsTreeHeight ftsTreeHeight + 0) := by
    rw [levelsHashCost_self, pow_succ]
    have := Nat.two_pow_pos ftsTreeHeight
    omega
  rw [hcost, buildFtsTree, liftM_bind]
  apply boundaryHashAtLeast_bind _ _ _ _ _
  · have h := boundaryHashAtLeast_lift_sequenceFin traceParameter
      (fun leafIdx : FtsLeaf => (do
        let value ← (pure (secret leafIdx) : OracleComp HashSpec Digest)
        let hashed ← ftsLeafHash parameter index tree leafIdx value
        return (value, hashed)))
      (fun _ => 1) (fun leafIdx => by
        rw [pure_bind, liftM_bind, ← Nat.add_zero 1]
        apply boundaryHashAtLeast_bind _ _ _ _ _ (boundaryHashAtLeast_tweakableHash _ _ _ _)
        intro _
        exact boundaryHashAtLeast_zero _ _)
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one] using h
  · intro leaves
    rw [liftM_bind]
    apply boundaryHashAtLeast_bind _ _ _ _ _
      (boundaryHashAtLeast_buildLevels _ _ (fun _ _ _ _ => boundaryHashAtLeast_tweakableHash _ _ _ _) _ _ _)
    intro _
    exact boundaryHashAtLeast_zero _ _

/-- **Every signature the signer completes builds the whole forest.** -/
theorem boundaryHashAtLeast_buildForest (traceParameter parameter : PublicParameter) (index : Index)
    (secret : FtsTree → FtsLeaf → Digest) (leaves : IndexGroup → FtsLeaf) :
    BoundaryHashAtLeast traceParameter
      (liftM (buildForest parameter index (fun tree leaf => pure (secret tree leaf)) leaves :
        OracleComp HashSpec _)) ftsOpenHashCost := by
  rw [ftsOpenHashCost_def, buildForest, liftM_bind]
  apply boundaryHashAtLeast_bind _ _ _ _ _
    (boundaryHashAtLeast_lift_sequenceFin traceParameter _ (fun _ => 2 ^ (ftsTreeHeight + 1) - 1)
      (fun tree => boundaryHashAtLeast_buildFtsTree _ _ _ _ _ _))
  intro trees
  rw [liftM_bind, ← Nat.add_zero 1]
  apply boundaryHashAtLeast_bind _ _ _ _ _ (boundaryHashAtLeast_tweakableHash _ _ _ _)
  intro _
  exact boundaryHashAtLeast_zero _ _

theorem boundaryHashAtLeast_signAttempt (parameter : PublicParameter) (key : SecretKey)
    (message : Message) (randomness : Randomness) :
    BoundaryHashAtLeast parameter (liftM (signAttempt key message randomness : OracleComp HashSpec _)) 1 := by
  unfold signAttempt messageDigest
  rw [liftM_bind, liftM_bind, bind_assoc]
  apply boundaryHashAtLeast_bind _ _ _ 1 0 (boundaryHashAtLeast_hash _ _)
  intro output
  exact boundaryHashAtLeast_zero _ _

theorem boundaryHashAtLeast_signDigestLoop_bind {α : Type} (parameter : PublicParameter)
    (key : SecretKey) (message : Message) (cost attempts : Nat)
    (next : Option (Randomness × Index × (IndexGroup → FtsLeaf)) → OracleComp OracleWorld α)
    (hnext : ∀ selected, BoundaryHashAtLeast parameter (next (some selected)) cost) :
    BoundaryHashAtLeast parameter (signDigestLoop attempts key message >>= next) (min attempts cost) := by
  induction attempts with
  | zero => exact boundaryHashAtLeast_zero _ _
  | succ attempts ih =>
      rw [signDigestLoop, bind_assoc, ← Nat.zero_add (min (attempts + 1) cost)]
      apply boundaryHashAtLeast_bind _ _ _ 0 _ (boundaryHashAtLeast_zero _ _)
      intro randomness
      rw [bind_assoc]
      apply BoundaryHashAtLeast.mono (a := 1 + min attempts cost) ?_ (by omega)
      apply boundaryHashAtLeast_bind _ _ _ 1 _ (boundaryHashAtLeast_signAttempt _ _ _ _)
      intro attempt
      cases attempt with
      | none => exact ih
      | some selected =>
          simp only [pure_bind]
          exact BoundaryHashAtLeast.mono (hnext _) (min_le_right _ _)

theorem boundaryHashAtLeast_sign (parameter : PublicParameter) (key : SecretKey) (message : Message) :
    BoundaryHashAtLeast parameter (sign key message) ftsOpenHashCost := by
  rw [sign_eq]
  apply BoundaryHashAtLeast.mono (a := min digestAttemptLimit ftsOpenHashCost) ?_
    (le_min ftsOpenHashCost_le_digestAttemptLimit le_rfl)
  apply boundaryHashAtLeast_signDigestLoop_bind
  rintro ⟨randomness, index, leaves⟩
  show BoundaryHashAtLeast parameter (liftM (signAfterDigest key randomness index leaves :
      OracleComp HashSpec (Option Signature))) ftsOpenHashCost
  rw [signAfterDigest, signFrom, liftM_bind, ← Nat.add_zero ftsOpenHashCost]
  apply boundaryHashAtLeast_bind _ _ _ _ _ (boundaryHashAtLeast_buildForest _ _ _ _ _)
  intro _
  exact boundaryHashAtLeast_zero _ _

end SphincsSecurity.Concrete
