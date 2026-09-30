import SigGolfCandidate.Keygen.Main
import SigGolfCandidate.Expand.Main
import SigGolfCandidate.Equiv.Main
import SigGolfCandidate.Final.Pending
import SigGolfCandidate.Final.Pipeline
import SigGolfCandidate.Final.Abstract

/-!
# From the phase refinements to the abstract scheme

* `refinements`: the four bytecode refinements in the form of `Equiv.Refinements` (keygen and
  expand proved, sign and verify pending).
* `successPipe_eq`: the success bit of the honest pipeline is the abstract honest game, relabelled
  by `padQ`.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Final
open SigGolf
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits
  SigGolfCandidate.submission SigGolf.Output SigGolf.Input

theorem keygen_value (sk : SecretKey) :
    (fun r => r.value) <$> submission.run .keygen sk =
      (fun pk => some (pk, (0 : Cache))) <$> Ref.keygenRef sk := by
  rw [Keygen.keygen_run, Functor.map_map]

theorem sign_value (hS : SignRefinementStatement) (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => r.value) <$> submission.run .sign (sk, cache, m) = Ref.signRef sk m := by
  have h := congrArg (fun x => Prod.fst <$> x) (hS sk cache m)
  simp only [Functor.map_map] at h
  exact h.trans (Sign.fst_countBoth _)

theorem expand_value (m : Message) (pk : PublicKey) (σ : Bytes 7756) :
    (fun r => r.value) <$> submission.run .expand (m, pk, σ) = pure (some (Ref.expandRef σ)) := by
  rw [Expand.expand_run, map_pure]

theorem isSome_countCalls (X : OracleComp HashSpec Bool) :
    (fun p : Option Unit × Nat => p.1.isSome) <$>
      ((fun p : Bool × Nat => (if p.1 then some () else none, p.2)) <$> Ref.countCalls X) = X := by
  rw [Functor.map_map]
  have e : (fun p : Bool × Nat => ((if p.1 then some () else none, p.2) : Option Unit × Nat).1.isSome) =
      Prod.fst := by
    funext p; rcases p with ⟨_ | _, n⟩ <;> rfl
  rw [e, Ref.fst_countCalls]

theorem verify_value (hV : VerifyRefinementStatement) (m : Message) (pk : PublicKey)
    (w : Bytes 7756) :
    (fun r => r.value.isSome) <$> submission.run .verify (m, pk, w) = Ref.verifyRef m pk w := by
  have h := congrArg (fun x => (fun p : Option Unit × Nat => p.1.isSome) <$> x) (hV m pk w)
  simp only at h
  rw [Functor.map_map] at h
  exact h.trans (isSome_countCalls _)

/-- The four bytecode refinements, in the form used by `Equiv.submission_secure`. -/
theorem refinements (hS : SignRefinementStatement) (hV : VerifyRefinementStatement) :
    Equiv.Refinements where
  keygen sk := by
    have h := congrArg (fun x => (fun p => (p.1, p.2.1)) <$> x) (Keygen.keygen_run_counts sk)
    simp only [Functor.map_map] at h
    rw [h, ← Sign.countBoth_calls]
    simp only [Functor.map_map]
  sign sk cache m := by
    have h := congrArg (fun x => (fun p => (p.1, p.2.1)) <$> x) (hS sk cache m)
    simp only [Functor.map_map] at h
    exact h.trans ((Sign.countBoth_calls _).trans (id_map _).symm)
  expand m pk σ := by
    rw [Expand.expand_run, map_pure]
  verify m pk w := hV m pk w

/-- The honest pipeline's success bit, with the reference programs. -/
theorem successPipe_eq_ref (hS : SignRefinementStatement) (hV : VerifyRefinementStatement)
    (sk : SecretKey) (m : Message) :
    successPipe submission sk m = (do
      let pk ← Ref.keygenRef sk
      match ← Ref.signRef sk m with
      | none => pure false
      | some σ => Ref.verifyRef m pk (Ref.expandRef σ)) := by
  unfold successPipe
  rw [keygen_value, bind_map_left]
  refine bind_congr fun pk => ?_
  simp only
  rw [sign_value hS]
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · rfl
  simp only
  rw [expand_value, pure_bind]
  exact verify_value hV m pk _


/-- The reference pipeline is the abstract honest game relabelled by `padQ`. -/
theorem ref_pipeline_eq (sk : SecretKey) (m : Message) :
    (do
      let pk ← Ref.keygenRef sk
      match ← Ref.signRef sk m with
      | none => pure false
      | some σ => Ref.verifyRef m pk (Ref.expandRef σ)) =
    relabel Equiv.padQ (game sk m) := by
  have hs : ∀ root : SphincsSecurity.Digest, Ref.signRef sk m =
      Option.map Equiv.sigCodec.symm <$>
        relabel Equiv.padQ (SphincsSecurity.Seeded.sign (m := Equiv.AComp) ⟨sk, 0, root⟩ m) :=
    fun root => Equiv.signRef_eq ⟨sk, 0, root⟩ rfl m
  rw [Equiv.keygenRef_eq]
  unfold game SphincsSecurity.Seeded.keygenFromSeed
  simp only [relabel_bind, bind_assoc, map_bind, relabel_pure, pure_bind, map_pure]
  refine bind_congr fun t => ?_
  rw [hs t.2.2, bind_map_left]
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · rfl
  · show Ref.verifySigRef m t.2.2 (Equiv.sigCodec.symm σ) = _
    rw [Equiv.verifySigRef_eq, Equiv.sigCodec.apply_symm_apply]


/-- **The honest pipeline's success bit is the abstract honest game** (relabelled by `padQ`). -/
theorem success_honest_eq_game (hS : SignRefinementStatement) (hV : VerifyRefinementStatement)
    (sk : SecretKey) (m : Message) :
    HonestResult.success <$> submission.honest sk m = relabel Equiv.padQ (game sk m) := by
  rw [success_honest_eq, successPipe_eq_ref hS hV, ref_pipeline_eq]

end SigGolfCandidate.Final
