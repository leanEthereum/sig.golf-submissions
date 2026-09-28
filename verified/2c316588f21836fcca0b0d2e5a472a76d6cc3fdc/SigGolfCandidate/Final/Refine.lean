import SigGolfCandidate.Expand.Main
import SigGolfCandidate.Equiv.Main
import SigGolfCandidate.Final.Pending
import SigGolfCandidate.Final.Pipeline
import SigGolfCandidate.Final.Abstract

/-!
# From the phase refinements to the abstract scheme

* `refinements`: the four bytecode refinements in the form of `Equiv.Refinements` (expand proved,
  keygen, sign and verify pending).
* `successPipe_eq`: the success bit of the honest pipeline is the abstract honest game, relabelled
  by `fmtQ`.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Final
open SigGolfCandidate.Legacy
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits
  SigGolfCandidate.submission SigGolfCandidate.Legacy.Output SigGolfCandidate.Legacy.Input

theorem keygen_value (hK : KeygenRefinementStatement) (sk : SecretKey) :
    (fun r => r.value) <$> submission.run .keygen sk = some <$> Ref.keygenRef sk := by
  have h := congrArg (fun x => Prod.fst <$> x) (hK sk)
  simp only [Functor.map_map] at h
  refine h.trans ?_
  have e : (fun a : (SigGolfCandidate.Legacy.PublicKey × SigGolfCandidate.Cache) × Nat × Nat => some a.1) <$>
      Sign.countBoth (Ref.keygenRef sk) = some <$> (Prod.fst <$> Sign.countBoth (Ref.keygenRef sk)) :=
    (Functor.map_map _ _ _).symm
  rw [e, Sign.fst_countBoth]

theorem sign_value (hS : SignRefinementStatement) (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => r.value) <$> submission.run .sign (sk, cache, m) = Ref.signRef sk cache m := by
  have h := congrArg (fun x => Prod.fst <$> x) (hS sk cache m)
  simp only [Functor.map_map] at h
  exact h.trans (Sign.fst_countBoth _)

theorem expand_value (m : Message) (pk : PublicKey) (σ : Bytes submission.sizes.signature) :
    (fun r => r.value) <$> submission.run .expand (m, pk, σ) = Ref.expandRef m pk σ := by
  have h := congrArg (fun x => Prod.fst <$> x) (Expand.expand_refines_counts m pk σ)
  simp only [Functor.map_map] at h
  exact h.trans (Sign.fst_countBoth _)

theorem isSome_countCalls (X : OracleComp HashSpec Bool) :
    (fun p : Option Unit × Nat => p.1.isSome) <$>
      ((fun p : Bool × Nat => (if p.1 then some () else none, p.2)) <$> Ref.countCalls X) = X := by
  rw [Functor.map_map]
  have e : (fun p : Bool × Nat => ((if p.1 then some () else none, p.2) : Option Unit × Nat).1.isSome) =
      Prod.fst := by
    funext p; rcases p with ⟨_ | _, n⟩ <;> rfl
  rw [e, Ref.fst_countCalls]

theorem verify_value (hV : VerifyRefinementStatement) (m : Message) (pk : PublicKey)
    (w : Bytes submission.sizes.witness) :
    (fun r => r.value.isSome) <$> submission.run .verify (m, pk, w) = Ref.verifyRef m pk w := by
  have h := congrArg (fun x => (fun p : Option Unit × Nat => p.1.isSome) <$> x) (hV m pk w)
  simp only at h
  rw [Functor.map_map] at h
  exact h.trans (isSome_countCalls _)

/-- The four bytecode refinements, in the form used by `Equiv.submission_secure`. -/
theorem refinements (hK : KeygenRefinementStatement) (hS : SignRefinementStatement)
    (hV : VerifyRefinementStatement) : Equiv.Refinements where
  keygen sk := by
    have h := congrArg (fun x => (fun p => (p.1, p.2.1)) <$> x) (hK sk)
    simp only [Functor.map_map] at h
    rw [h, ← Sign.countBoth_calls]
    simp only [Functor.map_map]
  sign sk cache m := by
    have h := congrArg (fun x => (fun p => (p.1, p.2.1)) <$> x) (hS sk cache m)
    simp only [Functor.map_map] at h
    exact h.trans ((Sign.countBoth_calls _).trans (id_map _).symm)
  expand m pk σ := by
    rw [Expand.expand_refines]
    exact id_map _
  verify m pk w := hV m pk w

/-- The honest pipeline's success bit, with the reference programs. -/
theorem successPipe_eq_ref (hK : KeygenRefinementStatement) (hS : SignRefinementStatement)
    (hV : VerifyRefinementStatement) (sk : SecretKey) (m : Message) :
    successPipe submission sk m = (do
      let (pk, cache) ← Ref.keygenRef sk
      match ← Ref.signRef sk cache m with
      | none => pure false
      | some σ =>
        match ← Ref.expandRef m pk σ with
        | none => pure false
        | some w => Ref.verifyRef m pk w) := by
  unfold successPipe
  rw [keygen_value hK, bind_map_left]
  refine bind_congr fun kc => ?_
  rcases kc with ⟨pk, cache⟩
  simp only
  rw [sign_value hS]
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · rfl
  simp only
  rw [expand_value]
  refine bind_congr fun e => ?_
  rcases e with _ | w
  · rfl
  · exact verify_value hV m pk _

/-- The reference pipeline is the abstract honest game relabelled by `fmtQ`. -/
theorem ref_pipeline_eq (sk : SecretKey) (m : Message) :
    (do
      let (pk, cache) ← Ref.keygenRef sk
      match ← Ref.signRef sk cache m with
      | none => pure false
      | some σ =>
        match ← Ref.expandRef m pk σ with
        | none => pure false
        | some w => Ref.verifyRef m pk w) =
    relabel Equiv.fmtQ (gameX sk m) := by
  have hs : ∀ (root : SphincsSecurity.Digest) (c : SphincsSecurity.TopCache),
      Ref.signRef sk (Equiv.cacheEnc c) m =
        Option.map Equiv.compress <$>
          relabel Equiv.fmtQ (SphincsSecurity.Seeded.sign (m := Equiv.AComp) ⟨sk, 0, root⟩ c m) :=
    fun root c => by rw [Equiv.signRef_eq ⟨sk, 0, root⟩ rfl (Equiv.cacheEnc c) m, Equiv.cacheDec_cacheEnc]
  rw [Equiv.keygenRef_eq]
  unfold gameX SphincsSecurity.Seeded.keygenFromSeed
  simp only [relabel_bind, bind_assoc, map_bind, relabel_pure, pure_bind, map_pure]
  refine bind_congr fun t => ?_
  refine bind_congr fun region => ?_
  refine bind_congr fun tag => ?_
  rw [hs, bind_map_left]
  refine bind_congr fun s => ?_
  rcases s with _ | σ
  · rfl
  · simp only [Option.map_some, relabel_bind]
    rw [Equiv.expandRef_eq m _ _ (Equiv.compress σ)]
    refine bind_congr fun e => ?_
    rcases e with _ | w
    · rfl
    · exact Equiv.verifyRef_eq m _ w

/-- **The honest pipeline's success bit is the abstract honest game** (relabelled by `fmtQ`). -/
theorem success_honest_eq_game (hK : KeygenRefinementStatement) (hS : SignRefinementStatement)
    (hV : VerifyRefinementStatement) (sk : SecretKey) (m : Message) :
    HonestResult.success <$> submission.honest sk m = relabel Equiv.fmtQ (gameX sk m) := by
  rw [success_honest_eq, successPipe_eq_ref hK hS hV, ref_pipeline_eq]

end SigGolfCandidate.Final
