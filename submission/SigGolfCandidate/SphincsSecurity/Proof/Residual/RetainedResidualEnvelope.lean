import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.ReferencePrefixGame
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualSource
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition canonicalGraphGameInputs
set_option backward.isDefEq.respectTransparency false

theorem signWithView_congr_top (key key' : SecretKey) (hparameter : key.parameter = key'.parameter)
    (hroot : key.root = key'.root) (hots : key.otsSecret = key'.otsSecret) (hfts : key.ftsSecret = key'.ftsSecret)
    (htop : TopRegionEq (m := OracleComp HashSpec) (fun level nodeIdx => pure (key.top level nodeIdx))
      (fun level nodeIdx => pure (key'.top level nodeIdx))) (message : Message) :
    signWithView key message = signWithView key' message := by
  unfold signWithView
  rw [signDigestLoop_congr_key digestAttemptLimit key key' hparameter hroot message]
  congr 1
  funext selected
  rcases selected with _ | ⟨randomness, index, leaves⟩
  · rfl
  · simp only [signAfterDigest_congr_top key key' hparameter hots hfts htop]

theorem sourceInputs_keyCode {Result : Type} (key : SecretKey) (computation : OracleComp (OracleWorld + SigningSpec) Result) :
    sourceInputs (keyCode key).key computation = sourceInputs key computation := by
  have hrequest : requestInputs (keyCode key).key = requestInputs key := by
    funext input
    cases input with
    | inl input => rfl
    | inr message =>
        simp only [requestInputs]
        rw [signWithView_congr_top (keyCode key).key key rfl rfl rfl rfl (keyCode_top key) message]
  unfold sourceInputs
  rw [hrequest]

attribute [local irreducible] signatureFintype

noncomputable def verificationInputs (key : SecretKey) : Finset HashInput :=
  Finset.univ.biUnion fun message : Message => Finset.univ.biUnion fun signature : Signature =>
    hashInputs (scheme.verify ⟨key.root, key.parameter⟩ message signature)

noncomputable def gameInputs (adversary : Adversary) : Finset HashInput :=
  canonicalGraphGameInputs adversary ∪ Finset.univ.biUnion fun code : KeyCode =>
    sourceInputs code.key (adversary.main ⟨code.key.root, code.key.parameter⟩) ∪ verificationInputs code.key

theorem sourceInputs_subset_gameInputs (adversary : Adversary) (key : SecretKey) :
    sourceInputs key (adversary.main ⟨key.root, key.parameter⟩) ⊆ gameInputs adversary := by
  intro input hinput
  rw [gameInputs, Finset.mem_union]
  rw [← sourceInputs_keyCode] at hinput
  exact Or.inr (Finset.mem_biUnion.mpr ⟨keyCode key, Finset.mem_univ _, Finset.mem_union_left _ hinput⟩)

theorem verifyInputs_subset_gameInputs (adversary : Adversary) (key : SecretKey) (forgery : Forgery) :
    hashInputs (scheme.verify ⟨key.root, key.parameter⟩ forgery.message forgery.signature) ⊆ gameInputs adversary := by
  intro input hinput
  rw [gameInputs, Finset.mem_union]
  apply Or.inr
  apply Finset.mem_biUnion.mpr
  refine ⟨keyCode key, Finset.mem_univ _, Finset.mem_union_right _ ?_⟩
  rw [verificationInputs, Finset.mem_biUnion]
  exact ⟨forgery.message, Finset.mem_univ _, Finset.mem_biUnion.mpr ⟨forgery.signature, Finset.mem_univ _, hinput⟩⟩

theorem canonicalEncodingInputs_subset_retainedGameInputs (adversary : Adversary) (parameter : PublicParameter) :
    canonicalEncodingInputs parameter ⊆ gameInputs adversary :=
  (canonicalEncodingInputs_subset_gameInputs adversary parameter).trans Finset.subset_union_left

theorem canonicalGraphInputs_subset_retainedGameInputs (adversary : Adversary) (parameter : PublicParameter) :
    canonicalGraphInputs parameter ⊆ gameInputs adversary :=
  (canonicalGraphInputs_subset_gameInputs adversary parameter).trans Finset.subset_union_left

theorem boundaryInputs_subset_retainedGameInputs (adversary : Adversary) :
    hashInputs (boundaryGameCore adversary) ⊆ gameInputs adversary :=
  (hashInputs_subset_canonicalGraphGameInputs adversary).trans Finset.subset_union_left

theorem boundaryGameCore_eq_retainedPrefixPrior (dummy : OtsReferenceWords) (adversary : Adversary) :
    𝒮[(simulateQ romImpl (boundaryGameCore adversary)).run' ∅] =
      Prod.snd <$> referencePrefixJointPriorGame (gameInputs adversary)
        (canonicalEncodingInputs_subset_retainedGameInputs adversary) dummy adversary := by
  rw [← referencePrefixCoordinateGame_eq_jointPrior, ← referenceResidualGame_eq_prefixCoordinates]
  exact evalDist_boundaryGameCore_referenceResidual (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary) (canonicalGraphInputs_subset_retainedGameInputs adversary)
    dummy adversary (boundaryInputs_subset_retainedGameInputs adversary)

end SphincsSecurity.Concrete.RetainedResidual
