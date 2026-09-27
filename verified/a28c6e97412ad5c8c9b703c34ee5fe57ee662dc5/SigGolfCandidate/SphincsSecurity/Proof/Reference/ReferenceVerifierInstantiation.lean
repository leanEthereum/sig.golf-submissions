import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingMarkerBound
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.FrontierSigningOrigin
import SigGolfCandidate.SphincsSecurity.Proof.Reference.ReferenceSigningReplay
namespace SphincsSecurity.Concrete.ReferenceVerifierWitness

open _root_.OracleComp OracleSpec OtsContactTrace OtsVerifierWitness
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] frontierRoot canonicalGraphInputs canonicalEncodingInputs instFintypePosition chainWalk sequenceFin

noncomputable abbrev rootedKey (key : SecretKey) (f : QueryImpl HashSpec Id) : SecretKey :=
  keyAtRoot f key (honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) (layerHeight topLayer) 0)

theorem keyTopHonest_rootedKey (key : SecretKey) (f : QueryImpl HashSpec Id) : KeyTopHonest f (rootedKey key f) :=
  keyTopHonest_keyAtRoot f key _

theorem source_root (key : SecretKey) (f : QueryImpl HashSpec Id) (words : OtsReferenceWords) :
    frontierRoot key.parameter (maskOtsPrefixes key.parameter words f) words
      (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) words) = (rootedKey key f).root := by
  rw [← frontierRoot_eq_of_agree key.parameter words f (maskOtsPrefixes key.parameter words f) (maskOtsPrefixes_agrees key.parameter words f),
    canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f words key.root key.top,
    frontierRoot_eq key f words _ (isSigningFrontier_canonical key f words)]
  rfl

theorem canonical_messages (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest) (index : Index) (lay : Layer) :
    canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ =
      evalWithAnswerFn f (layerMessage ((keyAtRoot f key root) : SecretKey) index lay) := by
  change canonicalGraphMessage (canonicalGraphLabels ((keyAtRoot f key root) : SecretKey).parameter ((keyAtRoot f key root) : SecretKey).otsSecret ((keyAtRoot f key root) : SecretKey).ftsSecret f)
    ⟨lay, treeIndexAt index lay, leafIndexAt index lay⟩ = _
  rw [canonicalGraphMessage_eq ((keyAtRoot f key root) : SecretKey) f, layerMessage_referenceIndex]

theorem referenceTableSelection_root (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest) :
    referenceTableSelection (keyAtRoot f key root) f = referenceTableSelection key f := rfl

theorem canonicalReferenceWords_root (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest) (dummy : OtsReferenceWords) :
    canonicalReferenceWords (keyAtRoot f key root) f dummy = canonicalReferenceWords key f dummy := by
  rw [← referenceFamilyWords_selected, referenceTableSelection_root, referenceFamilyWords_selected]

def SuccessWitnessFor (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest) (words : OtsReferenceWords)
    (selections : ReferenceFamily) (adversary : Adversary) (result : ContactResult) (before : AdversaryTrace) : Prop :=
  let actualKey : SecretKey := (keyAtRoot f key root)
  let labels := canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f
  let frontier := canonicalGraphFrontier key.otsSecret labels words
  let trace := result.before * result.after
  before ∈ support (fixedTrace f (CausalFrontierProgram.adversaryRun key.parameter actualKey.root f key.ftsSecret words frontier
    (adversary.main ⟨actualKey.root, key.parameter⟩))) ∧
  SigningTranscript.Valid before.1.1.2 ∧ ¬SigningTranscript.Contains before.1.1.2 before.1.1.1 ∧
  (∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ before.1.1.2 →
    ReferenceSigningWitness.SignatureOrigin actualKey f message signature before.1.2) ∧
  result.frontier = frontier ∧
  trace = before.2 * answerTrace f (verify ⟨actualKey.root, key.parameter⟩ before.1.1.1.message before.1.1.1.signature) ∧
  CountersInRange before.1.1.1.signature ∧
  ∃ digest, evalWithAnswerFn f (messageDigest key.parameter actualKey.root before.1.1.1.message before.1.1.1.signature.randomness) = digest ∧
    ContainsRun f trace (messageDigest key.parameter actualKey.root before.1.1.1.message before.1.1.1.signature.randomness) ∧ Admissible digest ∧
    ((FullyHonestOpening f (recordedCache f trace) actualKey (digestIndex digest) (digestLeaves digest) before.1.1.1.signature ∧
      (∀ lay, ReferenceLayerOpening f actualKey words selections (digestIndex digest) before.1.1.1.signature lay) ∧
      (∀ tree, FtsVerifierWitness.TrueSecretQuery f actualKey (digestIndex digest) tree (digestLeaves digest (ftsIndexOf tree)) trace) ∧
      ∀ message signature, (⟨message, some signature⟩ : SigningEntry) ∈ before.1.1.2 →
        messageDigestPayload actualKey.root message signature.randomness ≠
          messageDigestPayload actualKey.root before.1.1.1.message before.1.1.1.signature.randomness) ∨
      LayerException f actualKey words (canonicalGraphMessage labels) selections trace ∨ FtsVerifierWitness.Exception f actualKey (digestIndex digest) trace)

theorem run_success_atRoot (key : SecretKey) (f : QueryImpl HashSpec Id) (root : Digest)
    (hroot : root = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree) (layerHeight topLayer) 0)
    (selections : ReferenceFamily) (dummy : OtsReferenceWords) (adversary : Adversary) (result : ContactResult)
    (before : AdversaryTrace) (hselected : selections = referenceTableSelection key f)
    (hvalid : ∀ lay tree leaf, OtsCode.Valid (referenceFamilyWords selections dummy lay tree leaf))
    (hb : before ∈ support (fixedTrace f (CausalFrontierProgram.adversaryRun key.parameter root f key.ftsSecret
      (referenceFamilyWords selections dummy)
      (canonicalGraphFrontier key.otsSecret (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) (referenceFamilyWords selections dummy))
      (adversary.main ⟨root, key.parameter⟩))))
    (hv : SigningTranscript.Valid before.1.1.2) (hf : ¬SigningTranscript.Contains before.1.1.2 before.1.1.1)
    (hverify : evalWithAnswerFn f (verify ⟨root, key.parameter⟩ before.1.1.1.message before.1.1.1.signature) = true)
    (hfrontier : result.frontier = canonicalGraphFrontier key.otsSecret
      (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f) (referenceFamilyWords selections dummy))
    (ht : result.before * result.after = before.2 * answerTrace f (verify ⟨root, key.parameter⟩ before.1.1.1.message before.1.1.1.signature)) :
    SuccessWitnessFor key f root (referenceFamilyWords selections dummy) selections adversary result before := by
  have hrun : ContainsRun f (result.before * result.after) (verify ⟨root, key.parameter⟩ before.1.1.1.message before.1.1.1.signature) := by
    rw [ht]
    exact (containsRun_answerTrace f _).mul_left before.2
  have hw : referenceFamilyWords selections dummy = canonicalReferenceWords (keyAtRoot f key root) f dummy := by
    rw [hselected, referenceFamilyWords_selected]
    exact (canonicalReferenceWords_root key f root dummy).symm
  have hbc := hb
  rw [canonicalGraphLabels_frontier key.parameter key.otsSecret key.ftsSecret f _ root (honestTop f key.parameter (key.otsSecret topLayer rootTree)), hw] at hbc
  have horigin := ReferenceSigningWitness.fixedTrace_origin (keyAtRoot f key root) f
    (canonicalReferenceWords (keyAtRoot f key root) f dummy) _
    (isSigningFrontier_canonical (keyAtRoot f key root) f _) (keyTopHonest_keyAtRoot f key root)
    (frontierReferenceWord_canonical (keyAtRoot f key root) f dummy)
    (adversary.main ⟨root, key.parameter⟩) before hbc
  refine ⟨hb, hv, hf, horigin, hfrontier, ht, counters_of_verify _ _ _ hverify, ?_⟩
  obtain ⟨digest, hdigest, hdigestRun, hadmissible, hcases⟩ := verify_classification f (keyAtRoot f key root) (referenceFamilyWords selections dummy)
    (canonicalGraphMessage (canonicalGraphLabels key.parameter key.otsSecret key.ftsSecret f)) selections before.1.1.1.message before.1.1.1.signature
    (result.before * result.after) hvalid (canonical_messages key f root) hroot hverify hrun
  refine ⟨digest, hdigest, hdigestRun, hadmissible, ?_⟩
  rcases hcases with ⟨hfull, href, hqueries⟩ | hbad
  · refine Or.inl ⟨hfull, href, hqueries, ?_⟩
    intro message signature hentry
    have heval : evalWithAnswerFn f (messageDigest key.parameter root before.1.1.1.message before.1.1.1.signature.randomness) =
        truncateMessageDigest (f (tweakableHashInput key.parameter .message
          (messageDigestPayload root before.1.1.1.message before.1.1.1.signature.randomness))) := rfl
    have hd := hdigest.symm.trans heval
    rw [hd] at hfull href
    rw [hw, hselected, ← referenceTableSelection_root key f root] at href
    exact strong_signing_payload_ne (keyAtRoot f key root) f (keyTopHonest_keyAtRoot f key root) dummy (recordedCache f (result.before * result.after))
      before.1.1.2 before.1.1.1 hf hfull href message signature hentry (horigin message signature hentry).2.2
  · exact Or.inr hbad

end SphincsSecurity.Concrete.ReferenceVerifierWitness
