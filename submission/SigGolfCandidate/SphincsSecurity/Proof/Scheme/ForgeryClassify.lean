import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.LayerCompare
/-!
# Classifying an accepted forgery

Descent through the hypertree layers stops at a bad cache, at a one-time position not covered
exactly by the signing transcript, or at an honest few-time opening.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

def FullyHonestOpening (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (secretKey : SecretKey) (index : Index) (leaves : IndexGroup → FtsLeaf)
    (signature : Signature) : Prop :=
  (∀ lay, HonestLayerOpening f secretKey.parameter secretKey.otsSecret lay
        (treeIndexAt index lay) (leafIndexAt index lay)
        (evalWithAnswerFn f (layerMessage secretKey index lay)) (signature.counter lay)
        (signature.chainValue lay) (signaturePath signature lay)
      ∧ CachedRun cache f (otsLeafAttempt secretKey.parameter lay (treeIndexAt index lay)
        (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage secretKey index lay))
        (signature.counter lay) (signature.chainValue lay)))
    ∧ (∀ tree,
      signature.ftsSecret tree = secretKey.ftsSecret index tree (leaves (ftsIndexOf tree))
        ∧ ∀ level (hlevel : level < ftsTreeHeight), signature.ftsPath tree ⟨level, hlevel⟩
          = honestFtsNode f secretKey.parameter index tree (secretKey.ftsSecret index tree) level
            (Nat.xor ((leaves (ftsIndexOf tree)).val / 2 ^ level) 1))
    ∧ CachedRun cache f
      (ftsRecover secretKey.parameter index leaves signature.ftsSecret signature.ftsPath)

theorem exact_bottom_message_eq_fts_key (f : QueryImpl HashSpec Id) (secretKey : SecretKey)
    (signedIndex forgedIndex : Index) (message : Digest)
    (htree : treeIndexAt signedIndex bottomLayer = treeIndexAt forgedIndex bottomLayer)
    (hleaf : leafIndexAt signedIndex bottomLayer = leafIndexAt forgedIndex bottomLayer)
    (hmessage : evalWithAnswerFn f (layerMessage secretKey signedIndex bottomLayer) = message) :
    message = honestFtsKey f secretKey.parameter forgedIndex (secretKey.ftsSecret forgedIndex) := by
  have hindex := index_eq_of_bottom_position_eq htree hleaf
  subst signedIndex
  rw [← hmessage, layerMessage_bottomLayer]
  rfl

end SphincsSecurity.Concrete
