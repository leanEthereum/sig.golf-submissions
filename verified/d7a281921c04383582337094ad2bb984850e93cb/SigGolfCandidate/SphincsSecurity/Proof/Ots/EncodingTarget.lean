import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Ots.EncodingCached
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.ForgeryClassify
/-!
# Canonical signed encoding targets

Every successful signer invocation using one one-time position computes the same layer message and
the same least admissible counter. Consequently an encoding collision at that position targets one
canonical signed payload, even when several signatures reuse the position.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

theorem layerHeight_pos (lay : Layer) : 0 < layerHeight lay := by
  unfold layerHeight
  split <;> decide

theorem layerHeight_sub_one_lt (lay : Layer) : layerHeight lay - 1 < maxLayerHeight := by
  have h1 := layerHeight_le lay
  have h2 := layerHeight_pos lay
  omega

/-- The position whose value layer `lay` signs: the root of the tree below it, or the few-time key. -/
def layerMessagePosition (index : Index) (lay : Layer) : Position :=
  if hbelow : lay.val + 1 < numLayers then
    .node ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
      ⟨layerHeight ⟨lay.val + 1, hbelow⟩ - 1, layerHeight_sub_one_lt _⟩ ⟨0, by positivity⟩
  else .ftsRoots index

theorem layerMessagePosition_of_lt (index : Index) (lay : Layer) (hbelow : lay.val + 1 < numLayers) :
    layerMessagePosition index lay =
      .node ⟨lay.val + 1, hbelow⟩ (treeIndexAt index ⟨lay.val + 1, hbelow⟩)
        ⟨layerHeight ⟨lay.val + 1, hbelow⟩ - 1, layerHeight_sub_one_lt _⟩ ⟨0, by positivity⟩ := by
  rw [layerMessagePosition, dif_pos hbelow]

@[simp] theorem layerMessagePosition_bottom (index : Index) :
    layerMessagePosition index bottomLayer = .ftsRoots index := by
  rw [layerMessagePosition, dif_neg (by decide)]

theorem eval_layerMessage_eq_honestValue (f : QueryImpl HashSpec Id)
    (secretKey : SecretKey) (index : Index) (lay : Layer) :
    evalWithAnswerFn f (layerMessage secretKey index lay) =
      honestValue f secretKey.parameter secretKey.otsSecret secretKey.ftsSecret
        (layerMessagePosition index lay) := by
  by_cases hbelow : lay.val + 1 < numLayers
  · rw [layerMessage_of_lt secretKey index lay hbelow, layerMessagePosition_of_lt index lay hbelow,
      honestValue_node]
    have hh : layerHeight ⟨lay.val + 1, hbelow⟩ - 1 + 1 = layerHeight ⟨lay.val + 1, hbelow⟩ := by
      have := layerHeight_pos ⟨lay.val + 1, hbelow⟩
      omega
    simp only [hh]
    rfl
  · have hbottom : lay = bottomLayer := Fin.ext (by
      have := lay.isLt
      simp only [bottomLayer]
      omega)
    subst hbottom
    rw [layerMessage_bottomLayer secretKey index]
    rw [layerMessagePosition_bottom, honestValue_ftsRoots]
    rfl

end SphincsSecurity.Concrete
