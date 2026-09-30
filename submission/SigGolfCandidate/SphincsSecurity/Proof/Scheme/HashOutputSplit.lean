import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Guess
/-!
# Splitting a hash answer

Splitting an answer into its low and high bits is a bijection, so the low bits of a uniform answer are
uniform. (Split out of `Fts/FewTimeUniform` so that the one-time signature's encoding probability does not
import the few-time digest machinery.)
-/

namespace SphincsSecurity

open OracleComp OracleSpec ENNReal

def splitHashOutput (width : Nat) (output : HashOutput) :
    BitVec width × BitVec (hashOutputBits - width) :=
  (output.extractLsb' 0 width,
    output.extractLsb' width (hashOutputBits - width))

theorem splitHashOutput_injective {width : Nat} (hwidth : width ≤ hashOutputBits) :
    Function.Injective (splitHashOutput width) := by
  intro left right heq
  apply hashOutput_eq_of_extract hwidth
  · exact congrArg Prod.fst heq
  · exact congrArg Prod.snd heq

theorem splitHashOutput_bijective {width : Nat} (hwidth : width ≤ hashOutputBits) :
    Function.Bijective (splitHashOutput width) := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨splitHashOutput_injective hwidth, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bitVec, Fintype.card_bitVec, Fintype.card_bitVec, ← pow_add]
  congr
  omega

noncomputable def splitHashOutputEquiv (width : Nat) (hwidth : width ≤ hashOutputBits) :
    HashOutput ≃ BitVec width × BitVec (hashOutputBits - width) :=
  Equiv.ofBijective (splitHashOutput width) (splitHashOutput_bijective hwidth)

theorem evalDist_hashOutput_extract_uniform {width : Nat} (hwidth : width ≤ hashOutputBits) :
    𝒮[(fun output : HashOutput => output.extractLsb' 0 width) <$>
        ($ᵗ HashOutput : ProbComp HashOutput)] =
      𝒮[($ᵗ BitVec width : ProbComp (BitVec width))] := by
  let split := splitHashOutput width
  have hmap :
      (fun output : HashOutput => output.extractLsb' 0 width) <$>
          ($ᵗ HashOutput : ProbComp HashOutput) =
        Prod.fst <$> (split <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp [Functor.map_map, split, splitHashOutput]
  rw [hmap]
  have hsplit :
      𝒮[split <$> ($ᵗ HashOutput : ProbComp HashOutput)] =
        𝒮[($ᵗ (BitVec width × BitVec (hashOutputBits - width)) :
          ProbComp (BitVec width × BitVec (hashOutputBits - width)))] :=
    evalSPMF_map_bijective_uniform_cross
      (α := HashOutput) (β := BitVec width × BitVec (hashOutputBits - width))
      split (splitHashOutput_bijective hwidth)
  rw [evalSPMF_map, hsplit, ← evalSPMF_map]
  exact evalSPMF_map_fst_uniformSample_prod

end SphincsSecurity
