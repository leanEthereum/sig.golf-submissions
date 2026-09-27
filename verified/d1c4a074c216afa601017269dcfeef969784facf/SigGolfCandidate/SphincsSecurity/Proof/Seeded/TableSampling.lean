import SigGolfCandidate.SphincsSecurity.Proof.Seeded.AlgorithmErasure
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Guess

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option synthInstance.maxSize 512

abbrev OtsSecrets := Layer → TreeIndex → LeafIndex → ChainIndex → Digest
abbrev FtsSecrets := Index → FtsTree → FtsLeaf → Digest
abbrev Secrets := OtsSecrets × FtsSecrets

noncomputable local instance : SampleableType SecretOutputs := secretOutputsSampleableType
noncomputable local instance : SampleableType OtsSecrets := Concrete.otsSecretsSampleableType
noncomputable local instance : SampleableType FtsSecrets := Concrete.ftsSecretsSampleableType
noncomputable opaque secretsSampleableType : SampleableType Secrets := SampleableType.ofFintype Secrets
noncomputable local instance : SampleableType Secrets := secretsSampleableType
noncomputable opaque secretHalvesSampleableType : SampleableType (Secrets × Secrets) :=
  SampleableType.ofFintype (Secrets × Secrets)
noncomputable local instance : SampleableType (Secrets × Secrets) := secretHalvesSampleableType

def flattenSecrets (secrets : Secrets) : SecretValues
  | .inl (lay, tree, leaf, chain) => secrets.1 lay tree leaf chain
  | .inr (index, tree, leaf) => secrets.2 index tree leaf

/-- An oracle answer is its low and its high `128` bits. -/
def splitOutput (output : HashOutput) : Digest × Digest :=
  (output.extractLsb' 0 digestBits, output.extractLsb' digestBits digestBits)

theorem splitOutput_bijective : Function.Bijective splitOutput := by
  apply (Fintype.bijective_iff_injective_and_card _).2
  refine ⟨fun left right heq => hashOutput_eq_of_extract (width := digestBits) (by decide)
    (congrArg Prod.fst heq) (congrArg Prod.snd heq), ?_⟩
  simp only [Fintype.card_prod, Fintype.card_bitVec, Digest, HashOutput, digestBits, hashOutputBits]
  norm_num

noncomputable def outputHalves : HashOutput ≃ (Digest × Digest) :=
  Equiv.ofBijective splitOutput splitOutput_bijective

theorem outputHalves_low (output : HashOutput) : (outputHalves output).1 = truncateHash output := rfl

noncomputable def secretHalves : SecretOutputs ≃ (Secrets × Secrets) where
  toFun outputs := ((tableOts outputs, tableFts outputs),
    ((fun lay tree leaf chain => (outputHalves (outputs (.inl (lay, tree, leaf, chain)))).2),
      fun index tree leaf => (outputHalves (outputs (.inr (index, tree, leaf)))).2))
  invFun halves := fun position => outputHalves.symm (flattenSecrets halves.1 position, flattenSecrets halves.2 position)
  left_inv outputs := by
    funext position
    cases position <;> exact outputHalves.symm_apply_apply (outputs _)
  right_inv halves := by
    rcases halves with ⟨⟨ots, fts⟩, ⟨otsHigh, ftsHigh⟩⟩
    apply Prod.ext <;> apply Prod.ext
    · funext lay tree leaf chain
      exact congrArg Prod.fst (outputHalves.apply_symm_apply (ots lay tree leaf chain, otsHigh lay tree leaf chain))
    · funext index tree leaf
      exact congrArg Prod.fst (outputHalves.apply_symm_apply (fts index tree leaf, ftsHigh index tree leaf))
    · funext lay tree leaf chain
      exact congrArg Prod.snd (outputHalves.apply_symm_apply (ots lay tree leaf chain, otsHigh lay tree leaf chain))
    · funext index tree leaf
      exact congrArg Prod.snd (outputHalves.apply_symm_apply (fts index tree leaf, ftsHigh index tree leaf))

theorem tableOts_from_halves (low high : Secrets) : tableOts (secretHalves.symm (low, high)) = low.1 :=
  congrArg (fun halves => halves.1.1) (secretHalves.apply_symm_apply (low, high))

theorem tableFts_from_halves (low high : Secrets) : tableFts (secretHalves.symm (low, high)) = low.2 :=
  congrArg (fun halves => halves.1.2) (secretHalves.apply_symm_apply (low, high))

theorem truncate_from_halves (low high : Digest) : truncateHash (outputHalves.symm (low, high)) = low :=
  congrArg Prod.fst (outputHalves.apply_symm_apply (low, high))

noncomputable def sampleSecrets : ProbComp Secrets := do
  let ots ← Concrete.sampleOtsSecrets
  let fts ← Concrete.sampleFtsSecrets
  pure (ots, fts)

theorem evalDist_sampleSecrets : 𝒮[sampleSecrets] = 𝒮[$ᵗ Secrets] := by
  unfold sampleSecrets Concrete.sampleOtsSecrets Concrete.sampleFtsSecrets
  exact evalDist_independent_uniform_pair (α := OtsSecrets) (β := FtsSecrets)

theorem evalDist_secretOutputs_from_halves :
    𝒮[sampleSecretOutputs] = 𝒮[do
      let low ← sampleSecrets
      let high ← sampleSecrets
      pure (secretHalves.symm (low, high))] := by
  calc
    _ = 𝒮[secretHalves.symm <$> ($ᵗ (Secrets × Secrets))] :=
      (evalSPMF_map_bijective_uniform_cross (α := Secrets × Secrets) (β := SecretOutputs) secretHalves.symm secretHalves.symm.bijective).symm
    _ = 𝒮[secretHalves.symm <$> (do
        let low ← $ᵗ Secrets
        let high ← $ᵗ Secrets
        pure (low, high))] := by
      rw [evalSPMF_map, evalSPMF_map, evalDist_independent_uniform_pair]
    _ = _ := by
      simp only [map_bind, map_pure]
      rw [evalSPMF_bind, evalSPMF_bind, evalDist_sampleSecrets]
      apply bind_congr
      intro low
      rw [evalSPMF_bind, evalSPMF_bind, evalDist_sampleSecrets]

/-- The parameter is the constant `P = 0`. -/
theorem sampleParameter_eq_zero : Concrete.sampleParameter = pure 0 := by
  unfold Concrete.sampleParameter
  rfl

/-- The low half of a uniform answer is a uniform digest. -/
theorem evalDist_truncate_uniform :
    𝒮[truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput)] = 𝒮[($ᵗ Digest : ProbComp Digest)] := by
  have hmap : truncateHash <$> ($ᵗ HashOutput : ProbComp HashOutput) =
      Prod.fst <$> (outputHalves <$> ($ᵗ HashOutput : ProbComp HashOutput)) := by
    simp only [Functor.map_map]
    rfl
  rw [hmap, evalSPMF_map, evalSPMF_map_bijective_uniform_cross (α := HashOutput) (β := Digest × Digest)
    outputHalves outputHalves.bijective, ← evalSPMF_map]
  exact evalSPMF_map_fst_uniformSample_prod

noncomputable def programmedCache (seed : MasterSeed) (secret secretHigh : Secrets) : QueryCache HashSpec :=
  derivationCache seed (secretHalves.symm (secret, secretHigh))

end SphincsSecurity.Seeded
