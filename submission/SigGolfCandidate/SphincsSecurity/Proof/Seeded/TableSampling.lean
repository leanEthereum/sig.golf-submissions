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

theorem splitSecrets_eq (output : HashOutput) : splitSecrets output = outputHalves output := rfl

theorem evenChain_chainPairOf (chain : ChainIndex) (h : chain.val % 2 = 0) : evenChain (chainPairOf chain) = chain :=
  Fin.ext (by simp only [evenChain, chainPairOf]; omega)

theorem oddChain_chainPairOf (chain : ChainIndex) (h : ¬ chain.val % 2 = 0) : oddChain (chainPairOf chain) = chain :=
  Fin.ext (by simp only [oddChain, chainPairOf]; omega)

theorem evenFtsLeaf_ftsPairOf (leaf : FtsLeaf) (h : leaf.val % 2 = 0) : evenFtsLeaf (ftsPairOf leaf) = leaf :=
  Fin.ext (by simp only [evenFtsLeaf, ftsPairOf]; omega)

theorem oddFtsLeaf_ftsPairOf (leaf : FtsLeaf) (h : ¬ leaf.val % 2 = 0) : oddFtsLeaf (ftsPairOf leaf) = leaf :=
  Fin.ext (by simp only [oddFtsLeaf, ftsPairOf]; omega)

/-- The derivation answers are the secret tables: each answer is the pair of its two members' secrets. -/
noncomputable def secretTables : SecretOutputs ≃ Secrets where
  toFun outputs := (tableOts outputs, tableFts outputs)
  invFun secrets
    | .inl (lay, tree, leaf, pair) =>
        outputHalves.symm (Concrete.pairOf (secrets.1 lay tree leaf) pair)
    | .inr (index, tree, pair) =>
        outputHalves.symm (Concrete.ftsPairOf (secrets.2 index tree) pair)
  left_inv outputs := by
    funext position
    rcases position with ⟨lay, tree, leaf, pair⟩ | ⟨index, tree, pair⟩
    · show outputHalves.symm (Concrete.pairOf (tableOts outputs lay tree leaf) pair) = _
      rw [pairOf_tableOts, splitSecrets_eq, Equiv.symm_apply_apply]
    · show outputHalves.symm (Concrete.ftsPairOf (tableFts outputs index tree) pair) = _
      rw [ftsPairOf_tableFts, splitSecrets_eq, Equiv.symm_apply_apply]
  right_inv secrets := by
    rcases secrets with ⟨ots, fts⟩
    apply Prod.ext
    · funext lay tree leaf chain
      show unpairChains (fun pair => splitSecrets (outputHalves.symm (Concrete.pairOf (ots lay tree leaf) pair))) chain = _
      simp only [splitSecrets_eq, Equiv.apply_symm_apply, unpairChains, Concrete.pairOf]
      split
      · rename_i h; rw [evenChain_chainPairOf chain h]
      · rename_i h; rw [oddChain_chainPairOf chain h]
    · funext index tree leaf
      show unpairFtsLeaves (fun pair => splitSecrets (outputHalves.symm (Concrete.ftsPairOf (fts index tree) pair))) leaf = _
      simp only [splitSecrets_eq, Equiv.apply_symm_apply, unpairFtsLeaves, Concrete.ftsPairOf]
      split
      · rename_i h; rw [evenFtsLeaf_ftsPairOf leaf h]
      · rename_i h; rw [oddFtsLeaf_ftsPairOf leaf h]

theorem tableOts_secretTables (secrets : Secrets) : tableOts (secretTables.symm secrets) = secrets.1 :=
  congrArg Prod.fst (secretTables.apply_symm_apply secrets)

theorem tableFts_secretTables (secrets : Secrets) : tableFts (secretTables.symm secrets) = secrets.2 :=
  congrArg Prod.snd (secretTables.apply_symm_apply secrets)

theorem truncate_from_halves (low high : Digest) : truncateHash (outputHalves.symm (low, high)) = low :=
  congrArg Prod.fst (outputHalves.apply_symm_apply (low, high))

noncomputable def sampleSecrets : ProbComp Secrets := do
  let ots ← Concrete.sampleOtsSecrets
  let fts ← Concrete.sampleFtsSecrets
  pure (ots, fts)

theorem evalDist_sampleSecrets : 𝒮[sampleSecrets] = 𝒮[$ᵗ Secrets] := by
  unfold sampleSecrets Concrete.sampleOtsSecrets Concrete.sampleFtsSecrets
  exact evalDist_independent_uniform_pair (α := OtsSecrets) (β := FtsSecrets)

theorem evalDist_secretOutputs :
    𝒮[sampleSecretOutputs] = 𝒮[secretTables.symm <$> sampleSecrets] := by
  rw [evalSPMF_map, evalDist_sampleSecrets, ← evalSPMF_map]
  exact (evalSPMF_map_bijective_uniform_cross (α := Secrets) (β := SecretOutputs) secretTables.symm
    secretTables.symm.bijective).symm

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

end SphincsSecurity.Seeded
