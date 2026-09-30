import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.TableSigner
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Secrets

/-!
# Erasing the derivations from key generation

Key generation builds the top tree from the seed's one-time secrets, masks its nodes with the seed's
masks, and authenticates the masked region with the seed-keyed MAC. `keygenCachedWith` takes the three
derivations as arguments: with the seed's derivations it is `keygenFromSeed`, with the tables it makes
only the tree's hash queries. Once every derivation answer is known, the seeded key generation erases to
the table one; its first query, the derivation of the top tree's first secret, is what gives the table
game its one-query slack.
-/

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem Erases.simulateQ_writer {ι κ τ : Type} {source : OracleSpec ι} {target : OracleSpec κ}
    {logSpec : OracleSpec τ} {α : Type} (known : QueryCache target)
    (left right : QueryImpl source (WriterT (QueryLog logSpec) (OracleComp target)))
    (h : ∀ input, Erases known (left input).run (right input).run)
    (computation : OracleComp source α) :
    Erases known (simulateQ left computation).run (simulateQ right computation).run := by
  induction computation using OracleComp.inductionOn with
  | pure value => exact .pure _
  | query_bind input next ih =>
      simp only [simulateQ_query_bind, WriterT.run_bind]
      apply (h input).bind
      intro result
      exact (ih result.1).map _

open Concrete

/-- Key generation with its three derivations as arguments: the top tree from `secret`, the masked
region from `getMask`, and the tag from `getMac`. Returns the top tree's table and the cache. -/
def keygenCachedWith (secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (getMask : Nat → Nat → OracleComp HashSpec Digest) (getMac : TopRegion → OracleComp HashSpec HashOutput) :
    OracleComp HashSpec ((Nat → Nat → Digest) × TopCache) := do
  let (_, table) ← buildLayerTablePaired 0 topLayer rootTree secret ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
  let region ← maskRegionWith getMask table
  let tag ← getMac region
  return (table, ⟨tag, region⟩)

/-- The seeded key generation's outputs from the table and the cache. -/
def keysOf (seed : MasterSeed) (result : (Nat → Nat → Digest) × TopCache) : PublicKey × TopCache × SecretKey :=
  (⟨result.1 (layerHeight topLayer) 0, 0⟩, result.2, ⟨seed, 0, result.1 (layerHeight topLayer) 0⟩)

theorem keygenFromSeed_eq (seed : MasterSeed) :
    keygenFromSeed seed = keysOf seed <$> keygenCachedWith (otsSecret 0 seed topLayer rootTree)
      (maskSecret 0 seed) (fun region => oracleHash (macHashInput 0 seed region)) := by
  simp only [keygenFromSeed, keygenCachedWith, maskRegion_eq_with, keysOf, map_bind, bind_assoc, map_pure]

/-- The table key generation: the top tree's queries, and the rest read from the tables. -/
theorem keygenCachedWith_pure (outputs : SecretOutputs) (masks : MaskOutputs) (macs : MacOutputs) :
    keygenCachedWith (fun leaf pair => pure (pairOf (tableOts outputs topLayer rootTree leaf) pair))
        (fun level nodeIdx => pure (maskValue masks level nodeIdx)) (fun region => pure (macs region)) =
      (fun top => (top, (⟨macs (tableRegion top masks), tableRegion top masks⟩ : TopCache))) <$>
        (keygenTable 0 (tableOts outputs topLayer rootTree) : OracleComp HashSpec _) := by
  unfold keygenCachedWith keygenTable
  rw [buildLayerTablePaired_pure]
  simp only [maskRegionWith_pure, pure_bind, map_bind, map_pure]

/-- Key generation's first query: the derivation of the top tree's first secret. -/
def firstSecretPosition : SecretPosition :=
  .inl (topLayer, rootTree, leafOfNat 0, ⟨0, by decide⟩)

theorem keygenCachedWith_first (secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest))
    (getMask : Nat → Nat → OracleComp HashSpec Digest) (getMac : TopRegion → OracleComp HashSpec HashOutput) :
    keygenCachedWith secret getMask getMac =
      secret (leafOfNat 0) ⟨0, by decide⟩ >>= fun first =>
        keygenCachedWith (withFirstPair secret first) getMask getMac := by
  unfold keygenCachedWith
  rw [buildLayerTablePaired_split_first, bind_assoc]

theorem otsSecret_first (seed : MasterSeed) :
    (otsSecret 0 seed topLayer rootTree (leafOfNat 0) ⟨0, by decide⟩ : OracleComp HashSpec (Digest × Digest)) =
      (splitSecrets <$> (HashSpec.query (secretInputs 0 seed firstSecretPosition) : OracleComp HashSpec _)) := by
  simp only [otsSecret, oracleHash, bind_pure_comp]
  rfl

section Keygen

variable {known : QueryCache HashSpec} {seed : MasterSeed} {outputs : SecretOutputs}
  {masks : MaskOutputs} {macs : MacOutputs}
  (hsecrets : ∀ position, known (secretInputs 0 seed position) = some (outputs position))
  (hmasks : ∀ position, known (maskInputs 0 seed position) = some (masks position))
  (hmacs : ∀ region, known (macInputs 0 seed region) = some (macs region))

include hsecrets hmasks hmacs

theorem erases_keygenCachedWith {secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (hsecret : ∀ leaf pair, Erases known (secret leaf pair)
      (pure (pairOf (tableOts outputs topLayer rootTree leaf) pair))) :
    Erases known (keygenCachedWith secret (maskSecret 0 seed)
        (fun region => oracleHash (macHashInput 0 seed region)))
      (keygenCachedWith (fun leaf pair => pure (pairOf (tableOts outputs topLayer rootTree leaf) pair))
        (fun level nodeIdx => pure (maskValue masks level nodeIdx)) (fun region => pure (macs region))) := by
  unfold keygenCachedWith
  apply (erases_buildLayerTablePaired 0 _ _ hsecret _ _).bind
  rintro ⟨_, table⟩
  dsimp only
  rw [maskRegionWith_pure, pure_bind, ← maskRegion_eq_with]
  apply Erases.bind_known (erases_maskRegion known 0 seed masks hmasks table)
  unfold oracleHash
  exact Erases.skip _ _ (hmacs (tableRegion table masks)) _ _ (.pure _)

theorem erases_keygen :
    Erases known (keygenCachedWith (otsSecret 0 seed topLayer rootTree) (maskSecret 0 seed)
        (fun region => oracleHash (macHashInput 0 seed region)))
      (keygenCachedWith (fun leaf pair => pure (pairOf (tableOts outputs topLayer rootTree leaf) pair))
        (fun level nodeIdx => pure (maskValue masks level nodeIdx)) (fun region => pure (macs region))) :=
  erases_keygenCachedWith hsecrets hmasks hmacs fun leaf pair =>
    erases_otsSecret known 0 seed outputs hsecrets _ _ leaf pair

/-- With the first pair of secrets already known, the rest of key generation also erases. -/
theorem erases_keygen_first :
    Erases known (keygenCachedWith (withFirstPair (otsSecret 0 seed topLayer rootTree)
          (splitSecrets (outputs firstSecretPosition))) (maskSecret 0 seed)
        (fun region => oracleHash (macHashInput 0 seed region)))
      (keygenCachedWith (fun leaf pair => pure (pairOf (tableOts outputs topLayer rootTree leaf) pair))
        (fun level nodeIdx => pure (maskValue masks level nodeIdx)) (fun region => pure (macs region))) := by
  refine erases_keygenCachedWith hsecrets hmasks hmacs fun leaf pair => ?_
  unfold withFirstPair
  split
  · next hfirst =>
      have hleaf : leaf = leafOfNat 0 := Fin.ext (by simp [hfirst.1, leafOfNat])
      have hpair : pair = ⟨0, by decide⟩ := Fin.ext hfirst.2
      subst hleaf hpair
      rw [pairOf_tableOts]
      exact .pure _
  · exact erases_otsSecret known 0 seed outputs hsecrets _ _ leaf pair

end Keygen

end SphincsSecurity.Seeded
