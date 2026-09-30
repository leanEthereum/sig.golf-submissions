import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Erasure
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.DerivationTable
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.StatementLemmas

/-!
# Erasing the secret derivations from the signer

The seeded and the table signers share the tree builders and differ only in the secret getters: the
seeded getter makes a `deriveKey` query, the table getter returns the table value. Once every
derivation answer is known, the builders run in lockstep: every builder `Erases` as soon as each of
its getters does, and a seeded getter `Erases` to the `pure` table value by skipping its known query.

Key generation's first query is the derivation of the top tree's first secret (leaf `0`, chain `0`).
`buildLayerTree_split_first` pulls it out in front, which is what gives the table game its one-query
slack.
-/

open OracleComp OracleSpec

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

theorem sequenceFin_pure {m : Type → Type} [Monad m] [LawfulMonad m] {α : Type}
    {n : Nat} (values : Fin n → α) : Concrete.sequenceFin (fun i => (pure (values i) : m α)) = pure values := by
  induction n with
  | zero =>
      simp only [Concrete.sequenceFin]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      simp only [Concrete.sequenceFin, pure_bind, ih]
      congr 1
      funext i
      cases i using Fin.cases <;> rfl

theorem Erases.sequenceFin {ι : Type} {spec : OracleSpec ι} {α : Type} {n : Nat}
    (known : QueryCache spec) (left right : Fin n → OracleComp spec α)
    (h : ∀ i, Erases known (left i) (right i)) :
    Erases known (Concrete.sequenceFin left) (Concrete.sequenceFin right) := by
  induction n with
  | zero => exact .pure _
  | succ n ih =>
      simp only [Concrete.sequenceFin]
      apply (h 0).bind
      intro head
      apply (ih _ _ (fun i => h i.succ)).bind
      intro tail
      exact .pure _

theorem Erases.bind_map_right {ι : Type} {spec : OracleSpec ι} {α β γ : Type}
    {known : QueryCache spec} {left : OracleComp spec α} {right : OracleComp spec β}
    {f : β → α} (h : Erases known left (f <$> right))
    (nextLeft : α → OracleComp spec γ) (nextRight : β → OracleComp spec γ)
    (hnext : ∀ value, Erases known (nextLeft (f value)) (nextRight value)) :
    Erases known (left >>= nextLeft) (right >>= nextRight) := by
  apply Erases.trans (h.bind nextLeft nextLeft (fun _ => Erases.refl known _))
  simpa only [bind_map_left] using (Erases.refl known right).bind _ _ hnext

def tableOts (outputs : SecretOutputs) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) : Digest := truncateHash (outputs (.inl (lay, tree, leaf, chain)))

def tableFts (outputs : SecretOutputs) (index : Index) (tree : FtsTree) (leaf : FtsLeaf) : Digest :=
  truncateHash (outputs (.inr (index, tree, leaf)))

def tableKey (parameter : PublicParameter) (root : Digest) (outputs : SecretOutputs) : SphincsSecurity.SecretKey where
  parameter := parameter
  root := root
  otsSecret := tableOts outputs
  ftsSecret := tableFts outputs

/-! ## The builders are congruent in their getters -/

section Builders

open Concrete

variable {known : QueryCache HashSpec} (parameter : PublicParameter)

theorem erases_buildChain (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex)
    {left right : OracleComp HashSpec Digest} (h : Erases known left right) (digit : Nat) :
    Erases known (buildChain parameter lay tree leaf chainIdx left digit)
      (buildChain parameter lay tree leaf chainIdx right digit) := by
  unfold buildChain
  exact h.bind _ _ fun _ => .refl _ _

theorem erases_buildLeaf (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    {left right : ChainIndex → OracleComp HashSpec Digest}
    (h : ∀ chainIdx, Erases known (left chainIdx) (right chainIdx)) (digits : Encoding) :
    Erases known (buildLeaf parameter lay tree leaf left digits)
      (buildLeaf parameter lay tree leaf right digits) := by
  unfold buildLeaf
  exact (Erases.sequenceFin known _ _ fun chainIdx =>
    erases_buildChain parameter lay tree leaf chainIdx (h chainIdx) _).bind _ _ fun _ => .refl _ _

theorem erases_buildLayerTree (lay : Layer) (tree : TreeIndex)
    {left right : LeafIndex → ChainIndex → OracleComp HashSpec Digest}
    (h : ∀ leaf chainIdx, Erases known (left leaf chainIdx) (right leaf chainIdx))
    (leaf : LeafIndex) (digits : Encoding) :
    Erases known (buildLayerTree parameter lay tree left leaf digits)
      (buildLayerTree parameter lay tree right leaf digits) := by
  unfold buildLayerTree
  exact (Erases.sequenceFin known _ _ fun _ =>
    erases_buildLeaf parameter lay tree _ (h _) _).bind _ _ fun _ => .refl _ _

theorem erases_buildFtsTree (index : Index) (tree : FtsTree)
    {left right : FtsLeaf → OracleComp HashSpec Digest}
    (h : ∀ leaf, Erases known (left leaf) (right leaf)) (leaf : FtsLeaf) :
    Erases known (buildFtsTree parameter index tree left leaf)
      (buildFtsTree parameter index tree right leaf) := by
  unfold buildFtsTree
  exact (Erases.sequenceFin known _ _ fun leaf =>
    (h leaf).bind _ _ fun _ => .refl _ _).bind _ _ fun _ => .refl _ _

theorem erases_buildForest (index : Index)
    {left right : FtsTree → FtsLeaf → OracleComp HashSpec Digest}
    (h : ∀ tree leaf, Erases known (left tree leaf) (right tree leaf))
    (leaves : IndexGroup → FtsLeaf) :
    Erases known (buildForest parameter index left leaves)
      (buildForest parameter index right leaves) := by
  unfold buildForest
  exact (Erases.sequenceFin known _ _ fun tree =>
    erases_buildFtsTree parameter index tree (h tree) _).bind _ _ fun _ => .refl _ _

theorem erases_signLayers (index : Index)
    {left right : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest}
    (h : ∀ lay tree leaf chainIdx, Erases known (left lay tree leaf chainIdx) (right lay tree leaf chainIdx))
    (remaining : Nat) (message : Digest) :
    Erases known (signLayers parameter index left remaining message)
      (signLayers parameter index right remaining message) := by
  induction remaining generalizing message with
  | zero => exact .pure _
  | succ remaining ih =>
      simp only [signLayers]
      split
      · apply (Erases.refl known _).bind
        intro search
        rcases search with _ | ⟨counter, encoding⟩
        · exact .pure _
        · apply (erases_buildLayerTree parameter _ _ (h _ _) _ _).bind
          rintro ⟨values, path, root⟩
          apply (ih root).bind
          intro rest
          cases rest <;> exact .pure _
      · exact .pure _

theorem erases_signFrom (index : Index)
    {ftsLeft ftsRight : FtsTree → FtsLeaf → OracleComp HashSpec Digest}
    (hfts : ∀ tree leaf, Erases known (ftsLeft tree leaf) (ftsRight tree leaf))
    {otsLeft otsRight : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest}
    (hots : ∀ lay tree leaf chainIdx,
      Erases known (otsLeft lay tree leaf chainIdx) (otsRight lay tree leaf chainIdx))
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    Erases known (signFrom parameter index ftsLeft otsLeft randomness leaves)
      (signFrom parameter index ftsRight otsRight randomness leaves) := by
  unfold signFrom
  apply (erases_buildForest parameter index hfts leaves).bind
  rintro ⟨secrets, path, key⟩
  apply (erases_signLayers parameter index hots _ _).bind
  intro parts
  cases parts <;> exact .pure _

end Builders

/-! ## The first secret of key generation -/

section FirstSecret

open Concrete

variable {m : Type → Type} [Monad m] [LawfulMonad m]

theorem sequenceFin_split_first {α β : Type} {n : Nat} (hn : 0 < n) (computation : Fin n → m α)
    (first : m β) (rest : β → Fin n → m α)
    (hfirst : computation ⟨0, hn⟩ = first >>= fun value => rest value ⟨0, hn⟩)
    (hrest : ∀ value i, i.val ≠ 0 → rest value i = computation i) :
    sequenceFin computation = first >>= fun value => sequenceFin (rest value) := by
  cases n with
  | zero => omega
  | succ n =>
      simp only [sequenceFin]
      rw [show (0 : Fin (n + 1)) = ⟨0, hn⟩ from rfl, hfirst, bind_assoc]
      apply bind_congr
      intro value
      have htail : (fun i : Fin n => rest value i.succ) = fun i => computation i.succ :=
        funext fun i => hrest value i.succ (by simp)
      rw [htail]

/-- The getter with the secret of leaf `0`, chain `0` already known. -/
def withFirst {m : Type → Type} [Monad m] (secret : LeafIndex → ChainIndex → m Digest) (first : Digest) :
    LeafIndex → ChainIndex → m Digest :=
  fun leaf chainIdx => if leaf.val = 0 ∧ chainIdx.val = 0 then pure first else secret leaf chainIdx

theorem leafOfNat_val_ne_zero (lay : Layer) (i : Fin (2 ^ layerHeight lay)) (hi : i.val ≠ 0) :
    (leafOfNat i.val).val ≠ 0 := by
  have hheight : layerHeight lay ≤ maxLayerHeight := by
    unfold layerHeight
    split <;> decide
  have hlt : i.val < 2 ^ maxLayerHeight :=
    lt_of_lt_of_le i.isLt (Nat.pow_le_pow_right (by decide) hheight)
  simp only [leafOfNat, Nat.mod_eq_of_lt hlt]
  exact hi

variable [HasQuery HashSpec m]

theorem buildChain_split_first (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (chainIdx : ChainIndex) (secret : m Digest) (digit : Nat) :
    buildChain parameter lay tree leaf chainIdx secret digit =
      secret >>= fun value => buildChain parameter lay tree leaf chainIdx (pure value) digit := by
  simp only [buildChain, pure_bind]

/-- The tree's first query is the derivation of its first secret, which the rest of the build does
not repeat. -/
theorem buildLayerTree_split_first (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    buildLayerTree parameter lay tree secret leaf digits =
      secret (leafOfNat 0) ⟨0, by decide⟩ >>= fun first =>
        buildLayerTree parameter lay tree (withFirst secret first) leaf digits := by
  unfold buildLayerTree
  rw [sequenceFin_split_first (Nat.two_pow_pos _) _ (secret (leafOfNat 0) ⟨0, by decide⟩)
    (fun first leafNat => buildLeaf parameter lay tree (leafOfNat leafNat.val)
      (withFirst secret first (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)), bind_assoc]
  · unfold buildLeaf
    rw [sequenceFin_split_first (by decide) _ (secret (leafOfNat 0) ⟨0, by decide⟩)
      (fun first chainIdx => buildChain parameter lay tree (leafOfNat 0) chainIdx
        (withFirst secret first (leafOfNat 0) chainIdx)
        ((if (0 : Nat) = leaf.val then digits else zeroEncoding) chainIdx).val), bind_assoc]
    · rw [buildChain_split_first]
      apply bind_congr
      intro first
      simp [withFirst, leafOfNat]
    · intro first chainIdx hchain
      simp [withFirst, hchain]
  · intro first leafNat hleaf
    have hne := leafOfNat_val_ne_zero lay leafNat hleaf
    congr 1
    funext chainIdx
    simp [withFirst, hne]

end FirstSecret

section Algorithms

variable (known : QueryCache HashSpec) (parameter : PublicParameter) (seed : MasterSeed)
  (outputs : SecretOutputs)
  (hknown : ∀ position, known (secretInputs parameter seed position) = some (outputs position))

include hknown

theorem erases_deriveKey (position : SecretPosition) :
    Erases known (deriveKey parameter (secretDomain position) seed : OracleComp HashSpec Digest)
      (pure (truncateHash (outputs position))) := by
  unfold deriveKey Concrete.oracleHash
  exact Erases.skip _ _ (hknown position) _ _ (.pure _)

theorem erases_otsSecret (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (chainIdx : ChainIndex) :
    Erases known (otsSecret parameter seed lay tree leaf chainIdx : OracleComp HashSpec Digest)
      (pure (tableOts outputs lay tree leaf chainIdx)) :=
  erases_deriveKey known parameter seed outputs hknown (.inl (lay, tree, leaf, chainIdx))

theorem erases_ftsSecret (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    Erases known (ftsSecret parameter seed index tree leaf : OracleComp HashSpec Digest)
      (pure (tableFts outputs index tree leaf)) :=
  erases_deriveKey known parameter seed outputs hknown (.inr (index, tree, leaf))

/-- After the digest loop, the seeded signer erases to the table signer. -/
theorem erases_signFrom_table (root : Digest) (index : Index) (randomness : Randomness)
    (leaves : IndexGroup → FtsLeaf) :
    Erases known
      (Concrete.signFrom parameter index (ftsSecret parameter seed index) (otsSecret parameter seed)
        randomness leaves : OracleComp HashSpec (Option Signature))
      (Concrete.signAfterDigest (tableKey parameter root outputs) randomness index leaves) := by
  rw [Concrete.signAfterDigest]
  exact erases_signFrom parameter index
    (fun tree leaf => erases_ftsSecret known parameter seed outputs hknown index tree leaf)
    (fun lay tree leaf chainIdx => erases_otsSecret known parameter seed outputs hknown lay tree leaf chainIdx)
    randomness leaves

omit hknown in
theorem signDigestLoop_tableKey (root : Digest) (message : Message) (attempts : Nat) :
    randomizedDigestLoop attempts ⟨seed, parameter, root⟩ message =
      Concrete.signDigestLoop attempts (tableKey parameter root outputs) message := by
  induction attempts with
  | zero => rfl
  | succ attempts ih =>
      simp only [randomizedDigestLoop, Concrete.signDigestLoop, signAttempt, Concrete.signAttempt, tableKey, ih]

theorem erases_sign (root : Digest) (message : Message) :
    Erases (worldKnown known) (randomizedSign ⟨seed, parameter, root⟩ message)
      (Concrete.sign (tableKey parameter root outputs) message) := by
  unfold randomizedSign
  rw [Concrete.sign_eq, signDigestLoop_tableKey parameter seed outputs root message]
  apply (Erases.refl (worldKnown known) _).bind
  intro attempt
  rcases attempt with _ | ⟨randomness, index, leaves⟩
  · exact .pure _
  · exact (erases_signFrom_table known parameter seed outputs hknown root index randomness leaves).lift_hash

end Algorithms
end SphincsSecurity.Seeded
