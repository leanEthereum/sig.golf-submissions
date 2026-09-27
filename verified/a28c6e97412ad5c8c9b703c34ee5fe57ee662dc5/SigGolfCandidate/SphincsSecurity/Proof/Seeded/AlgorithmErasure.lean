import SigGolfCandidate.SphincsSecurity.Proof.Seeded.Erasure
import SigGolfCandidate.SphincsSecurity.Proof.Seeded.DerivationTable
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.StatementLemmas
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.PairedEquations

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

/-- A chain's secret: its pair's derivation answer, low half for chain `2k`, high half for `2k + 1`. -/
def tableOts (outputs : SecretOutputs) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (chain : ChainIndex) : Digest :=
  unpairChains (fun pair => splitSecrets (outputs (.inl (lay, tree, leaf, pair)))) chain

/-- A few-time leaf's secret: its pair's derivation answer, low half for leaf `2k`, high half for `2k + 1`. -/
def tableFts (outputs : SecretOutputs) (index : Index) (tree : FtsTree) (leaf : FtsLeaf) : Digest :=
  unpairFtsLeaves (fun pair => splitSecrets (outputs (.inr (index, tree, pair)))) leaf

theorem pairOf_tableOts (outputs : SecretOutputs) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (pair : ChainPair) :
    Concrete.pairOf (tableOts outputs lay tree leaf) pair = splitSecrets (outputs (.inl (lay, tree, leaf, pair))) := by
  unfold Concrete.pairOf tableOts unpairChains
  have he : (evenChain pair).val % 2 = 0 := by simp [evenChain]
  have ho : ¬ (oddChain pair).val % 2 = 0 := by simp [oddChain]
  have hpe : chainPairOf (evenChain pair) = pair := Fin.ext (by simp [chainPairOf, evenChain])
  have hpo : chainPairOf (oddChain pair) = pair := Fin.ext (by simp [chainPairOf, oddChain]; omega)
  simp only [he, ho, if_true, if_false, hpe, hpo]

theorem ftsPairOf_tableFts (outputs : SecretOutputs) (index : Index) (tree : FtsTree) (pair : FtsPair) :
    Concrete.ftsPairOf (tableFts outputs index tree) pair = splitSecrets (outputs (.inr (index, tree, pair))) := by
  unfold Concrete.ftsPairOf tableFts unpairFtsLeaves
  have he : (evenFtsLeaf pair).val % 2 = 0 := by simp [evenFtsLeaf]
  have ho : ¬ (oddFtsLeaf pair).val % 2 = 0 := by simp [oddFtsLeaf]
  have hpe : ftsPairOf (evenFtsLeaf pair) = pair := Fin.ext (by simp [ftsPairOf, evenFtsLeaf])
  have hpo : ftsPairOf (oddFtsLeaf pair) = pair := Fin.ext (by simp [ftsPairOf, oddFtsLeaf]; omega)
  simp only [he, ho, if_true, if_false, hpe, hpo]

/-- The table key: the secrets from `outputs`, the top tree's node table `top` built by key generation,
and its root. -/
def tableKey (parameter : PublicParameter) (top : Nat → Nat → Digest) (outputs : SecretOutputs) :
    SphincsSecurity.SecretKey where
  parameter := parameter
  root := top (layerHeight topLayer) 0
  otsSecret := tableOts outputs
  ftsSecret := tableFts outputs
  top := top

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

theorem erases_buildLayerTable (lay : Layer) (tree : TreeIndex)
    {left right : LeafIndex → ChainIndex → OracleComp HashSpec Digest}
    (h : ∀ leaf chainIdx, Erases known (left leaf chainIdx) (right leaf chainIdx))
    (leaf : LeafIndex) (digits : Encoding) :
    Erases known (buildLayerTable parameter lay tree left leaf digits)
      (buildLayerTable parameter lay tree right leaf digits) := by
  unfold buildLayerTable
  exact (Erases.sequenceFin known _ _ fun _ =>
    erases_buildLeaf parameter lay tree _ (h _) _).bind _ _ fun _ => .refl _ _

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

theorem erases_signTopLayer (index : Index)
    {left right : LeafIndex → ChainIndex → OracleComp HashSpec Digest}
    (h : ∀ leaf chainIdx, Erases known (left leaf chainIdx) (right leaf chainIdx))
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (message : Digest) :
    Erases known (signTopLayer parameter index left topLeft message)
      (signTopLayer parameter index right topRight message) := by
  unfold signTopLayer
  apply (Erases.refl known _).bind
  intro search
  rcases search with _ | ⟨counter, encoding⟩
  · exact .pure _
  · apply (Erases.sequenceFin known _ _ fun chainIdx =>
      (h _ chainIdx).bind _ _ fun _ => .refl _ _).bind
    intro values
    apply (Erases.sequenceFin known _ _ fun level => htop _ _).bind
    intro path
    exact .pure _

theorem erases_signLayers (index : Index)
    {left right : Layer → TreeIndex → LeafIndex → ChainIndex → OracleComp HashSpec Digest}
    (h : ∀ lay tree leaf chainIdx, Erases known (left lay tree leaf chainIdx) (right lay tree leaf chainIdx))
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (remaining : Nat) (message : Digest) :
    Erases known (signLayers parameter index left topLeft remaining message)
      (signLayers parameter index right topRight remaining message) := by
  induction remaining generalizing message with
  | zero => exact .pure _
  | succ remaining ih =>
      simp only [signLayers]
      split
      · split
        · apply (erases_signTopLayer parameter index (h _ _) htop message).bind
          intro output
          cases output <;> exact .pure _
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
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    Erases known (signFrom parameter index ftsLeft otsLeft topLeft randomness leaves)
      (signFrom parameter index ftsRight otsRight topRight randomness leaves) := by
  unfold signFrom
  apply (erases_buildForest parameter index hfts leaves).bind
  rintro ⟨secrets, path, key⟩
  apply (erases_signLayers parameter index hots htop _ _).bind
  intro parts
  cases parts <;> exact .pure _

theorem erases_buildLeafPaired (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    {left right : ChainPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ pair, Erases known (left pair) (right pair)) (digits : Encoding) :
    Erases known (buildLeafPaired parameter lay tree leaf left digits)
      (buildLeafPaired parameter lay tree leaf right digits) := by
  unfold buildLeafPaired
  exact (Erases.sequenceFin known _ _ fun pair =>
    (h pair).bind _ _ fun _ => .refl _ _).bind _ _ fun _ => .refl _ _

theorem erases_buildLayerTablePaired (lay : Layer) (tree : TreeIndex)
    {left right : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ leaf pair, Erases known (left leaf pair) (right leaf pair))
    (leaf : LeafIndex) (digits : Encoding) :
    Erases known (buildLayerTablePaired parameter lay tree left leaf digits)
      (buildLayerTablePaired parameter lay tree right leaf digits) := by
  unfold buildLayerTablePaired
  exact (Erases.sequenceFin known _ _ fun _ =>
    erases_buildLeafPaired parameter lay tree _ (h _) _).bind _ _ fun _ => .refl _ _

theorem erases_buildLayerTreePaired (lay : Layer) (tree : TreeIndex)
    {left right : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ leaf pair, Erases known (left leaf pair) (right leaf pair))
    (leaf : LeafIndex) (digits : Encoding) :
    Erases known (buildLayerTreePaired parameter lay tree left leaf digits)
      (buildLayerTreePaired parameter lay tree right leaf digits) := by
  unfold buildLayerTreePaired
  exact (erases_buildLayerTablePaired parameter lay tree h leaf digits).bind _ _ fun _ => .refl _ _

theorem erases_buildFtsTreePaired (index : Index) (tree : FtsTree)
    {left right : FtsPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ pair, Erases known (left pair) (right pair)) (leaf : FtsLeaf) :
    Erases known (buildFtsTreePaired parameter index tree left leaf)
      (buildFtsTreePaired parameter index tree right leaf) := by
  unfold buildFtsTreePaired
  exact (Erases.sequenceFin known _ _ fun pair =>
    (h pair).bind _ _ fun _ => .refl _ _).bind _ _ fun _ => .refl _ _

theorem erases_buildForestPaired (index : Index)
    {left right : FtsTree → FtsPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ tree pair, Erases known (left tree pair) (right tree pair))
    (leaves : IndexGroup → FtsLeaf) :
    Erases known (buildForestPaired parameter index left leaves)
      (buildForestPaired parameter index right leaves) := by
  unfold buildForestPaired
  exact (Erases.sequenceFin known _ _ fun tree =>
    erases_buildFtsTreePaired parameter index tree (h tree) _).bind _ _ fun _ => .refl _ _

theorem erases_signTopLayerPaired (index : Index)
    {left right : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ leaf pair, Erases known (left leaf pair) (right leaf pair))
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (message : Digest) :
    Erases known (signTopLayerPaired parameter index left topLeft message)
      (signTopLayerPaired parameter index right topRight message) := by
  unfold signTopLayerPaired
  apply (Erases.refl known _).bind
  intro search
  rcases search with _ | ⟨counter, encoding⟩
  · exact .pure _
  · apply (Erases.sequenceFin known _ _ fun pair =>
      (h _ pair).bind _ _ fun _ => .refl _ _).bind
    intro values
    apply (Erases.sequenceFin known _ _ fun level => htop _ _).bind
    intro path
    exact .pure _

theorem erases_signLayersPaired (index : Index)
    {left right : Layer → TreeIndex → LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (h : ∀ lay tree leaf pair, Erases known (left lay tree leaf pair) (right lay tree leaf pair))
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (remaining : Nat) (message : Digest) :
    Erases known (signLayersPaired parameter index left topLeft remaining message)
      (signLayersPaired parameter index right topRight remaining message) := by
  induction remaining generalizing message with
  | zero => exact .pure _
  | succ remaining ih =>
      simp only [signLayersPaired]
      split
      · split
        · apply (erases_signTopLayerPaired parameter index (h _ _) htop message).bind
          intro output
          cases output <;> exact .pure _
        · apply (Erases.refl known _).bind
          intro search
          rcases search with _ | ⟨counter, encoding⟩
          · exact .pure _
          · apply (erases_buildLayerTreePaired parameter _ _ (h _ _) _ _).bind
            rintro ⟨values, path, root⟩
            apply (ih root).bind
            intro rest
            cases rest <;> exact .pure _
      · exact .pure _

theorem erases_signFromPaired (index : Index)
    {ftsLeft ftsRight : FtsTree → FtsPair → OracleComp HashSpec (Digest × Digest)}
    (hfts : ∀ tree pair, Erases known (ftsLeft tree pair) (ftsRight tree pair))
    {otsLeft otsRight : Layer → TreeIndex → LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)}
    (hots : ∀ lay tree leaf pair,
      Erases known (otsLeft lay tree leaf pair) (otsRight lay tree leaf pair))
    {topLeft topRight : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topLeft level nodeIdx) (topRight level nodeIdx))
    (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    Erases known (signFromPaired parameter index ftsLeft otsLeft topLeft randomness leaves)
      (signFromPaired parameter index ftsRight otsRight topRight randomness leaves) := by
  unfold signFromPaired
  apply (erases_buildForestPaired parameter index hfts leaves).bind
  rintro ⟨secrets, path, key⟩
  apply (erases_signLayersPaired parameter index hots htop _ _).bind
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
    unfold layerHeight maxLayerHeight
    split <;> (try split) <;> omega
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

/-- The same split for the table-keeping build of key generation. -/
theorem buildLayerTable_split_first (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → m Digest) (leaf : LeafIndex) (digits : Encoding) :
    buildLayerTable parameter lay tree secret leaf digits =
      secret (leafOfNat 0) ⟨0, by decide⟩ >>= fun first =>
        buildLayerTable parameter lay tree (withFirst secret first) leaf digits := by
  unfold buildLayerTable
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

/-- The pair getter with the secrets of leaf `0`, pair `0` already known. -/
def withFirstPair {m : Type → Type} [Monad m] (secret : LeafIndex → ChainPair → m (Digest × Digest))
    (first : Digest × Digest) : LeafIndex → ChainPair → m (Digest × Digest) :=
  fun leaf pair => if leaf.val = 0 ∧ pair.val = 0 then pure first else secret leaf pair

/-- The paired table build's first query is the derivation of its first pair of secrets. -/
theorem buildLayerTablePaired_split_first (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → m (Digest × Digest)) (leaf : LeafIndex) (digits : Encoding) :
    buildLayerTablePaired parameter lay tree secret leaf digits =
      secret (leafOfNat 0) ⟨0, by decide⟩ >>= fun first =>
        buildLayerTablePaired parameter lay tree (withFirstPair secret first) leaf digits := by
  unfold buildLayerTablePaired
  rw [sequenceFin_split_first (Nat.two_pow_pos _) _ (secret (leafOfNat 0) ⟨0, by decide⟩)
    (fun first leafNat => buildLeafPaired parameter lay tree (leafOfNat leafNat.val)
      (withFirstPair secret first (leafOfNat leafNat.val))
      (if leafNat.val = leaf.val then digits else zeroEncoding)), bind_assoc]
  · unfold buildLeafPaired
    rw [sequenceFin_split_first (by decide) _ (secret (leafOfNat 0) ⟨0, by decide⟩)
      (fun first pair => do
        let secrets ← withFirstPair secret first (leafOfNat 0) pair
        let a ← buildChain parameter lay tree (leafOfNat 0) (evenChain pair) (pure secrets.1)
          ((if (0 : Nat) = leaf.val then digits else zeroEncoding) (evenChain pair)).val
        let b ← buildChain parameter lay tree (leafOfNat 0) (oddChain pair) (pure secrets.2)
          ((if (0 : Nat) = leaf.val then digits else zeroEncoding) (oddChain pair)).val
        return (a, b)), bind_assoc]
    · apply bind_congr
      intro first
      simp [withFirstPair, leafOfNat]
    · intro first pair hpair
      simp [withFirstPair, hpair]
  · intro first leafNat hleaf
    have hne := leafOfNat_val_ne_zero lay leafNat hleaf
    congr 1
    funext pair
    simp [withFirstPair, hne]

end FirstSecret

section Algorithms

variable (known : QueryCache HashSpec) (parameter : PublicParameter) (seed : MasterSeed)
  (outputs : SecretOutputs)
  (hknown : ∀ position, known (secretInputs parameter seed position) = some (outputs position))

include hknown

theorem erases_derivePair (position : SecretPosition) :
    Erases known ((do return splitSecrets (← Concrete.oracleHash
        (keygenHashInput parameter (secretDomain position) seed))) : OracleComp HashSpec (Digest × Digest))
      (pure (splitSecrets (outputs position))) := by
  unfold Concrete.oracleHash
  exact Erases.skip _ _ (hknown position) _ _ (.pure _)

theorem erases_otsSecret (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex) (pair : ChainPair) :
    Erases known (otsSecret parameter seed lay tree leaf pair : OracleComp HashSpec (Digest × Digest))
      (pure (Concrete.pairOf (tableOts outputs lay tree leaf) pair)) := by
  rw [pairOf_tableOts]
  exact erases_derivePair known parameter seed outputs hknown (.inl (lay, tree, leaf, pair))

theorem erases_ftsSecret (index : Index) (tree : FtsTree) (pair : FtsPair) :
    Erases known (ftsSecret parameter seed index tree pair : OracleComp HashSpec (Digest × Digest))
      (pure (Concrete.ftsPairOf (tableFts outputs index tree) pair)) := by
  rw [ftsPairOf_tableFts]
  exact erases_derivePair known parameter seed outputs hknown (.inr (index, tree, pair))

/-- After the digest loop, the seeded signer (paired derivations) erases to the table signer, provided the
seeded top-node getter erases to the table's. -/
theorem erases_signFrom_table (top : Nat → Nat → Digest) (index : Index) (randomness : Randomness)
    (leaves : IndexGroup → FtsLeaf) {topNode : Nat → Nat → OracleComp HashSpec Digest}
    (htop : ∀ level nodeIdx, Erases known (topNode level nodeIdx) (pure (top level nodeIdx))) :
    Erases known
      (Concrete.signFromPaired parameter index (ftsSecret parameter seed index) (otsSecret parameter seed)
        topNode randomness leaves : OracleComp HashSpec (Option Signature))
      (Concrete.signAfterDigest (tableKey parameter top outputs) randomness index leaves) := by
  rw [Concrete.signAfterDigest, ← Concrete.signFromPaired_pure]
  exact erases_signFromPaired parameter index
    (fun tree pair => erases_ftsSecret known parameter seed outputs hknown index tree pair)
    (fun lay tree leaf pair => erases_otsSecret known parameter seed outputs hknown lay tree leaf pair)
    htop randomness leaves

end Algorithms
end SphincsSecurity.Seeded
