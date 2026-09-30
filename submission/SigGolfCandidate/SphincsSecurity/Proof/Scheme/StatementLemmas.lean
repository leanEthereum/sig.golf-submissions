import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.IdealStatement

/-!
# Facts about the statement

`Scheme.lean` seals the two tree recursions against accidental unfolding, which also stops Lean from generating their equational theorems. Unsealing them locally makes the equations hold by `rfl`, so this module states them once as ordinary theorems and the rest of the development rewrites with those instead of unfolding anything. It also checks the arithmetic the concrete parameters fix: the layer heights, the index decomposition and the authentication path offsets.
-/

namespace SphincsSecurity.Concrete

attribute [local semireducible] treeNode ftsNode verify sign sampleRandomness

noncomputable local instance instSampleableTypeRandomness_1 : SampleableType Randomness :=
  randomnessSampleableType

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

@[simp]
theorem treeNode_zero_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (nodeIdx : Nat) :
    treeNode (m := m) parameter lay tree secret 0 nodeIdx
      = (do
          let endpoints ← oneTimePublicKey parameter lay tree (leafOfNat nodeIdx)
            (secret (leafOfNat nodeIdx))
          leafHash parameter lay tree (leafOfNat nodeIdx) endpoints) := rfl

theorem treeNode_succ_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (level nodeIdx : Nat) :
    treeNode (m := m) parameter lay tree secret (level + 1) nodeIdx
      = (do
          let left ← treeNode parameter lay tree secret level (2 * nodeIdx)
          let right ← treeNode parameter lay tree secret level (2 * nodeIdx + 1)
          tweakableHash parameter (.node lay tree (level + 1) nodeIdx) (nodePayload left right)) := rfl

@[simp]
theorem ftsNode_zero_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (nodeIdx : Nat) :
    ftsNode (m := m) parameter index tree secret 0 nodeIdx
      = ftsLeafHash parameter index tree (ftsLeafOfNat nodeIdx) (secret (ftsLeafOfNat nodeIdx)) := rfl

theorem ftsNode_succ_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (secret : FtsLeaf → Digest) (level nodeIdx : Nat) :
    ftsNode (m := m) parameter index tree secret (level + 1) nodeIdx
      = (do
          let left ← ftsNode parameter index tree secret level (2 * nodeIdx)
          let right ← ftsNode parameter index tree secret level (2 * nodeIdx + 1)
          tweakableHash parameter (.ftsNode index tree (level + 1) nodeIdx)
            (nodePayload left right)) := rfl

@[simp]
theorem treeFold_zero_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) (value : Digest) :
    treeFold (m := m) parameter lay tree leaf path 0 value = pure value := rfl

theorem treeFold_succ_eq (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (path : Nat → Digest) (levels : Nat) (value : Digest) :
    treeFold (m := m) parameter lay tree leaf path (levels + 1) value
      = (do
          let current ← treeFold parameter lay tree leaf path levels value
          if leaf.val.testBit levels then
            tweakableHash parameter (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload (path levels) current)
          else
            tweakableHash parameter (.node lay tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload current (path levels))) := rfl

@[simp]
theorem ftsFold_zero_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest) (value : Digest) :
    ftsFold (m := m) parameter index tree leaf path 0 value = pure value := rfl

theorem ftsFold_succ_eq (parameter : PublicParameter) (index : Index) (tree : FtsTree)
    (leaf : FtsLeaf) (path : Fin ftsTreeHeight → Digest) (levels : Nat) (value : Digest) :
    ftsFold (m := m) parameter index tree leaf path (levels + 1) value
      = (do
          let current ← ftsFold parameter index tree leaf path levels value
          let sibling := if hlevel : levels < ftsTreeHeight then path ⟨levels, hlevel⟩ else 0
          if leaf.val.testBit levels then
            tweakableHash parameter (.ftsNode index tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload sibling current)
          else
            tweakableHash parameter (.ftsNode index tree (levels + 1) (leaf.val / 2 ^ (levels + 1)))
              (nodePayload current sibling)) := rfl

@[simp]
theorem verifyLayers_zero_eq (parameter : PublicParameter) (index : Index) (signature : Signature)
    (message : Digest) :
    verifyLayers (m := m) parameter index signature 0 message = pure (some message) := rfl

theorem verifyLayers_succ_eq (parameter : PublicParameter) (index : Index) (signature : Signature)
    (remaining : Nat) (message : Digest) :
    verifyLayers (m := m) parameter index signature (remaining + 1) message
      = (if hlayer : remaining < numLayers then
          (do
            match ← otsLeafAttempt parameter ⟨remaining, hlayer⟩ (treeIndexAt index ⟨remaining, hlayer⟩)
                (leafIndexAt index ⟨remaining, hlayer⟩) message
                (signature.counter ⟨remaining, hlayer⟩)
                (signature.chainValue ⟨remaining, hlayer⟩) with
            | none => pure none
            | some value => do
                let root ← treeFold parameter ⟨remaining, hlayer⟩
                  (treeIndexAt index ⟨remaining, hlayer⟩) (leafIndexAt index ⟨remaining, hlayer⟩)
                  (signaturePath signature ⟨remaining, hlayer⟩) (layerHeight ⟨remaining, hlayer⟩)
                  value
                verifyLayers parameter index signature remaining root)
        else pure none) := by
  rw [verifyLayers]
  split
  · simp only [otsLeaf_eq]
    apply bind_congr
    intro result
    cases result <;> rfl
  · rfl

attribute [local irreducible] verifyLayers

theorem verifyCore_eq (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verifyCore (m := m) publicKey message signature
      = (do
          let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
          if ¬ Admissible digest then
            return false
          else
            let ftsPublicKey ← ftsRecover publicKey.parameter (digestIndex digest)
              (digestLeaves digest) signature.ftsSecret signature.ftsPath
            match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
                ftsPublicKey with
            | none => return false
            | some root => return decide (root = publicKey.root)) := by
  unfold verifyCore
  apply bind_congr
  intro digest
  split
  · rfl
  · apply bind_congr
    intro key
    apply bind_congr
    intro result
    cases result <;> rfl

theorem verify_eq_ite (publicKey : PublicKey) (message : Message) (signature : Signature) :
    verify (m := m) publicKey message signature
      = if CountersInRange signature then verifyCore publicKey message signature else pure false := rfl

theorem verify_eq (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hcounters : CountersInRange signature) :
    verify (m := m) publicKey message signature
      = (do
          let digest ← messageDigest publicKey.parameter publicKey.root message signature.randomness
          if ¬ Admissible digest then
            return false
          else
            let ftsPublicKey ← ftsRecover publicKey.parameter (digestIndex digest)
              (digestLeaves digest) signature.ftsSecret signature.ftsPath
            match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
                ftsPublicKey with
            | none => return false
            | some root => return decide (root = publicKey.root)) := by
  rw [verify_eq_ite, if_pos hcounters, verifyCore_eq]

theorem verify_eq_of_not_counters (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hcounters : ¬ CountersInRange signature) :
    verify (m := m) publicKey message signature = pure false := by
  rw [verify_eq_ite, if_neg hcounters]

theorem sign_eq (secretKey : SecretKey) (message : Message) :
    sign secretKey message
      = (do
          match ← signDigestLoop digestAttemptLimit secretKey message with
          | none => return none
          | some (randomness, index, leaves) =>
              liftM (signAfterDigest secretKey randomness index leaves :
                OracleComp HashSpec (Option Signature))) := rfl

theorem sampleRandomness_eq :
    sampleRandomness = ($ᵗ Randomness : ProbComp Randomness) := rfl

/-! ## Parameter arithmetic -/

example : ∑ lay : Layer, layerHeight lay = totalHeight := by decide

example : (List.ofFn fun lay : Layer => layerHeight lay) = [5, 5, 5, 5, 5, 5, 4] := by decide

example : (List.ofFn fun lay : Layer => heightAbove lay) = [0, 5, 10, 15, 20, 25, 30] := by decide

example : (List.ofFn fun lay : Layer => heightBelow lay) = [29, 24, 19, 14, 9, 4, 0] := by decide

/-- The digest is `h + k * a = 184` bits and has to fit in one oracle output. -/
example : messageDigestBits = 184 ∧ messageDigestBits ≤ hashOutputBits := by decide

theorem treeIndexAt_val (index : Index) (lay : Layer) :
    (treeIndexAt index lay).val = index.val / 2 ^ (totalHeight - heightAbove lay) := rfl

theorem leafIndexAt_val (index : Index) (lay : Layer) :
    (leafIndexAt index lay).val = index.val / 2 ^ heightBelow lay % 2 ^ layerHeight lay := rfl

theorem leafIndexAt_lt (index : Index) (lay : Layer) :
    (leafIndexAt index lay).val < 2 ^ layerHeight lay := by
  rw [leafIndexAt_val]
  exact Nat.mod_lt _ (Nat.two_pow_pos _)

theorem heightAbove_top : heightAbove topLayer = 0 := by decide

/-- The layer below `lay` sits `h_lay` bits lower in the index. -/
theorem heightAbove_succ (lay : Layer) (hbelow : lay.val + 1 < numLayers) :
    heightAbove ⟨lay.val + 1, hbelow⟩ = heightAbove lay + layerHeight lay := by
  revert lay; decide

theorem heightAbove_add_le (lay : Layer) : heightAbove lay + layerHeight lay ≤ totalHeight := by
  revert lay; decide

theorem heightBelow_eq (lay : Layer) :
    heightBelow lay + layerHeight lay + heightAbove lay = totalHeight := by
  revert lay; decide

/-- Layer `0` holds a single tree, the public key's. -/
theorem treeIndexAt_topLayer (index : Index) : (treeIndexAt index topLayer).val = 0 := by
  have hlt : index.val < 2 ^ totalHeight := index.isLt
  rw [treeIndexAt_val, heightAbove_top, Nat.sub_zero]
  exact Nat.div_eq_of_lt hlt

/-- The layers link: the tree used on the layer below `lay` is the one whose root sits at leaf
`e_lay` of the tree used on `lay`. -/
theorem layers_link (index : Index) (lay : Layer) (hbelow : lay.val + 1 < numLayers) :
    (treeIndexAt index ⟨lay.val + 1, hbelow⟩).val
      = (treeIndexAt index lay).val * 2 ^ layerHeight lay + (leafIndexAt index lay).val := by
  have hsum := heightBelow_eq lay
  have habove := heightAbove_succ lay hbelow
  rw [treeIndexAt_val, treeIndexAt_val, leafIndexAt_val, habove]
  have hb : totalHeight - (heightAbove lay + layerHeight lay) = heightBelow lay := by omega
  have ht : totalHeight - heightAbove lay = heightBelow lay + layerHeight lay := by omega
  rw [hb, ht, pow_add, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod' _ _).symm

/-- The bottom layer's leaves are the `2^h` indices themselves. -/
theorem leafIndexAt_bottomLayer (index : Index) :
    (leafIndexAt index bottomLayer).val = index.val % 2 ^ layerHeight bottomLayer := by
  have hb : heightBelow bottomLayer = 0 := by decide
  simp [leafIndexAt_val, hb]

end SphincsSecurity.Concrete
