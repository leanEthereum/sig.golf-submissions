import SigGolfCandidate.SphincsSecurity.Completeness.Paired
import SigGolfCandidate.SphincsSecurity.Completeness.Stack
import Mathlib.Data.Nat.Bitwise

/-!
# Recovery: what the signer produces, the verifier accepts

The specification's §sec:ver argues that each one-time recovery returns the leaf the signer built
and each authentication path returns its root, so verification accepts whenever signing succeeds.
This file is that argument. For the PORS part the verifier is a stack machine; that it returns the root
on the honest opening of admissible leaves is `Stack.lean` (`eval_ftsRecover_honest`).

Everything is deterministic once the oracle is fixed, so the whole file works under an answer
function `f`: `evalWithAnswerFn f` reads each algorithm as a plain function. Nothing here is
probabilistic, and nothing depends on the answers being uniform.

The signer builds each tree once; `BuildEval.lean` shows that under `f` it computes the recursive
specification of `IdealStatement.lean` (`eval_signFrom`, `eval_buildLayerTree`), read with the
secrets the seed derives under `f`. So the argument is made once, against the specification: each
layer's counter search returns a counter below `C_max` that encodes its message, the verifier's
chains end at the specification's endpoints, its folds climb the specification's trees, and the
root it reaches at the top is the public key's.
-/

open OracleComp

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

namespace SphincsSecurity.Completeness

open Concrete

-- the attempt limits are `2 ^ 20` and `2 ^ 22`; unfolding them unfolds the loops that many times
attribute [local irreducible] digestAttemptLimit encodingAttemptLimit

variable (f : QueryImpl HashSpec Id)

/-! ## Climbing a tree

The signer's authentication path is the sibling at every level, so folding the signed leaf through
it climbs the honest tree: one level at a time, the pair the verifier hashes is exactly the pair the
specification's node hashed. -/

private theorem even_parts (value : Nat) (hbit : value.testBit 0 = false) :
    value = 2 * (value / 2) ∧ Nat.xor value 1 = 2 * (value / 2) + 1 := by
  have heven : Even value := Nat.even_iff.mpr (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit)
  have hmod : value % 2 = 0 := Nat.even_iff.mp heven
  refine ⟨by omega, ?_⟩
  show value ^^^ 1 = _
  rw [Nat.xor_one_of_even heven]
  omega

private theorem odd_parts (value : Nat) (hbit : value.testBit 0 = true) :
    value = 2 * (value / 2) + 1 ∧ Nat.xor value 1 = 2 * (value / 2) := by
  have hodd : Odd value := Nat.odd_iff.mpr (Nat.mod_two_eq_one_iff_testBit_zero.mpr hbit)
  have hmod : value % 2 = 1 := Nat.odd_iff.mp hodd
  refine ⟨by omega, ?_⟩
  show value ^^^ 1 = _
  rw [Nat.xor_one_of_odd hodd]
  omega

private theorem testBit_div_pow (value level : Nat) :
    (value / 2 ^ level).testBit 0 = value.testBit level := by
  simpa only [Nat.zero_add] using (Nat.testBit_add value 0 level).symm

private theorem parts_odd (value level : Nat) (hbit : value.testBit level = true) :
    value / 2 ^ level = 2 * (value / 2 ^ (level + 1)) + 1
      ∧ Nat.xor (value / 2 ^ level) 1 = 2 * (value / 2 ^ (level + 1)) := by
  have hdiv : value / 2 ^ (level + 1) = value / 2 ^ level / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hdiv]
  exact odd_parts (value / 2 ^ level) (by rw [testBit_div_pow, hbit])

private theorem parts_even (value level : Nat) (hbit : value.testBit level = false) :
    value / 2 ^ level = 2 * (value / 2 ^ (level + 1))
      ∧ Nat.xor (value / 2 ^ level) 1 = 2 * (value / 2 ^ (level + 1)) + 1 := by
  have hdiv : value / 2 ^ (level + 1) = value / 2 ^ level / 2 := by
    rw [pow_succ, Nat.div_div_eq_div_mul]
  rw [hdiv]
  exact even_parts (value / 2 ^ level) (by rw [testBit_div_pow, hbit])

/-- Folding the honest leaf through the honest siblings reaches the honest node above it. -/
theorem eval_treeFold_honest (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (path : Nat → Digest) :
    ∀ levels : Nat, (∀ level, level < levels →
        path level = honestNode f parameter lay tree secret level (Nat.xor (leaf.val / 2 ^ level) 1)) →
      evalWithAnswerFn f (treeFold parameter lay tree leaf path levels
          (honestNode f parameter lay tree secret 0 leaf.val) : OracleComp HashSpec Digest)
        = honestNode f parameter lay tree secret levels (leaf.val / 2 ^ levels) := by
  intro levels
  induction levels with
  | zero => intro _; simp [treeFold]
  | succ levels ih =>
      intro hpath
      rw [treeFold, evalWithAnswerFn_bind,
        ih (fun level hlevel => hpath level (Nat.lt_succ_of_lt hlevel))]
      rw [hpath levels (Nat.lt_succ_self levels), honestNode_succ]
      cases hbit : leaf.val.testBit levels with
      | true =>
          obtain ⟨hcur, hsib⟩ := parts_odd leaf.val levels hbit
          simp only [if_true, Concrete.eval_tweakableHash]
          rw [hsib, hcur]
      | false =>
          obtain ⟨hcur, hsib⟩ := parts_even leaf.val levels hbit
          simp only [Bool.false_eq_true, if_false, Concrete.eval_tweakableHash]
          rw [hsib, hcur]

/-! ## The PORS tree

The specification's tree is an honest table for the stack machine (`Stack.lean`): every inner node is
the hash of its children under its heap index, every leaf the hash of its secret. -/

theorem honestTable_honestFtsNode (parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → Digest) :
    HonestTable f parameter index (honestFtsNode f parameter index porsTree secret) := by
  intro x k _ _
  rw [honestFtsNode_succ, Concrete.eval_tweakableHash]

theorem eval_ftsLeafHash_honest (parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → Digest) (leaf : FtsLeaf) :
    evalWithAnswerFn f (ftsLeafHash parameter index porsTree leaf.val (secret leaf)
      : OracleComp HashSpec Digest) = honestFtsNode f parameter index porsTree secret 0 leaf.val := by
  rw [honestFtsNode_zero, ftsLeafHash, Concrete.eval_tweakableHash]

/-- The verifier recovers the specification's few-time public key from the specification's opening of
admissible leaves. -/
theorem eval_ftsRecover_ftsOpen (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (hadm : AdmissibleLeaves leaves) (secret : FtsTree → FtsLeaf → Digest) :
    evalWithAnswerFn f (ftsRecover parameter index (slotValue leaves)
        (evalWithAnswerFn f (ftsOpen parameter index leaves secret)) : OracleComp HashSpec (Option Digest))
      = some (evalWithAnswerFn f (ftsKey parameter index secret : OracleComp HashSpec Digest)) := by
  rw [eval_ftsOpen]
  exact eval_ftsRecover_honest (honestTable_honestFtsNode f parameter index (secret porsTree)) leaves hadm
    (secret porsTree) (eval_ftsLeafHash_honest f parameter index (secret porsTree))

/-! ## One layer

A layer's counter search returns a counter below `C_max` that encodes the layer's message; the
signer's chain values are the partial walks at that encoding, so the verifier's halves of the chains
reach the specification's endpoints and the leaf it hashes is the specification's leaf. -/

/-- What a successful counter search returned: an encoding of the message, at a counter it tried. -/
theorem encodingSearch_spec (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) :
    ∀ (attempts start : Nat) {counter : Counter} {word : Encoding}, start + attempts ≤ 2 ^ 32 →
      evalWithAnswerFn f (encodingSearch parameter lay tree leaf message attempts start
          : OracleComp HashSpec (Option (Counter × Encoding))) = some (counter, word) →
      evalWithAnswerFn f (encode parameter lay tree leaf message counter
          : OracleComp HashSpec (Option Encoding)) = some word
        ∧ counter.toNat < start + attempts := by
  intro attempts
  induction attempts with
  | zero => intro start counter word _ h; simp [encodingSearch] at h
  | succ attempts ih =>
      intro start counter word hbound h
      rw [encodingSearch, evalWithAnswerFn_bind] at h
      cases hencode : evalWithAnswerFn f (encode parameter lay tree leaf message
          (BitVec.ofNat counterBits start) : OracleComp HashSpec (Option Encoding)) with
      | none =>
          rw [hencode] at h
          obtain ⟨hword, hlt⟩ := ih (start + 1) (by omega) h
          exact ⟨hword, by omega⟩
      | some found =>
          rw [hencode] at h
          simp only [evalWithAnswerFn_pure, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          refine ⟨hencode, ?_⟩
          rw [BitVec.toNat_ofNat, counterBits, Nat.mod_eq_of_lt (by omega)]
          omega

/-- What one layer of the specification signs, when it signs: a counter below `C_max`, chain values
the verifier completes to the specification's leaf, and the specification's path. -/
theorem signLayer_spec (key : SecretKey) (index : Index) (lay : Layer) {part : PaddedLayer}
    (h : evalWithAnswerFn f (signLayer key index lay) = some part) :
    part.1.toNat < encodingAttemptLimit
      ∧ evalWithAnswerFn f (otsLeaf key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (evalWithAnswerFn f (layerMessage key index lay : OracleComp HashSpec Digest))
          part.1 part.2.1 : OracleComp HashSpec (Option Digest))
        = some (honestNode f key.parameter lay (treeIndexAt index lay)
            (key.otsSecret lay (treeIndexAt index lay)) 0 (leafIndexAt index lay).val)
      ∧ ∀ (level : Nat) (hlevel : level < layerHeight lay),
          part.2.2 ⟨level, Nat.lt_of_lt_of_le hlevel (layerHeight_le lay)⟩
            = honestNode f key.parameter lay (treeIndexAt index lay)
                (key.otsSecret lay (treeIndexAt index lay)) level
                (Nat.xor ((leafIndexAt index lay).val / 2 ^ level) 1) := by
  have hlimit : 0 + encodingAttemptLimit ≤ 2 ^ 32 := by rw [encodingAttemptLimit]; norm_num
  rw [signLayer, evalWithAnswerFn_bind, otsSign, evalWithAnswerFn_bind, eval_otsSignFrom] at h
  cases hsearch : evalWithAnswerFn f (encodingSearch key.parameter lay (treeIndexAt index lay)
      (leafIndexAt index lay) (evalWithAnswerFn f (layerMessage key index lay : OracleComp HashSpec Digest))
      encodingAttemptLimit 0 : OracleComp HashSpec (Option (Counter × Encoding))) with
  | none =>
      rw [hsearch] at h
      simp at h
  | some result =>
      obtain ⟨counter, word⟩ := result
      obtain ⟨hencode, hlt⟩ := encodingSearch_spec f key.parameter lay _ _ _
        encodingAttemptLimit 0 hlimit hsearch
      rw [hsearch] at h
      simp only [Option.map_some, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
        Option.some.injEq] at h
      subst h
      refine ⟨by simpa using hlt, ?_, ?_⟩
      · rw [otsLeaf, evalWithAnswerFn_bind, hencode]
        simp only [evalWithAnswerFn_sequenceFin, evalWithAnswerFn_bind, evalWithAnswerFn_pure,
          eval_recoverChain]
        rw [honestNode_zero_eq_leafHash, honestEndpoints_def]
        simp only [leafHash, Concrete.eval_tweakableHash]
      · intro level hlevel
        rw [eval_treePath]
        simp only [hlevel, if_true]

/-! ## The hypertree

Layer `lay` signs the root of the tree below it, so the value the verifier carries up is the message
the next layer signed, and layer `0`'s root is the public key. -/

/-- The root of the tree layer `lay` carries, on the route `index` selects. -/
def layerRoot (key : SecretKey) (index : Index) (lay : Layer) : Digest :=
  honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay))
    (layerHeight lay) 0

/-- The message entering the verifier's walk with `remaining` layers left to check. -/
def enterMessage (key : SecretKey) (index : Index) : Nat → Digest
  | 0 => layerRoot f key index topLayer
  | r + 1 => if h : r < numLayers then
      evalWithAnswerFn f (layerMessage key index ⟨r, h⟩ : OracleComp HashSpec Digest) else 0

theorem layerRoot_eq_enterMessage (key : SecretKey) (index : Index) (r : Nat) (h : r < numLayers) :
    layerRoot f key index ⟨r, h⟩ = enterMessage f key index r := by
  cases r with
  | zero => rfl
  | succ r =>
      rw [enterMessage, dif_pos (Nat.lt_of_succ_lt h), layerMessage, dif_pos h]
      rfl

/-- The verifier's walk up the hypertree ends at the root of the top tree. -/
theorem eval_verifyLayers (key : SecretKey) (index : Index) (signature : Signature)
    (hlayers : ∀ lay : Layer, ∃ part, evalWithAnswerFn f (signLayer key index lay) = some part
      ∧ signature.layers lay = LayerSignature.ofPadded lay part) :
    ∀ remaining : Nat, remaining ≤ numLayers →
      evalWithAnswerFn f (verifyLayers key.parameter index signature remaining
          (enterMessage f key index remaining) : OracleComp HashSpec (Option Digest))
        = some (layerRoot f key index topLayer) := by
  intro remaining
  induction remaining with
  | zero => intro _; rw [verifyLayers]; rfl
  | succ r ih =>
      intro hrem
      have hlayer : r < numLayers := Nat.lt_of_succ_le hrem
      obtain ⟨part, hpart, hsig⟩ := hlayers ⟨r, hlayer⟩
      obtain ⟨_, hleaf, hpath⟩ := signLayer_spec f key index ⟨r, hlayer⟩ hpart
      have hfold := eval_treeFold_honest f key.parameter ⟨r, hlayer⟩
        (treeIndexAt index ⟨r, hlayer⟩) (key.otsSecret ⟨r, hlayer⟩ (treeIndexAt index ⟨r, hlayer⟩))
        (leafIndexAt index ⟨r, hlayer⟩) (signaturePath signature ⟨r, hlayer⟩)
        (layerHeight ⟨r, hlayer⟩) (fun level hlevel => by
          rw [signaturePath, dif_pos hlevel, hsig]
          exact hpath level hlevel)
      rw [Nat.div_eq_of_lt (leafIndexAt_lt index _)] at hfold
      rw [verifyLayers, dif_pos hlayer, enterMessage, dif_pos hlayer]
      dsimp only
      rw [hsig]
      simp only [evalWithAnswerFn_bind, hleaf, hfold]
      rw [show honestNode f key.parameter ⟨r, hlayer⟩ (treeIndexAt index ⟨r, hlayer⟩)
          (key.otsSecret ⟨r, hlayer⟩ (treeIndexAt index ⟨r, hlayer⟩)) (layerHeight ⟨r, hlayer⟩) 0
          = layerRoot f key index ⟨r, hlayer⟩ from rfl,
        layerRoot_eq_enterMessage f key index r hlayer]
      exact ih (Nat.le_of_succ_le hrem)

attribute [local semireducible] Concrete.verify

/-- **Recovery for the specification.** If the digest is admissible and the specification signs
after it, the verifier accepts, for a key whose root is its top tree's. -/
theorem verify_of_signatureValue (key : SecretKey) (message : Message) (randomness : Randomness)
    {signature : Signature}
    (hroot : key.root = honestNode f key.parameter topLayer rootTree
      (key.otsSecret topLayer rootTree) (layerHeight topLayer) 0)
    (hadmissible : Admissible (evalWithAnswerFn f (messageDigest key.parameter key.root message
      randomness : OracleComp HashSpec MessageDigest)))
    (hsig : signatureValue f key randomness
      (digestIndex (evalWithAnswerFn f (messageDigest key.parameter key.root message randomness)))
      (digestLeaves (evalWithAnswerFn f (messageDigest key.parameter key.root message randomness)))
      = some signature) :
    evalWithAnswerFn f (Concrete.verify ⟨key.root, key.parameter⟩ message signature
      : OracleComp HashSpec Bool) = true := by
  set digest := evalWithAnswerFn f (messageDigest key.parameter key.root message randomness
    : OracleComp HashSpec MessageDigest) with hdigest
  set index := digestIndex digest with hindex
  unfold signatureValue at hsig
  rw [sequenceFin_option_eq] at hsig
  split at hsig
  next hall =>
    simp only [Option.map_some, Option.some.injEq] at hsig
    have hlayers : ∀ lay : Layer, ∃ part, evalWithAnswerFn f (signLayer key index lay) = some part
        ∧ signature.layers lay = LayerSignature.ofPadded lay part := fun lay => by
      rw [← hsig]
      exact ⟨_, (Option.some_get (hall lay)).symm, rfl⟩
    have hcounters : CountersInRange signature := fun lay => by
      rw [← hsig]
      exact (signLayer_spec f key index lay (Option.some_get (hall lay)).symm).1
    have hrandomness : signature.randomness = randomness := by rw [← hsig]
    have hfts : signature.fts
        = evalWithAnswerFn f (ftsOpen key.parameter index (digestLeaves digest) (key.ftsSecret index)) := by
      rw [← hsig]
    have hbottom : enterMessage f key index numLayers
        = evalWithAnswerFn f (ftsKey key.parameter index (key.ftsSecret index)
          : OracleComp HashSpec Digest) := by
      rw [show numLayers = 4 + 1 from rfl, enterMessage, dif_pos (by decide),
        ← layerMessage_bottomLayer_eq]
      rfl
    have htop : layerRoot f key index topLayer = key.root := by
      rw [hroot, layerRoot, show treeIndexAt index topLayer = rootTree from
        Fin.ext (treeIndexAt_topLayer index)]
    rw [verify_eq _ _ _ hcounters]
    simp only [evalWithAnswerFn_bind, hrandomness, ← hdigest, ← hindex, hfts,
      eval_ftsRecover_ftsOpen f key.parameter index _ hadmissible]
    rw [← hbottom, eval_verifyLayers f key index signature hlayers numLayers (Nat.le_refl _), htop]
    simp
  next => simp at hsig

/-! ## The seeded signer

The seeded signer derives its secrets from the seed, two per query; read under `f`, they are a table
of secrets (`unpairedOts`, `unpairedFts`), the paired builders compute what the per-secret builders
compute with that table (`Paired.lean`), and the key they form is a key of the specification. It reads the top layer's path from the cache,
unmasking each node with a freshly derived mask; for the cache key generation wrote, that is the top
tree's node. -/

/-- The specification's key the seeded key stands for under `f`. Its node table is the top tree the
derived secrets span (the signer reads the top path through the cache instead). -/
def tableKey (secretKey : Seeded.SecretKey) : SecretKey where
  parameter := secretKey.parameter
  root := secretKey.root
  otsSecret lay tree leaf chainIdx := unpairedOts f (Seeded.otsSecret secretKey.parameter secretKey.seed lay tree leaf) chainIdx
  ftsSecret index tree leaf := unpairedFts f (Seeded.ftsSecret secretKey.parameter secretKey.seed index tree) leaf
  top level nodeIdx := honestNode f secretKey.parameter topLayer rootTree
    (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret secretKey.parameter secretKey.seed topLayer rootTree leaf) chainIdx) level nodeIdx

@[simp] theorem eval_oracleHash (input : HashInput) :
    evalWithAnswerFn f (oracleHash input : OracleComp HashSpec HashOutput) = f input := by
  simp only [oracleHash, HasQuery.query]
  exact simulateQ_spec_query f input

/-- The cache holds the top tree the seeded key's secrets span, each node masked with its derived mask. -/
def CacheHonest (secretKey : Seeded.SecretKey) (cache : TopCache) : Prop :=
  ∀ (level : Nat) (hlevel : level < maxLayerHeight) (nodeIdx : Nat)
    (hnodeIdx : nodeIdx < 2 ^ (maxLayerHeight - level)),
    cache.region ⟨level, hlevel⟩ ⟨nodeIdx, hnodeIdx⟩
      = honestNode f secretKey.parameter topLayer rootTree
          (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret secretKey.parameter secretKey.seed topLayer rootTree leaf) chainIdx) level nodeIdx
        ^^^ evalWithAnswerFn f (Seeded.maskSecret secretKey.parameter secretKey.seed level nodeIdx
          : OracleComp HashSpec Digest)

/-- Reading an honest cache unmasks to the top tree: the mask derivation returns the mask the node
was stored under. -/
theorem cachedTopNode_agrees (secretKey : Seeded.SecretKey) (cache : TopCache)
    (hcache : CacheHonest f secretKey cache) :
    TopAgrees f (tableKey f secretKey) (Seeded.cachedTopNode secretKey.parameter secretKey.seed cache) := by
  intro level hlevel nodeIdx hnodeIdx
  have hnode : cache.node level nodeIdx = cache.region ⟨level, hlevel⟩ ⟨nodeIdx, hnodeIdx⟩ := by
    simp only [TopCache.node, dif_pos hlevel, dif_pos hnodeIdx]
  simp only [Seeded.cachedTopNode, evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  rw [hnode, hcache level hlevel nodeIdx hnodeIdx, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
  rfl

/-- The digest the signer accepted. -/
def digestValue (secretKey : Seeded.SecretKey) (message : Message) (randomness : Randomness) :
    MessageDigest :=
  evalWithAnswerFn f (messageDigest secretKey.parameter secretKey.root message randomness
    : OracleComp HashSpec MessageDigest)

theorem signDigestLoop_spec (secretKey : Seeded.SecretKey) (message : Message) :
    ∀ (attempts trial : Nat) {randomness : Randomness} {index : Index}
      {leaves : IndexGroup → FtsLeaf},
      evalWithAnswerFn f (Seeded.signDigestLoop secretKey message attempts trial
          : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf))))
          = some (randomness, index, leaves) →
      Admissible (digestValue f secretKey message randomness)
        ∧ index = digestIndex (digestValue f secretKey message randomness)
        ∧ leaves = digestLeaves (digestValue f secretKey message randomness) := by
  intro attempts
  induction attempts with
  | zero => intro trial randomness index leaves h; simp [Seeded.signDigestLoop] at h
  | succ attempts ih =>
      intro trial randomness index leaves h
      simp only [Seeded.signDigestLoop, Seeded.signAttempt, evalWithAnswerFn_bind] at h
      by_cases hadmissible : Admissible (digestValue f secretKey
          (message := message) (randomness := truncateHash (f (randomizerHashInput
            secretKey.parameter secretKey.seed message (BitVec.ofNat 32 trial)))))
      · rw [digestValue] at hadmissible
        simp only [deriveRandomizer, evalWithAnswerFn_bind, eval_oracleHash,
          evalWithAnswerFn_pure, if_pos hadmissible, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨hrand, hindex, hleaves⟩ := h
        subst hrand
        exact ⟨hadmissible, hindex.symm, hleaves.symm⟩
      · rw [digestValue] at hadmissible
        simp only [deriveRandomizer, evalWithAnswerFn_bind, eval_oracleHash,
          evalWithAnswerFn_pure, if_neg hadmissible] at h
        exact ih (trial + 1) h

-- Below, only the shape of `sign` matters; sealing the loop keeps the unfolding shallow.
attribute [local irreducible] Seeded.signDigestLoop Concrete.signFrom Concrete.signFromPaired

/-- What a successful signing after the MAC check produced: an admissible digest, and the
specification's signature after it for the key the seed derives. -/
theorem signChecked_spec (secretKey : Seeded.SecretKey) (cache : TopCache)
    (hcache : CacheHonest f secretKey cache) (message : Message) {signature : Signature}
    (h : evalWithAnswerFn f (Seeded.signChecked secretKey cache message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    Admissible (digestValue f secretKey message signature.randomness)
      ∧ signatureValue f (tableKey f secretKey) signature.randomness
          (digestIndex (digestValue f secretKey message signature.randomness))
          (digestLeaves (digestValue f secretKey message signature.randomness)) = some signature := by
  rw [Seeded.signChecked, evalWithAnswerFn_bind] at h
  cases hloop : evalWithAnswerFn f (Seeded.signDigestLoop secretKey message digestAttemptLimit 0
      : OracleComp HashSpec (Option (Randomness × Index × (IndexGroup → FtsLeaf)))) with
  | none => rw [hloop] at h; simp at h
  | some result =>
      obtain ⟨randomness, index, leaves⟩ := result
      rw [hloop] at h
      obtain ⟨hadmissible, hindex, hleaves⟩ :=
        signDigestLoop_spec f secretKey message digestAttemptLimit 0 hloop
      change evalWithAnswerFn f (signFromPaired secretKey.parameter index
        (Seeded.ftsSecret secretKey.parameter secretKey.seed index)
        (Seeded.otsSecret secretKey.parameter secretKey.seed)
        (Seeded.cachedTopNode secretKey.parameter secretKey.seed cache) randomness leaves
          : OracleComp HashSpec (Option Signature)) = some signature at h
      rw [eval_signFromPaired] at h
      have hsf := eval_signFrom f (tableKey f secretKey) index
        (fun tree leaf => pure (unpairedFts f
          (Seeded.ftsSecret secretKey.parameter secretKey.seed index tree) leaf))
        (fun lay tree leaf chainIdx => pure (unpairedOts f
          (Seeded.otsSecret secretKey.parameter secretKey.seed lay tree leaf) chainIdx))
        (fun _ _ => rfl) (fun _ _ _ _ => rfl)
        (Seeded.cachedTopNode secretKey.parameter secretKey.seed cache)
        (cachedTopNode_agrees f secretKey cache hcache) randomness leaves
      rw [show (tableKey f secretKey).parameter = secretKey.parameter from rfl] at hsf
      rw [hsf] at h
      have hrand : signature.randomness = randomness := by
        unfold signatureValue at h
        cases hparts : sequenceFin (m := Option) fun lay =>
            evalWithAnswerFn f (signLayer (tableKey f secretKey) index lay) with
        | none => rw [hparts] at h; simp at h
        | some parts =>
            rw [hparts] at h
            simp only [Option.map_some, Option.some.injEq] at h
            rw [← h]
      rw [hrand]
      subst hindex hleaves
      exact ⟨hadmissible, h⟩

/-- A successful signing passed the MAC check and then signed. -/
theorem signChecked_of_sign (secretKey : Seeded.SecretKey) (cache : TopCache) (message : Message)
    {signature : Signature}
    (h : evalWithAnswerFn f (Seeded.sign secretKey cache message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Seeded.signChecked secretKey cache message
        : OracleComp HashSpec (Option Signature)) = some signature := by
  rw [Seeded.sign, evalWithAnswerFn_bind, eval_oracleHash] at h
  split_ifs at h with htag
  · exact h
  · simp at h

/-- **Recovery.** A signature the signer produced with an honest cache is one the verifier accepts:
`doc/sphincs` §sec:ver. -/
theorem verify_of_sign (secretKey : Seeded.SecretKey) (cache : TopCache) (message : Message)
    {signature : Signature}
    (hroot : secretKey.root = honestNode f secretKey.parameter topLayer rootTree
      (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret secretKey.parameter secretKey.seed topLayer rootTree leaf) chainIdx) (layerHeight topLayer) 0)
    (hcache : CacheHonest f secretKey cache)
    (h : evalWithAnswerFn f (Seeded.sign secretKey cache message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Concrete.verify ⟨secretKey.root, secretKey.parameter⟩ message signature
      : OracleComp HashSpec Bool) = true := by
  obtain ⟨hadmissible, hsig⟩ :=
    signChecked_spec f secretKey cache hcache message (signChecked_of_sign f secretKey cache message h)
  exact verify_of_signatureValue f (tableKey f secretKey) message signature.randomness hroot
    hadmissible hsig

/-! ## Key generation -/

/-- The node table key generation builds from the seed under `f`. -/
def keygenTableValue (seed : MasterSeed) : Nat → Nat → Digest :=
  (evalWithAnswerFn f (buildLayerTablePaired 0 topLayer rootTree (Seeded.otsSecret 0 seed topLayer rootTree)
    ⟨0, Nat.two_pow_pos _⟩ zeroEncoding : OracleComp HashSpec _)).2

/-- `keygenTableValue`'s definition, proved at the level of the function: the generated equation
lemma would make the kernel unfold `Prod.snd` first and so run the whole tree build. -/
theorem keygenTableValue_def (seed : MasterSeed) :
    keygenTableValue f seed = (evalWithAnswerFn f (buildLayerTablePaired 0 topLayer rootTree
      (Seeded.otsSecret 0 seed topLayer rootTree) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
        : OracleComp HashSpec _)).2 :=
  congrFun (congrFun (show keygenTableValue = fun f seed => (evalWithAnswerFn f (buildLayerTablePaired 0
    topLayer rootTree (Seeded.otsSecret 0 seed topLayer rootTree) ⟨0, Nat.two_pow_pos _⟩ zeroEncoding
      : OracleComp HashSpec _)).2 from rfl) f) seed

/-- The masked region key generation writes under `f`. -/
def keygenRegionValue (seed : MasterSeed) : TopRegion :=
  evalWithAnswerFn f (Seeded.maskRegion 0 seed (keygenTableValue f seed) : OracleComp HashSpec TopRegion)

theorem keygenRegionValue_def (seed : MasterSeed) :
    keygenRegionValue f seed = evalWithAnswerFn f
      (Seeded.maskRegion 0 seed (keygenTableValue f seed) : OracleComp HashSpec TopRegion) := rfl

-- Both values stand for a whole tree build under `f`; unfolding them runs it.
attribute [local irreducible] keygenTableValue keygenRegionValue

theorem eval_keygenFromSeed (seed : MasterSeed) :
    evalWithAnswerFn f (Seeded.keygenFromSeed seed)
      = (⟨keygenTableValue f seed (layerHeight topLayer) 0, 0⟩,
          ⟨f (macHashInput 0 seed (keygenRegionValue f seed)), keygenRegionValue f seed⟩,
          ⟨seed, 0, keygenTableValue f seed (layerHeight topLayer) 0⟩) := by
  rw [Seeded.keygenFromSeed, evalWithAnswerFn_bind, keygenRegionValue_def, keygenTableValue_def]
  split
  next leaves table h =>
    rw [h]
    simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure, eval_oracleHash]

/-- A built table carries the specification's nodes, for every tree and every secret derivation. -/
theorem eval_buildLayerTable_node (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → OracleComp HashSpec Digest) (leaf : LeafIndex) (digits : Encoding)
    (level : Nat) (hlevel : level ≤ layerHeight lay) (nodeIdx : Nat)
    (hnodeIdx : nodeIdx < 2 ^ (layerHeight lay - level)) :
    (evalWithAnswerFn f (buildLayerTable parameter lay tree secret leaf digits)).2 level nodeIdx
      = honestNode f parameter lay tree
          (fun leaf chainIdx => evalWithAnswerFn f (secret leaf chainIdx)) level nodeIdx := by
  have htable := eval_buildLayerTree_table f parameter lay tree secret leaf digits
    level hlevel nodeIdx hnodeIdx
  unfold buildLayerTable
  simp only [evalWithAnswerFn_bind, evalWithAnswerFn_pure]
  exact htable

/-- A table built with pair getters carries the specification's nodes for the secrets they hand out. -/
theorem eval_buildLayerTablePaired_node (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainPair → OracleComp HashSpec (Digest × Digest)) (leaf : LeafIndex)
    (digits : Encoding) (level : Nat) (hlevel : level ≤ layerHeight lay) (nodeIdx : Nat)
    (hnodeIdx : nodeIdx < 2 ^ (layerHeight lay - level)) :
    (evalWithAnswerFn f (buildLayerTablePaired parameter lay tree secret leaf digits)).2 level nodeIdx
      = honestNode f parameter lay tree
          (fun leaf chainIdx => unpairedOts f (secret leaf) chainIdx) level nodeIdx := by
  rw [eval_buildLayerTablePaired]
  exact eval_buildLayerTable_node f parameter lay tree _ leaf digits level hlevel nodeIdx hnodeIdx

/-- Key generation's table is the specification's top tree for the derived secrets. -/
theorem keygenTableValue_eq (seed : MasterSeed) (level : Nat) (hlevel : level ≤ layerHeight topLayer)
    (nodeIdx : Nat) (hnodeIdx : nodeIdx < 2 ^ (layerHeight topLayer - level)) :
    keygenTableValue f seed level nodeIdx = honestNode f 0 topLayer rootTree
      (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret 0 seed topLayer rootTree leaf) chainIdx) level nodeIdx := by
  rw [keygenTableValue_def]
  exact eval_buildLayerTablePaired_node f 0 topLayer rootTree _ _ _ level hlevel nodeIdx hnodeIdx

theorem eval_maskRegion (parameter : PublicParameter) (seed : MasterSeed) (table : Nat → Nat → Digest)
    (level : Fin maxLayerHeight) (nodeIdx : Fin (2 ^ (maxLayerHeight - level.val))) :
    evalWithAnswerFn f (Seeded.maskRegion parameter seed table : OracleComp HashSpec TopRegion) level nodeIdx
      = table level.val nodeIdx.val ^^^ evalWithAnswerFn f
          (Seeded.maskSecret parameter seed level.val nodeIdx.val : OracleComp HashSpec Digest) := by
  simp only [Seeded.maskRegion, evalWithAnswerFn_bind, evalWithAnswerFn_sequenceFin,
    evalWithAnswerFn_pure, dif_pos nodeIdx.isLt]

/-- Masking a table of the top tree gives an honest cache. -/
theorem cacheHonest_of_table (seed : MasterSeed) (root : Digest) (tag : HashOutput)
    (table : Nat → Nat → Digest)
    (htable : ∀ level, level ≤ layerHeight topLayer → ∀ nodeIdx, nodeIdx < 2 ^ (layerHeight topLayer - level) →
      table level nodeIdx = honestNode f 0 topLayer rootTree
        (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret 0 seed topLayer rootTree leaf) chainIdx) level nodeIdx) :
    CacheHonest f ⟨seed, 0, root⟩
      ⟨tag, evalWithAnswerFn f (Seeded.maskRegion 0 seed table : OracleComp HashSpec TopRegion)⟩ := by
  intro level hlevel nodeIdx hnodeIdx
  have hheight : layerHeight topLayer = maxLayerHeight := rfl
  have hmask := eval_maskRegion f 0 seed table ⟨level, hlevel⟩ ⟨nodeIdx, hnodeIdx⟩
  dsimp only at hmask
  rw [htable level (by rw [hheight]; omega) nodeIdx (by rw [hheight]; exact hnodeIdx)] at hmask
  -- reduce the key's projections first: comparing them unreduced unfolds the evaluations
  dsimp only
  exact hmask

/-- The cache key generation writes is honest for the key it returns. -/
theorem keygen_cacheHonest (seed : MasterSeed) (tag : HashOutput) :
    CacheHonest f ⟨seed, 0, keygenTableValue f seed (layerHeight topLayer) 0⟩
      ⟨tag, keygenRegionValue f seed⟩ := by
  rw [keygenRegionValue_def]
  exact cacheHonest_of_table f seed _ tag _ (keygenTableValue_eq f seed)

/-- The root is the specification's root of the top tree for the derived secrets. -/
theorem keygenRootValue_eq (seed : MasterSeed) :
    keygenTableValue f seed (layerHeight topLayer) 0 = honestNode f 0 topLayer rootTree
      (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret 0 seed topLayer rootTree leaf) chainIdx) (layerHeight topLayer) 0 :=
  keygenTableValue_eq f seed _ le_rfl 0 (by simp)

/-- Recovery for a key of key generation's shape, stated with its fields as variables. -/
theorem verify_of_sign_seeded (seed : MasterSeed) (root : Digest) (cache : TopCache) (message : Message)
    {signature : Signature}
    (hroot : root = honestNode f 0 topLayer rootTree
      (fun leaf chainIdx => unpairedOts f (Seeded.otsSecret 0 seed topLayer rootTree leaf) chainIdx) (layerHeight topLayer) 0)
    (hcache : CacheHonest f ⟨seed, 0, root⟩ cache)
    (h : evalWithAnswerFn f (Seeded.sign ⟨seed, 0, root⟩ cache message
        : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Concrete.verify ⟨root, 0⟩ message signature : OracleComp HashSpec Bool) = true :=
  verify_of_sign f ⟨seed, 0, root⟩ cache message hroot hcache h

/-- **Correctness for key generation.** What the signer produces with the key and cache key
generation returned, the verifier accepts. -/
theorem verify_of_keygen_sign (seed : MasterSeed) (message : Message) {publicKey : PublicKey}
    {cache : TopCache} {secretKey : Seeded.SecretKey} {signature : Signature}
    (hkeys : evalWithAnswerFn f (Seeded.keygenFromSeed seed) = (publicKey, cache, secretKey))
    (hsign : evalWithAnswerFn f (Seeded.sign secretKey cache message
      : OracleComp HashSpec (Option Signature)) = some signature) :
    evalWithAnswerFn f (Concrete.verify publicKey message signature : OracleComp HashSpec Bool)
      = true := by
  rw [eval_keygenFromSeed] at hkeys
  simp only [Prod.mk.injEq] at hkeys
  obtain ⟨rfl, rfl, rfl⟩ := hkeys
  exact verify_of_sign_seeded f seed _ _ message (keygenRootValue_eq f seed)
    (keygen_cacheHonest f seed _) hsign

end SphincsSecurity.Completeness
