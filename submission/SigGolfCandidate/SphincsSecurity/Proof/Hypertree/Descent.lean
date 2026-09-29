import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Cached
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Charge
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.Hypertree
/-!
# Deterministic forgery descent

At one hypertree layer, acceptance at the honest root either creates `Bad`, or the supplied chain
values and authentication path are exactly the honest values selected by the decoded codeword.
-/

namespace SphincsSecurity.Concrete

open OracleComp OracleSpec

variable {f : QueryImpl HashSpec Id} {parameter : PublicParameter}
  {otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest}
  {ftsSecret : Index → FtsTree → FtsLeaf → Digest}
  {cache : QueryCache HashSpec}

/-- An accepted signature has every counter below `C_max`: the verifier checks this first. -/
theorem counters_of_verify (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hverify : evalWithAnswerFn f (verify publicKey message signature) = true) :
    CountersInRange signature := by
  by_contra hcounters
  rw [verify_eq_of_not_counters publicKey message signature hcounters] at hverify
  simp at hverify

/-- An accepted signature: its digest, the PORS root the stack machine accepts (admissibility of the
digest is a property of an accepting `ftsRecover` run, proved with the PORS extraction), and the hypertree
walk from that root to the public root, each with its cached run. -/
theorem verify_extract (publicKey : PublicKey) (message : Message) (signature : Signature)
    (hverify : evalWithAnswerFn f (verify publicKey message signature) = true)
    (hrun : CachedRun cache f (verify publicKey message signature)) :
    ∃ digest : MessageDigest,
      evalWithAnswerFn f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness) = digest
        ∧ CachedRun cache f
          (messageDigest publicKey.parameter publicKey.root message signature.randomness)
        ∧ ∃ ftsPublicKey : Digest,
          evalWithAnswerFn f (ftsRecover publicKey.parameter (digestIndex digest)
              (slotValue (digestLeaves digest)) signature.fts) = some ftsPublicKey
            ∧ evalWithAnswerFn f
              (verifyLayers publicKey.parameter (digestIndex digest) signature numLayers ftsPublicKey)
              = some publicKey.root
            ∧ CachedRun cache f (ftsRecover publicKey.parameter (digestIndex digest)
              (slotValue (digestLeaves digest)) signature.fts)
            ∧ CachedRun cache f
              (verifyLayers publicKey.parameter (digestIndex digest) signature numLayers ftsPublicKey) := by
  have hcounters := counters_of_verify publicKey message signature hverify
  let digest := evalWithAnswerFn f
    (messageDigest publicKey.parameter publicKey.root message signature.randomness)
  rw [verify_eq _ _ _ hcounters] at hverify hrun
  rw [evalWithAnswerFn_bind] at hverify
  have hmessageRun := hrun.bind_left
  have hafterDigest := hrun.bind_right
  change evalWithAnswerFn f (do
    match ← ftsRecover publicKey.parameter (digestIndex digest) (slotValue (digestLeaves digest))
        signature.fts with
    | none => pure false
    | some ftsPublicKey =>
        match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
            ftsPublicKey with
        | none => pure false
        | some root => pure (decide (root = publicKey.root))) = true at hverify
  change CachedRun cache f (do
    match ← ftsRecover publicKey.parameter (digestIndex digest) (slotValue (digestLeaves digest))
        signature.fts with
    | none => pure false
    | some ftsPublicKey =>
        match ← verifyLayers publicKey.parameter (digestIndex digest) signature numLayers
            ftsPublicKey with
        | none => pure false
        | some root => pure (decide (root = publicKey.root))) at hafterDigest
  have hfts := hafterDigest.bind_left
  rw [evalWithAnswerFn_bind] at hverify
  have hafterFts := hafterDigest.bind_right
  revert hverify hafterFts
  cases hkey : evalWithAnswerFn f (ftsRecover publicKey.parameter (digestIndex digest)
      (slotValue (digestLeaves digest)) signature.fts) with
  | none => intro hverify; simp at hverify
  | some ftsPublicKey =>
      intro hverify hafterFts
      simp only at hverify hafterFts
      rw [evalWithAnswerFn_bind] at hverify
      have hlayersRun := hafterFts.bind_left
      refine ⟨digest, rfl, hmessageRun, ftsPublicKey, hkey, ?_, hfts, hlayersRun⟩
      cases hresult : evalWithAnswerFn f
          (verifyLayers publicKey.parameter (digestIndex digest) signature numLayers ftsPublicKey) with
      | none =>
          rw [hresult] at hverify
          simp at hverify
      | some root =>
          rw [hresult] at hverify
          simp only [evalWithAnswerFn_pure, decide_eq_true_eq] at hverify
          simp [hverify]

theorem verifyLayers_succ_extract_cached (index : Index) (signature : Signature)
    (remaining : Nat) (hlayer : remaining < numLayers) (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature (remaining + 1) message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature (remaining + 1) message)) :
    ∃ leafValue,
      let lay : Layer := ⟨remaining, hlayer⟩
      let tree := treeIndexAt index lay
      let leafIdx := leafIndexAt index lay
      let rootValue := foldValue f parameter lay tree leafIdx (signaturePath signature lay)
        leafValue (layerHeight lay)
      evalWithAnswerFn f (otsLeafAttempt parameter lay tree leafIdx message (signature.counter lay)
          (signature.chainValue lay)) = some leafValue
        ∧ evalWithAnswerFn f (verifyLayers parameter index signature remaining rootValue)
          = some target
        ∧ CachedRun cache f (otsLeafAttempt parameter lay tree leafIdx message (signature.counter lay)
          (signature.chainValue lay))
        ∧ CachedRun cache f (treeFold parameter lay tree leafIdx (signaturePath signature lay)
          (layerHeight lay) leafValue)
        ∧ CachedRun cache f (verifyLayers parameter index signature remaining rootValue) := by
  obtain ⟨leafValue, hleaf, hrest⟩ :=
    verifyLayers_succ_extract f parameter index signature remaining hlayer message target hverify
  rw [verifyLayers_succ_eq, dif_pos hlayer] at hrun
  have hots := hrun.bind_left
  have hafter := hrun.bind_right
  rw [hleaf] at hafter
  exact ⟨leafValue, hleaf, hrest, hots, hafter.bind_left, hafter.bind_right⟩

def LayerFrame (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (lay : Layer) (message target leafValue : Digest) : Prop :=
  evalWithAnswerFn f
        (otsLeafAttempt parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay)) = some leafValue
      ∧ evalWithAnswerFn f
        (verifyLayers parameter index signature lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay))) = some target
      ∧ CachedRun cache f
        (otsLeafAttempt parameter lay (treeIndexAt index lay) (leafIndexAt index lay) message
          (signature.counter lay) (signature.chainValue lay))
      ∧ CachedRun cache f
        (treeFold parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath signature lay) (layerHeight lay) leafValue)
      ∧ CachedRun cache f
        (verifyLayers parameter index signature lay.val
          (foldValue f parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay)))

def LayerRun (f : QueryImpl HashSpec Id) (cache : QueryCache HashSpec)
    (parameter : PublicParameter) (index : Index) (signature : Signature)
    (lay : Layer) (message target : Digest) : Prop :=
  ∃ leafValue, LayerFrame f cache parameter index signature lay message target leafValue

theorem layerRun_of_verify (index : Index) (signature : Signature)
    (lay : Layer) (message target : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers parameter index signature (lay.val + 1) message) = some target)
    (hrun : CachedRun cache f
      (verifyLayers parameter index signature (lay.val + 1) message)) :
    LayerRun f cache parameter index signature lay message target := by
  obtain ⟨leafValue, hleaf, hnext, hleafRun, hfoldRun, hnextRun⟩ :=
    verifyLayers_succ_extract_cached (f := f) (cache := cache) index signature lay.val lay.isLt
      message target hverify hrun
  exact ⟨leafValue, hleaf, hnext, hleafRun, hfoldRun, hnextRun⟩

/-- **The verifier's walk, top down.** Suppose every layer frame whose fold reaches the honest root
of its tree carries the specification's message and some property `Q` of the layer. Then an
accepted hypertree walk from the few-time key to the honest public root has `Q` at every layer, and
the few-time key it starts from is the bottom layer's message. -/
theorem hypertree_walk (key : SecretKey) (index : Index) (signature : Signature) (Q : Layer → Prop)
    (hstep : ∀ lay message leafValue,
      LayerFrame f cache key.parameter index signature lay message key.root leafValue →
      foldValue f key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
          (signaturePath signature lay) leafValue (layerHeight lay) =
        honestNode f key.parameter lay (treeIndexAt index lay) (key.otsSecret lay (treeIndexAt index lay))
          (layerHeight lay) 0 →
      message = evalWithAnswerFn f (layerMessage key index lay) ∧ Q lay)
    (hroot : key.root = honestNode f key.parameter topLayer rootTree (key.otsSecret topLayer rootTree)
      (layerHeight topLayer) 0)
    (ftsPublicKey : Digest)
    (hverify : evalWithAnswerFn f
      (verifyLayers key.parameter index signature numLayers ftsPublicKey) = some key.root)
    (hrun : CachedRun cache f (verifyLayers key.parameter index signature numLayers ftsPublicKey)) :
    (∀ lay, Q lay) ∧ ftsPublicKey = evalWithAnswerFn f (layerMessage key index bottomLayer) := by
  have hwalk : ∀ remaining, (hr : remaining ≤ numLayers) → ∀ message,
      evalWithAnswerFn f (verifyLayers key.parameter index signature remaining message) = some key.root →
      CachedRun cache f (verifyLayers key.parameter index signature remaining message) →
      (∀ lay : Layer, lay.val < remaining → Q lay) ∧
        (∀ h : 0 < remaining,
          message = evalWithAnswerFn f (layerMessage key index ⟨remaining - 1, by have := hr; omega⟩)) ∧
        (remaining = 0 → message = key.root) := by
    intro remaining
    induction remaining with
    | zero =>
        intro _ message hv _
        simp only [verifyLayers_zero_eq, evalWithAnswerFn_pure, Option.some.injEq] at hv
        exact ⟨fun lay h => absurd h (Nat.not_lt_zero _), fun h => absurd h (Nat.lt_irrefl _),
          fun _ => hv⟩
    | succ r ih =>
        intro hr message hv hc
        have hlayer : r < numLayers := by omega
        let lay : Layer := ⟨r, hlayer⟩
        obtain ⟨leafValue, hframe⟩ :=
          layerRun_of_verify (f := f) (cache := cache) index signature lay message key.root hv hc
        have hrest := ih (by omega) _ hframe.2.1 hframe.2.2.2.2
        have hfold : foldValue f key.parameter lay (treeIndexAt index lay) (leafIndexAt index lay)
            (signaturePath signature lay) leafValue (layerHeight lay) =
            honestNode f key.parameter lay (treeIndexAt index lay)
              (key.otsSecret lay (treeIndexAt index lay)) (layerHeight lay) 0 := by
          rcases Nat.eq_zero_or_pos r with hzero | hpos
          · have htop : lay = topLayer := Fin.ext hzero
            have htree : treeIndexAt index lay = rootTree := by
              rw [htop]
              exact Fin.ext (treeIndexAt_topLayer index)
            rw [hrest.2.2 hzero, hroot, htree, htop]
          · rw [hrest.2.1 hpos]
            have hbelow : r - 1 + 1 < numLayers := by omega
            rw [layerMessage_of_lt key index ⟨r - 1, by omega⟩ hbelow]
            have hl : (⟨r - 1 + 1, hbelow⟩ : Layer) = lay := Fin.ext (by simp [lay]; omega)
            simp only [hl]
            rfl
        obtain ⟨hmessage, hq⟩ := hstep lay message leafValue hframe hfold
        refine ⟨fun other hother => ?_, fun _ => hmessage, fun h => absurd h (Nat.succ_ne_zero r)⟩
        by_cases heq : other.val = r
        · have : other = lay := Fin.ext heq
          rw [this]
          exact hq
        · exact hrest.1 other (by omega)
  obtain ⟨hq, hmessage, _⟩ := hwalk numLayers le_rfl ftsPublicKey hverify hrun
  exact ⟨fun lay => hq lay lay.isLt, hmessage (by decide)⟩

def HonestLayerOpening (f : QueryImpl HashSpec Id) (parameter : PublicParameter)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (lay : Layer) (tree : TreeIndex) (leafIdx : LeafIndex) (message : Digest)
    (counter : Counter) (values : ChainIndex → Digest) (path : Nat → Digest) : Prop :=
  ∃ codeword : Encoding,
    evalWithAnswerFn f (encodeAttempt parameter lay tree leafIdx message counter) = some codeword
      ∧ (∀ chainIdx, values chainIdx
        = honestChain f parameter lay tree leafIdx chainIdx
          (otsSecret lay tree leafIdx chainIdx) (codeword chainIdx).val)
      ∧ ∀ level, level < layerHeight lay → path level
        = honestNode f parameter lay tree (otsSecret lay tree) level
          (Nat.xor (leafIdx.val / 2 ^ level) 1)

end SphincsSecurity.Concrete
