import SigGolfCandidate.SphincsSecurity.Proof.Reference.VerifierTraceDescent
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.TreeFoldBound
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.GraphPayloadInputs
import SigGolfCandidate.SphincsSecurity.Proof.Fts.ExtractFts
/-!
# The few-time part of an accepted forgery, on the verifier's trace

`ftsRecover_extract` (Fts/ExtractFts) in the vocabulary of the structural-match bound: an accepting run of the
stack machine reaching the honest PORS root makes the digest's leaves admissible, and either the signature's
PORS part is the honest opening and the verifier queried the true secret of every opened leaf
(`TrueSecretQuery`, one per digest slot), or some query on the trace is a structural match at a PORS position
of the instance (`Exception`).
-/
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec OtsContactTrace
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
attribute [local irreducible] canonicalPayloadInputs

def QueriedOutputMatch (f : QueryImpl HashSpec Id) (key : SecretKey) (position : Position) (trace : Trace) : Prop :=
  position.TreeBound ∧ ∃ payload, payload ∈ canonicalPayloadInputs ∧
    (tweakableHashInput key.parameter position.domain payload, f (tweakableHashInput key.parameter position.domain payload)) ∈ trace.toList ∧
    payload ≠ honestPayload f key.parameter key.otsSecret key.ftsSecret position ∧
    truncateHash (f (tweakableHashInput key.parameter position.domain payload)) = honestValue f key.parameter key.otsSecret key.ftsSecret position

namespace FtsVerifierWitness

variable (f : QueryImpl HashSpec Id) (key : SecretKey) (index : Index)

/-- The PORS positions of an instance: its leaves and its nodes. -/
def AtIndex : Position → Prop
  | .ftsLeaf actual _ _ | .ftsNode actual _ _ => actual = index
  | _ => False

/-- A structural match at a PORS position of the instance. -/
def Exception (trace : Trace) : Prop := ∃ position, AtIndex index position ∧ QueriedOutputMatch f key position trace

/-- The verifier hashed the true secret of `leaf` (one opened leaf, i.e. one digest slot). -/
def TrueSecretQuery (leaf : FtsLeaf) (trace : Trace) : Prop :=
  let input := tweakableHashInput key.parameter (.ftsLeaf index porsTree leaf.val)
    (digestBytes (key.ftsSecret index porsTree leaf))
  (input, f input) ∈ trace.toList

/-- A hit of the stack machine is a structural match at a PORS position. -/
theorem hit_exception (trace : Trace) (input : HashInput) (hinput : (input, f input) ∈ trace.toList)
    (hhit : PorsMachine.Hit f key.parameter index (key.ftsSecret index porsTree) input) :
    Exception f key index trace := by
  rcases hhit with ⟨heap, left, right, hpos, hlt, rfl, hne, hvalue⟩ | ⟨leaf, candidate, rfl, hne, hvalue⟩
  · refine ⟨.ftsNode index porsTree ⟨heap, hlt⟩, rfl, hpos, nodePayload left right,
      nodePayload_mem_canonicalPayloadInputs _ _, hinput, hne, ?_⟩
    rw [honestValue_ftsNode f key.parameter key.otsSecret key.ftsSecret index porsTree ⟨heap, hlt⟩ hpos]
    exact hvalue
  · refine ⟨.ftsLeaf index porsTree leaf, rfl, trivial, digestBytes candidate,
      digestBytes_mem_canonicalPayloadInputs _, hinput, fun h => hne (digestBytes_injective h), ?_⟩
    rw [honestValue_ftsLeaf, ← honestFtsHeap_leaf]
    exact hvalue

/-- **The classification of an accepted PORS opening.** -/
theorem recover_classification (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (trace : Trace)
    (hrecover : evalWithAnswerFn f (ftsRecover key.parameter index (slotValue leaves) fts)
      = some (honestFtsKey f key.parameter index (key.ftsSecret index)))
    (hrun : ContainsRun f trace (ftsRecover key.parameter index (slotValue leaves) fts)) :
    AdmissibleLeaves leaves ∧
      ((fts = evalWithAnswerFn f (ftsOpen key.parameter index leaves (key.ftsSecret index)) ∧
          ∀ slot, TrueSecretQuery f key index (leaves slot) trace) ∨
        Exception f key index trace) := by
  obtain ⟨hadmissible, hcase⟩ := ftsRecover_extract f key.parameter index leaves (key.ftsSecret index) fts hrecover
  refine ⟨hadmissible, ?_⟩
  rcases hcase with ⟨hopen, hqueries⟩ | ⟨input, hinput, hhit⟩
  · exact Or.inl ⟨hopen, fun slot => hrun _ (hqueries slot)⟩
  · exact Or.inr (hit_exception f key index trace input (hrun _ hinput) hhit)

/-- Distinct digest slots of admissible leaves open distinct leaves (for the two-guesses outcome: two
uncovered slots are two distinct secret-guess coordinates). -/
theorem slot_leaf_ne {leaves : IndexGroup → FtsLeaf} (hadmissible : AdmissibleLeaves leaves)
    {first second : IndexGroup} (hne : first ≠ second) : leaves first ≠ leaves second :=
  fun h => hne (hadmissible.1 h)

end FtsVerifierWitness

end SphincsSecurity.Concrete
