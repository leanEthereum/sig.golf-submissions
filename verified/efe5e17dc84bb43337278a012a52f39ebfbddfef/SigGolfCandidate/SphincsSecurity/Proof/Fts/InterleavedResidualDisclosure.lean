import SigGolfCandidate.SphincsSecurity.Proof.Base.Prelude
import SigGolfCandidate.SphincsSecurity.Proof.Hypertree.CanonicalProbeCache
import SigGolfCandidate.SphincsSecurity.Proof.Fts.PublicSigningRecord
namespace SphincsSecurity.Concrete.InterleavedResidual

open _root_.OracleComp OracleSpec CanonicalProbeRouting
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] honestFts honestFtsOfSlots sortedSlots schedule

structure Routing where
  disclosed : Index → FtsTree → FtsLeaf → Prop
  known : Labels

abbrev SigningRecord := (Option Signature × Option FewTimeView) × SigningBoundaryTrace

/-- The leaf a signature on the view opens at sorted position `s`. -/
def slotLeaf (view : FewTimeView) (s : Fin ftsOpenings) : FtsLeaf :=
  view.2 ((sortedSlots view.2).getD s.val ⟨0, by decide⟩)

/-- Every slot's leaf is opened at some sorted position. -/
theorem exists_slotLeaf (view : FewTimeView) (slot : IndexGroup) : ∃ s, view.2 slot = slotLeaf view s := by
  have hperm : (sortedSlots view.2).Perm (List.finRange ftsOpenings) := by
    unfold sortedSlots
    exact List.perm_insertionSort _ _
  have hmem : slot ∈ sortedSlots view.2 := hperm.mem_iff.mpr (List.mem_finRange slot)
  obtain ⟨i, hi, heq⟩ := List.getElem_of_mem hmem
  have hlen : (sortedSlots view.2).length = ftsOpenings := hperm.length_eq.trans (List.length_finRange)
  refine ⟨⟨i, hlen ▸ hi⟩, ?_⟩
  unfold slotLeaf
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some, heq]

/-- Disclose the opened leaves of a signature on `view`, with their secrets in sorted order. -/
noncomputable def Routing.disclose (routing : Routing) (view : FewTimeView) (secrets : Fin ftsOpenings → Digest) :
    Routing where
  disclosed index tree leaf := routing.disclosed index tree leaf ∨ index = view.1 ∧ ∃ s, leaf = slotLeaf view s
  known coordinate := match coordinate with
    | .ftsStart index _ leaf =>
        if h : index = view.1 ∧ ∃ s, leaf = slotLeaf view s then secrets h.2.choose else routing.known coordinate
    | _ => routing.known coordinate

noncomputable def Routing.afterSigning (routing : Routing) (record : SigningRecord) : Routing :=
  match record.1.1, record.1.2 with
  | some signature, some view => routing.disclose view signature.fts.secrets
  | _, _ => routing

theorem Routing.afterSigning_mono (routing : Routing) (record : SigningRecord)
    (index : Index) (tree : FtsTree) (leaf : FtsLeaf) :
    routing.disclosed index tree leaf → (routing.afterSigning record).disclosed index tree leaf := by
  rcases record with ⟨⟨signature, view⟩, trace⟩
  cases signature <;> cases view <;> first | exact id | exact Or.inl

theorem hidden_graph_disclosed (words : OtsReferenceWords)
    (before after : Index → FtsTree → FtsLeaf → Prop) (position : Position) :
    CanonicalCoordinate.Hidden words before (.graph position) = CanonicalCoordinate.Hidden words after (.graph position) := by
  cases position <;> rfl

theorem Routing.disclose_agreement (routing : Routing) (words : OtsReferenceWords) (actual : Labels)
    (hagrees : PublicAgreement words routing.disclosed routing.known actual)
    (view : FewTimeView) (secrets : Fin ftsOpenings → Digest)
    (hsecrets : ∀ s, secrets s = actual (.ftsStart view.1 porsTree (slotLeaf view s))) :
    PublicAgreement words (routing.disclose view secrets).disclosed (routing.disclose view secrets).known actual := by
  intro coordinate hpublic
  cases coordinate with
  | otsStart lay tree leaf chain => exact hagrees _ hpublic
  | graph position =>
      apply hagrees
      rw [hidden_graph_disclosed words routing.disclosed (routing.disclose view secrets).disclosed position]
      exact hpublic
  | ftsStart index tree leaf =>
      change ¬¬(routing.disclosed index tree leaf ∨ index = view.1 ∧ ∃ s, leaf = slotLeaf view s) at hpublic
      change (if h : index = view.1 ∧ ∃ s, leaf = slotLeaf view s then secrets h.2.choose
        else routing.known (.ftsStart index tree leaf)) = _
      split
      · rename_i h
        rw [hsecrets, ← h.2.choose_spec, ← h.1, Subsingleton.elim tree porsTree]
      · rename_i h
        exact hagrees _ (not_not.mpr ((not_not.mp hpublic).resolve_right h))

theorem Routing.afterSigning_graph (routing : Routing) (record : SigningRecord) (position : Position) :
    (routing.afterSigning record).known (.graph position) = routing.known (.graph position) := by
  rcases record with ⟨⟨signature, view⟩, trace⟩
  cases signature <;> cases view <;> rfl

theorem Routing.afterSigning_cacheClean (routing : Routing) (record : SigningRecord)
    (parameter : PublicParameter) (words : OtsReferenceWords) (actual : Labels) (cache : ExternalCache)
    (hclean : CacheClean parameter words routing.disclosed actual cache) :
    CacheClean parameter words (routing.afterSigning record).disclosed actual cache :=
  cacheClean_disclose parameter words routing.disclosed (routing.afterSigning record).disclosed
    (routing.afterSigning_mono record) actual cache hclean

theorem Routing.afterSigning_completed_agreement (routing : Routing) (words : OtsReferenceWords) (actual : Labels)
    (hagrees : PublicAgreement words routing.disclosed routing.known actual) (record : PublicSigningRecord) :
    let completed := completePublicSigningRecord (fun index tree leaf => actual (.ftsStart index tree leaf)) record
    PublicAgreement words (routing.afterSigning completed).disclosed (routing.afterSigning completed).known actual := by
  rcases record with ⟨⟨plan, view⟩, trace⟩
  cases view with
  | none => exact hagrees
  | some view =>
      cases plan with
      | none => exact hagrees
      | some plan =>
          exact routing.disclose_agreement words actual hagrees view _
            (fun s => honestFtsOfSlots_secrets _ _ _ s)

end SphincsSecurity.Concrete.InterleavedResidual
