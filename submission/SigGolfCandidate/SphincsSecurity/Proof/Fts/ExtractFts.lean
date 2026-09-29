import SigGolfCandidate.SphincsSecurity.Proof.Fts.PorsExtract
import SigGolfCandidate.SphincsSecurity.Proof.Fts.PorsSchedule
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.BuildEval
/-!
# Extracting a few-time opening

The one extraction lemma both routes use (the reference route's `FtsVerifierWitness` and the crude route's
`RetainedResidualRecovery`). An accepting run of the PORS stack machine on a digest's leaves makes the leaves
admissible (`PorsStructure`), and if its root is the honest root of the instance, then either the signature's
PORS part is the honest opening — the sorted slots, the true secrets, the honest schedule's segments with the
honest nodes — and the verifier hashed every opened leaf's true secret, or one of the verifier's queries hit a
PORS node or leaf (`PorsExtract`, `PorsSchedule`). Supplying the honest secrets is the only alternative that is not
a hash break, and it means the secrets were revealed by signatures: that is the leak the parameters are chosen
against.
-/

namespace SphincsSecurity.Concrete

open OracleComp

/-- **The PORS extraction.** -/
theorem ftsRecover_extract (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (secret : FtsTree → FtsLeaf → Digest) (fts : FtsSignature)
    (hrecover : evalWithAnswerFn f (ftsRecover parameter index (slotValue leaves) fts)
      = some (honestFtsKey f parameter index secret)) :
    AdmissibleLeaves leaves ∧
      ((fts = evalWithAnswerFn f (ftsOpen parameter index leaves secret) ∧
          ∀ slot, tweakableHashInput parameter (.ftsLeaf index porsTree (leaves slot).val)
              (digestBytes (secret porsTree (leaves slot)))
            ∈ queriedInputs f (ftsRecover parameter index (slotValue leaves) fts))
        ∨ ∃ input ∈ queriedInputs f (ftsRecover parameter index (slotValue leaves) fts),
            PorsMachine.Hit f parameter index (secret porsTree) input) := by
  rw [PorsMachine.eval_ftsRecover] at hrecover
  rcases hrun : PorsMachine.recoverRun f parameter index (slotValue leaves) fts with _ | r
  · rw [hrun] at hrecover
    simp at hrecover
  rw [hrun] at hrecover
  have hnode : r.node = honestFtsKey f parameter index secret := Option.some.inj hrecover
  obtain ⟨slot, hperm, hsorted, _, _, hadmissible, hbij⟩ :=
    PorsMachine.recoverRun_structure f parameter index leaves fts r hrun
  obtain ⟨_, hlt⟩ := PorsMachine.recoverRun_order f parameter index (slotValue leaves) fts r hrun
  have hvalues : ∀ s : Fin ftsOpenings, slotValue leaves (fts.perm s) < 2 ^ ftsTreeHeight := by
    intro s
    have := hlt s.val s.isLt
    rwa [PorsMachine.leafValue_of_lt _ _ _ s.isLt] at this
  have hroot : r.node = PorsMachine.honest f parameter index (secret porsTree) 1 := by
    rw [hnode, honestFtsKey_eq_heap]
  refine ⟨hadmissible, ?_⟩
  rcases PorsMachine.recoverRun_extract f parameter index (secret porsTree) (slotValue leaves) fts hvalues r
      hrun hroot with hconsumed | ⟨input, hinput, hhit⟩
  · left
    have hhonest := PorsMachine.recoverRun_honest f parameter index leaves fts (secret porsTree) r hrun hconsumed
    refine ⟨by rw [eval_ftsOpen]; exact hhonest, fun r' => ?_⟩
    -- the leaf `leaves r'` is opened at the slot position `s` with `slot s = r'`
    obtain ⟨s, hs⟩ := hbij.2 r'
    obtain ⟨_, hopen⟩ := PorsMachine.recoverRun_schedule f parameter index leaves fts r hrun
    have hquery := PorsMachine.recoverRun_leafQuery f parameter index (slotValue leaves) fts r hrun _ (hopen s)
    rw [← PorsMachine.recoverRun_queries f parameter index _ _ r hrun]
    have hsecret : fts.secrets s = secret porsTree (leaves r') := by
      have := congrArg FtsSignature.secrets hhonest
      have hs' := congrFun this s
      rw [hs', honestFts]
      dsimp only
      rw [hsorted, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn, hs]
    have hvalue : PorsMachine.leafValue (slotValue leaves) fts s.val = (leaves r').val := by
      rw [PorsMachine.leafValue_of_lt _ _ _ s.isLt, Fin.eta, hperm s, PorsMachine.slotValue_castSucc, hs]
    simp only at hquery
    rw [hvalue, hsecret] at hquery
    exact hquery
  · right
    exact ⟨input, by rw [← PorsMachine.recoverRun_queries f parameter index _ _ r hrun]; exact hinput, hhit⟩

end SphincsSecurity.Concrete
