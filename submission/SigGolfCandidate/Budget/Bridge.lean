import SigGolfCandidate.Budget.Main
import SigGolfCandidate.Sign.Sim

/-!
# Budget: bridge to the bytecode refinement theorems

The refinement proofs state phases as
`(fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run phase input =
  (fun p => (F p.1, p.2.1, p.2.2)) <$> Sign.countBoth oa` (`Sign.Sim.run_eq`). This file turns
such statements into the hypotheses of `compressionBounds_of_refinement` (no dependency on the
Keygen / Sign proofs; `Final.lean` discharges keygen and sign with them).
-/

namespace SigGolfCandidate.Budget
open SigGolf SigGolfCandidate.Ref OracleComp

section
variable (sub : Submission)

/-- The refinement form of a phase: `F <$> countBoth oa`. -/
def RefinesCounts (phase : Phase) (input : Input sub.sizes phase) {α : Type}
    (oa : OracleComp HashSpec α) : Prop :=
  ∃ F : α → Option (Output sub.sizes phase),
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> sub.run phase input =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> Sign.countBoth oa

theorem compressions_of_refinesCounts {phase : Phase} {input : Input sub.sizes phase} {α : Type}
    {oa : OracleComp HashSpec α} (h : RefinesCounts sub phase input oa) :
    ∃ F : α → Option (Output sub.sizes phase),
      (fun r => (r.value, r.hashCompressions)) <$> sub.run phase input =
        (fun p => (F p.1, p.2)) <$> countBlocks oa := by
  obtain ⟨F, hF⟩ := h
  refine ⟨F, ?_⟩
  have h2 := congrArg (fun x => (fun t => (t.1, t.2.2)) <$> x) hF
  simp only [Functor.map_map] at h2
  rw [h2, ← Sign.countBoth_blocks, Functor.map_map]

theorem keygenRefines_of_counts (h : ∀ sk, RefinesCounts sub .keygen sk (keygenRef sk)) :
    KeygenRefines sub := fun sk => compressions_of_refinesCounts sub (h sk)

theorem signRefines_of_counts (hc : sub.sizes.cache = CACHE_BYTES)
    (h : ∀ sk cache m, RefinesCounts sub .sign (sk, cache, m) (signRef sk (refCache hc cache) m)) :
    SignRefines sub hc := by
  intro sk cache m
  obtain ⟨F, hF⟩ := compressions_of_refinesCounts sub (h sk cache m)
  have h2 := congrArg (fun x => Prod.snd <$> x) hF
  simp only [Functor.map_map] at h2
  exact h2

end

/-- `expandRef` makes one query, the one-block digest of `rho` and `m`. -/
theorem spec_expandRef (m : Bytes 32) (pk : Bytes 16) (sig : Bytes 6100) :
    Spec (fun _ => True) (fun _ => True) 1 (expandRef m pk sig) := by
  have hr : (sigRho (toList sig)).length = 16 := by
    simp [sigRho, slice, length_toList]
  obtain ⟨-, hb⟩ := dig_ok (sigRho (toList sig)) (toList m) hr (length_toList m)
  unfold expandRef expandList digest
  simp only [bind_assoc, pure_bind]
  exact Spec.qry_bind trivial (fun u => Spec.pure _ 0 trivial) (by omega)

/-- Expand of the submission from its refinement of `expandRef` (in the form of `Sign.Sim.run_eq`). -/
theorem expandOneBlock_of_counts
    (h : ∀ m pk (sig : Bytes 6100), RefinesCounts submission .expand (m, pk, sig) (expandRef m pk sig)) :
    ExpandOneBlock submission := by
  rintro ⟨m, pk, sig⟩
  refine ⟨_, expandRef m pk sig, spec_expandRef m pk sig, ?_⟩
  obtain ⟨F, hF⟩ := compressions_of_refinesCounts submission (h m pk sig)
  have h2 := congrArg (fun x => Prod.snd <$> x) hF
  simp only [Functor.map_map] at h2
  exact h2

/-- **Compression bounds** for `SigGolfCandidate.submission`, given the keygen, sign and expand
refinements in the form of `Sign.Sim.run_eq` (`Final.lean` discharges `hK` and `hS`). -/
theorem submission_compressionBounds_of_counts'
    (hK : ∀ sk, RefinesCounts submission .keygen sk (keygenRef sk))
    (hS : ∀ sk cache m, RefinesCounts submission .sign (sk, cache, m) (signRef sk cache m))
    (hE : ∀ m pk (sig : Bytes 6100), RefinesCounts submission .expand (m, pk, sig) (expandRef m pk sig)) :
    submission.CompressionBounds :=
  submission_compressionBounds_of_refines (keygenRefines_of_counts submission hK)
    (signRefines_of_counts submission rfl hS) (expandOneBlock_of_counts hE)

end SigGolfCandidate.Budget
