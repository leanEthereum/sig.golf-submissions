import SigGolfCandidate.Budget.Main
import SigGolfCandidate.Sign.Sim

/-!
# Budget: bridge to the bytecode refinement theorems

The refinement proofs state phases as
`(fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run phase input =
  (fun p => (F p.1, p.2.1, p.2.2)) <$> Sign.countBoth oa` (`Sign.Sim.run_eq`). This file turns
such statements into the hypotheses of `compressionBounds_of_refinement`, and discharges the
keygen one taken as a hypothesis (no dependency on the Keygen build).
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

/-- Expand refines a pure computation (no queries). -/
theorem expandNoHash_of_counts
    (h : ∀ input, ∃ (α : Type) (a : α), RefinesCounts sub .expand input (pure a)) :
    ExpandNoHash sub := by
  intro input
  obtain ⟨α, a, F, hF⟩ := h input
  have h2 := congrArg (fun x => (fun t => t.2.2) <$> x) hF
  simp only [Functor.map_map, Sign.countBoth_pure, map_pure] at h2
  exact h2

end

/-- **Compression bounds** for `SigGolfCandidate.submission`, given the keygen, sign and expand
refinements in the form of `Sign.Sim.run_eq`.

(Budget does not import the Keygen proofs; once it states `RefinesCounts submission .keygen sk (keygenRef sk)`, `hK` is discharged by it and
`submission_compressionBounds_of_counts` below takes only `hS` and `hE` again.) -/
theorem submission_compressionBounds_of_counts'
    (hK : ∀ sk, RefinesCounts submission .keygen sk (keygenRef sk))
    (hS : ∀ sk cache m, RefinesCounts submission .sign (sk, cache, m) (signRef sk cache m))
    (hE : ∀ input, ∃ (α : Type) (a : α), RefinesCounts submission .expand input (pure a)) :
    submission.CompressionBounds :=
  submission_compressionBounds (keygenRefines_of_counts submission hK)
    (signRefines_of_counts submission rfl hS) (expandNoHash_of_counts submission hE)

end SigGolfCandidate.Budget
