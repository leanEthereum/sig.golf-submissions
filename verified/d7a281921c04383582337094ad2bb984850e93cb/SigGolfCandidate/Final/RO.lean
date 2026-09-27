import SigGolfCandidate.Bridge.Basic
import VCVio.OracleComp.QueryTracking.RandomOracle.EagerTable

/-!
# Random-oracle tools for completeness

* `run'_relabel`: the lazy random oracle is invariant under an injective relabelling of the
  query inputs (single-oracle version of `Bridge.run'_relabelW`).
* `probOutput_false_foldAll_le`: for programs over a *finite* query domain, the probability that
  the conjunction of the outputs of a sequence of programs, all run against one shared lazy random
  oracle, is `false` is at most the sum of the individual failure probabilities (each program run
  against a fresh oracle). The proof goes through the eager (full-table) random oracle
  (`evalSPMF_simulateQ_randomOracle_run'_empty_eq_uniformTable`).
-/

open OracleSpec OracleComp

namespace SigGolfCandidate.Final
open SigGolfCandidate.Bridge

section relabel
variable {ι ι' R : Type} [DecidableEq ι] [DecidableEq ι'] [SampleableType R]

/-- **Lazy random oracle relabelling** (single oracle). -/
theorem run'_relabel (enc : ι' → ι) (henc : Function.Injective enc) {α : Type}
    (P : OracleComp (ι' →ₒ R) α) (cO : QueryCache (ι' →ₒ R)) (cA : QueryCache (ι →ₒ R))
    (hc : ∀ x, cO x = cA (enc x)) :
    (simulateQ randomOracle P).run' cO =
      (simulateQ randomOracle (relabel enc P)).run' cA := by
  induction P using OracleComp.inductionOn generalizing cO cA with
  | pure x => rfl
  | query_bind x k ih =>
    rw [relabel_query_bind]
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
    rw [randomOracle.run_eq, randomOracle.run_eq]
    have hx := hc x
    have hrel : ∀ u, ∀ y, (cO.cacheQuery x u) y = (cA.cacheQuery (enc x) u) (enc y) := by
      intro u y
      by_cases hy : y = x
      · subst hy; simp [QueryCache.cacheQuery_self]
      · rw [QueryCache.cacheQuery_of_ne _ _ hy,
          QueryCache.cacheQuery_of_ne _ _ (fun h => hy (henc h))]
        exact hc y
    revert hx
    cases cO x <;> cases cA (enc x) <;> intro hx <;> simp at hx
    · simp only [bind_assoc, pure_bind]
      refine bind_congr fun u => ?_
      have := ih u _ _ (hrel u)
      simpa [StateT.run'_eq] using this
    · subst hx
      simp only [pure_bind]
      rename_i u
      have := ih u cO cA hc
      simpa [StateT.run'_eq] using this

end relabel


section fold
variable {ι κ R : Type} {spec : OracleSpec ι}

/-- Run the programs `P k` for `k ∈ L` in order (against one oracle) and conjoin their outputs. -/
def foldAll (L : List κ) (P : κ → OracleComp spec Bool) (b : Bool) : OracleComp spec Bool :=
  L.foldlM (fun b k => (b && ·) <$> P k) b

@[simp] theorem foldAll_nil (P : κ → OracleComp spec Bool) (b : Bool) :
    foldAll [] P b = pure b := rfl

theorem foldAll_cons (k : κ) (L : List κ) (P : κ → OracleComp spec Bool) (b : Bool) :
    foldAll (k :: L) P b = P k >>= fun c => foldAll L P (b && c) := by
  simp [foldAll, List.foldlM_cons]

theorem evalWithAnswerFn_foldAll (h : QueryImpl spec Id) (L : List κ)
    (P : κ → OracleComp spec Bool) (b : Bool) :
    evalWithAnswerFn h (foldAll L P b) = (b && L.all fun k => evalWithAnswerFn h (P k)) := by
  induction L generalizing b with
  | nil => simp [foldAll_nil]
  | cons k L ih =>
    rw [foldAll_cons, evalWithAnswerFn_bind, ih]
    simp [Bool.and_assoc]

end fold

/-- Union bound over a list of events. -/
theorem probEvent_exists_list_le {α κ : Type} (mx : ProbComp α) (L : List κ) (E : κ → α → Prop) :
    Pr[fun x => ∃ k ∈ L, E k x | mx] ≤ (L.map fun k => Pr[E k | mx]).sum := by
  induction L with
  | nil => simp
  | cons k L ih =>
    simp only [List.mem_cons, exists_eq_or_imp, List.map_cons, List.sum_cons]
    exact (probEvent_or_le mx _ _).trans (add_le_add le_rfl ih)

section eager
variable {D R : Type} [DecidableEq D] [Finite D] [Finite R] [Nonempty R]
  [SampleableType R] [SampleableType (D → R)]

/-- **Union bound under one shared lazy random oracle** (finite query domain). -/
theorem probOutput_false_foldAll_le {κ : Type} (L : List κ) (P : κ → OracleComp (D →ₒ R) Bool) :
    Pr[= false | (simulateQ randomOracle (foldAll L P true)).run' ∅] ≤
      (L.map fun k => Pr[= false | (simulateQ randomOracle (P k)).run' ∅]).sum := by
  have e : ∀ {β : Type} (oa : OracleComp (D →ₒ R) β) (y : β),
      Pr[= y | (simulateQ randomOracle oa).run' ∅] =
        Pr[fun g => evalWithAnswerFn (QueryImpl.ofFn g) oa = y | $ᵗ (D → R)] := by
    intro β oa y
    have h1 := evalSPMF_simulateQ_randomOracle_run'_empty_eq_uniformTable (D := D) (R := R) oa
    have h2 : Pr[= y | (simulateQ randomOracle oa).run' ∅] =
        Pr[= y | (fun g => evalWithAnswerFn (QueryImpl.ofFn g) oa) <$> ($ᵗ (D → R) : ProbComp _)] := by
      simp only [probOutput_def, h1, map_eq_bind_pure_comp]
      rfl
    rw [h2, ← probEvent_eq_eq_probOutput, probEvent_map]
    rfl
  rw [e]
  simp_rw [e]
  refine le_trans (probEvent_mono ?_) (probEvent_exists_list_le _ L
    (fun k g => evalWithAnswerFn (QueryImpl.ofFn g) (P k) = false))
  intro g _ hg
  rw [evalWithAnswerFn_foldAll] at hg
  simpa using hg

end eager

end SigGolfCandidate.Final
