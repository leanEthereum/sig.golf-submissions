import SigGolfCandidate.Ref.Basic

/-!
# Counting oracle calls

`countWith wt oa` runs `oa` against the real oracle and additionally returns the total weight
`wt q` of the queries `q` it made (`simulateQ` into `StateT Nat`). `countCalls = countWith 1`
counts calls, `countBlocks = countWith Query.blocks` counts compressions.
-/

namespace SigGolfCandidate.Ref
open SigGolf OracleComp OracleSpec

universe u

/-- Forward a query and add its weight to the counter. -/
def countImpl (wt : Query → Nat) : QueryImpl HashSpec (StateT Nat (OracleComp HashSpec)) :=
  fun q => do
    modify (· + wt q)
    liftM (HashSpec.query q)

def countWith (wt : Query → Nat) {α : Type} (oa : OracleComp HashSpec α) :
    OracleComp HashSpec (α × Nat) :=
  (simulateQ (countImpl wt) oa).run 0

/-- The result and the number of oracle calls. -/
def countCalls {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Nat) :=
  countWith (fun _ => 1) oa

/-- The result and the number of compressions (64-byte blocks). -/
def countBlocks {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Nat) :=
  countWith Query.blocks oa

section
variable (wt : Query → Nat) {α β : Type}

/-- Running from counter `n` adds `n` to the count. -/
theorem countImpl_run (oa : OracleComp HashSpec α) (n : Nat) :
    (simulateQ (countImpl wt) oa).run n = (fun p => (p.1, n + p.2)) <$> countWith wt oa := by
  unfold countWith
  induction oa using OracleComp.inductionOn generalizing n with
  | pure a => simp
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, countImpl]
    simp only [StateT.run_modify, pure_bind, map_bind]
    have hl : ∀ s, (liftM (OracleSpec.query q) : StateT Nat (OracleComp HashSpec) _).run s =
        (fun a => (a, s)) <$> (liftM (OracleSpec.query q) : OracleComp HashSpec _) := fun s => rfl
    simp only [hl, bind_map_left, ih _ (n + wt q), ih _ (0 + wt q), Functor.map_map]
    congr 1; funext a; congr 1; funext p; simp only [Prod.mk.injEq, true_and]; omega

@[simp] theorem countWith_pure (a : α) : countWith wt (pure a : OracleComp HashSpec α) = pure (a, 0) :=
  rfl

/-- Counts add up along a bind. -/
theorem countWith_bind (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    countWith wt (oa >>= f) =
      countWith wt oa >>= fun p => (fun r => (r.1, p.2 + r.2)) <$> countWith wt (f p.1) := by
  conv_lhs => unfold countWith
  rw [simulateQ_bind, StateT.run_bind]
  exact congrArg _ (funext fun p => countImpl_run wt (f p.1) p.2)

@[simp] theorem countWith_query (q : Query) :
    countWith wt (liftM (HashSpec.query q) : OracleComp HashSpec _) =
      (fun a => (a, wt q)) <$> (liftM (HashSpec.query q) : OracleComp HashSpec _) := by
  unfold countWith
  rw [simulateQ_spec_query]
  simp only [countImpl, StateT.run_bind, StateT.run_modify, pure_bind, Nat.zero_add]
  rfl

/-- Dropping the count gives back the computation. -/
@[simp] theorem fst_countWith (oa : OracleComp HashSpec α) : Prod.fst <$> countWith wt oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countWith_bind, countWith_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    exact ih a

@[simp] theorem countWith_H (x : List Byte) :
    countWith wt (H x) = (fun a => (a, wt (pad64 x))) <$> H x :=
  countWith_query wt (pad64 x)

end

theorem countCalls_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    countCalls (oa >>= f) =
      countCalls oa >>= fun p => (fun r => (r.1, p.2 + r.2)) <$> countCalls (f p.1) :=
  countWith_bind _ oa f

@[simp] theorem countCalls_pure {α : Type} (a : α) :
    countCalls (pure a : OracleComp HashSpec α) = pure (a, 0) := rfl

@[simp] theorem countCalls_query (q : Query) :
    countCalls (liftM (HashSpec.query q) : OracleComp HashSpec _) =
      (fun a => (a, 1)) <$> (liftM (HashSpec.query q) : OracleComp HashSpec _) :=
  countWith_query _ q

@[simp] theorem countCalls_H (x : List Byte) : countCalls (H x) = (fun a => (a, 1)) <$> H x :=
  countWith_H _ x

@[simp] theorem fst_countCalls {α : Type} (oa : OracleComp HashSpec α) :
    Prod.fst <$> countCalls oa = oa := fst_countWith _ oa

/-- Under a fixed answer function, the counted run returns the plain result. -/
theorem evalWith_countCalls_fst {α : Type} (hash : Hash) (oa : OracleComp HashSpec α) :
    (evalWithAnswerFn hash (countCalls oa)).1 = evalWithAnswerFn hash oa := by
  conv_rhs => rw [← fst_countCalls oa]
  simp only [evalWithAnswerFn, simulateQ_map]
  rfl

end SigGolfCandidate.Ref
