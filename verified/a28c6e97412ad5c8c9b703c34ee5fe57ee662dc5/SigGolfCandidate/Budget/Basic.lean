import SigGolfCandidate.Ref
import VCVio.EvalDist.Expectation

/-!
# Budget: the weighted-expectation calculus

For a computation `oa : OracleComp HashSpec α` run under the lazy random oracle from a cache `c`,
`V z oa c` is the expectation of `z ^ K`, where `K` is the number of compressions of `oa`'s
queries (`countBlocks`). It is multiplicative along binds (`V_bind_le`), and a query contributes
`z ^ blocks` times the average over the random oracle's answer (`V_query`).

`Spec P Post k oa` is a small Hoare-style predicate: every query of `oa` satisfies `P`, every
result satisfies `Post`, and the compressions along every path are at most `k`. It gives
`V z oa c ≤ z ^ k` (`Spec.V_le`) and the cache invariants of the reachable states
(`Spec.support`).
-/

namespace SigGolfCandidate.Budget
open SigGolf OracleComp OracleSpec ENNReal OracleComp.EvalDist
open SigGolfCandidate.Ref

/-- The random-oracle cache. -/
abbrev RCache := QueryCache HashSpec

/-- One query as an `OracleComp`. -/
abbrev qry (q : Query) : OracleComp HashSpec (BitVec 256) :=
  liftM (OracleSpec.query (spec := HashSpec) q)

/-- Run under the lazy random oracle from cache `c`. -/
noncomputable def roRun {α : Type} (oa : OracleComp HashSpec α) (c : RCache) :
    ProbComp (α × RCache) :=
  (simulateQ randomOracle oa).run c

theorem roRun_bind {α β : Type} (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β)
    (c : RCache) : roRun (oa >>= f) c = roRun oa c >>= fun x => roRun (f x.1) x.2 := by
  simp only [roRun, simulateQ_bind, StateT.run_bind]

theorem roRun_map {α β : Type} (g : α → β) (oa : OracleComp HashSpec α) (c : RCache) :
    roRun (g <$> oa) c = (fun x => (g x.1, x.2)) <$> roRun oa c := by
  simp only [roRun, simulateQ_map, StateT.run_map]

@[simp] theorem roRun_pure {α : Type} (a : α) (c : RCache) :
    roRun (pure a : OracleComp HashSpec α) c = pure (a, c) := by
  simp [roRun]

theorem roRun_qry (q : Query) (c : RCache) :
    roRun (qry q) c = (randomOracle q).run c := by
  simp [roRun, qry]

/-- The reachable states of the counted run are those of the plain run. -/
theorem mem_support_roRun_of_count {α : Type} (wt : Query → Nat) (oa : OracleComp HashSpec α)
    (c : RCache) (x : (α × Nat) × RCache) (hx : x ∈ support (roRun (countWith wt oa) c)) :
    (x.1.1, x.2) ∈ support (roRun oa c) := by
  have h : roRun oa c = (fun x => (x.1.1, x.2)) <$> roRun (countWith wt oa) c := by
    conv_lhs => rw [← fst_countWith wt oa]
    rw [roRun_map]
  rw [h, support_map]
  exact ⟨x, hx, rfl⟩

theorem ev_const_mul {γ : Type} (mx : ProbComp γ) (g : γ → ℝ≥0∞) (a : ℝ≥0∞) :
    expectedValue mx (fun x => a * g x) = a * expectedValue mx g := by
  simp only [mul_comm a]
  exact expectedValue_mul_const mx g a

/-- The expectation of `z ^ compressions`. -/
noncomputable def V (z : ℝ≥0∞) {α : Type} (oa : OracleComp HashSpec α) (c : RCache) : ℝ≥0∞ :=
  expectedValue (roRun (countBlocks oa) c) (fun x => z ^ x.1.2)

@[simp] theorem V_pure (z : ℝ≥0∞) {α : Type} (a : α) (c : RCache) :
    V z (pure a : OracleComp HashSpec α) c = 1 := by
  simp [V, countBlocks]

theorem V_bind_eq (z : ℝ≥0∞) {α β : Type} (oa : OracleComp HashSpec α)
    (f : α → OracleComp HashSpec β) (c : RCache) :
    V z (oa >>= f) c = expectedValue (roRun (countBlocks oa) c)
      (fun x => z ^ x.1.2 * V z (f x.1.1) x.2) := by
  unfold V countBlocks
  rw [countWith_bind, roRun_bind, expectedValue_bind]
  congr 1; funext x
  rw [roRun_map, expectedValue_map]
  simp only [pow_add]
  exact ev_const_mul _ _ _

/-- Multiplicativity: a bound on the continuation from every reachable state. -/
theorem V_bind_le (z : ℝ≥0∞) {α β : Type} (oa : OracleComp HashSpec α)
    (f : α → OracleComp HashSpec β) (c : RCache) (b : ℝ≥0∞)
    (h : ∀ x ∈ support (roRun oa c), V z (f x.1) x.2 ≤ b) :
    V z (oa >>= f) c ≤ V z oa c * b := by
  rw [V_bind_eq]
  unfold V
  rw [← expectedValue_mul_const]
  refine expectedValue_mono_of_support fun x hx => ?_
  have := h (x.1.1, x.2) (mem_support_roRun_of_count _ oa c x hx)
  exact mul_le_mul' le_rfl this

theorem V_map (z : ℝ≥0∞) {α β : Type} (g : α → β) (oa : OracleComp HashSpec α) (c : RCache) :
    V z (g <$> oa) c = V z oa c := by
  rw [map_eq_bind_pure_comp, V_bind_eq, V]
  simp

theorem V_map_le (z : ℝ≥0∞) {α β : Type} (g : α → β) (oa : OracleComp HashSpec α) (c : RCache)
    (b : ℝ≥0∞) (h : V z oa c ≤ b) : V z (g <$> oa) c ≤ b := by
  rwa [V_map]

/-- One query: its blocks, then the average over the random oracle's answer. -/
theorem V_query (z : ℝ≥0∞) {α : Type} (q : Query) (f : BitVec 256 → OracleComp HashSpec α)
    (c : RCache) :
    V z (qry q >>= f) c =
      z ^ q.blocks * expectedValue ((randomOracle q).run c) (fun y => V z (f y.1) y.2) := by
  rw [V_bind_eq]
  unfold countBlocks
  rw [countWith_query, roRun_map, expectedValue_map, roRun_qry]
  exact ev_const_mul ((randomOracle q).run c) (fun y => V z (f y.1) y.2) (z ^ q.blocks)

/-- The random oracle's answer to a query: cached, or a fresh uniform draw. -/
theorem expectedValue_ro_fresh (q : Query) (c : RCache) (hq : c q = none)
    (g : BitVec 256 × RCache → ℝ≥0∞) :
    expectedValue ((randomOracle q).run c) g =
      expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256)) (fun u => g (u, c.cacheQuery q u)) := by
  rw [randomOracle.run_eq, hq]
  simp only
  rw [expectedValue_bind]
  simp

theorem expectedValue_ro_cached (q : Query) (c : RCache) (u : BitVec 256) (hq : c q = some u)
    (g : BitVec 256 × RCache → ℝ≥0∞) :
    expectedValue ((randomOracle q).run c) g = g (u, c) := by
  rw [randomOracle.run_eq, hq]
  simp

/-- The support of one random-oracle step: the cache only grows by the queried entry. -/
theorem mem_support_ro (q : Query) (c : RCache) (y : BitVec 256 × RCache)
    (hy : y ∈ support ((randomOracle q).run c)) :
    (c q = some y.1 ∧ y.2 = c) ∨ (c q = none ∧ y.2 = c.cacheQuery q y.1) := by
  rw [randomOracle.run_eq] at hy
  cases hq : c q with
  | some u =>
    rw [hq] at hy
    simp only [support_pure, Set.mem_singleton_iff] at hy
    subst hy
    left; exact ⟨rfl, rfl⟩
  | none =>
    rw [hq] at hy
    simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
      exists_prop] at hy
    obtain ⟨u, _, rfl⟩ := hy
    right; exact ⟨rfl, rfl⟩

/-! ## `Spec` -/

/-- Every query satisfies `P`, every result `Post`, and every path costs at most `k` blocks. -/
inductive Spec (P : Query → Prop) {α : Type} (Post : α → Prop) :
    Nat → OracleComp HashSpec α → Prop
  | pure (a : α) (k : Nat) : Post a → Spec P Post k (pure a)
  | query (q : Query) (f : BitVec 256 → OracleComp HashSpec α) (k : Nat) :
      P q → (∀ u, Spec P Post k (f u)) → Spec P Post (q.blocks + k) (qry q >>= f)

namespace Spec

variable {P : Query → Prop} {α β : Type}

theorem mono_k {Post : α → Prop} {k k' : Nat} {oa : OracleComp HashSpec α}
    (h : Spec P Post k oa) (hk : k ≤ k') : Spec P Post k' oa := by
  induction h generalizing k' with
  | pure a k hp => exact .pure a k' hp
  | query q f k hq _ ih =>
    have : k' = q.blocks + (k' - q.blocks) := by omega
    rw [this]
    exact .query q f _ hq fun u => ih u (by omega)

theorem mono {P' : Query → Prop} {Post Post' : α → Prop} {k : Nat} {oa : OracleComp HashSpec α}
    (h : Spec P Post k oa) (hP : ∀ q, P q → P' q) (hQ : ∀ a, Post a → Post' a) :
    Spec P' Post' k oa := by
  induction h with
  | pure a k hp => exact .pure a k (hQ a hp)
  | query q f k hq _ ih => exact .query q f k (hP q hq) ih

theorem bind {Q : α → Prop} {R : β → Prop} {k l : Nat} {oa : OracleComp HashSpec α}
    {f : α → OracleComp HashSpec β} (h : Spec P Q k oa) (hf : ∀ a, Q a → Spec P R l (f a)) :
    Spec P R (k + l) (oa >>= f) := by
  induction h with
  | pure a k hp => rw [pure_bind]; exact (hf a hp).mono_k (by omega)
  | query q g k hq _ ih =>
    rw [bind_assoc, Nat.add_assoc]
    exact .query q _ _ hq ih

theorem bind' {Q : α → Prop} {R : β → Prop} {k l n : Nat} {oa : OracleComp HashSpec α}
    {f : α → OracleComp HashSpec β} (h : Spec P Q k oa) (hf : ∀ a, Q a → Spec P R l (f a))
    (hn : k + l ≤ n) : Spec P R n (oa >>= f) :=
  (h.bind hf).mono_k hn

theorem map {Q : α → Prop} {R : β → Prop} {k : Nat} {oa : OracleComp HashSpec α} (g : α → β)
    (h : Spec P Q k oa) (hg : ∀ a, Q a → R (g a)) : Spec P R k (g <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact (h.bind (l := 0) fun a ha => .pure _ 0 (hg a ha))

theorem qry_bind {R : β → Prop} {q : Query} {f : BitVec 256 → OracleComp HashSpec β} {k n : Nat}
    (hq : P q) (hf : ∀ u, Spec P R k (f u)) (hn : q.blocks + k ≤ n) :
    Spec P R n (qry q >>= f) :=
  (Spec.query q f k hq hf).mono_k hn

/-- The expectation bound. -/
theorem V_le {Post : α → Prop} {k : Nat} {oa : OracleComp HashSpec α} (h : Spec P Post k oa)
    {z : ℝ≥0∞} (hz : 1 ≤ z) (c : RCache) : V z oa c ≤ z ^ k := by
  induction h generalizing c with
  | pure a k _ => rw [V_pure]; exact one_le_pow₀ hz
  | query q f k _ _ ih =>
    rw [V_query, pow_add]
    exact mul_le_mul' le_rfl (expectedValue_le_of_le _ fun y => ih y.1 y.2)

/-- A cache invariant: every cached entry satisfies `I`. -/
def _root_.SigGolfCandidate.Budget.CacheInv (I : Query → Prop) (c : RCache) : Prop :=
  ∀ q u, c q = some u → I q

/-- Reachable states: results satisfy `Post`, and a cache invariant implied by `P` is kept. -/
theorem support {Post : α → Prop} {k : Nat} {oa : OracleComp HashSpec α} (h : Spec P Post k oa)
    {I : Query → Prop} (hPI : ∀ q, P q → I q) (c : RCache) (hc : CacheInv I c)
    (x : α × RCache) (hx : x ∈ support (roRun oa c)) : Post x.1 ∧ CacheInv I x.2 := by
  induction h generalizing c with
  | pure a k hp =>
    rw [roRun_pure, support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact ⟨hp, hc⟩
  | query q f k hq _ ih =>
    rw [roRun_bind, support_bind] at hx
    simp only [Set.mem_iUnion, exists_prop] at hx
    obtain ⟨y, hy, hx⟩ := hx
    rw [roRun_qry] at hy
    refine ih y.1 y.2 ?_ hx
    rcases mem_support_ro q c y hy with ⟨_, h2⟩ | ⟨_, h2⟩
    · rw [h2]; exact hc
    · rw [h2]
      intro q' u hq'
      by_cases hqq : q' = q
      · subst hqq; exact hPI _ hq
      · rw [QueryCache.cacheQuery_of_ne _ _ hqq] at hq'
        exact hc q' u hq'

end Spec

theorem CacheInv.mono {I I' : Query → Prop} {c : RCache} (h : CacheInv I c)
    (hI : ∀ q, I q → I' q) : CacheInv I' c := fun q u hq => hI q (h q u hq)

end SigGolfCandidate.Budget
