import VCVio.OracleComp.QueryTracking.RandomOracle.Simulation
import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Generic free-monad tools for the security bridge

* `relabel` / `relabelW`: rename hash-oracle inputs (constant-range specs).
* `countFrom` / `countCalls`: thread a query counter through a computation (`StateT ℕ`).
* `AllQ`: every query made along every path satisfies a predicate.
-/

open OracleSpec OracleComp

namespace SigGolfCandidate.Bridge

section relabel

variable {ι ι' ι'' : Type} {R : Type}

/-- Rename every query input by `f`. -/
def relabelImpl (f : ι → ι') : QueryImpl (ι →ₒ R) (OracleComp (ι' →ₒ R)) :=
  fun t => ((ι' →ₒ R).query (f t) : OracleComp (ι' →ₒ R) R)

/-- Rename every query input by `f`. -/
def relabel (f : ι → ι') {α : Type} (oa : OracleComp (ι →ₒ R) α) : OracleComp (ι' →ₒ R) α :=
  simulateQ (relabelImpl f) oa

@[simp] lemma relabel_pure (f : ι → ι') {α : Type} (x : α) :
    relabel (R := R) f (pure x) = pure x := rfl

@[simp] lemma relabel_bind (f : ι → ι') {α β : Type} (oa : OracleComp (ι →ₒ R) α)
    (ob : α → OracleComp (ι →ₒ R) β) :
    relabel f (oa >>= ob) = relabel f oa >>= fun x => relabel f (ob x) := by
  simp [relabel]

@[simp] lemma relabel_map (f : ι → ι') {α β : Type} (oa : OracleComp (ι →ₒ R) α) (g : α → β) :
    relabel f (g <$> oa) = g <$> relabel f oa := by
  simp [relabel]

@[simp] lemma relabel_query (f : ι → ι') (t : ι) :
    relabel f ((ι →ₒ R).query t : OracleComp (ι →ₒ R) R) =
      ((ι' →ₒ R).query (f t) : OracleComp (ι' →ₒ R) R) := by
  simp [relabel, relabelImpl]

lemma relabel_query_bind (f : ι → ι') {α : Type} (t : ι) (k : R → OracleComp (ι →ₒ R) α) :
    relabel f (((ι →ₒ R).query t : OracleComp (ι →ₒ R) R) >>= k) =
      ((ι' →ₒ R).query (f t) : OracleComp (ι' →ₒ R) R) >>= fun u => relabel f (k u) := by
  simp

lemma relabel_relabel (f : ι → ι') (g : ι' → ι'') {α : Type} (oa : OracleComp (ι →ₒ R) α) :
    relabel g (relabel f oa) = relabel (g ∘ f) oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [relabel_bind, ih]
    simp [relabel, relabelImpl]

end relabel

section count

variable {ι : Type} {spec : OracleSpec.{0,0} ι}

/-- Charge `cost t` for every query `t`, forwarding the query unchanged. -/
def countImpl (spec : OracleSpec.{0,0} ι) (cost : ι → ℕ) : QueryImpl spec (StateT ℕ (OracleComp spec)) :=
  fun t => do modify (· + cost t); liftM (spec.query t)

/-- Run `oa`, counting from `c`. -/
def countFrom (cost : ι → ℕ) {α : Type} (oa : OracleComp spec α) (c : ℕ) :
    OracleComp spec (α × ℕ) :=
  (simulateQ (countImpl spec cost) oa).run c

/-- Run `oa` and return how many queries it made (every query costs one). -/
def countCalls {α : Type} (oa : OracleComp spec α) : OracleComp spec (α × ℕ) :=
  countFrom (fun _ => 1) oa 0

variable (cost : ι → ℕ)

@[simp] lemma countFrom_pure {α : Type} (x : α) (c : ℕ) :
    countFrom (spec := spec) cost (pure x) c = pure (x, c) := rfl

lemma countFrom_bind {α β : Type} (oa : OracleComp spec α) (ob : α → OracleComp spec β) (c : ℕ) :
    countFrom cost (oa >>= ob) c = countFrom cost oa c >>= fun p => countFrom cost (ob p.1) p.2 := by
  simp [countFrom]

lemma countFrom_query_bind {α : Type} (t : ι) (k : spec.Range t → OracleComp spec α) (c : ℕ) :
    countFrom cost ((spec.query t : OracleComp spec _) >>= k) c =
      (spec.query t : OracleComp spec _) >>= fun u => countFrom cost (k u) (c + cost t) := by
  simp [countFrom, countImpl]

lemma countFrom_query (t : ι) (c : ℕ) :
    countFrom cost (spec.query t : OracleComp spec _) c =
      (fun u => (u, c + cost t)) <$> (spec.query t : OracleComp spec _) := by
  have := countFrom_query_bind cost t (fun u => (pure u : OracleComp spec _)) c
  simpa [map_eq_bind_pure_comp] using this

lemma countFrom_map {α β : Type} (oa : OracleComp spec α) (g : α → β) (c : ℕ) :
    countFrom cost (g <$> oa) c = (fun p => (g p.1, p.2)) <$> countFrom cost oa c := by
  simp [countFrom]

lemma fst_map_countFrom {α : Type} (oa : OracleComp spec α) (c : ℕ) :
    Prod.fst <$> countFrom cost oa c = oa := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x => rfl
  | query_bind t k ih =>
    rw [countFrom_query_bind]
    simp [ih]

lemma countFrom_shift {α : Type} (oa : OracleComp spec α) (c : ℕ) :
    countFrom cost oa c = (fun p => (p.1, c + p.2)) <$> countFrom cost oa 0 := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x => simp
  | query_bind t k ih =>
    rw [countFrom_query_bind, countFrom_query_bind]
    simp only [map_bind]
    refine bind_congr fun u => ?_
    rw [ih u (0 + cost t), ih u (c + cost t)]
    simp [Nat.add_assoc]

end count

section countRelabel

variable {ι ι' : Type} {R : Type}

lemma relabel_countFrom (f : ι → ι') {α : Type} (oa : OracleComp (ι →ₒ R) α) (c : ℕ) :
    relabel f (countFrom (fun _ => 1) oa c) = countFrom (fun _ => 1) (relabel f oa) c := by
  induction oa using OracleComp.inductionOn generalizing c with
  | pure x => rfl
  | query_bind t k ih =>
    rw [countFrom_query_bind, relabel_bind, relabel_bind, relabel_query, countFrom_query_bind]
    simp only [ih]

lemma relabel_countCalls (f : ι → ι') {α : Type} (oa : OracleComp (ι →ₒ R) α) :
    relabel f (countCalls oa) = countCalls (relabel f oa) :=
  relabel_countFrom f oa 0

end countRelabel

section allQ

variable {ι : Type} {R : Type}

/-- Every query made along every execution path satisfies `P`. -/
def AllQ (P : ι → Prop) {α : Type} : OracleComp (ι →ₒ R) α → Prop
  | .pure _ => True
  | .liftBind t k => P t ∧ ∀ u, AllQ P (k u)

variable (P : ι → Prop)

@[simp] lemma allQ_pure {α : Type} (x : α) : AllQ (R := R) P (pure x) := trivial

@[simp] lemma allQ_query_bind {α : Type} (t : ι) (k : R → OracleComp (ι →ₒ R) α) :
    AllQ P (((ι →ₒ R).query t : OracleComp (ι →ₒ R) R) >>= k) ↔ P t ∧ ∀ u, AllQ P (k u) :=
  Iff.rfl

lemma allQ_bind {α β : Type} {oa : OracleComp (ι →ₒ R) α} {ob : α → OracleComp (ι →ₒ R) β}
    (h : AllQ P oa) (h' : ∀ x, AllQ P (ob x)) : AllQ P (oa >>= ob) := by
  induction oa using OracleComp.inductionOn with
  | pure x => simpa using h' x
  | query_bind t k ih =>
    rw [bind_assoc, allQ_query_bind]
    rw [allQ_query_bind] at h
    exact ⟨h.1, fun u => ih u (h.2 u)⟩

@[simp] lemma allQ_query (t : ι) :
    AllQ P ((ι →ₒ R).query t : OracleComp (ι →ₒ R) R) ↔ P t := by
  have := allQ_query_bind P t (fun u => (pure u : OracleComp (ι →ₒ R) R))
  simp only [bind_pure] at this
  simpa using this

lemma allQ_map {α β : Type} {oa : OracleComp (ι →ₒ R) α} (g : α → β) (h : AllQ P oa) :
    AllQ P (g <$> oa) := by
  rw [map_eq_bind_pure_comp]
  exact allQ_bind P h fun _ => trivial

/-- Relabelling by a map that fixes every `P`-query changes nothing. -/
lemma relabel_eq_self_of_allQ (h : ι → ι) (hP : ∀ x, P x → h x = x) {α : Type}
    {oa : OracleComp (ι →ₒ R) α} (hq : AllQ P oa) : relabel h oa = oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    rw [allQ_query_bind] at hq
    rw [relabel_bind, relabel_query, hP t hq.1]
    exact bind_congr fun u => ih u (hq.2 u)

end allQ

section coupling

variable {ι : Type} {spec : OracleSpec.{0,0} ι}

/-- `Ext p p'`: `p'` is `p` followed by extra queries whose results are discarded. -/
inductive Ext {α : Type} : OracleComp spec α → OracleComp spec α → Prop
  | leaf {β : Type} (x : α) (q : OracleComp spec β) : Ext (pure x) ((fun _ => x) <$> q)
  | queryBind (t : ι) (k k' : spec.Range t → OracleComp spec α) :
      (∀ u, Ext (k u) (k' u)) → Ext ((spec.query t : OracleComp spec _) >>= k)
        ((spec.query t : OracleComp spec _) >>= k')

lemma Ext.refl {α : Type} (p : OracleComp spec α) : Ext p p := by
  induction p using OracleComp.inductionOn with
  | pure x => simpa using Ext.leaf (spec := spec) x (pure ())
  | query_bind t k ih => exact Ext.queryBind t k k ih

lemma Ext.bind_congr {α γ : Type} (m : OracleComp spec γ) {h h' : γ → OracleComp spec α}
    (hh : ∀ z, Ext (h z) (h' z)) : Ext (m >>= h) (m >>= h') := by
  induction m using OracleComp.inductionOn with
  | pure z => simpa using hh z
  | query_bind t k ih =>
    simp only [bind_assoc]
    exact Ext.queryBind t _ _ ih

/-- A synchronized coupling of `p` and `q` whose outputs satisfy `R`, where `p` may stop early
(the queries `q` makes afterwards are discarded on `p`'s side). -/
def Rel {α β : Type} (p : OracleComp spec α) (q : OracleComp spec β) (R : α → β → Prop) : Prop :=
  ∃ J : OracleComp spec {z : α × β // R z.1 z.2},
    Ext p ((fun z => z.1.1) <$> J) ∧ (fun z => z.1.2) <$> J = q

lemma Rel.pure_left {α β : Type} {R : α → β → Prop} (x : α) (q : OracleComp spec β)
    (h : ∀ b, R x b) : Rel (pure x) q R := by
  refine ⟨(fun b => ⟨(x, b), h b⟩) <$> q, ?_, ?_⟩
  · rw [Functor.map_map]; exact Ext.leaf x q
  · rw [Functor.map_map]; simp

lemma Rel.of_map {α β γ : Type} {R : α → β → Prop} (X : OracleComp spec γ) (f : γ → α)
    (g : γ → β) (h : ∀ z, R (f z) (g z)) : Rel (f <$> X) (g <$> X) R := by
  refine ⟨(fun z => ⟨(f z, g z), h z⟩) <$> X, ?_, ?_⟩
  · rw [Functor.map_map]; exact Ext.refl _
  · rw [Functor.map_map]

lemma Rel.of_eq {α : Type} (X : OracleComp spec α) : Rel X X (· = ·) := by
  simpa using Rel.of_map (R := (· = ·)) X id id (fun _ => rfl)

lemma Rel.mono {α β : Type} {R R' : α → β → Prop} {p : OracleComp spec α} {q : OracleComp spec β}
    (h : Rel p q R) (hR : ∀ a b, R a b → R' a b) : Rel p q R' := by
  obtain ⟨J, h1, h2⟩ := h
  refine ⟨(fun z => ⟨z.1, hR _ _ z.2⟩) <$> J, ?_, ?_⟩
  · rw [Functor.map_map]; exact h1
  · rw [Functor.map_map]; exact h2

/-- Sequential composition, where the first stage is an exact (non-truncated) coupling. -/
lemma Rel.bind {α β α' β' : Type} {R : α → β → Prop} {R' : α' → β' → Prop}
    (J : OracleComp spec {z : α × β // R z.1 z.2})
    {f : α → OracleComp spec α'} {g : β → OracleComp spec β'}
    (hfg : ∀ a b, R a b → Rel (f a) (g b) R') :
    Rel (((fun z => z.1.1) <$> J) >>= f) (((fun z => z.1.2) <$> J) >>= g) R' := by
  choose K hK1 hK2 using hfg
  refine ⟨J >>= fun z => K z.1.1 z.1.2 z.2, ?_, ?_⟩
  · rw [map_bind, bind_map_left]
    exact Ext.bind_congr J fun z => hK1 _ _ z.2
  · rw [map_bind, bind_map_left]
    exact bind_congr fun z => hK2 _ _ z.2

lemma Rel.bind_eq {α α' β' : Type} {R' : α' → β' → Prop}
    (X : OracleComp spec α) {f : α → OracleComp spec α'} {g : α → OracleComp spec β'}
    (hfg : ∀ a, Rel (f a) (g a) R') : Rel (X >>= f) (X >>= g) R' := by
  have := Rel.bind (R := (· = ·)) ((fun a => ⟨(a, a), rfl⟩) <$> X) (f := f) (g := g)
    (fun a b h => by subst h; exact hfg a)
  simpa [Functor.map_map] using this

lemma Rel.bind_eq_of_support {α α' β' : Type} {R' : α' → β' → Prop}
    (X : OracleComp spec α) {f : α → OracleComp spec α'} {g : α → OracleComp spec β'}
    (hfg : ∀ a ∈ support X, Rel (f a) (g a) R') : Rel (X >>= f) (X >>= g) R' := by
  induction X using OracleComp.inductionOn with
  | pure x => simpa using hfg x (by simp)
  | query_bind t k ih =>
    simp only [bind_assoc]
    exact Rel.bind_eq _ fun u => ih u fun a ha => hfg a (by
      simp only [support_bind, Set.mem_iUnion]
      exact ⟨u, by simp, ha⟩)

variable {σ : Type}

lemma Ext.probEvent_eq (impl : QueryImpl spec (StateT σ ProbComp)) {α : Type}
    {p p' : OracleComp spec α} (h : Ext p p') (E : α → Prop) (s : σ) :
    Pr[E | (simulateQ impl p).run' s] = Pr[E | (simulateQ impl p').run' s] := by
  induction h generalizing s with
  | leaf x q =>
    rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map]
    simp only [simulateQ_pure, StateT.run_pure, map_pure]
    rw [probEvent_map_const]
    simp
  | queryBind t k k' _ ih =>
    simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
    refine probEvent_bind_congr' _ _ fun z => ?_
    have := ih z.1 z.2
    simpa [StateT.run'_eq] using this

lemma Rel.probEvent_le (impl : QueryImpl spec (StateT σ ProbComp)) {α β : Type}
    {R : α → β → Prop} {p : OracleComp spec α} {q : OracleComp spec β} (h : Rel p q R)
    (E₁ : α → Prop) (E₂ : β → Prop) (hE : ∀ a b, R a b → E₁ a → E₂ b) (s : σ) :
    Pr[E₁ | (simulateQ impl p).run' s] ≤ Pr[E₂ | (simulateQ impl q).run' s] := by
  obtain ⟨J, h1, h2⟩ := h
  rw [h1.probEvent_eq impl E₁ s, ← h2]
  simp only [simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map, probEvent_map]
  exact probEvent_mono fun z _ hz => hE _ _ z.1.2 hz

end coupling

section world

variable {ι ι' : Type} {R : Type}

/-- Rename hash inputs in the world `unifSpec + (ι →ₒ R)`, forwarding uniform sampling. -/
def relabelWImpl (f : ι → ι') :
    QueryImpl (unifSpec + (ι →ₒ R)) (OracleComp (unifSpec + (ι' →ₒ R))) :=
  QueryImpl.add
    (fun n => ((unifSpec + (ι' →ₒ R)).query (.inl n) : OracleComp (unifSpec + (ι' →ₒ R)) _))
    (fun t => ((unifSpec + (ι' →ₒ R)).query (.inr (f t)) : OracleComp (unifSpec + (ι' →ₒ R)) _))

/-- Rename hash inputs in the world `unifSpec + (ι →ₒ R)`. -/
def relabelW (f : ι → ι') {α : Type} (oa : OracleComp (unifSpec + (ι →ₒ R)) α) :
    OracleComp (unifSpec + (ι' →ₒ R)) α :=
  simulateQ (relabelWImpl f) oa

@[simp] lemma relabelW_pure (f : ι → ι') {α : Type} (x : α) :
    relabelW (R := R) f (pure x) = pure x := rfl

@[simp] lemma relabelW_bind (f : ι → ι') {α β : Type} (oa : OracleComp (unifSpec + (ι →ₒ R)) α)
    (ob : α → OracleComp (unifSpec + (ι →ₒ R)) β) :
    relabelW f (oa >>= ob) = relabelW f oa >>= fun x => relabelW f (ob x) := by
  simp [relabelW]

@[simp] lemma relabelW_map (f : ι → ι') {α β : Type} (oa : OracleComp (unifSpec + (ι →ₒ R)) α)
    (g : α → β) : relabelW f (g <$> oa) = g <$> relabelW f oa := by
  simp [relabelW]

@[simp] lemma relabelW_ite (f : ι → ι') {α : Type} (p : Prop) [Decidable p]
    (oa ob : OracleComp (unifSpec + (ι →ₒ R)) α) :
    relabelW f (if p then oa else ob) = if p then relabelW f oa else relabelW f ob := by
  split_ifs <;> rfl

@[simp] lemma relabelW_liftM_hash (f : ι → ι') {α : Type} (Y : OracleComp (ι →ₒ R) α) :
    relabelW f (liftM Y : OracleComp (unifSpec + (ι →ₒ R)) α) =
      (liftM (relabel f Y) : OracleComp (unifSpec + (ι' →ₒ R)) α) := by
  induction Y using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [liftM_bind, relabelW_bind, relabel_bind, ih, relabel_query]
    congr 1

@[simp] lemma relabelW_liftM_unif (f : ι → ι') {α : Type} (p : ProbComp α) :
    relabelW (R := R) f (liftM p : OracleComp (unifSpec + (ι →ₒ R)) α) =
      (liftM p : OracleComp (unifSpec + (ι' →ₒ R)) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [liftM_bind, relabelW_bind, ih]
    congr 1

@[simp] lemma relabelW_query_hash (f : ι → ι') (t : ι) :
    relabelW f (liftM ((ι →ₒ R).query t) : OracleComp (unifSpec + (ι →ₒ R)) R) =
      (liftM ((ι' →ₒ R).query (f t)) : OracleComp (unifSpec + (ι' →ₒ R)) R) := by
  rfl

@[simp] lemma relabelW_query_unif (f : ι → ι') (n : ℕ) :
    relabelW (R := R) f (liftM (unifSpec.query n) : OracleComp (unifSpec + (ι →ₒ R)) _) =
      (liftM (unifSpec.query n) : OracleComp (unifSpec + (ι' →ₒ R)) _) := by
  rfl

lemma countFrom_liftM_unif (cost : (unifSpec + (ι →ₒ R)).Domain → ℕ) (h0 : ∀ n, cost (.inl n) = 0)
    {α : Type} (p : ProbComp α) (c : ℕ) :
    countFrom cost (liftM p : OracleComp (unifSpec + (ι →ₒ R)) α) c =
      (fun x => (x, c)) <$> (liftM p : OracleComp (unifSpec + (ι →ₒ R)) α) := by
  induction p using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [liftM_bind, map_bind]
    have e : (liftM (liftM (unifSpec.query t) : ProbComp _) : OracleComp (unifSpec + (ι →ₒ R)) _) =
        ((unifSpec + (ι →ₒ R)).query (.inl t) : OracleComp (unifSpec + (ι →ₒ R)) _) := rfl
    rw [e, countFrom_query_bind, h0, Nat.add_zero]
    exact bind_congr fun u => ih u

lemma countFrom_liftM_hash (cost : (unifSpec + (ι →ₒ R)).Domain → ℕ) (h1 : ∀ t, cost (.inr t) = 1)
    {α : Type} (Y : OracleComp (ι →ₒ R) α) (c : ℕ) :
    countFrom cost (liftM Y : OracleComp (unifSpec + (ι →ₒ R)) α) c =
      (liftM (countFrom (fun _ => 1) Y c) : OracleComp (unifSpec + (ι →ₒ R)) _) := by
  induction Y using OracleComp.inductionOn generalizing c with
  | pure x => rfl
  | query_bind t k ih =>
    simp only [liftM_bind]
    have e : (liftM ((ι →ₒ R).query t : OracleComp (ι →ₒ R) _) :
        OracleComp (unifSpec + (ι →ₒ R)) _) =
        ((unifSpec + (ι →ₒ R)).query (.inr t) : OracleComp (unifSpec + (ι →ₒ R)) _) := rfl
    rw [e, countFrom_query_bind, h1, countFrom_query_bind, liftM_bind, e]
    exact bind_congr fun u => ih u _

variable [DecidableEq ι] [DecidableEq ι'] [SampleableType R]

/-- Uniform sampling forwarded, hash queries answered by the lazy random oracle. -/
noncomputable abbrev roImpl (ι R : Type) [DecidableEq ι] [SampleableType R] :
    QueryImpl (unifSpec + (ι →ₒ R)) (StateT (QueryCache (ι →ₒ R)) ProbComp) :=
  unifFwdImpl (ι →ₒ R) + (randomOracle : QueryImpl (ι →ₒ R) (StateT (QueryCache (ι →ₒ R)) ProbComp))

omit [DecidableEq ι'] in
lemma roImpl_inl_run (n : ℕ) (c : QueryCache (ι →ₒ R)) :
    (roImpl ι R (.inl n)).run c = (fun u => (u, c)) <$> (unifSpec.query n : ProbComp _) := by
  simp [unifFwdImpl]

omit [DecidableEq ι'] in
lemma roImpl_inr (x : ι) : roImpl ι R (.inr x) = randomOracle x := rfl

/-- **Lazy random oracle relabelling.** Running a computation against the lazy random oracle on
`ι'` equals running its relabelling by an injective `enc : ι' → ι` against the lazy random
oracle on `ι`, from related caches. -/
theorem run'_relabelW (enc : ι' → ι) (henc : Function.Injective enc) {α : Type}
    (P : OracleComp (unifSpec + (ι' →ₒ R)) α) (cO : QueryCache (ι' →ₒ R))
    (cA : QueryCache (ι →ₒ R)) (hc : ∀ x, cO x = cA (enc x)) :
    (simulateQ (roImpl ι' R) P).run' cO = (simulateQ (roImpl ι R) (relabelW enc P)).run' cA := by
  induction P using OracleComp.inductionOn generalizing cO cA with
  | pure x => rfl
  | query_bind t k ih =>
    rcases t with n | x
    · simp only [relabelW, simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
      have h1 : relabelWImpl (R := R) enc (.inl n) =
          ((unifSpec + (ι →ₒ R)).query (.inl n) : OracleComp (unifSpec + (ι →ₒ R)) _) := rfl
      rw [h1, simulateQ_spec_query, roImpl_inl_run, roImpl_inl_run, bind_map_left, bind_map_left]
      refine bind_congr fun u => ?_
      have := ih u cO cA hc
      simpa [relabelW, StateT.run'_eq] using this
    · simp only [relabelW, simulateQ_bind, simulateQ_spec_query, StateT.run'_eq, StateT.run_bind, map_bind]
      have h1 : relabelWImpl (R := R) enc (.inr x) =
          ((unifSpec + (ι →ₒ R)).query (.inr (enc x)) : OracleComp (unifSpec + (ι →ₒ R)) _) := rfl
      rw [h1, simulateQ_spec_query, roImpl_inr, roImpl_inr, randomOracle.run_eq,
        randomOracle.run_eq]
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
        simpa [relabelW, StateT.run'_eq] using this
      · subst hx
        simp only [pure_bind]
        rename_i u
        have := ih u cO cA hc
        simpa [relabelW, StateT.run'_eq] using this

end world

section writer

variable {ι : Type} {spec : OracleSpec.{0,0} ι} {σ : Type}

/-- Additive-writer cost instrumentation of a stateful handler equals explicit counting in the
program followed by the handler. -/
theorem withAddCost_run_eq_countFrom (impl : QueryImpl spec (StateT σ ProbComp))
    (cost : ι → ℕ) {α : Type} (G : OracleComp spec α) (n : ℕ) (s : σ) :
    (fun p => ((p.1.1, n + Multiplicative.toAdd p.1.2), p.2)) <$>
        (simulateQ (impl.withAddCost cost) G).run.run s =
      (simulateQ impl (countFrom cost G n)).run s := by
  induction G using OracleComp.inductionOn generalizing n s with
  | pure x => simp
  | query_bind t k ih =>
    rw [countFrom_query_bind]
    simp only [simulateQ_bind, simulateQ_spec_query, QueryImpl.withAddCost_apply]
    simp [WriterT.run_bind, AddWriterT.run_addTell]
    refine bind_congr fun p => ?_
    rw [← ih p.1 (n + cost t) p.2]
    simp [Nat.add_assoc]

lemma probEvent_countFrom_eq (impl : QueryImpl spec (StateT σ ProbComp)) (cost : ι → ℕ)
    {α : Type} (G : OracleComp spec α) (s : σ) (E : α × ℕ → Prop) :
    Pr[E | (simulateQ impl (countFrom cost G 0)).run' s] =
      Pr[fun p => E (p.1, Multiplicative.toAdd p.2) |
        (simulateQ (impl.withAddCost cost) G).run.run' s] := by
  rw [StateT.run'_eq, ← withAddCost_run_eq_countFrom, StateT.run'_eq, Functor.map_map,
    probEvent_map, probEvent_map]
  congr 1
  funext p
  simp

end writer

end SigGolfCandidate.Bridge
