import SigGolfCandidate.Ref
import SigGolfCandidate.Rv

/-!
# Refinement of oracle computations by machine runs (`Sim`)

`Sim image s W oa Q` : running the organizer machine from `s` performs *exactly* the oracle
queries of the spec `oa` (query for query), and after them reaches a state `t` with `Q a t`,
where `a` is the value returned by `oa`; the machine part costs at most `W` cycles (and at most
`W` steps / fuel). Formally there is a computation `oc` over the outcomes
(`Out`: value, #calls, #blocks, steps, cycles, final state) such that

* projecting `oc` to `(value, calls, blocks)` gives `countBoth oa` (joint counter), and
* for every `fuel ≥ W`, `execute fuel image s` is `oc` followed by the rest of the execution
  from the outcome's state, charged with the outcome's costs.

Combinators: `Sim.pure`, `Sim.steps` (prefix a block of ordinary steps), `Sim.query` / `Sim.hash`
(one HASH `ECALL`), `Sim.bind`, `Sim.mono`, `Sim.foldlM_range` (loops), and
`Sim.run_eq` / `Sim.runWith` (a whole phase: refinement and termination).
-/

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.Rv
  SigGolfCandidate.Ref

/-! ## Joint call / compression counter -/

/-- Forward a query, counting one call and its blocks. -/
def countImpl2 : QueryImpl HashSpec (StateT (Nat × Nat) (OracleComp HashSpec)) :=
  fun q => do
    modify (fun p => (p.1 + 1, p.2 + Query.blocks q))
    liftM (HashSpec.query q)

/-- The result, the number of oracle calls and the number of compressions. -/
def countBoth {α : Type} (oa : OracleComp HashSpec α) : OracleComp HashSpec (α × Nat × Nat) :=
  (simulateQ countImpl2 oa).run (0, 0)

section count
variable {α β : Type}

theorem countImpl2_run (oa : OracleComp HashSpec α) (c b : Nat) :
    (simulateQ countImpl2 oa).run (c, b) =
      (fun p => (p.1, c + p.2.1, b + p.2.2)) <$> countBoth oa := by
  unfold countBoth
  induction oa using OracleComp.inductionOn generalizing c b with
  | pure a => simp
  | query_bind q oa ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, countImpl2]
    simp only [StateT.run_modify, pure_bind, map_bind]
    have hl : ∀ s, (liftM (OracleSpec.query q) : StateT (Nat × Nat) (OracleComp HashSpec) _).run s =
        (fun a => (a, s)) <$> (liftM (OracleSpec.query q) : OracleComp HashSpec _) := fun s => rfl
    simp only [hl, bind_map_left]
    congr 1; funext a
    rw [ih a (c + 1) (b + Query.blocks q), ih a (0 + 1) (0 + Query.blocks q), Functor.map_map]
    congr 1; funext p
    simp only [Prod.mk.injEq, true_and]; omega

@[simp] theorem countBoth_pure (a : α) :
    countBoth (pure a : OracleComp HashSpec α) = pure (a, 0, 0) := rfl

theorem countBoth_bind (oa : OracleComp HashSpec α) (f : α → OracleComp HashSpec β) :
    countBoth (oa >>= f) =
      countBoth oa >>= fun p => (fun r => (r.1, p.2.1 + r.2.1, p.2.2 + r.2.2)) <$> countBoth (f p.1) := by
  conv_lhs => unfold countBoth
  rw [simulateQ_bind, StateT.run_bind]
  exact congrArg _ (funext fun p => countImpl2_run (f p.1) p.2.1 p.2.2)

@[simp] theorem countBoth_query (q : Query) :
    countBoth (liftM (HashSpec.query q) : OracleComp HashSpec _) =
      (fun a => (a, 1, q.blocks)) <$> (liftM (HashSpec.query q) : OracleComp HashSpec _) := by
  unfold countBoth
  rw [simulateQ_spec_query]
  simp only [countImpl2, StateT.run_bind, StateT.run_modify, pure_bind, Nat.zero_add]
  rfl

@[simp] theorem countBoth_H (x : List Byte) :
    countBoth (H x) = (fun a => (a, 1, (pad64 x).blocks)) <$> H x := by
  rw [← blocks_fmt]; exact countBoth_query (fmt x)

/-- The joint counter projects to `countCalls`. -/
theorem countBoth_calls (oa : OracleComp HashSpec α) :
    (fun p => (p.1, p.2.1)) <$> countBoth oa = countCalls oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countBoth_bind, countCalls_bind, countBoth_query, countCalls_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    rw [← ih a, Functor.map_map]

/-- The joint counter projects to `countBlocks`. -/
theorem countBoth_blocks (oa : OracleComp HashSpec α) :
    (fun p => (p.1, p.2.2)) <$> countBoth oa = countBlocks oa := by
  induction oa using OracleComp.inductionOn with
  | pure a => rfl
  | query_bind q oa ih =>
    rw [countBoth_bind, countBlocks, countWith_bind, countBoth_query, countWith_query]
    simp only [map_bind, bind_map_left, Functor.map_map]
    congr 1; funext a
    rw [show countWith Query.blocks (oa a) = countBlocks (oa a) from rfl, ← ih a, Functor.map_map]

@[simp] theorem fst_countBoth (oa : OracleComp HashSpec α) : Prod.fst <$> countBoth oa = oa := by
  have := congrArg (fun x => Prod.fst <$> x) (countBoth_calls oa)
  simp only [Functor.map_map] at this
  rw [this, fst_countCalls]

end count

/-! ## `Sim` -/

/-- An outcome of a machine segment: spec value, calls, blocks, steps (fuel), cycles, state. -/
structure Out (α : Type) where
  val : α
  calls : Nat
  blocks : Nat
  steps : Nat
  cycles : Nat
  st : MachineState

/-- Admissible outcomes: steps ≤ cycles ≤ W and the postcondition. -/
def Out.Good {α : Type} (W : Nat) (Q : α → MachineState → Prop) (o : Out α) : Prop :=
  o.steps ≤ o.cycles ∧ o.cycles ≤ W ∧ Q o.val o.st

/-- `Sim image s W oa Q`: see the module docstring. -/
def Sim {α : Type} (image : Image) (s : MachineState) (W : Nat) (oa : OracleComp HashSpec α)
    (Q : α → MachineState → Prop) : Prop :=
  ∃ oc : OracleComp HashSpec {o : Out α // o.Good W Q},
    (fun o => (o.1.val, o.1.calls, o.1.blocks)) <$> oc = countBoth oa ∧
    ∀ fuel, W ≤ fuel → Riscv.execute fuel image s =
      oc >>= fun o => (fun r => r.charge o.1.cycles o.1.calls o.1.blocks) <$>
        Riscv.execute (fuel - o.1.steps) image o.1.st

theorem steps_le_cycles {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) : k ≤ c := by
  induction h with
  | refl => exact le_refl _
  | @step s t u i k c _ _ _ ih =>
    have : 1 ≤ instructionCycles i := by
      unfold instructionCycles; split <;> omega
    omega

section sim
variable {α β : Type} {image : Image}

/-- A block of ordinary steps returning a pure value. -/
theorem Sim.pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : Sim image s c (pure a) Q := by
  refine ⟨pure ⟨⟨a, 0, 0, k, c, t⟩, steps_le_cycles h, le_refl _, hQ⟩, rfl, ?_⟩
  intro fuel hf
  rw [pure_bind, h.execute_le (le_trans (steps_le_cycles h) hf)]

theorem Sim.pure {s : MachineState} {a : α} {Q : α → MachineState → Prop} (hQ : Q a s) :
    Sim image s 0 (pure a) Q :=
  Sim.pure_steps (Steps.refl s) hQ

theorem Sim.mono {s : MachineState} {W W' : Nat} {oa : OracleComp HashSpec α}
    {Q Q' : α → MachineState → Prop} (h : Sim image s W oa Q) (hW : W ≤ W')
    (hQ : ∀ a t, Q a t → Q' a t) : Sim image s W' oa Q' := by
  obtain ⟨oc, hp, hf⟩ := h
  refine ⟨(fun o => ⟨o.1, o.2.1, le_trans o.2.2.1 hW, hQ _ _ o.2.2.2⟩) <$> oc, ?_, ?_⟩
  · rw [Functor.map_map]; exact hp
  · intro fuel hfuel
    rw [hf fuel (le_trans hW hfuel), bind_map_left]

theorem Sim.of_eq {s : MachineState} {W : Nat} {oa ob : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} (h : Sim image s W oa Q) (he : oa = ob) : Sim image s W ob Q :=
  he ▸ h

theorem Sim.bind {s : MachineState} {W₁ W₂ : Nat} {oa : OracleComp HashSpec α}
    {f : α → OracleComp HashSpec β} {Q₁ : α → MachineState → Prop}
    {Q₂ : β → MachineState → Prop} (h₁ : Sim image s W₁ oa Q₁)
    (h₂ : ∀ a t, Q₁ a t → Sim image t W₂ (f a) Q₂) : Sim image s (W₁ + W₂) (oa >>= f) Q₂ := by
  classical
  obtain ⟨oc₁, hp₁, hf₁⟩ := h₁
  have h₂' : ∀ o : {o : Out α // o.Good W₁ Q₁}, Sim image o.1.st W₂ (f o.1.val) Q₂ :=
    fun o => h₂ _ _ o.2.2.2
  let oc₂ := fun o => Classical.choose (h₂' o)
  have hp₂ := fun o => (Classical.choose_spec (h₂' o)).1
  have hf₂ := fun o => (Classical.choose_spec (h₂' o)).2
  let comb : (o₁ : {o : Out α // o.Good W₁ Q₁}) → {o : Out β // o.Good W₂ Q₂} →
      {o : Out β // o.Good (W₁ + W₂) Q₂} := fun o₁ o₂ =>
    ⟨⟨o₂.1.val, o₁.1.calls + o₂.1.calls, o₁.1.blocks + o₂.1.blocks, o₁.1.steps + o₂.1.steps,
      o₁.1.cycles + o₂.1.cycles, o₂.1.st⟩,
      by have := o₁.2; have := o₂.2; simp only [Out.Good] at *; omega,
      by have := o₁.2; have := o₂.2; simp only [Out.Good] at *; omega, o₂.2.2.2⟩
  refine ⟨oc₁ >>= fun o₁ => comb o₁ <$> oc₂ o₁, ?_, ?_⟩
  · rw [countBoth_bind, ← hp₁, map_bind, bind_map_left]
    congr 1; funext o₁
    rw [← hp₂ o₁, Functor.map_map, Functor.map_map]
  · intro fuel hfuel
    rw [hf₁ fuel (le_trans (Nat.le_add_right _ _) hfuel), bind_assoc]
    congr 1; funext o₁
    have hs : o₁.1.steps ≤ W₁ := le_trans o₁.2.1 o₁.2.2.1
    rw [hf₂ o₁ (fuel - o₁.1.steps) (by omega), map_bind, bind_map_left]
    congr 1; funext o₂
    simp only [Functor.map_map, Execution.charge_charge, comb]
    rw [Nat.sub_sub]

/-- Prefix a block of ordinary steps. -/
theorem Sim.steps {s t : MachineState} {k c W : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} (h : Steps image s k c t) (h₂ : Sim image t W oa Q) :
    Sim image s (c + W) oa Q := by
  have := Sim.bind (Sim.pure_steps (Q := fun _ t' => t' = t) (a := ()) h rfl)
    (f := fun _ => oa) (fun _ t' ht => ht ▸ h₂)
  simpa using this

/-- One HASH `ECALL`. -/
theorem Sim.query {s : MachineState} {q : Query}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = q) :
    Sim image s (8 * q.blocks) (liftM (HashSpec.query q) : OracleComp HashSpec _)
      (fun a t => t = writeHash s a) := by
  subst hq
  have hb : 1 ≤ (hashInput s).blocks := by unfold Query.blocks; omega
  refine ⟨(fun a => ⟨⟨a, 1, (hashInput s).blocks, 1, 8 * (hashInput s).blocks, writeHash s a⟩,
      by show 1 ≤ 8 * _; omega, le_refl _, rfl⟩) <$> (liftM (HashSpec.query (hashInput s)) : OracleComp HashSpec _),
      ?_, ?_⟩
  · rw [Functor.map_map, countBoth_query]
  · intro fuel hfuel
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    rw [execute_hash f hf ht0 hv, bind_map_left]
    rfl

/-- One HASH `ECALL` followed by a continuation. -/
theorem Sim.query_bind {s : MachineState} {q : Query} {W : Nat}
    {f : BitVec 256 → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = q)
    (h : ∀ a, Sim image (writeHash s a) W (f a) Q) :
    Sim image s (8 * q.blocks + W) ((liftM (HashSpec.query q) : OracleComp HashSpec _) >>= f) Q :=
  Sim.bind (Sim.query hf ht0 hv hq) (fun a _ ht => ht ▸ h a)

/-- `hash16 x` (one HASH `ECALL` on `fmt x`) followed by a continuation. -/
theorem Sim.hash16_bindF {s : MachineState} {x : List Byte} {W : Nat}
    {f : Val → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = fmt x)
    (h : ∀ a, Sim image (writeHash s a) W (f (answerBytes 16 a)) Q) :
    Sim image s (8 * (pad64 x).blocks + W) (hash16 x >>= f) Q := by
  have : hash16 x >>= f = (liftM (HashSpec.query (fmt x)) : OracleComp HashSpec _) >>=
      fun a => f (answerBytes 16 a) := by
    simp only [hash16, H, bind_assoc, pure_bind]
  rw [this, ← blocks_fmt]
  exact Sim.query_bind hf ht0 hv hq h

/-- `hash16 x` for a zero-padded input (`fmt x = pad64 x`) followed by a continuation. -/
theorem Sim.hash16_bind {s : MachineState} {x : List Byte} {W : Nat}
    {f : Val → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = pad64 x) (hx : fmt x = pad64 x)
    (h : ∀ a, Sim image (writeHash s a) W (f (answerBytes 16 a)) Q) :
    Sim image s (8 * (pad64 x).blocks + W) (hash16 x >>= f) Q :=
  Sim.hash16_bindF hf ht0 hv (hq.trans hx.symm) h

/-- `hash16 x` at the end. -/
theorem Sim.hash16 {s : MachineState} {x : List Byte} {W : Nat} {Q : Val → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = pad64 x) (hx : fmt x = pad64 x)
    (h : ∀ a, Sim image (writeHash s a) W (Pure.pure (answerBytes 16 a)) Q) :
    Sim image s (8 * (pad64 x).blocks + W) (Ref.hash16 x) Q := by
  have := Sim.hash16_bind (f := Pure.pure) hf ht0 hv hq hx h
  rwa [bind_pure] at this

/-- Loop over `List.range n` with an invariant indexed by the number of processed elements. -/
theorem Sim.foldlM_range {γ : Type} (n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (W : Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → Sim image t W (f acc j) (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    Sim image s (n * W) ((List.range n).foldlM f init) (Inv n) := by
  induction n with
  | zero => simpa using Sim.pure (image := image) h0
  | succ n ih =>
    rw [List.range_succ, List.foldlM_append]
    have := Sim.bind (ih (fun j hj => hbody j (by omega))) (f := fun acc => [n].foldlM f acc)
      (W₂ := W) (Q₂ := Inv (n + 1)) (fun acc t ht => by
        simpa using hbody n (by omega) acc t ht)
    refine this.mono ?_ (fun _ _ h => h)
    rw [Nat.succ_mul]

/-- Loop over `List.range' a n` (`a, …, a+n-1`); the invariant is indexed by the number `j` of
processed elements. -/
theorem Sim.foldlM_range' {γ : Type} (a n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (W : Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → Sim image t W (f acc (a + j)) (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    Sim image s (n * W) ((List.range' a n).foldlM f init) (Inv n) := by
  induction n with
  | zero => simpa using Sim.pure (image := image) h0
  | succ n ih =>
    rw [List.range'_concat, Nat.one_mul, List.foldlM_append]
    have := Sim.bind (ih (fun j hj => hbody j (by omega))) (f := fun acc => [a + n].foldlM f acc)
      (W₂ := W) (Q₂ := Inv (n + 1)) (fun acc t ht => by
        simpa using hbody n (by omega) acc t ht)
    refine this.mono ?_ (fun _ _ h => h)
    rw [Nat.succ_mul]

end sim

/-! ## Whole phases -/

section run
variable {α : Type}

/-- **Refinement of a whole phase.** If the machine refines `oa` from the initial state and every
final state is at a HALT `ECALL` whose output (`a0 = 0`: success with `readOutput`) is `F a`, then
`submission.run` has the value / call / compression distribution of `F <$> countBoth oa`. -/
theorem Sim.run_eq (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {W : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q) (hW : W < CYCLE_LIMIT)
    (F : α → Option (Output submission.sizes phase))
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧
      F a = if t.getReg .x10 = 0 then some (readOutput submission.sizes submission.layout phase t)
        else none) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run phase input =
      (fun p => (F p.1, p.2.1, p.2.2)) <$> countBoth oa := by
  obtain ⟨oc, hp, hf⟩ := hsim
  rw [Rv.run_eq submission phase input s hinit, hf CYCLE_LIMIT (le_of_lt hW), ← hp,
    Functor.map_map]
  simp only [map_bind, Functor.map_map]
  rw [map_eq_bind_pure_comp (x := oc)]
  congr 1; funext o
  obtain ⟨h1, h2, h3⟩ := hQ _ _ o.2.2.2
  have hs : o.1.steps < CYCLE_LIMIT := lt_of_le_of_lt (le_trans o.2.1 o.2.2.1) hW
  obtain ⟨f, hf'⟩ : ∃ f, CYCLE_LIMIT - o.1.steps = f + 1 := ⟨CYCLE_LIMIT - o.1.steps - 1, by omega⟩
  rw [hf', execute_halt f h1 h2]
  simp only [map_pure, Function.comp, toRunResult, Execution.charge, h3]
  congr 2
  split <;> simp_all

/-- `Sim.run_eq` including the `finished` flag (always `true`). -/
theorem Sim.run_eq_fin (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {W : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q) (hW : W < CYCLE_LIMIT)
    (F : α → Option (Output submission.sizes phase))
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧
      F a = if t.getReg .x10 = 0 then some (readOutput submission.sizes submission.layout phase t)
        else none) :
    (fun r => (r.value, r.finished, r.hashCalls, r.hashCompressions)) <$> submission.run phase input =
      (fun p => (F p.1, true, p.2.1, p.2.2)) <$> countBoth oa := by
  obtain ⟨oc, hp, hf⟩ := hsim
  rw [Rv.run_eq submission phase input s hinit, hf CYCLE_LIMIT (le_of_lt hW), ← hp,
    Functor.map_map]
  simp only [map_bind, Functor.map_map]
  rw [map_eq_bind_pure_comp (x := oc)]
  congr 1; funext o
  obtain ⟨h1, h2, h3⟩ := hQ _ _ o.2.2.2
  have hs : o.1.steps < CYCLE_LIMIT := lt_of_le_of_lt (le_trans o.2.1 o.2.2.1) hW
  obtain ⟨f, hf'⟩ : ∃ f, CYCLE_LIMIT - o.1.steps = f + 1 := ⟨CYCLE_LIMIT - o.1.steps - 1, by omega⟩
  rw [hf', execute_halt f h1 h2]
  simp only [map_pure, Function.comp, toRunResult, Execution.charge, h3]
  congr 2
  · split <;> simp_all
  · split <;> rfl

/-- **Termination of a whole phase** under every fixed oracle: finished, and at most `W + 1`
cycles (`W + 1 < CYCLE_LIMIT`). -/
theorem Sim.runWith (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {W : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : Sim (submission.image phase) s W oa Q) (hW : W + 1 < CYCLE_LIMIT)
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧ t.getReg .x5 = 1)
    (hash : Hash) :
    (submission.runWith hash phase input).finished = true ∧
      (submission.runWith hash phase input).cycles ≤ W + 1 := by
  obtain ⟨oc, _, hf⟩ := hsim
  rw [runWith_eq submission hash phase input s hinit, hf CYCLE_LIMIT (by omega),
    evalWithAnswerFn_bind, evalWithAnswerFn_map]
  generalize evalWithAnswerFn hash oc = o
  obtain ⟨h1, h2⟩ := hQ _ _ o.2.2.2
  have hs : o.1.steps < CYCLE_LIMIT := by have := o.2.1; have := o.2.2.1; omega
  obtain ⟨f, hf'⟩ : ∃ f, CYCLE_LIMIT - o.1.steps = f + 1 := ⟨CYCLE_LIMIT - o.1.steps - 1, by omega⟩
  rw [hf', evalWith_halt hash f h1 h2]
  have := o.2.2.1
  simp only [toRunResult, Execution.charge]
  constructor
  · split <;> rfl
  · omega

end run

end SigGolfCandidate.Sign
