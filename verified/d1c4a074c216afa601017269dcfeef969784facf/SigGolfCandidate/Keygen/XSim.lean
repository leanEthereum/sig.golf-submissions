import SigGolfCandidate.Sign.Sim

/-!
# Exact refinement of oracle computations by machine runs (`XSim`)

`XSim image s k c n b oa Q` : from `s` the machine performs exactly the oracle queries of `oa`
(query for query), in exactly `k` steps (fuel) and `c` cycles, with exactly `n` HASH calls and
`b` compressions, independently of the oracle answers; the final state `t` satisfies `Q a t`
(`a` the value of `oa`). Formally, there is `oc` over `{(a, t) // Q a t}` with

* `Sign.countBoth oa = (·.1.1, n, b) <$> oc` (the joint call / compression counter);
* `execute (fuel + k) image s = oc >>= fun p => (·.charge c n b) <$> execute fuel image p.1.2`.

This is an exact-cost variant of `SigGolfCandidate.Sign.Sim` (which bounds the cycles); it fits
programs whose control flow does not depend on the answers, like `keygen`.
-/

namespace SigGolfCandidate.Keygen
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec SigGolfCandidate.Rv
  SigGolfCandidate.Ref SigGolfCandidate.Sign

def XSim {α : Type} (image : Image) (s : MachineState) (k c n b : Nat)
    (oa : OracleComp HashSpec α) (Q : α → MachineState → Prop) : Prop :=
  ∃ oc : OracleComp HashSpec {p : α × MachineState // Q p.1 p.2},
    (fun p => (p.1.1, n, b)) <$> oc = countBoth oa ∧
    ∀ fuel, Riscv.execute (fuel + k) image s =
      oc >>= fun p => (fun r => r.charge c n b) <$> Riscv.execute fuel image p.1.2

section
variable {α β : Type} {image : Image}

theorem XSim.val {n b : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} {oc : OracleComp HashSpec {p : α × MachineState // Q p.1 p.2}}
    (h : (fun p => (p.1.1, n, b)) <$> oc = countBoth oa) :
    (fun p => p.1.1) <$> oc = oa := by
  have := congrArg (fun x => Prod.fst <$> x) h
  simp only [Functor.map_map, fst_countBoth] at this
  exact this

theorem XSim.pure_steps {s t : MachineState} {k c : Nat} {a : α} {Q : α → MachineState → Prop}
    (h : Steps image s k c t) (hQ : Q a t) : XSim image s k c 0 0 (pure a) Q := by
  refine ⟨pure ⟨(a, t), hQ⟩, rfl, ?_⟩
  intro fuel
  rw [pure_bind, h.execute]

theorem XSim.pure {s : MachineState} {a : α} {Q : α → MachineState → Prop} (hQ : Q a s) :
    XSim image s 0 0 0 0 (pure a) Q :=
  XSim.pure_steps (Steps.refl s) hQ

theorem XSim.mono {s : MachineState} {k c n b : Nat} {oa : OracleComp HashSpec α}
    {Q Q' : α → MachineState → Prop} (h : XSim image s k c n b oa Q)
    (hQ : ∀ a t, Q a t → Q' a t) : XSim image s k c n b oa Q' := by
  obtain ⟨oc, h1, h3⟩ := h
  refine ⟨(fun p => ⟨p.1, hQ _ _ p.2⟩) <$> oc, ?_, ?_⟩
  · rw [Functor.map_map]; exact h1
  · intro fuel; rw [h3 fuel, bind_map_left]

theorem XSim.of_eq {s : MachineState} {k c n b k' c' n' b' : Nat} {oa ob : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} (h : XSim image s k c n b oa Q) (he : oa = ob)
    (hk : k = k') (hc : c = c') (hn : n = n') (hb : b = b') : XSim image s k' c' n' b' ob Q := by
  subst he hk hc hn hb; exact h

private theorem count_bind_aux {P₁ : α × MachineState → Prop}
    {P₂ : β × MachineState → Prop} (oc₁ : OracleComp HashSpec {p // P₁ p})
    (oc₂ : {p // P₁ p} → OracleComp HashSpec {q // P₂ q}) (f : α → OracleComp HashSpec β)
    (n₁ b₁ n₂ b₂ : Nat) (oa : OracleComp HashSpec α)
    (h₁ : (fun p => (p.1.1, n₁, b₁)) <$> oc₁ = countBoth oa)
    (h₂ : ∀ p, (fun q => (q.1.1, n₂, b₂)) <$> oc₂ p = countBoth (f p.1.1)) :
    (fun q => (q.1.1, n₁ + n₂, b₁ + b₂)) <$> (oc₁ >>= oc₂) = countBoth (oa >>= f) := by
  rw [countBoth_bind, ← h₁, bind_map_left, map_bind]
  congr 1; funext p
  rw [← h₂ p, Functor.map_map]

theorem XSim.bind {s : MachineState} {k₁ c₁ n₁ b₁ k₂ c₂ n₂ b₂ : Nat}
    {oa : OracleComp HashSpec α} {f : α → OracleComp HashSpec β}
    {Q₁ : α → MachineState → Prop} {Q₂ : β → MachineState → Prop}
    (h₁ : XSim image s k₁ c₁ n₁ b₁ oa Q₁)
    (h₂ : ∀ a t, Q₁ a t → XSim image t k₂ c₂ n₂ b₂ (f a) Q₂) :
    XSim image s (k₁ + k₂) (c₁ + c₂) (n₁ + n₂) (b₁ + b₂) (oa >>= f) Q₂ := by
  classical
  obtain ⟨oc₁, hc₁, he₁⟩ := h₁
  have h₂' : ∀ p : {p : α × MachineState // Q₁ p.1 p.2}, XSim image p.1.2 k₂ c₂ n₂ b₂ (f p.1.1) Q₂ :=
    fun p => h₂ _ _ p.2
  let oc₂ := fun p => Classical.choose (h₂' p)
  have spec := fun p => Classical.choose_spec (h₂' p)
  refine ⟨oc₁ >>= oc₂, count_bind_aux oc₁ oc₂ f n₁ b₁ n₂ b₂ oa hc₁ (fun p => (spec p).1), ?_⟩
  intro fuel
  rw [show fuel + (k₁ + k₂) = (fuel + k₂) + k₁ by omega, he₁, bind_assoc]
  congr 1; funext p
  rw [(spec p).2 fuel, map_bind]
  congr 1; funext q
  rw [Functor.map_map]
  congr 1; funext r
  rw [Execution.charge_charge]

theorem XSim.steps {s t : MachineState} {k c k' c' n b : Nat} {oa : OracleComp HashSpec α}
    {Q : α → MachineState → Prop} (h : Steps image s k c t) (h₂ : XSim image t k' c' n b oa Q) :
    XSim image s (k + k') (c + c') n b oa Q := by
  have := XSim.bind (XSim.pure_steps (Q := fun _ t' => t' = t) (a := ()) h rfl)
    (f := fun _ => oa) (fun _ t' ht => ht ▸ h₂)
  simpa using this

/-- One HASH `ECALL`. -/
theorem XSim.query {s : MachineState} {q : Query}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = q) :
    XSim image s 1 (8 * q.blocks) 1 q.blocks (liftM (HashSpec.query q) : OracleComp HashSpec _)
      (fun a t => t = writeHash s a) := by
  subst hq
  refine ⟨(fun a => ⟨(a, writeHash s a), rfl⟩) <$>
      (liftM (HashSpec.query (hashInput s)) : OracleComp HashSpec _), ?_, ?_⟩
  · rw [Functor.map_map, countBoth_query]
  · intro fuel
    rw [execute_hash fuel hf ht0 hv, bind_map_left]

/-- `hash16 x` followed by a continuation. -/
theorem XSim.hash16_bind {s : MachineState} {x : List Byte} {k c n b : Nat}
    {f : Val → OracleComp HashSpec β} {Q : β → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = pad64 x)
    (h : ∀ a, XSim image (writeHash s a) k c n b (f (answerBytes 16 a)) Q) :
    XSim image s (1 + k) (8 * (pad64 x).blocks + c) (1 + n) ((pad64 x).blocks + b)
      (Ref.hash16 x >>= f) Q := by
  have : Ref.hash16 x >>= f = (liftM (HashSpec.query (pad64 x)) : OracleComp HashSpec _) >>=
      fun a => f (answerBytes 16 a) := by
    simp only [Ref.hash16, H, bind_assoc, pure_bind]
  rw [this]
  exact XSim.bind (XSim.query hf ht0 hv hq) (fun a t ht => ht ▸ h a)

/-- `hash16 x` at the end. -/
theorem XSim.hash16 {s : MachineState} {x : List Byte} {k c n b : Nat}
    {Q : Val → MachineState → Prop}
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) (hq : hashInput s = pad64 x)
    (h : ∀ a, XSim image (writeHash s a) k c n b (Pure.pure (answerBytes 16 a)) Q) :
    XSim image s (1 + k) (8 * (pad64 x).blocks + c) (1 + n) ((pad64 x).blocks + b)
      (Ref.hash16 x) Q := by
  have := XSim.hash16_bind (f := Pure.pure) hf ht0 hv hq h
  rwa [bind_pure] at this

/-- Sum `f 0 + … + f (n-1)`. -/
def sumTo (f : Nat → Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_const (c n : Nat) : sumTo (fun _ => c) n = n * c := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => simp [sumTo, ih, Nat.succ_mul]

/-- Loop over `List.range' a n` with an invariant indexed by the number `j` of processed
elements and iteration costs depending on `j`. -/
theorem XSim.foldlM_range' {γ : Type} (a n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (K C N B : Nat → Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → XSim image t (K j) (C j) (N j) (B j) (f acc (a + j))
      (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    XSim image s (sumTo K n) (sumTo C n) (sumTo N n) (sumTo B n)
      ((List.range' a n).foldlM f init) (Inv n) := by
  induction n with
  | zero => simpa [sumTo] using XSim.pure (image := image) h0
  | succ n ih =>
    rw [List.range'_concat, Nat.one_mul, List.foldlM_append]
    have := XSim.bind (ih (fun j hj => hbody j (by omega))) (f := fun acc => [a + n].foldlM f acc)
      (Q₂ := Inv (n + 1)) (fun acc t ht => by
        simpa using hbody n (by omega) acc t ht)
    exact this

theorem XSim.foldlM_range {γ : Type} (n : Nat) (f : γ → Nat → OracleComp HashSpec γ) (init : γ)
    (Inv : Nat → γ → MachineState → Prop) (K C N B : Nat → Nat)
    (hbody : ∀ j < n, ∀ acc t, Inv j acc t → XSim image t (K j) (C j) (N j) (B j) (f acc j)
      (Inv (j + 1)))
    {s : MachineState} (h0 : Inv 0 init s) :
    XSim image s (sumTo K n) (sumTo C n) (sumTo N n) (sumTo B n)
      ((List.range n).foldlM f init) (Inv n) := by
  have := XSim.foldlM_range' 0 n f init Inv K C N B (fun j hj acc t h => by
    simpa using hbody j hj acc t h) h0
  rwa [List.range_eq_range'] 

end

/-- The counts of a refined computation are constant. -/
theorem XSim.count_eq {α : Type} {image : Image} {s : MachineState} {k c n b : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop} (h : XSim image s k c n b oa Q) :
    countWith (fun _ => 1) oa = (fun a => (a, n)) <$> oa ∧
      countWith Query.blocks oa = (fun a => (a, b)) <$> oa := by
  obtain ⟨oc, hc, _⟩ := h
  have hv := XSim.val hc
  refine ⟨?_, ?_⟩
  · rw [show countWith (fun _ => 1) oa = countCalls oa from rfl, ← countBoth_calls, ← hc, ← hv,
      Functor.map_map, Functor.map_map]
  · rw [show countWith Query.blocks oa = countBlocks oa from rfl, ← countBoth_blocks, ← hc, ← hv,
      Functor.map_map, Functor.map_map]

theorem XSim.countBoth_eq {α : Type} {image : Image} {s : MachineState} {k c n b : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop} (h : XSim image s k c n b oa Q) :
    countBoth oa = (fun a => (a, n, b)) <$> oa := by
  obtain ⟨oc, hc, _⟩ := h
  rw [← hc, ← XSim.val hc, Functor.map_map]

/-! ## Whole phases -/

/-- **A whole phase, exactly.** If the machine refines `oa` from the initial state in `k` steps
(`k < CYCLE_LIMIT`) and every final state is at a HALT `ECALL` with `a0 = 0` and output `F a`,
then `submission.run` returns `⟨some (F a), true, c + 1, n, b⟩` for the value `a` of `oa`. -/
theorem XSim.run_eq {α : Type} (submission : Submission) (phase : Phase)
    (input : Input submission.sizes phase)
    {s : MachineState} (hinit : initialState submission phase input = some s) {k c n b : Nat}
    {oa : OracleComp HashSpec α} {Q : α → MachineState → Prop}
    (hsim : XSim (submission.image phase) s k c n b oa Q) (hk : k < CYCLE_LIMIT)
    (F : α → Output submission.sizes phase)
    (hQ : ∀ a t, Q a t → fetch (submission.image phase) t = some (.base .ECALL) ∧
      t.getReg .x5 = 1 ∧ t.getReg .x10 = 0 ∧
      readOutput submission.sizes submission.layout phase t = F a) :
    submission.run phase input = (fun a => ⟨some (F a), true, c + 1, n, b⟩) <$> oa := by
  obtain ⟨oc, hc, he⟩ := hsim
  have e1 := he (CYCLE_LIMIT - k - 1 + 1)
  rw [show CYCLE_LIMIT - k - 1 + 1 + k = CYCLE_LIMIT by omega] at e1
  rw [Rv.run_eq submission phase input s hinit, e1, map_bind, ← XSim.val hc,
    Functor.map_map, map_eq_bind_pure_comp]
  refine congrArg (oc >>= ·) (funext fun p => ?_)
  obtain ⟨h1, h2, h3, h4⟩ := hQ _ _ p.2
  rw [execute_halt _ h1 h2, map_pure, map_pure]
  simp only [Function.comp, toRunResult, Execution.charge, h3, if_true, h4]
  rfl

end SigGolfCandidate.Keygen
