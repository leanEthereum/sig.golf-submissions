import SigGolf

/-!
# Generic execution lemmas for the organizer interpreter

`Steps image s k c t` : from `s`, the organizer machine performs `k` ordinary (non-`ECALL`)
successful steps with total cycle cost `c` and reaches `t`.

Main laws:
* `Steps.execute`      : `execute (fuel + k) image s = (·.charge c 0 0) <$> execute fuel image t`
* `execute_hash`       : one HASH `ECALL`
* `execute_halt`       : one HALT `ECALL`
* `evalWithAnswerFn` versions of all of the above (`Steps.evalWith`, `evalWith_hash`, ...)
* `run_eq` / `runWith_eq` : `Submission.run` / `runWith` in terms of `execute` from `initialState`.
-/

namespace SigGolfCandidate.Rv
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp OracleSpec

/-- `k` ordinary steps with total cycle count `c`. -/
inductive Steps (image : Image) : MachineState → Nat → Nat → MachineState → Prop where
  | refl (s : MachineState) : Steps image s 0 0 s
  | step {s t u : MachineState} {i : Instruction} {k c : Nat}
      (hf : fetch image s = some i) (hs : ordinaryStep s i = some t)
      (tail : Steps image t k c u) :
      Steps image s (k + 1) (instructionCycles i + c) u

theorem Steps.of_eq {image : Image} {s t : MachineState} {k c k' c' : Nat}
    (h : Steps image s k c t) (hk : k = k') (hc : c = c') : Steps image s k' c' t := by
  subst hk hc; exact h

theorem Steps.trans {image : Image} {s t u : MachineState} {k₁ c₁ k₂ c₂ : Nat}
    (h₁ : Steps image s k₁ c₁ t) (h₂ : Steps image t k₂ c₂ u) :
    Steps image s (k₁ + k₂) (c₁ + c₂) u := by
  induction h₁ with
  | refl => simpa using h₂
  | @step s t u i k c hf hs _ ih =>
    have := Steps.step hf hs (ih h₂)
    exact Steps.of_eq this (by omega) (by omega)

@[simp] theorem Execution.charge_zero (e : Execution) : e.charge 0 0 0 = e := by
  cases e; simp [Execution.charge]

@[simp] theorem Execution.charge_charge (e : Execution) (a b c a' b' c' : Nat) :
    (e.charge a b c).charge a' b' c' = e.charge (a' + a) (b' + b) (c' + c) := by
  cases e; simp [Execution.charge, Nat.add_assoc]

@[simp] theorem Execution.charge_exit (e : Execution) (a b c : Nat) : (e.charge a b c).exit = e.exit := rfl
@[simp] theorem Execution.charge_state (e : Execution) (a b c : Nat) : (e.charge a b c).state = e.state := rfl
@[simp] theorem Execution.charge_cycles (e : Execution) (a b c : Nat) :
    (e.charge a b c).cycles = a + e.cycles := rfl
@[simp] theorem Execution.charge_hashCalls (e : Execution) (a b c : Nat) :
    (e.charge a b c).hashCalls = b + e.hashCalls := rfl
@[simp] theorem Execution.charge_hashCompressions (e : Execution) (a b c : Nat) :
    (e.charge a b c).hashCompressions = c + e.hashCompressions := rfl

theorem ordinaryStep_ne_ecall {s t : MachineState} {i : Instruction}
    (h : ordinaryStep s i = some t) : i ≠ .base .ECALL := by
  rintro rfl; simp [ordinaryStep] at h

/-- One ordinary step of `execute`. -/
theorem execute_ordinary {image : Image} {s t : MachineState} {i : Instruction} (fuel : Nat)
    (hf : fetch image s = some i) (hs : ordinaryStep s i = some t) :
    execute (fuel + 1) image s =
      (fun r => r.charge (instructionCycles i) 0 0) <$> execute fuel image t := by
  cases i with
  | base j =>
    have hne := ordinaryStep_ne_ecall hs
    cases j <;> first | exact absurd rfl hne | simp_all [execute]
  | word op rd rs1 rs2 => simp [execute, hf, hs]
  | sraiw rd rs sh => simp [execute, hf, hs]

/-- Composition law for a block of ordinary steps. -/
theorem Steps.execute {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) (fuel : Nat) :
    Riscv.execute (fuel + k) image s = (fun r => r.charge c 0 0) <$> Riscv.execute fuel image t := by
  induction h with
  | refl => simp
  | @step s t u i k c hf hs _ ih =>
    rw [← Nat.add_assoc, execute_ordinary _ hf hs, ih, Functor.map_map]
    simp [Nat.add_comm]

/-- Composition law with a fuel inequality. -/
theorem Steps.execute_le {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) {fuel : Nat} (hle : k ≤ fuel) :
    Riscv.execute fuel image s =
      (fun r => r.charge c 0 0) <$> Riscv.execute (fuel - k) image t := by
  have := h.execute (fuel - k)
  rwa [Nat.sub_add_cancel hle] at this

/-- The HASH system call (`t0 = 0`, valid arguments). -/
theorem execute_hash {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) :
    Riscv.execute (fuel + 1) image s = (do
      let a ← HashSpec.query (hashInput s)
      (fun r => r.charge (8 * (hashInput s).blocks) 1 (hashInput s).blocks) <$>
        Riscv.execute fuel image (writeHash s a)) := by
  simp [Riscv.execute, hf, ht0, hv, map_eq_bind_pure_comp]

/-- The HALT system call (`t0 = 1`). -/
theorem execute_halt {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 1) :
    Riscv.execute (fuel + 1) image s =
      pure ⟨if s.getReg .x10 = 0 then .success else .failure, s, 1, 0, 0⟩ := by
  simp [Riscv.execute, hf, ht0]

/-- `ECALL` with a selector other than HASH (with valid arguments) or HALT fails. -/
theorem execute_ecall_fail {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL))
    (hbad : ¬ (s.getReg .x5 = 0 ∧ hashArgumentsValid s = true)) (ht0 : s.getReg .x5 ≠ 1) :
    Riscv.execute (fuel + 1) image s = pure ⟨.failure, s, 1, 0, 0⟩ := by
  have hbad' : ¬ (s.getReg .x5 = 0#64 ∧ hashArgumentsValid s = true) := hbad
  have ht0' : ¬ s.getReg .x5 = 1#64 := ht0
  simp [Riscv.execute, hf]
  rw [if_neg hbad', if_neg ht0']

/-- Fetch failure. -/
theorem execute_fetch_none {image : Image} {s : MachineState} (fuel : Nat)
    (hf : fetch image s = none) :
    Riscv.execute (fuel + 1) image s = pure ⟨.failure, s, 0, 0, 0⟩ := by
  simp [Riscv.execute, hf]

/-! ## Fixed-oracle versions -/

theorem Steps.evalWith {image : Image} {s t : MachineState} {k c : Nat}
    (h : Steps image s k c t) (hash : Hash) (fuel : Nat) :
    evalWithAnswerFn hash (Riscv.execute (fuel + k) image s) =
      (evalWithAnswerFn hash (Riscv.execute fuel image t)).charge c 0 0 := by
  rw [h.execute, evalWithAnswerFn_map]

theorem evalWith_hash {image : Image} {s : MachineState} (hash : Hash) (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 0)
    (hv : hashArgumentsValid s = true) :
    evalWithAnswerFn hash (Riscv.execute (fuel + 1) image s) =
      (evalWithAnswerFn hash (Riscv.execute fuel image (writeHash s (hash (hashInput s))))).charge
        (8 * (hashInput s).blocks) 1 (hashInput s).blocks := by
  rw [execute_hash fuel hf ht0 hv, evalWithAnswerFn_bind, evalWithAnswerFn_map]
  have : evalWithAnswerFn hash (HashSpec.query (hashInput s) : OracleComp HashSpec _) =
      hash (hashInput s) := evalWithAnswerFn_query hash _
  rw [this]

theorem evalWith_halt {image : Image} {s : MachineState} (hash : Hash) (fuel : Nat)
    (hf : fetch image s = some (.base .ECALL)) (ht0 : s.getReg .x5 = 1) :
    evalWithAnswerFn hash (Riscv.execute (fuel + 1) image s) =
      ⟨if s.getReg .x10 = 0 then .success else .failure, s, 1, 0, 0⟩ := by
  rw [execute_halt fuel hf ht0]; rfl

/-! ## Submission-level lemmas -/

/-- The `RunResult` produced by `Submission.run` from a final `Execution`. -/
def toRunResult (submission : Submission) (phase : Phase) (e : Execution) :
    RunResult (Output submission.sizes phase) :=
  ⟨if e.exit = .success then
      some (readOutput submission.sizes submission.layout phase e.state) else none,
    e.exit != .unfinished, e.cycles, e.hashCalls, e.hashCompressions⟩

theorem run_eq (submission : Submission) (phase : Phase) (input : Input submission.sizes phase)
    (s : MachineState) (hinit : initialState submission phase input = some s) :
    submission.run phase input =
      toRunResult submission phase <$> Riscv.execute CYCLE_LIMIT (submission.image phase) s := by
  simp only [Submission.run, hinit, map_eq_bind_pure_comp]
  rfl

theorem runWith_eq (submission : Submission) (hash : Hash) (phase : Phase)
    (input : Input submission.sizes phase)
    (s : MachineState) (hinit : initialState submission phase input = some s) :
    submission.runWith hash phase input =
      toRunResult submission phase
        (evalWithAnswerFn hash (Riscv.execute CYCLE_LIMIT (submission.image phase) s)) := by
  rw [Submission.runWith, run_eq submission phase input s hinit, evalWithAnswerFn_map]

theorem initialState_pc (submission : Submission) (phase : Phase)
    (input : Input submission.sizes phase) (s : MachineState)
    (hinit : initialState submission phase input = some s) : s.pc = 0x1000 := by
  unfold initialState at hinit
  dsimp only at hinit
  split at hinit
  · cases hinit
    simp only [MachineState.pc_setReg]
    generalize (inputBuffers submission.sizes submission.layout phase input) = bufs
    suffices ∀ (st : MachineState), st.pc = 0x1000 → (bufs.foldl (fun state buffer =>
        state.writeBytesAsWords (BitVec.ofNat 64 buffer.1) buffer.2) st).pc = 0x1000 from
      this _ (by simp)
    induction bufs with
    | nil => intro st h; exact h
    | cons b bs ih => intro st h; exact ih _ (by simp [h])
  · cases hinit

end SigGolfCandidate.Rv
