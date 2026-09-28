import SigGolfCandidate.Expand.Blocks

/-!
# Deterministic runs of the expand image

`Run s B P` : from `s` the expand image performs ordinary steps (no `ECALL`) costing at most `B`
cycles and reaches a state satisfying `P`. Everything after the digest query is such a run.

`Final res t` : `t` is at a HALT `ECALL` (`x5 = 1`) whose outcome is `res`: failure (`x10 ≠ 0`)
for `none`, success with witness buffer bytes `w` for `some w`.
-/

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def Run (s : MachineState) (B : Nat) (P : MachineState → Prop) : Prop :=
  ∃ t k c, Steps image s k c t ∧ c ≤ B ∧ P t

theorem Run.of {s t : MachineState} {k c B : Nat} {P : MachineState → Prop}
    (h : Steps image s k c t) (hc : c ≤ B) (hP : P t) : Run s B P := ⟨t, k, c, h, hc, hP⟩

theorem Run.done {s : MachineState} {P : MachineState → Prop} (hP : P s) : Run s 0 P :=
  ⟨s, 0, 0, Steps.refl s, le_refl _, hP⟩

theorem Run.done' {s : MachineState} {B : Nat} {P : MachineState → Prop} (hP : P s) : Run s B P :=
  ⟨s, 0, 0, Steps.refl s, Nat.zero_le _, hP⟩

theorem Run.mono {s : MachineState} {B B' : Nat} {P P' : MachineState → Prop} (h : Run s B P)
    (hB : B ≤ B') (hP : ∀ t, P t → P' t) : Run s B' P' := by
  obtain ⟨t, k, c, h1, h2, h3⟩ := h
  exact ⟨t, k, c, h1, le_trans h2 hB, hP t h3⟩

theorem Run.bind {s : MachineState} {B₁ B₂ : Nat} {Q P : MachineState → Prop} (h₁ : Run s B₁ Q)
    (h₂ : ∀ t, Q t → Run t B₂ P) : Run s (B₁ + B₂) P := by
  obtain ⟨t, k, c, h1, h2, h3⟩ := h₁
  obtain ⟨u, k', c', h1', h2', h3'⟩ := h₂ t h3
  exact ⟨u, k + k', c + c', h1.trans h1', by omega, h3'⟩

/-- Sequential composition with a separate bound check (useful when the continuation's bound is
only known after it has been constructed). -/
theorem Run.seq {s : MachineState} {B₁ B₂ B : Nat} {Q P : MachineState → Prop} (h₁ : Run s B₁ Q)
    (h₂ : ∀ t, Q t → Run t B₂ P) (hB : B₁ + B₂ ≤ B) : Run s B P :=
  (Run.bind h₁ h₂).mono hB (fun _ h => h)

theorem Run.steps {s t : MachineState} {k c B : Nat} {P : MachineState → Prop}
    (h : Steps image s k c t) (h₂ : Run t B P) : Run s (c + B) P :=
  Run.bind (Run.of (P := fun u => u = t) h (le_refl c) rfl) (fun _ hu => hu ▸ h₂)

/-- Run one symbolic block, then continue. -/
theorem Run.blk {cfg : Config} {code : List (BitVec 32)} {pc : Word} {fuel : Nat} {r : Result}
    (hrun : symRun cfg code pc fuel = some r) (hcode : CodeAt image pc code) {s : MachineState}
    (hpc : s.pc = pc) (hobl : r.obligs s) {B : Nat} {P : MachineState → Prop}
    (h : Run (r.toState s) B P) : Run s (r.cycles + B) P :=
  Run.steps (symRun_sound hrun hcode s hpc hobl) h

/-- A loop: `n` iterations of a body costing at most `B` each. -/
theorem Run.loop (Inv : Nat → MachineState → Prop) (B : Nat)
    (body : ∀ i s, Inv (i + 1) s → Run s B (Inv i)) :
    ∀ n s, Inv n s → Run s (n * B) (Inv 0) := by
  intro n
  induction n with
  | zero => intro s h; simpa using Run.done h
  | succ n ih =>
    intro s h
    exact (Run.bind (body n s h) (fun t ht => ih t ht)).mono (by rw [Nat.succ_mul, Nat.add_comm]) (fun _ h => h)

theorem toState_getMem_nil {r : Result} (h : r.st.mem = []) (t : MachineState) (a : Word) :
    (r.toState t).getMem a = t.getMem a := by
  rw [Result.toState_getMem, h]; rfl

theorem toState_getMem_one {r : Result} {k : Addr} {e : E} (h : r.st.mem = [(k, e)]) (t : MachineState)
    (a : Word) : (r.toState t).getMem a = if a = k.eval t then e.eval t else t.getMem a := by
  rw [Result.toState_getMem, h]; rfl

theorem toState_getMem_two {r : Result} {k₁ k₂ : Addr} {e₁ e₂ : E} (h : r.st.mem = [(k₁, e₁), (k₂, e₂)])
    (t : MachineState) (a : Word) : (r.toState t).getMem a =
      if a = k₁.eval t then e₁.eval t else if a = k₂.eval t then e₂.eval t else t.getMem a := by
  rw [Result.toState_getMem, h]; rfl

/-- The outcome of a run. -/
def Final (res : Option (List Byte)) (t : MachineState) : Prop :=
  fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
    match res with
    | none => t.getReg .x10 ≠ 0
    | some w => t.getReg .x10 = 0 ∧ ∀ i < 6348, t.getByte (BitVec.ofNat 64 (0x800 + i)) = w.getD i 0

/-- The `fail` stub (instructions 284 .. 286). -/
theorem run_fail (s : MachineState) (hpc : s.pc = pcOf 284) : Run s 2 (Final none) := by
  have hst := symRun_sound blk284 codeAt_284 s hpc (by simp only [blk284.res, rv_simp])
  refine Run.of hst (le_refl _) ⟨symRun_ecall blk284 codeAt_284 s (by simp only [blk284.res, rv_simp]) rfl,
    by simp only [blk284.res, rv_simp], ?_⟩
  simp only [blk284.res, rv_simp]; decide

end SigGolfCandidate.Expand
