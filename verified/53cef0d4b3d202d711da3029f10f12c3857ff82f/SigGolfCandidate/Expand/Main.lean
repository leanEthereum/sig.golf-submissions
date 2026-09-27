import SigGolfCandidate.Expand.Chain

/-!
# `expand` refines `expandRef`

`expand_run` : for every input `(m, pk, σ)`,
`submission.run .expand (m, pk, σ) = pure ⟨some (expandRef σ), true, 11711, 0, 0⟩`:
the program makes no oracle query, halts with success after exactly 11711 cycles, and its
witness buffer is `expandRef σ`.
-/

namespace SigGolfCandidate.Expand

set_option maxRecDepth 100000
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Mem OracleComp

/-- The initial state of `expand` on `(m, pk, σ)`. -/
def initState (m : Message) (pk : PublicKey) (σ : Bytes 7756) : MachineState :=
  let blank : MachineState := { regs := fun _ => 0, mem := fun _ => 0, pc := 0x1000 }
  ((((blank.writeBytesAsWords (BitVec.ofNat 64 (dataBase image)) image.data).writeBytesAsWords
      (BitVec.ofNat 64 0x40) (bytes m)).writeBytesAsWords (BitVec.ofNat 64 0xA0) (bytes pk)).writeBytesAsWords
      (BitVec.ofNat 64 0x2650) (bytes σ)).setReg .x2 (BitVec.ofNat 64 (dataBase image))

theorem initialState_eq (m : Message) (pk : PublicKey) (σ : Bytes 7756) :
    initialState submission .expand (m, pk, σ) = some (initState m pk σ) := by
  unfold initialState
  rw [if_pos (submission_admissible.2 .expand)]
  rfl

theorem initState_sig (m : Message) (pk : PublicKey) (σ : Bytes 7756) (j : Nat) (hj : j < 7756) :
    (initState m pk σ).getByte (BitVec.ofNat 64 (0x2650 + j)) = (bytes σ).getD j 0 := by
  unfold initState
  simp only [getByte_setReg]
  rw [getByte_writeBytesAsWords _ _ _ _ (by decide) (by simp [SigGolf.bytes]) (by omega),
    if_pos (by simp [SigGolf.bytes]; omega)]
  congr 1; omega

theorem readBuffer_final (m : Message) (pk : PublicKey) (σ : Bytes 7756) (u : MachineState)
    (hu : BytesEq u (applyCopies copies (fun a => (initState m pk σ).getByte (BitVec.ofNat 64 a)))) :
    readBuffer u 0x800 7756 = Ref.expandRef σ := by
  rw [readBuffer_eq, Ref.expandRef, Ref.ofList, Ref.toWitness]
  congr 2
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  obtain ⟨c, hc, h1, h2, h3⟩ := copies_cover i hi
  rw [hu _ (by omega), applyCopies_hit copies _ (by decide) (by decide) c hc _ h1 h2, h3,
    initState_sig m pk σ _ (Ref.witnessSrc_lt i hi)]
  rfl

/-- **expand**: for every input, one run makes no hash query, halts with success after exactly
11711 cycles, and outputs `expandRef σ`. -/
theorem expand_run (m : Message) (pk : PublicKey) (σ : Bytes submission.sizes.signature) :
    submission.run .expand (m, pk, σ) =
      pure ⟨some (Ref.expandRef σ), true, 11711, 0, 0⟩ := by
  rw [run_eq submission .expand _ _ (initialState_eq m pk σ)]
  obtain ⟨u, hst, hf, h5, h10, hb⟩ := expand_steps (initState m pk σ)
    (initialState_pc _ _ _ _ (initialState_eq m pk σ))
  rw [hst.execute_le (by decide : 11710 ≤ CYCLE_LIMIT),
    show CYCLE_LIMIT - 11710 = (CYCLE_LIMIT - 11711) + 1 by decide,
    execute_halt _ hf h5, map_pure]
  have hr : readOutput submission.sizes submission.layout .expand u = Ref.expandRef σ :=
    readBuffer_final m pk σ u hb
  rw [h10, if_pos rfl, map_pure]
  unfold toRunResult
  simp only [Execution.charge_exit, Execution.charge_state, if_pos, hr]
  rfl

/-- Fixed-oracle form (termination and cycle count for every oracle). -/
theorem expand_runWith (hash : Hash) (m : Message) (pk : PublicKey)
    (σ : Bytes submission.sizes.signature) :
    submission.runWith hash .expand (m, pk, σ) = ⟨some (Ref.expandRef σ), true, 11711, 0, 0⟩ := by
  unfold Submission.runWith; rw [expand_run]; rfl

end SigGolfCandidate.Expand
