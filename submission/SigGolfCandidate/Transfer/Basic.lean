import SigGolf
import SigGolfCandidate.Legacy

/-!
# Transfer from the legacy contract (70ba436) to the current one (51ea544)

The certificate of this submission was written against the previous organizer contract, kept
verbatim as `SigGolfCandidate.Legacy` (only the namespace changed). This file relates the two
contracts:

* the renamed data (`Program`/`Phase`, sizes, layout, images, inputs and outputs), with
  `legacyOf : SigGolf.Submission → Legacy.Submission`;
* the machines: both decoders, `fetch`, `ordinaryStep`, the memory checks, `HASH`/`HALT` and all
  charges agree, so `SigGolf.Riscv.execute` is `Legacy.Riscv.execute` with the hash-call counter
  dropped (`execute_eq`);
* the runs (`run_eq`): the legacy `run` refuses an image that fails `Image.Valid` (returning a
  finished, costless, failed run) while the current one runs it as is; for a submission whose
  images are valid (`ImagesValid`) the current run is the legacy run with the result record
  translated (`RunAgrees`). The fixed-oracle form is `runWith_eq`.
-/

namespace SigGolfCandidate.Transfer
open OracleComp OracleSpec RiscvZkvm.Rv64

/-! ### Renamed data -/

def phaseOf : SigGolf.Program → Legacy.Phase
  | .keygen => .keygen
  | .sign => .sign
  | .expand => .expand
  | .verify => .verify

def programOf : Legacy.Phase → SigGolf.Program
  | .keygen => .keygen
  | .sign => .sign
  | .expand => .expand
  | .verify => .verify

@[simp] theorem phaseOf_programOf (phase : Legacy.Phase) : phaseOf (programOf phase) = phase := by
  cases phase <;> rfl

@[simp] theorem programOf_phaseOf (program : SigGolf.Program) :
    programOf (phaseOf program) = program := by
  cases program <;> rfl

def sizesOf (sizes : SigGolf.Sizes) : Legacy.Sizes := ⟨sizes.signature, sizes.witness, sizes.cache⟩

def layoutOf (layout : SigGolf.Layout) : Legacy.Layout :=
  ⟨layout.message, layout.secretKey, layout.publicKey, layout.cache, layout.signature,
    layout.witness⟩

def imageOf (image : SigGolf.Riscv.Image) : Legacy.Riscv.Image := ⟨image.code, image.data⟩

/-- The legacy view of a current submission: same sizes, layout and images. -/
@[reducible] def legacyOf (submission : SigGolf.Submission) : Legacy.Submission where
  sizes := sizesOf submission.sizes
  layout := layoutOf submission.layout
  image phase := imageOf (submission.image (programOf phase))

/-- The current view of a legacy submission. -/
def currentOf (submission : Legacy.Submission) : SigGolf.Submission where
  sizes := ⟨submission.sizes.signature, submission.sizes.witness, submission.sizes.cache⟩
  layout := ⟨submission.layout.message, submission.layout.secretKey, submission.layout.publicKey,
    submission.layout.cache, submission.layout.signature, submission.layout.witness⟩
  image program :=
    ⟨(submission.image (phaseOf program)).code, (submission.image (phaseOf program)).data⟩

theorem legacyOf_currentOf (submission : Legacy.Submission) :
    legacyOf (currentOf submission) = submission := by
  obtain ⟨⟨s, w, k⟩, ⟨m, sk, pk, c, sg, wt⟩, image⟩ := submission
  simp only [legacyOf, currentOf, sizesOf, layoutOf, imageOf, phaseOf_programOf]

@[simp] theorem legacyOf_sizes (submission : SigGolf.Submission) :
    (legacyOf submission).sizes = sizesOf submission.sizes := rfl

/-- Inputs of a program, as inputs of the corresponding legacy phase (the same values). -/
def inputOf {sizes : SigGolf.Sizes} :
    (program : SigGolf.Program) → SigGolf.Input sizes program →
      Legacy.Input (sizesOf sizes) (phaseOf program)
  | .keygen, input => input
  | .sign, input => input
  | .expand, input => input
  | .verify, input => input

/-- Outputs of a legacy phase, as outputs of the corresponding program (the same values). -/
def outputOf {sizes : SigGolf.Sizes} :
    (program : SigGolf.Program) → Legacy.Output (sizesOf sizes) (phaseOf program) →
      SigGolf.Output sizes program
  | .keygen, output => output
  | .sign, output => output
  | .expand, output => output
  | .verify, output => output

/-- A legacy run record as a current one: the hash-call count and `finished` flag are dropped. -/
def resultOf {sizes : SigGolf.Sizes} (program : SigGolf.Program)
    (result : Legacy.RunResult (Legacy.Output (sizesOf sizes) (phaseOf program))) :
    SigGolf.RunResult (SigGolf.Output sizes program) :=
  ⟨result.value.map (outputOf program), result.cycles, result.hashCompressions⟩

/-! ### Machines -/

namespace Riscv

def wordOpOf : Legacy.Riscv.WordOp → SigGolf.Riscv.WordOp
  | .add => .add | .sub => .sub | .sll => .sll | .srl => .srl | .sra => .sra
  | .mul => .mul | .div => .div | .divu => .divu | .rem => .rem | .remu => .remu

def instructionOf : Legacy.Riscv.Instruction → SigGolf.Riscv.Instruction
  | .base instruction => .base instruction
  | .word op rd rs1 rs2 => .word (wordOpOf op) rd rs1 rs2
  | .sraiw rd rs1 shift => .sraiw rd rs1 shift

def exitOf : Legacy.Riscv.Exit → SigGolf.Riscv.Exit
  | .success => .success
  | .failure => .failure
  | .unfinished => .unfinished

def executionOf (execution : Legacy.Riscv.Execution) : SigGolf.Riscv.Execution :=
  ⟨exitOf execution.exit, execution.state, execution.cycles, execution.hashCompressions⟩

theorem decodeInstruction_eq (word : BitVec 32) :
    SigGolf.Riscv.decodeInstruction word =
      (Legacy.Riscv.decodeInstruction word).map instructionOf := by
  unfold SigGolf.Riscv.decodeInstruction Legacy.Riscv.decodeInstruction
  simp only
  split_ifs <;> simp only [Option.map_some, Option.map_none, instructionOf, Option.pure_def,
    Option.bind_eq_bind]
  · generalize (BitVec.extractLsb' 25 7 word).toNat = a
    generalize (BitVec.extractLsb' 12 3 word).toNat = b
    split
    any_goals rfl
    split
    any_goals rfl
    all_goals (exfalso; simp at *)
  · cases RiscvZkvm.Interpreter.decode word <;> rfl

theorem fetch_eq (image : SigGolf.Riscv.Image) (state : MachineState) :
    SigGolf.Riscv.fetch image state =
      (Legacy.Riscv.fetch (imageOf image) state).map instructionOf := by
  unfold SigGolf.Riscv.fetch Legacy.Riscv.fetch
  by_cases h : 0x1000 ≤ state.pc.toNat ∧ state.pc.toNat % 4 = 0
  · have h' : (decide (state.pc.toNat < 0x1000) || state.pc.toNat % 4 != 0) = false := by
      simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, Nat.not_lt, bne_eq_false_iff_eq]
      exact h
    rw [if_pos h]
    simp only [h', Bool.false_eq_true, ↓reduceIte, imageOf, Option.bind_eq_bind]
    cases image.code[(state.pc.toNat - 0x1000) / 4]? with
    | none => rfl
    | some word => simpa using decodeInstruction_eq word
  · have h' : (decide (state.pc.toNat < 0x1000) || state.pc.toNat % 4 != 0) = true := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq]
      omega
    rw [if_neg h]
    simp [h']

theorem memoryArgumentsValid_eq (state : MachineState) (instruction : Instr) :
    SigGolf.Riscv.memoryArgumentsValid state instruction =
      Legacy.Riscv.memoryArgumentsValid state instruction := by
  cases instruction <;> rfl

theorem ordinaryStep_eq (state : MachineState) (instruction : Legacy.Riscv.Instruction) :
    SigGolf.Riscv.ordinaryStep state (instructionOf instruction) =
      Legacy.Riscv.ordinaryStep state instruction := by
  cases instruction with
  | base instruction =>
      cases instruction <;>
        simp only [instructionOf, SigGolf.Riscv.ordinaryStep, Legacy.Riscv.ordinaryStep,
          memoryArgumentsValid_eq]
  | word op rd rs1 rs2 => cases op <;> rfl
  | sraiw rd rs1 shift => rfl

theorem instructionCycles_eq (instruction : Legacy.Riscv.Instruction) :
    SigGolf.Riscv.instructionCycles (instructionOf instruction) =
      Legacy.Riscv.instructionCycles instruction := by
  cases instruction with
  | base instruction => cases instruction <;> rfl
  | word op rd rs1 rs2 => cases op <;> rfl
  | sraiw rd rs1 shift => rfl

theorem hashArgumentsValid_eq (state : MachineState) :
    SigGolf.Riscv.hashArgumentsValid state = Legacy.Riscv.hashArgumentsValid state := by
  unfold SigGolf.Riscv.hashArgumentsValid Legacy.Riscv.hashArgumentsValid
    Legacy.Riscv.accessValid
  simp only [SigGolf.Riscv.rangeValid, Legacy.Riscv.rangeValid, SigGolf.MEMORY_BYTES,
    Legacy.MEMORY_BYTES]
  generalize (state.getReg .x12).toNat = d
  by_cases h : d + 32 ≤ 2 ^ 24
  · have h8 : d + 8 ≤ 2 ^ 24 := by omega
    simp only [h, h8, decide_true, Bool.true_and, Bool.and_true]
    rfl
  · simp only [h, decide_false, Bool.and_false]

/-- The little-endian sum as a left fold over `List.range`, as the legacy files write it. -/
theorem foldl_range_eq_sum (f : Nat → Nat) (n : Nat) :
    (List.range n).foldl (fun acc i => acc + f i) 0 = ∑ i ∈ Finset.range n, f i := by
  suffices h : ∀ a, (List.range n).foldl (fun acc i => acc + f i) a =
      a + ∑ i ∈ Finset.range n, f i by simpa using h 0
  induction n with
  | zero => intro a; simp
  | succ n ih =>
      intro a
      rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]
      simp [Nat.add_assoc]

theorem ofNat_toNat_add (address : BitVec 64) (i : Nat) :
    BitVec.ofNat 64 (address.toNat + i) = address + BitVec.ofNat 64 i := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

theorem hashInput_eq (state : MachineState) :
    SigGolf.Riscv.hashInput state = Legacy.Riscv.hashInput state := by
  unfold SigGolf.Riscv.hashInput Legacy.Riscv.hashInput SigGolf.Riscv.readBuffer
  simp only [foldl_range_eq_sum, ofNat_toNat_add]

theorem readBuffer_eq (state : MachineState) (address n : Nat) :
    SigGolf.Riscv.readBuffer state address n = Legacy.readBuffer state address n := by
  unfold SigGolf.Riscv.readBuffer Legacy.readBuffer
  rw [foldl_range_eq_sum]

/-- The two step-bounded interpreters agree: the current one is the legacy one without the
hash-call counter. -/
theorem execute_eq (image : SigGolf.Riscv.Image) (steps : Nat) (state : MachineState) :
    SigGolf.Riscv.execute image steps state =
      executionOf <$> Legacy.Riscv.execute steps (imageOf image) state := by
  induction steps generalizing state with
  | zero => simp [SigGolf.Riscv.execute, Legacy.Riscv.execute, executionOf, exitOf]
  | succ steps ih =>
      rw [SigGolf.Riscv.execute, Legacy.Riscv.execute, fetch_eq]
      rcases Legacy.Riscv.fetch (imageOf image) state with _ | instruction
      · simp [executionOf, exitOf]
      · simp only [Option.map_some]
        rcases em (instruction = .base .ECALL) with hE | hE
        · subst hE
          simp only [instructionOf, hashArgumentsValid_eq, hashInput_eq]
          split_ifs
          · rw [hashInput_eq]
            simp only [map_bind, map_pure, ih, bind_map_left]
            rfl
          all_goals simp [executionOf, exitOf]
        · have hE' : instructionOf instruction ≠ .base .ECALL := by
            cases instruction <;> simp_all [instructionOf]
          split
          · rename_i heq; cases heq
          · rename_i heq; exact absurd (Option.some.inj heq) hE'
          · rename_i instruction' _ heq
            obtain rfl := Option.some.inj heq
            rw [ordinaryStep_eq, instructionCycles_eq]
            cases hstep : Legacy.Riscv.ordinaryStep state instruction with
            | none =>
                dsimp only
                split
                · rename_i heq'; cases heq'
                · rename_i heq'; exact absurd (Option.some.inj heq') hE
                · rename_i instruction'' _ heq'
                  obtain rfl := Option.some.inj heq'
                  simp [hstep, executionOf, exitOf]
            | some next =>
                dsimp only
                split
                · rename_i heq'; cases heq'
                · rename_i heq'; exact absurd (Option.some.inj heq') hE
                · rename_i instruction'' _ heq'
                  obtain rfl := Option.some.inj heq'
                  simp only [hstep, ih, Functor.map_map, bind_pure_comp]
                  rfl

end Riscv

/-! ### Runs -/

open Riscv in
/-- Loading: when the image is valid, the legacy loader produces the current initial state. -/
theorem initialState_eq (submission : SigGolf.Submission) (program : SigGolf.Program)
    (input : SigGolf.Input submission.sizes program)
    (hvalid : ((legacyOf submission).image (phaseOf program)).Valid (legacyOf submission).sizes
      (legacyOf submission).layout) :
    Legacy.initialState (legacyOf submission) (phaseOf program) (inputOf program input) =
      some (SigGolf.initialState submission program input) := by
  unfold Legacy.initialState
  rw [if_pos hvalid]
  cases program <;> rfl

theorem readOutput_eq (sizes : SigGolf.Sizes) (layout : SigGolf.Layout)
    (program : SigGolf.Program) (state : MachineState) :
    SigGolf.readOutput sizes layout program state =
      outputOf program (Legacy.readOutput (sizesOf sizes) (layoutOf layout) (phaseOf program) state) := by
  cases program <;>
    simp only [SigGolf.readOutput, Legacy.readOutput, Riscv.readBuffer_eq, outputOf, phaseOf,
      sizesOf, layoutOf] <;> rfl

/-- Every image of the submission passes the legacy admission check (which the legacy `run`
performs before running). -/
def ImagesValid (submission : SigGolf.Submission) : Prop :=
  ∀ phase, ((legacyOf submission).image phase).Valid (legacyOf submission).sizes
    (legacyOf submission).layout

/-- Run agreement: each current run is the legacy run of the same program on the same input,
with the result record translated. -/
def RunAgrees (submission : SigGolf.Submission) : Prop :=
  ∀ (program : SigGolf.Program) (input : SigGolf.Input submission.sizes program),
    submission.run program input =
      resultOf program <$> (legacyOf submission).run (phaseOf program) (inputOf program input)

theorem runAgrees_of_imagesValid (submission : SigGolf.Submission)
    (hvalid : ImagesValid submission) : RunAgrees submission := by
  intro program input
  unfold SigGolf.Submission.run Legacy.Submission.run
  rw [initialState_eq submission program input (hvalid _)]
  have hprog : (legacyOf submission).image (phaseOf program) =
      imageOf (submission.image program) := by
    cases program <;> rfl
  have hlimit : Legacy.CYCLE_LIMIT = SigGolf.CYCLE_LIMIT := rfl
  rw [hprog, hlimit, Riscv.execute_eq]
  dsimp only
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind, Function.comp_apply]
  congr 1
  funext execution
  congr 1
  obtain ⟨exit, state, cycles, calls, compressions⟩ := execution
  cases exit <;> simp only [resultOf, Riscv.executionOf, Riscv.exitOf, readOutput_eq] <;> rfl

theorem imagesValid_of_admissible (submission : SigGolf.Submission)
    (hadmissible : (legacyOf submission).Admissible) : ImagesValid submission :=
  hadmissible.2

theorem runAgrees_of_admissible (submission : SigGolf.Submission)
    (hadmissible : (legacyOf submission).Admissible) : RunAgrees submission :=
  runAgrees_of_imagesValid submission (imagesValid_of_admissible submission hadmissible)

/-- Run agreement for a fixed oracle `H`. -/
theorem evalWithAnswerFn_run (submission : SigGolf.Submission) (hrun : RunAgrees submission)
    (hash : SigGolf.Hash) (program : SigGolf.Program)
    (input : SigGolf.Input submission.sizes program) :
    evalWithAnswerFn hash (submission.run program input) =
      resultOf program ((legacyOf submission).runWith hash (phaseOf program)
        (inputOf program input)) := by
  rw [hrun, evalWithAnswerFn_map]
  rfl

end SigGolfCandidate.Transfer
