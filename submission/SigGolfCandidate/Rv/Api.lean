import SigGolfCandidate.Rv.Hash
import SigGolfCandidate.Rv.Tactic
import SigGolfCandidate.Rv.SimpAttr

/-!
# User-facing API

* `BlockSpec image entry k c P Q` and `BlockSpec.of_symRun`, `BlockSpec.execute`, `BlockSpec.evalWith`
* `Steps.iterate` : loop-invariant lemma for loops whose body is a block
* `Layout` / `codeAt_layout` : place many segments in one image without walking the image per
  instruction (`layoutOk` is checked once for the whole image)
* `readWordsSym` / `readWords_toState` : reflective reads of the final memory
* `hashInput_toState` : the HASH input of a buffer written in a block
* the `rv_simp` simp set
-/

namespace SigGolfCandidate.Rv
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 OracleComp

/-! ## Block specifications -/

/-- From every state at `entry` satisfying `P`, the machine performs exactly `k` ordinary steps
costing `c` cycles and reaches a state `t` with `Q s t`. -/
def BlockSpec (image : Image) (entry : Word) (k c : Nat) (P : MachineState → Prop)
    (Q : MachineState → MachineState → Prop) : Prop :=
  ∀ s, s.pc = entry → P s → ∃ t, Steps image s k c t ∧ Q s t

theorem BlockSpec.of_symRun {cfg : Config} {image : Image} {code : List (BitVec 32)} {pc : Word}
    {fuel : Nat} {r : Result} (hrun : symRun cfg code pc fuel = some r)
    (hcode : CodeAt image pc code) {P : MachineState → Prop}
    {Q : MachineState → MachineState → Prop}
    (hobl : ∀ s, P s → r.obligs s) (hQ : ∀ s, P s → Q s (r.toState s)) :
    BlockSpec image pc r.steps r.cycles P Q :=
  fun s hpc hP => ⟨_, symRun_sound hrun hcode s hpc (hobl s hP), hQ s hP⟩

theorem BlockSpec.execute {image : Image} {entry : Word} {k c : Nat} {P : MachineState → Prop}
    {Q : MachineState → MachineState → Prop} (h : BlockSpec image entry k c P Q)
    (s : MachineState) (hpc : s.pc = entry) (hP : P s) (fuel : Nat) :
    ∃ t, Q s t ∧ Riscv.execute (fuel + k) image s =
      (fun e => e.charge c 0 0) <$> Riscv.execute fuel image t := by
  obtain ⟨t, hst, hQ⟩ := h s hpc hP
  exact ⟨t, hQ, hst.execute fuel⟩

theorem BlockSpec.evalWith {image : Image} {entry : Word} {k c : Nat} {P : MachineState → Prop}
    {Q : MachineState → MachineState → Prop} (h : BlockSpec image entry k c P Q) (hash : Hash)
    (s : MachineState) (hpc : s.pc = entry) (hP : P s) (fuel : Nat) :
    ∃ t, Q s t ∧ evalWithAnswerFn hash (Riscv.execute (fuel + k) image s) =
      (evalWithAnswerFn hash (Riscv.execute fuel image t)).charge c 0 0 := by
  obtain ⟨t, hst, hQ⟩ := h s hpc hP
  exact ⟨t, hQ, hst.evalWith hash fuel⟩

theorem BlockSpec.mono {image : Image} {entry : Word} {k c : Nat} {P P' : MachineState → Prop}
    {Q Q' : MachineState → MachineState → Prop} (h : BlockSpec image entry k c P Q)
    (hP : ∀ s, P' s → P s) (hQ : ∀ s t, P' s → Q s t → Q' s t) :
    BlockSpec image entry k c P' Q' := by
  intro s hpc hs
  obtain ⟨t, h1, h2⟩ := h s hpc (hP s hs)
  exact ⟨t, h1, hQ s t hs h2⟩

/-! ## Loops -/

/-- Loop-invariant lemma: if from `Inv (i+1)` one body execution (`k` steps, `c` cycles) reaches
`Inv i`, then from `Inv n` the machine reaches `Inv 0` in `n * k` steps and `n * c` cycles. -/
theorem Steps.iterate {image : Image} {k c : Nat} (Inv : Nat → MachineState → Prop)
    (body : ∀ i s, Inv (i + 1) s → ∃ t, Steps image s k c t ∧ Inv i t) :
    ∀ n s, Inv n s → ∃ t, Steps image s (n * k) (n * c) t ∧ Inv 0 t := by
  intro n
  induction n with
  | zero => intro s h; exact ⟨s, by simpa using Steps.refl s, h⟩
  | succ n ih =>
    intro s h
    obtain ⟨t, h1, h2⟩ := body n s h
    obtain ⟨u, h3, h4⟩ := ih t h2
    exact ⟨u, Steps.of_eq (h1.trans h3) (by rw [Nat.succ_mul, Nat.add_comm])
      (by rw [Nat.succ_mul, Nat.add_comm]), h4⟩

/-! ## Code layout -/

/-- A list of `(instruction offset, segment)` pairs. -/
abbrev Layout := List (Nat × List (BitVec 32))

/-- Offsets are consecutive, starting from `n`. Check once with `decide +kernel`. -/
def layoutOk : Nat → Layout → Bool
  | _, [] => true
  | n, (o, seg) :: rest => (o == n) && layoutOk (n + seg.length) rest

/-- The code of a layout. -/
def layoutCode (L : Layout) : List (BitVec 32) := (L.map Prod.snd).flatten

theorem layout_split : ∀ (L : Layout) (n i o : Nat) (seg : List (BitVec 32)),
    layoutOk n L = true → L[i]? = some (o, seg) →
    ∃ pre post, layoutCode L = pre ++ seg ++ post ∧ n + pre.length = o := by
  intro L
  induction L with
  | nil => intro n i o seg _ h; simp at h
  | cons p L ih =>
    intro n i o seg hok hi
    obtain ⟨o', seg'⟩ := p
    simp only [layoutOk, Bool.and_eq_true, beq_iff_eq] at hok
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
      obtain ⟨rfl, rfl⟩ := hi
      exact ⟨[], layoutCode L, by simp [layoutCode], by simp [hok.1]⟩
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      obtain ⟨pre, post, h1, h2⟩ := ih _ i o seg hok.2 hi
      refine ⟨seg' ++ pre, post, ?_, ?_⟩
      · simp only [layoutCode, List.map_cons, List.flatten_cons] at h1 ⊢
        rw [h1]; simp
      · simp only [List.length_append]; omega

/-- Segment placement from a layout table. -/
theorem codeAt_layout {image : Image} {L : Layout} (himage : image.code = layoutCode L)
    (hok : layoutOk 0 L = true) {i o : Nat} {seg : List (BitVec 32)}
    (hi : L[i]? = some (o, seg)) (hrange : 0x1000 + 4 * (o + seg.length) < 2 ^ 64) :
    CodeAt image (BitVec.ofNat 64 (0x1000 + 4 * o)) seg := by
  obtain ⟨pre, post, h1, h2⟩ := layout_split L 0 i o seg hok hi
  refine CodeAt.of_append (himage.trans h1) _ ?_ (by omega)
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  omega

/-! ## Reading final memory -/

/-- Symbolically read `n` consecutive doublewords starting at `k` from a symbolic memory. -/
def readWordsSym (cfg : Config) (mem : SymMem) (k : Addr) : Nat → Option (List E × List Oblig)
  | 0 => some ([], [])
  | n + 1 =>
    match readMem cfg k mem, readWordsSym cfg mem ⟨k.base, k.off + 8⟩ n with
    | some (e, os), some (es, os') => some (e :: es, os ++ os')
    | _, _ => none

theorem Addr.eval_add8 (s : MachineState) (k : Addr) :
    (⟨k.base, k.off + 8⟩ : Addr).eval s = k.eval s + 8 := by
  rcases k with ⟨_ | b, off⟩
  · rfl
  · simp [Addr.eval, BitVec.add_assoc]

theorem readWordsSym_sound {cfg : Config} {mem : SymMem} (s : MachineState) (t : MachineState)
    (ht : ∀ a, t.getMem a = memEval s mem a) :
    ∀ (n : Nat) (k : Addr) (es : List E) (os : List Oblig),
      readWordsSym cfg mem k n = some (es, os) → (∀ o ∈ os, o.holds s) →
      t.readWords (k.eval s) n = es.map (E.eval s) := by
  intro n
  induction n with
  | zero => intro k es os h _; simp [readWordsSym] at h; rw [h.1]; rfl
  | succ n ih =>
    intro k es os h hos
    simp only [readWordsSym] at h
    split at h
    · rename_i e os1 es' os2 h1 h2
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [MachineState.readWords_succ, ht, readMem_sound h1 s (fun o ho => hos o
        (List.mem_append_left _ ho)), ← Addr.eval_add8,
        ih _ es' os2 h2 (fun o ho => hos o (List.mem_append_right _ ho))]
      rfl
    · cases h

/-- Reflective `readWords` of a block's final state. -/
theorem Result.readWords_toState (r : Result) (s : MachineState) {cfg : Config} {k : Addr}
    {n : Nat} {es : List E} {os : List Oblig} (h : readWordsSym cfg r.st.mem k n = some (es, os))
    (hos : Oblig.all s os) :
    (r.toState s).readWords (k.eval s) n = es.map (E.eval s) :=
  readWordsSym_sound s (r.toState s) (fun _ => rfl) n k es os h ((Oblig.all_iff s _).mp hos)

/-- The HASH input of a block's final state, when the buffer (`x10 = k`, `x11 = 64 (n+1)`)
can be read back symbolically as `es`. -/
theorem Result.hashInput_toState (r : Result) (s : MachineState) {cfg : Config} {k : Addr}
    {n : Nat} {es : List E} {os : List Oblig}
    (h10 : (r.st.regs.get .x10).eval s = k.eval s)
    (h11 : (r.st.regs.get .x11).eval s = BitVec.ofNat 64 (64 * (n + 1)))
    (hn : 64 * (n + 1) < 2 ^ 64) (hal : (k.eval s).toNat % 8 = 0)
    (h : readWordsSym cfg r.st.mem k (8 * (n + 1)) = some (es, os)) (hos : Oblig.all s os) :
    hashInput (r.toState s) = queryOfWords n (es.map (E.eval s)) := by
  rw [hashInput_eq_words (r.toState s) n (by simpa using h11) hn
    (by simpa [h10] using hal)]
  rw [Result.toState_getReg, h10, r.readWords_toState s h hos]

/-! ## Deduplicating side conditions -/

/-- Remove duplicate side conditions (`ne` conditions are not deduplicated during execution). -/
def Oblig.dedup : List Oblig → List Oblig
  | [] => []
  | o :: os => if os.any (Oblig.beq o) then Oblig.dedup os else o :: Oblig.dedup os

theorem Oblig.mem_dedup : ∀ {l : List Oblig} {o : Oblig}, o ∈ l → o ∈ Oblig.dedup l := by
  intro l
  induction l with
  | nil => intro o h; cases h
  | cons x xs ih =>
    intro o h
    simp only [Oblig.dedup]
    split
    · rename_i hany
      rcases List.mem_cons.mp h with rfl | h
      · obtain ⟨y, hy, hb⟩ := List.any_eq_true.mp hany
        rw [Oblig.beq_eq hb]; exact ih hy
      · exact ih h
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih h)

/-- Prove the side conditions of a block from a deduplicated list, e.g.
`r.obligs_of_dedup (l := _) (by sym_eval) (by rv_obligs [...])`. -/
theorem Result.obligs_of_dedup (r : Result) (s : MachineState) {l : List Oblig}
    (hl : Oblig.dedup r.st.obl = l) (h : Oblig.all s l) : r.obligs s := by
  subst hl
  rw [Result.obligs, Oblig.all_iff]
  intro o ho
  exact (Oblig.all_iff s _).mp h o (Oblig.mem_dedup ho)

/-! ## Readability simp set -/

theorem add_ofNat_big (x : Word) (n : Nat) (h1 : 2 ^ 63 ≤ n) (h2 : n < 2 ^ 64) :
    x + BitVec.ofNat 64 n = x - BitVec.ofNat 64 (2 ^ 64 - n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat]
  have := x.isLt
  rw [Nat.mod_eq_of_lt h2, Nat.mod_eq_of_lt (by omega : 2 ^ 64 - n < 2 ^ 64)]
  omega

attribute [rv_simp] Result.toState_getReg Result.toState_getMem Result.toState_pc
  Result.toState_code SymState.toState_getReg SymState.toState_getMem SymState.toState_pc
  RegFile.get E.eval BinOp.eval UnOp.eval CmpOp.eval LoadKind.fromWord StoreKind.merge
  Addr.eval memEval_cons memEval_nil BitVec.add_zero Oblig.all Oblig.holds Result.obligs
  Result.toState_getMem Result.pc Result.st Result.steps Result.cycles Result.stop
  SymState.regs SymState.mem SymState.obl BitVec.ofNat_eq_ofNat

open Lean Meta Simp in
/-- `x + c` with a "negative" 64-bit literal `c ≥ 2^63` becomes `x - (2^64 - c)`. -/
simproc [rv_simp] addNegLit ((_ : BitVec 64) + BitVec.ofNat 64 _) := fun e => do
  let_expr HAdd.hAdd _ _ _ _ x c := e | return .continue
  let_expr BitVec.ofNat w n := c | return .continue
  let some wv := (← instantiateMVars w).nat? | return .continue
  unless wv == 64 do return .continue
  let some nv := (← instantiateMVars n).nat? | return .continue
  unless 2 ^ 63 ≤ nv ∧ nv < 2 ^ 64 do return .continue
  let m := 2 ^ 64 - nv
  let rhs ← mkAppM ``HSub.hSub #[x, mkApp2 (mkConst ``BitVec.ofNat) (mkNatLit 64) (mkNatLit m)]
  let h1 ← mkDecideProof (← mkAppM ``LE.le #[mkNatLit (2 ^ 63), n])
  let h2 ← mkDecideProof (← mkAppM ``LT.lt #[n, mkNatLit (2 ^ 64)])
  let pf := mkApp4 (mkConst ``add_ofNat_big) x n h1 h2
  -- `add_ofNat_big` states the rhs with `2 ^ 64 - n`; it is defeq to the literal `m`
  let pf ← mkExpectedTypeHint pf (← mkEq e rhs)
  return .done { expr := rhs, proof? := some pf }

/-- Arithmetic normalization lemmas used by `rv_obligs`. -/
theorem accessValid_iff (a : Word) (w : Nat) :
    accessValid a w = true ↔ a.toNat + w ≤ MEMORY_BYTES ∧ a.toNat % w = 0 := by
  simp [accessValid, rangeValid]

/-- `rv_obligs [h₁, …]` : unfold the side conditions (`Result.obligs`, `Oblig.all …`) and the
memory-validity predicates to `Nat` arithmetic on `toNat`, rewrite with the given hypotheses
(typically `s.getReg .x10 = BitVec.ofNat 64 p`) and close every conjunct with `omega`. -/
macro "rv_obligs" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| (simp only [rv_simp, accessValid_iff, MEMORY_BYTES, ne_eq, BitVec.toNat_eq,
      BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, $ts',*] <;>
    (try and_intros) <;> omega))

end SigGolfCandidate.Rv
