import SigGolfCandidate.Rv
import SigGolfCandidate.Submission

/-!
# Path-guided symbolic execution for the verify image

`pathAux cfg look stops fuel pc dirs σ brs` symbolically executes code fetched through `look`
(instruction index ↦ word), starting at `pc` from the symbolic state `σ`. Unlike `symRun` it does
not stop at jumps and branches: a jump with a constant target is followed, and a branch whose
condition is symbolic takes the direction given by the next element of `dirs`, recording the
assumed outcome as a *branch obligation* (`Br`). It stops before an `ECALL` (`ecall = true`) or
after reaching a pc in `stops` (`ecall = false`).

The initial symbolic state `σK known` has the registers in `known` replaced by constants.
-/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

/-- An assumed branch outcome: `op.eval x y = d`. -/
structure Br where
  op : CmpOp
  x : E
  y : E
  d : Bool
  deriving Repr

def Br.holds (s : MachineState) (b : Br) : Prop := b.op.eval (b.x.eval s) (b.y.eval s) = b.d

structure PRes where
  st : SymState
  pc : Word
  ecall : Bool
  steps : Nat
  cycles : Nat
  brs : List Br
  deriving Repr

def PRes.toState (r : PRes) (s : MachineState) : MachineState := r.st.toState s r.pc

/-- Next pc of a micro-op, resolving a symbolic branch with `dirs`. -/
def nextSym (pc : Word) (ctl : Option E) (dirs : List Bool) : Option (Word × List Bool × List Br) :=
  match ctl with
  | none => some (pc + 4, dirs, [])
  | some (.c t) => some (t, dirs, [])
  | some (.ite op x y (.c a) (.c b)) =>
    match dirs with
    | [] => none
    | d :: ds => some (if d then a else b, ds, [⟨op, x, y, d⟩])
  | some _ => none

def pathAux (cfg : Config) (look : Nat → Option (BitVec 32)) (stops : List Word) :
    Nat → Word → List Bool → SymState → List Br → Option PRes
  | 0, _, _, _, _ => none
  | f + 1, pc, dirs, σ, brs =>
    if pc.toNat < 0x1000 || pc.toNat % 4 != 0 then none else
    match look ((pc.toNat - 0x1000) / 4) with
    | none => none
    | some w =>
      match decodeInstruction w with
      | none => none
      | some i =>
        if isEcall i then some ⟨σ, pc, true, 0, 0, brs⟩ else
        match classify i with
        | none => none
        | some m =>
          match symMicro cfg pc σ m with
          | none => none
          | some (σ', ctl) =>
            match nextSym pc ctl dirs with
            | none => none
            | some (pc', dirs', nb) =>
              if stops.contains pc' then some ⟨σ', pc', false, 1, instructionCycles i, nb ++ brs⟩
              else
                match pathAux cfg look stops f pc' dirs' σ' (nb ++ brs) with
                | none => none
                | some r => some { r with steps := r.steps + 1, cycles := instructionCycles i + r.cycles }

/-! ## Soundness -/

/-- `look` agrees with the image code. -/
def LookOK (image : Image) (look : Nat → Option (BitVec 32)) : Prop :=
  ∀ n w, look n = some w → image.code[n]? = some w

theorem nextSym_sound {pc pc' : Word} {ctl : Option E} {dirs ds : List Bool} {nb : List Br}
    (h : nextSym pc ctl dirs = some (pc', ds, nb)) (s : MachineState) (hb : ∀ b ∈ nb, b.holds s) :
    nextPc s pc ctl = pc' := by
  unfold nextSym at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, -⟩ := h; rfl
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨rfl, -, -⟩ := h; rfl
  · rename_i op x y a b
    split at h
    · cases h
    · rename_i d ds'
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -, rfl⟩ := h
      have := hb _ (List.mem_singleton_self _)
      simp only [Br.holds] at this
      simp only [nextPc, E.eval, this]

  · cases h

theorem fetch_of_look {image : Image} {look : Nat → Option (BitVec 32)} (hl : LookOK image look)
    {pc : Word} {w : BitVec 32} (hpc : (pc.toNat < 0x1000 || pc.toNat % 4 != 0) = false)
    (hw : look ((pc.toNat - 0x1000) / 4) = some w) (t : MachineState) (ht : t.pc = pc) :
    fetch image t = decodeInstruction w := by
  unfold Riscv.fetch
  rw [ht, hpc]
  simp only [Bool.false_eq_true, if_false, hl _ _ hw]
  rfl

theorem pathAux_sound (cfg : Config) (image : Image) (look : Nat → Option (BitVec 32))
    (stops : List Word) (hl : LookOK image look) (s : MachineState) :
    ∀ (fuel : Nat) (pc : Word) (dirs : List Bool) (σ : SymState) (brs : List Br) (r : PRes),
      pathAux cfg look stops fuel pc dirs σ brs = some r →
      (∀ o ∈ r.st.obl, o.holds s) → (∀ b ∈ r.brs, b.holds s) →
      Steps image (σ.toState s pc) r.steps r.cycles (r.toState s) ∧ σ.obl ⊆ r.st.obl ∧
        brs ⊆ r.brs ∧ (r.ecall = true → fetch image (r.toState s) = some (.base .ECALL)) := by
  intro fuel
  induction fuel with
  | zero => intro pc dirs σ brs r h; simp [pathAux] at h
  | succ f ih =>
    intro pc dirs σ brs r h hobl hbr
    simp only [pathAux] at h
    split at h
    · cases h
    · rename_i hpc
      have hpc' : (pc.toNat < 0x1000 || pc.toNat % 4 != 0) = false := by simpa using hpc
      split at h
      · cases h
      · rename_i w hw
        split at h
        · cases h
        · rename_i i hdec
          have hfetch : ∀ t : MachineState, t.pc = pc → fetch image t = some i := fun t ht =>
            (fetch_of_look hl hpc' hw t ht).trans hdec
          split at h
          · rename_i he
            simp only [Option.some.injEq] at h; subst h
            refine ⟨Steps.refl _, List.Subset.refl _, List.Subset.refl _, fun _ => ?_⟩
            rw [hfetch _ rfl, isEcall_eq he]
          · split at h
            · cases h
            · rename_i m hcl
              split at h
              · cases h
              · rename_i σ' ctl hm
                split at h
                · cases h
                · rename_i pc' dirs' nb hns
                  split at h
                  · simp only [Option.some.injEq] at h; subst h
                    have hnb : ∀ b ∈ nb, b.holds s := fun b hb => hbr b (List.mem_append_left _ hb)
                    obtain ⟨hsub', hexec⟩ := symMicro_sound hm s hobl
                    refine ⟨?_, hsub', List.subset_append_right _ _, fun h => by cases h⟩
                    refine Steps.step (i := i) (hfetch _ rfl) ?_ (Steps.refl _)
                    rw [classify_sound hcl, hexec, nextSym_sound hns s hnb]; try rfl
                  · split at h
                    · cases h
                    · rename_i r' hr'
                      simp only [Option.some.injEq] at h; subst h
                      obtain ⟨hsteps, hsub, hbsub, hec⟩ := ih pc' dirs' σ' (nb ++ brs) r' hr' hobl hbr
                      have hnb : ∀ b ∈ nb, b.holds s := fun b hb =>
                        hbr b (hbsub (List.mem_append_left _ hb))
                      obtain ⟨hsub', hexec⟩ := symMicro_sound hm s (fun o ho => hobl o (hsub ho))
                      refine ⟨?_, List.Subset.trans hsub' hsub,
                        List.Subset.trans (List.subset_append_right _ _) hbsub, hec⟩
                      refine Steps.step (hfetch _ rfl) ?_ hsteps
                      rw [classify_sound hcl, hexec, nextSym_sound hns s hnb]; try rfl

/-! ## Initial state with known registers -/

def RegFile.withKnown (known : List (Reg × Word)) : RegFile :=
  known.foldl (fun rf p => rf.set p.1 (.c p.2)) RegFile.init

def σK (known : List (Reg × Word)) : SymState := ⟨RegFile.withKnown known, [], []⟩

theorem RegFile.withKnown_eval (s : MachineState) (known : List (Reg × Word))
    (hk : ∀ p ∈ known, s.getReg p.1 = p.2) (r : Reg) :
    ((RegFile.withKnown known).get r).eval s = s.getReg r := by
  unfold RegFile.withKnown
  suffices ∀ (l : List (Reg × Word)) (rf : RegFile), (∀ p ∈ l, s.getReg p.1 = p.2) →
      (∀ r, (rf.get r).eval s = s.getReg r) →
      ∀ r, ((l.foldl (fun rf p => rf.set p.1 (.c p.2)) rf).get r).eval s = s.getReg r from
    this known _ hk (RegFile.init_get_eval s) r
  intro l
  induction l with
  | nil => intro rf _ h; exact h
  | cons p l ih =>
    intro rf hl hrf
    obtain ⟨q, v⟩ := p
    simp only [List.foldl_cons]
    apply ih _ (fun q hq => hl q (List.mem_cons_of_mem _ hq))
    intro r
    by_cases hr : r = q
    · subst hr
      by_cases h0 : r = .x0
      · subst h0; rfl
      · rw [RegFile.get_set_self _ _ h0]; simp only [E.eval]
        exact (hl (r, v) (List.mem_cons_self ..)).symm
    · rw [RegFile.get_set_ne _ _ hr]; exact hrf r

theorem σK_toState (s : MachineState) (known : List (Reg × Word))
    (hk : ∀ p ∈ known, s.getReg p.1 = p.2) : (σK known).toState s s.pc = s := by
  apply MachineState.ext' <;> try rfl
  funext r
  simp only [SymState.toState, σK]
  split
  · rename_i h; subst h; rfl
  · rename_i h
    rw [RegFile.withKnown_eval s known hk r]
    cases r <;> first | exact absurd rfl h | rfl

/-- Soundness of a path run from `σK known`. -/
theorem pathRun_sound {cfg : Config} {image : Image} {look : Nat → Option (BitVec 32)}
    {stops : List Word} {fuel : Nat} {pc : Word} {dirs : List Bool} {known : List (Reg × Word)}
    {r : PRes} (h : pathAux cfg look stops fuel pc dirs (σK known) [] = some r)
    (hl : LookOK image look) (s : MachineState) (hpc : s.pc = pc)
    (hk : ∀ p ∈ known, s.getReg p.1 = p.2) (hobl : ∀ o ∈ r.st.obl, o.holds s)
    (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch image (r.toState s) = some (.base .ECALL)) := by
  obtain ⟨h1, -, -, h4⟩ := pathAux_sound cfg image look stops hl s fuel pc dirs _ [] r h hobl hbr
  rw [← hpc, σK_toState s known hk] at h1
  exact ⟨h1, h4⟩

/-! ## Structural equality checks (for kernel-checked families of runs) -/

def listBeq {α : Type} (f : α → α → Bool) : List α → List α → Bool
  | [], [] => true
  | a :: as, b :: bs => f a b && listBeq f as bs
  | _, _ => false

theorem listBeq_eq {α : Type} {f : α → α → Bool} (hf : ∀ a b, f a b = true → a = b) :
    ∀ {l l' : List α}, listBeq f l l' = true → l = l' := by
  intro l
  induction l with
  | nil => intro l' h; cases l' <;> simp_all [listBeq]
  | cons a as ih =>
    intro l' h
    cases l' with
    | nil => simp [listBeq] at h
    | cons b bs =>
      simp only [listBeq, Bool.and_eq_true] at h
      rw [hf _ _ h.1, ih h.2]

def RegFile.beq (a b : RegFile) : Bool := listBeq E.beq a.fields b.fields

theorem RegFile.beq_eq {a b : RegFile} (h : RegFile.beq a b = true) : a = b := by
  have := listBeq_eq (fun _ _ => E.beq_eq) h
  cases a; cases b
  simp only [RegFile.fields, List.cons.injEq] at this
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19,
    h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31, -⟩ := this
  subst_vars; rfl

def pairBeq (a b : Addr × E) : Bool := Addr.beq a.1 b.1 && E.beq a.2 b.2

theorem pairBeq_eq {a b : Addr × E} (h : pairBeq a b = true) : a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [pairBeq, Bool.and_eq_true] at h
  rw [Addr.beq_eq h.1, E.beq_eq h.2]

def SymState.beq (a b : SymState) : Bool :=
  RegFile.beq a.regs b.regs && listBeq pairBeq a.mem b.mem && listBeq Oblig.beq a.obl b.obl

theorem SymState.beq_eq {a b : SymState} (h : SymState.beq a b = true) : a = b := by
  obtain ⟨ar, am, ao⟩ := a; obtain ⟨br, bm, bo⟩ := b
  simp only [SymState.beq, Bool.and_eq_true] at h
  rw [RegFile.beq_eq h.1.1, listBeq_eq (fun _ _ => pairBeq_eq) h.1.2,
    listBeq_eq (fun _ _ => Oblig.beq_eq) h.2]

def Br.beq (a b : Br) : Bool :=
  decide (a.op = b.op) && E.beq a.x b.x && E.beq a.y b.y && a.d == b.d

theorem Br.beq_eq {a b : Br} (h : Br.beq a b = true) : a = b := by
  obtain ⟨o, x, y, d⟩ := a; obtain ⟨o', x', y', d'⟩ := b
  simp only [Br.beq, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  rw [h1, E.beq_eq h2, E.beq_eq h3, h4]

def PRes.beq (a b : PRes) : Bool :=
  SymState.beq a.st b.st && a.pc.toNat == b.pc.toNat && a.ecall == b.ecall &&
    a.steps == b.steps && a.cycles == b.cycles && listBeq Br.beq a.brs b.brs

theorem PRes.beq_eq {a b : PRes} (h : PRes.beq a b = true) : a = b := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := a; obtain ⟨b1, b2, b3, b4, b5, b6⟩ := b
  simp only [PRes.beq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  rw [SymState.beq_eq h1, BitVec.eq_of_toNat_eq h2, h3, h4, h5, listBeq_eq (fun _ _ => Br.beq_eq) h6]

/-- `o = some r`, as a Boolean check. -/
def optBeq (o : Option PRes) (r : PRes) : Bool :=
  match o with
  | some r' => PRes.beq r' r
  | none => false

theorem optBeq_eq {o : Option PRes} {r : PRes} (h : optBeq o r = true) : o = some r := by
  cases o with
  | none => simp [optBeq] at h
  | some r' => simp only [optBeq] at h; rw [PRes.beq_eq h]

end SigGolfCandidate.Verify
