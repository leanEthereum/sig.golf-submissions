import SigGolfCandidate.Verify.PorsGood

/-! # The whole verify program -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

/-- The cycle bound of accepting runs: `9784 + 17 · 120 + 2 · 29` (every accepting run costs
exactly `9784 + 17 F + 2 G`, `F ≤ 120` the total folds, `G ≤ 29` the segments with `a ≥ 1`). -/
def cycleBound : Nat := 11882

/-- A cycle bound of every run (`256` per segment instead of `16` / `18 + 17 a`). -/
def cycleBoundAll : Nat := 16744

/-- A step bound (fuel) sufficient for every run. -/
def fuelBound : Nat := 45000

def Kb : Bool → OracleComp HashSpec Obs := fun b => pure (b, 0)

theorem layersCost_val : layersCost 5 = 8846 := by decide
theorem layC_val : layC = 8846 := by unfold layC; exact layersCost_val

theorem tail_eq (pk : List Byte) (w : List Byte) (idx : Nat) (M : Val) :
    cc (do
      let o ← verifyLayers w idx nLayers M
      match o with
      | none => pure false
      | some root => pure (root == pk)) Kb = cc (verifyLayers w idx 5 M) (Kfin pk) := by
  rw [cc_bind]
  congr 1; funext o
  cases o <;> simp [Kfin, Kb]

/-- After the PORS root: the layers and the comparison. -/
def Klay (P : PCtx) : Option Val → OracleComp HashSpec Obs := fun r =>
  cc (match r with
    | none => pure false
    | some M => do
      let o ← verifyLayers P.wl P.idx nLayers M
      match o with
      | none => pure false
      | some root => pure (root == P.pk)) Kb

/-- After the leaves: the root checks, then `Klay`. -/
def Kr (P : PCtx) : Option PorsState → OracleComp HashSpec Obs := fun r =>
  cc (match r with
    | none => pure none
    | some st => if st.folds > porsM ∨ st.E ≠ 1 ∨ st.stack ≠ [] then pure none else pure (some st.node))
    (Klay P)

theorem Kr_none (P : PCtx) : Kr P none = pure (false, 0) := by
  simp [Kr, Klay, Kb]

theorem root_good (P : PCtx) (hP : P.ok) (s0 : MachineState) (x c : Nat) (st : PorsState)
    (u : MachineState) (hT : TailIn P s0 14 x 2 c st.ptr st.E st.folds st.node st.stack u) :
    GoodQ u (22 + layC + layN) (22 + layC) (st.folds ≤ 120) (22 + layC) (Kr P (some st)) := by
  obtain ⟨hrej, hacc⟩ := tailF_step P hP s0 x c st.ptr st.E st.folds st.node st.stack u hT
  have hL : layC = layersCost 5 := by unfold layC; rfl
  by_cases hc : st.folds > porsM ∨ st.E ≠ 1 ∨ st.stack ≠ []
  · simp only [Kr, if_pos hc, cc_pure, Klay, Kb]
    obtain ⟨v, k, hk, hst, hf, h5, h10⟩ := hrej hc
    exact GoodQ.steps' hst (GoodQ.reject (Q := st.folds ≤ 120) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  · simp only [Kr, if_neg hc, cc_pure, Klay]
    obtain ⟨v, hst, hL4⟩ := hacc hc
    rw [tail_eq]
    have hg := layers_good P.wl P.pk hP.2 P.idx P.idx_lt hP.1 5 (le_refl _) st.node v hL4
    have hfolds : st.folds ≤ 120 := by simp only [porsM] at hc; omega
    exact GoodQ.steps' hst hg.toQ (by unfold layN; omega) (by rw [hL]; omega) (fun _ => ⟨hfolds, by rw [hL]; omega⟩)

/-- The PORS part: from the leaf-0 state after the setup to the verdict. -/
theorem pors_good (P : PCtx) (hP : P.ok) (s0 : MachineState)
    (h : LeafIn P s0 0 ⟨wStream, 0, 0, 0, [], []⟩ s0) :
    GoodQ s0 (leafCost 0 + Nseg 0 0) (leafCost 0 + Cseg 0 0) True (leafCost 0 + Aseg 0 0 0)
      (cc (porsRoot P.idx P.v P.wl) (Klay P)) := by
  have hr : ∀ (x c : Nat) (st : PorsState) (u : MachineState),
      TailIn P s0 14 x 2 c st.ptr st.E st.folds st.node st.stack u →
      GoodQ u (22 + layC + layN) (22 + layC) (st.folds ≤ 120) (22 + layC) (Kr P (some st)) :=
    fun x c st u hT => root_good P hP s0 x c st u hT
  have hg0 := leaves_good P hP s0 (Kr P) (Kr_none P) hr
  have hg := hg0 15 0 ⟨wStream, 0, 0, 0, [], []⟩ s0 (by rfl) h
  have e : cc (porsRoot P.idx P.v P.wl) (Klay P) =
      cc (porsLeaves P.idx P.v P.wl (List.range' 0 15) ⟨wStream, 0, 0, 0, [], []⟩) (Kr P) := by
    unfold porsRoot
    rw [cc_bind, List.range_eq_range']
    rfl
  rw [e]
  have l0 : (⟨wStream, 0, 0, 0, [], []⟩ : PorsState).stack.length = 0 := rfl
  have f0 : (⟨wStream, 0, 0, 0, [], []⟩ : PorsState).folds = 0 := rfl
  rw [l0, f0] at hg
  exact hg.mono (le_refl _) (le_refl _) (fun _ => ⟨trivial, le_refl _⟩)

theorem lrest_0 : lrest 0 = 158 := by decide

theorem cost_vals : leafCost 0 + Cseg 0 0 = 7754 + layC ∧ leafCost 0 + Aseg 0 0 0 = 2892 + layC ∧
    leafCost 0 + Nseg 0 0 = 7754 + layC + layN := by
  have h0 : leafCost 0 = 10 := rfl
  refine ⟨?_, ?_, ?_⟩ <;> simp only [Cseg, Aseg, Nseg, segR, lrest_0, h0] <;> omega

theorem main_good (ml pkl wl : List Byte) (hml : ml.length = 32) (hpk : pkl.length = 16)
    (hwl : wl.length = 6348) (s : MachineState) (hs : InitOK ml pkl wl s) :
    GoodQ s fuelBound cycleBoundAll True cycleBound (cc (verifyList ml pkl wl) Kb) := by
  unfold verifyList
  obtain ⟨hrej, hacc⟩ := start_step ml pkl wl hml hwl s hs
  have hL := layC_val
  obtain ⟨c1, c2, c3⟩ := cost_vals
  cases hc : countersOk wl
  · simp only [Bool.not_false, if_true, cc_pure, Kb]
    obtain ⟨t, hst, hf, h5, h10⟩ := hrej hc
    exact GoodQ.steps' hst (GoodQ.reject (Q := True) (A := 0) hf h5 h10)
      (by unfold fuelBound; omega) (by unfold cycleBoundAll; omega) (fun q => ⟨q, by unfold cycleBound; omega⟩)
  · simp only [Bool.not_true, Bool.false_eq_true, if_false]
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := hacc hc
    unfold digest
    rw [cc_bind, cc_bind]
    simp only [cc_pure]
    have H : ∀ a, GoodQ (writeHash t a) (108 + (leafCost 0 + Nseg 0 0)) (108 + (leafCost 0 + Cseg 0 0)) True
        (108 + (leafCost 0 + Aseg 0 0 0))
        (cc (do
          let r ← porsRoot (idxOf a.toNat) (leavesOf a.toNat) wl
          match r with
          | none => pure false
          | some M => do
            let o ← verifyLayers wl (idxOf a.toNat) nLayers M
            match o with
            | none => pure false
            | some root => pure (root == pkl)) Kb) := by
      intro a
      rw [cc_bind]
      set P : PCtx := ⟨wl, pkl, a⟩
      obtain ⟨u, hsu, hS0, hLI⟩ := setup_step P ⟨hwl, hpk⟩ _ (hpost a)
      have := pors_good P ⟨hwl, hpk⟩ u hLI
      exact (GoodQ.steps hsu this).mono (by omega) (by omega) (fun q => ⟨q, by omega⟩)
    have hrho : (witRho wl).length = 16 := by unfold witRho; apply length_slice16; omega
    have h3 := GoodQ.hashH (x := digestInput (witRho wl) ml) hf h5 hv hin H
    rw [fmt_digestInput_words _ _ hrho hml, blocks_q] at h3
    have hN : layN = 25009 := rfl
    exact GoodQ.steps' hst h3 (by unfold fuelBound; omega) (by unfold cycleBoundAll; omega)
      (fun q => ⟨q, by unfold cycleBound; omega⟩)

end SigGolfCandidate.Verify
