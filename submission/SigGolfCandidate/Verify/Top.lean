import SigGolfCandidate.Verify.ForsGood

/-! # The whole verify program -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

/-- The cycle bound of the verify program (every run, honest or not). -/
def cycleBound : Nat := 11592

/-- A step bound (fuel) sufficient for every run. -/
def fuelBound : Nat := 40100

def Kb : Bool → OracleComp HashSpec Obs := fun b => pure (b, 0)

theorem idxOf_eq (d : DCtx) : idxOf (d.A % 2 ^ 184) = d.idx := by
  unfold idxOf totalH DCtx.idx; omega

theorem uOf_eq (d : DCtx) (k : Nat) (hk : k < 14) : uOf (d.A % 2 ^ 184) k = d.u k := by
  unfold uOf DCtx.u totalH ftsA
  rw [show 2 ^ 184 = 2 ^ (34 + 10 * k) * 2 ^ (150 - 10 * k) by rw [← Nat.pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem foldlM_congr {α β : Type} (f g : β → α → OracleComp HashSpec β) :
    ∀ (l : List α) (init : β), (∀ x ∈ l, ∀ b, f b x = g b x) → l.foldlM f init = l.foldlM g init := by
  intro l
  induction l with
  | nil => intro _ _; rfl
  | cons x xs ih =>
    intro init h
    simp only [List.foldlM_cons]
    rw [h x (List.mem_cons_self ..)]
    congr 1; funext b
    exact ih b (fun y hy => h y (List.mem_cons_of_mem _ hy))

theorem verifyFors_eq (d : DCtx) :
    verifyFors d.wl (d.A % 2 ^ 184) = (List.range' 0 14).foldlM (forsF d) [] := by
  unfold verifyFors
  rw [show ftsTrees = 14 from rfl, List.range_eq_range']
  apply foldlM_congr
  intro k hk roots
  simp only [List.mem_range'] at hk
  simp only [forsF, idxOf_eq, uOf_eq d k (by omega)]

theorem tail_eq (pk : List Byte) (w : List Byte) (idx : Nat) (M : Val) :
    cc (do
      let o ← verifyLayers w idx nLayers M
      match o with
      | none => pure false
      | some root => pure (root == pk)) Kb = cc (verifyLayers w idx 5 M) (Kfin pk) := by
  rw [cc_bind]
  congr 1; funext o
  cases o <;> simp [Kfin, Kb]

theorem after_roots (wl pk : List Byte) (hpk : pk.length = 16) (hwl : wl.length = 6404) (idx : Nat)
    (hidx : idx < 2 ^ 34) (M : Val) (t : MachineState) (ht : LayerIn ⟨wl, pk, 4, idx⟩ M t) :
    Good t (5000 * 5 + 9) (layersCost 5) (cc (do
      let o ← verifyLayers wl idx nLayers M
      match o with
      | none => pure false
      | some root => pure (root == pk)) Kb) := by
  rw [tail_eq]
  exact layers_good wl pk hpk idx hidx hwl 5 (le_refl _) M t ht

theorem after_fors (d : DCtx) (hpk : d.pk.length = 16) (hwl : d.wl.length = 6404) (roots : List Val)
    (t : MachineState) (ht : ForsIn d 14 roots t) :
    Good t (5000 * 5 + 9 + 6) (layersCost 5 + 5 + 32) (cc (do
      let M ← hash16 (rootsInput d.idx roots)
      let o ← verifyLayers d.wl d.idx nLayers M
      match o with
      | none => pure false
      | some root => pure (root == d.pk)) Kb) := by
  rw [cc_bind]
  exact roots_good d roots _ _ _ (fun ans t ht => after_roots d.wl d.pk hpk hwl d.idx (d_idx_lt d) _ t ht) t ht

theorem treesCost_val : treesCost 1 13 = 2497 := by decide
theorem layersCost_val : layersCost 5 = 8815 := by decide

theorem after_digest (d : DCtx) (hpk : d.pk.length = 16) (hwl : d.wl.length = 6404)
    (s : MachineState) (hs : DigestOut d s) :
    Good s 40000 (8815 + 37 + 2497 + 169 + 8 + 32)
      (cc (if (!admissible (d.A % 2 ^ 184)) = true then pure false else do
        let roots ← verifyFors d.wl (d.A % 2 ^ 184)
        let M ← hash16 (rootsInput (idxOf (d.A % 2 ^ 184)) roots)
        let o ← verifyLayers d.wl (idxOf (d.A % 2 ^ 184)) nLayers M
        match o with
        | none => pure false
        | some root => pure (root == d.pk)) Kb) := by
  obtain ⟨hrej, hacc⟩ := dg_leaf d hwl s hs
  cases hadm : admissible (d.A % 2 ^ 184)
  · simp only [Bool.not_false, if_true, cc_pure, Kb]
    obtain ⟨t, hst, hf, h5, h10⟩ := hrej hadm
    exact Good.steps' hst (Good.reject hf h5 h10) (by omega) (by omega)
  · simp only [Bool.not_true, Bool.false_eq_true, if_false]
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := hacc hadm
    rw [verifyFors_eq, idxOf_eq, List.range'_succ, List.foldlM_cons]
    simp only [forsF, ftsRoot, bind_assoc, cc_bind, cc_pure]
    let Kr : Val → OracleComp HashSpec Obs := fun r =>
      cc (List.foldlM (forsF d) ([] ++ [r]) (List.range' (0 + 1) 13)) fun a =>
          cc (hash16 (rootsInput d.idx a)) fun a =>
            cc (verifyLayers d.wl d.idx nLayers a) fun a =>
              cc
                (match a with
                | none => pure false
                | some root => pure (root == d.pk))
                Kb
    have H := fun ans => treeRest_good d hwl 0 (by decide) [] Kr (5000 * 5 + 9 + 6 + 200 * 13)
      (layersCost 5 + 5 + 32 + treesCost 1 13)
      (fun ans t ht => (trees_good d hwl _ _ _ (fun roots t ht => (after_fors d hpk hwl roots t ht).congr
          (by simp only [cc_bind]))
        13 1 rfl (le_refl _) _ t ht)) _ _ (hpost ans)
    have hsl : (witFtsSecret d.wl 0).length = 16 := by unfold witFtsSecret; apply length_slice16; omega
    have h3 := Good.hashP (x := ftsLeafInput 0 d.idx (d.u 0) (witFtsSecret d.wl 0))
      (K := fun v => cc (foldPath (ftsNodeInput 0 d.idx) (d.u 0) v
      (witFtsPath d.wl 0)) Kr) (fmt_th _ _ _ _ _ _ (by decide)) hf h5 hv hin H
    rw [pad64_ftsLeafInput _ _ _ _ hsl, blocks_q] at h3
    exact Good.steps' (N' := 40000) (C' := 8815 + 37 + 2497 + 169 + 8 + 32) hst h3 (by omega)
      (by rw [treesCost_val, layersCost_val])

theorem main_good (ml pkl wl : List Byte) (hml : ml.length = 32) (hpk : pkl.length = 16)
    (hwl : wl.length = 6404) (s : MachineState) (hs : InitOK ml pkl wl s) :
    Good s fuelBound cycleBound (cc (verifyList ml pkl wl) Kb) := by
  unfold verifyList
  obtain ⟨hrej, hacc⟩ := start_step ml pkl wl hml hwl s hs
  cases hc : countersOk wl
  · simp only [Bool.not_false, if_true, cc_pure, Kb]
    obtain ⟨t, hst, hf, h5, h10⟩ := hrej hc
    exact Good.steps' hst (Good.reject hf h5 h10) (by unfold fuelBound; omega) (by unfold cycleBound; omega)
  · simp only [Bool.not_true, Bool.false_eq_true, if_false]
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := hacc hc
    unfold digest
    rw [cc_bind, cc_bind]
    simp only [cc_pure]
    have H := fun a => after_digest ⟨wl, pkl, a⟩ hpk hwl _ (hpost a)
    have hrho : (witRho wl).length = 16 := by unfold witRho; apply length_slice16; omega
    have h3 := Good.hashH (x := digestInput (witRho wl) ml) hf h5 hv hin H
    rw [fmt_digestInput_words _ _ hrho hml, blocks_q] at h3
    exact Good.steps' hst (h3.congr rfl) (by unfold fuelBound; omega) (by unfold cycleBound; omega)

end SigGolfCandidate.Verify
