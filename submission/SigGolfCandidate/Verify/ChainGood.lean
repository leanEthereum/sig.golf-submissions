import SigGolfCandidate.Verify.ChainHead
import SigGolfCandidate.Verify.Judg

/-! # Chains: the simulation judgment for one chain and for all 42 chains of a layer -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

def restFold (c : CCtx) (i mu : Nat) (v : Val) : OracleComp HashSpec Val :=
  (List.range' mu (8 - mu)).foldlM (fun v mu => hash16 (chainInput c.lay c.tau c.e i mu v)) v

theorem restFold_succ (c : CCtx) (i mu : Nat) (h : mu ≤ 7) (v : Val) :
    restFold c i mu v = hash16 (chainInput c.lay c.tau c.e i mu v) >>= restFold c i (mu + 1) := by
  unfold restFold
  rw [show 8 - mu = (8 - (mu + 1)) + 1 by omega, List.range'_succ, List.foldlM_cons]

theorem restFold_8 (c : CCtx) (i : Nat) (v : Val) : restFold c i 8 v = pure v := rfl

theorem blocks_chain (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16) :
    (pad64 (chainInput lay tau e i mu v)).blocks = 1 := by
  rw [pad64_chainInput _ _ _ _ _ _ hv]; rfl

theorem StepInv.vlen {c : CCtx} {i : Nat} {acc : List Val} {mu : Nat} {v : Val} {s : MachineState}
    (hs : StepInv c i acc mu v s) : v.length = 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h, -⟩ := hs; exact h

theorem steps_good (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ v t, v.length = 16 → HeadInv c (i + 1) (acc ++ [v]) t → Good t N C (K (acc ++ [v]))) :
    ∀ k mu, mu + k = 7 → 1 ≤ mu → ∀ v s, StepInv c i acc mu v s →
      Good s (N + 6 * (8 - mu)) (C + 12 * (8 - mu))
        (cc (restFold c i mu v) (fun v => K (acc ++ [v]))) := by
  intro k
  induction k with
  | zero =>
    intro mu hmu h1 v s hs
    obtain rfl : mu = 7 := by omega
    have hvl := hs.vlen
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := step_7 c hc i hi acc hchk v s hs
    rw [restFold_succ c i 7 (le_refl _), cc_bind]
    simp only [show 7 + 1 = 8 from rfl, restFold_8, cc_pure]
    have h2 : ∀ a, Good (writeHash t a) (N + 1) (C + 1) (K (acc ++ [answerBytes 16 a])) := fun a => by
      obtain ⟨t', hst', hH⟩ := chain_end c hc i hi acc hchk _ _ (hpost a)
      exact Good.steps hst' (hK _ t' (by simp) hH)
    have h3 := Good.hash (K := fun v => K (acc ++ [v])) hf h5 hv hin h2
    rw [blocks_chain _ _ _ _ _ _ hvl] at h3
    exact Good.steps' hst h3 (by omega) (by omega)
  | succ k ih =>
    intro mu hmu h1 v s hs
    have hvl := hs.vlen
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := step_head c hc i hi acc mu h1 (by omega) hchk v s hs
    rw [restFold_succ c i mu (by omega), cc_bind]
    have h2 : ∀ a, Good (writeHash t a) (N + 6 * (8 - (mu + 1)) + 2) (C + 12 * (8 - (mu + 1)) + 2)
        (cc (restFold c i (mu + 1) (answerBytes 16 a)) (fun v => K (acc ++ [v]))) := fun a => by
      obtain ⟨t', hst', hS⟩ := step_tail c i hi acc mu h1 (by omega) hchk _ _ (hpost a)
      exact Good.steps hst' (ih (mu + 1) (by omega) (by omega) _ _ hS)
    have h3 := Good.hash (K := fun v => cc (restFold c i (mu + 1) v) (fun v => K (acc ++ [v])))
      hf h5 hv hin h2
    rw [blocks_chain _ _ _ _ _ _ hvl] at h3
    exact Good.steps' hst h3 (by omega) (by omega)

/-- Cost of chain `i` of layer `lay` at digit `x` (chain 0's head is part of the layer code). -/
def chainCost (lay i x : Nat) : Nat := (if i = 0 then 0 else headCost lay i) + 3 + 12 * (7 - x)

theorem chain_good_ent (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ v t, v.length = 16 → HeadInv c (i + 1) (acc ++ [v]) t → Good t N C (K (acc ++ [v])))
    (s : MachineState) (hs : EntInv c i acc s) :
    Good s (N + 51) (C + 3 + 12 * (7 - dig c i))
      (cc (chainFrom c.lay c.tau c.e i (dig c i) (witChain c.wl c.lay i)) (fun v => K (acc ++ [v]))) := by
  have hx := dig_lt c i
  have hw := length_witChain c hc i hi
  by_cases h7 : dig c i = 7
  · obtain ⟨t, hst, hH⟩ := entry_7 c hc i hi acc hchk s hs h7
    rw [h7]
    have : chainFrom c.lay c.tau c.e i 7 (witChain c.wl c.lay i) = pure (witChain c.wl c.lay i) := rfl
    rw [this, cc_pure]
    exact Good.steps' hst (hK _ t hw hH) (by omega) (by omega)
  · obtain ⟨t, hst, hS⟩ := entry_lt7 c hc i hi acc hchk s hs (by omega)
    have hcf : chainFrom c.lay c.tau c.e i (dig c i) (witChain c.wl c.lay i) =
        restFold c i (dig c i + 1) (witChain c.wl c.lay i) := by
      unfold chainFrom restFold; congr 2; omega
    rw [hcf]
    have := steps_good c hc i hi acc hchk K N C hK (6 - dig c i) (dig c i + 1) (by omega) (by omega) _ _ hS
    exact Good.steps' hst this (by omega) (by omega)

theorem chain_good_head (c : CCtx) (hc : c.ok) (i : Nat) (hi1 : 1 ≤ i) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ v t, v.length = 16 → HeadInv c (i + 1) (acc ++ [v]) t → Good t N C (K (acc ++ [v])))
    (s : MachineState) (hs : HeadInv c i acc s) :
    Good s (N + 60) (C + chainCost c.lay i (dig c i))
      (cc (chainFrom c.lay c.tau c.e i (dig c i) (witChain c.wl c.lay i)) (fun v => K (acc ++ [v]))) := by
  obtain ⟨t, hst, hE⟩ := head_step c hc i hi1 hi acc hchk s hs
  have hh : headCost c.lay i ≤ 7 := by unfold headCost; split_ifs <;> simp_all
  have := chain_good_ent c hc i hi acc hchk K N C hK t hE
  refine Good.steps' hst this (by omega) ?_
  unfold chainCost; rw [if_neg (by omega)]; omega

/-! ## All chains -/

def chainF (c : CCtx) (xs : List Nat) (ends : List Val) (i : Nat) : OracleComp HashSpec (List Val) := do
  let v ← chainFrom c.lay c.tau c.e i (xs.getD i 0) (witChain c.wl c.lay i)
  pure (ends ++ [v])

def chainsCost (c : CCtx) (i k : Nat) : Nat :=
  ((List.range' i k).map fun j => chainCost c.lay j (dig c j)).sum

theorem chains_good (c : CCtx) (hc : c.ok) (xs : List Nat) (hxs : ∀ i < 42, xs.getD i 0 = dig c i)
    (hchk : ∀ i < 42, chainCheck c.lay i = true) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ ends t, HeadInv c 42 ends t → Good t N C (K ends)) :
    ∀ k i, 1 ≤ i → i + k = 42 → ∀ acc s, HeadInv c i acc s →
      Good s (N + 60 * k) (C + chainsCost c i k)
        (cc ((List.range' i k).foldlM (chainF c xs) acc) K) := by
  intro k
  induction k with
  | zero =>
    intro i _ hik acc s hs
    obtain rfl : i = 42 := by omega
    simpa [chainsCost] using hK acc s hs
  | succ k ih =>
    intro i hi1 hik acc s hs
    rw [List.range'_succ, List.foldlM_cons]
    simp only [chainF, bind_assoc, pure_bind, cc_bind]
    rw [hxs i (by omega)]
    have := chain_good_head c hc i hi1 (by omega) acc (hchk i (by omega))
      (fun ends => cc ((List.range' (i + 1) k).foldlM (chainF c xs) ends) K)
      (N + 60 * k) (C + chainsCost c (i + 1) k)
      (fun v t _ ht => by
        have := ih (i + 1) (by omega) (by omega) (acc ++ [v]) t ht
        simpa [chainF] using this) s hs
    refine this.mono (by omega) ?_
    simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]
    omega

/-- All 42 chains, from the dispatch of chain 0 (at its table entry). -/
theorem chains_good0 (c : CCtx) (hc : c.ok) (xs : List Nat) (hxs : ∀ i < 42, xs.getD i 0 = dig c i)
    (hchk : ∀ i < 42, chainCheck c.lay i = true) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ ends t, HeadInv c 42 ends t → Good t N C (K ends)) (s : MachineState)
    (hs : EntInv c 0 [] s) :
    Good s (N + 60 * 42) (C + chainsCost c 0 42) (cc ((List.range 42).foldlM (chainF c xs) []) K) := by
  rw [show List.range 42 = 0 :: List.range' 1 41 from rfl, List.foldlM_cons]
  simp only [chainF, bind_assoc, pure_bind, cc_bind]
  rw [hxs 0 (by omega)]
  have := chain_good_ent c hc 0 (by omega) [] (hchk 0 (by omega))
    (fun ends => cc ((List.range' 1 41).foldlM (chainF c xs) ends) K)
    (N + 60 * 41) (C + chainsCost c 1 41)
    (fun v t _ ht => by
      have := chains_good c hc xs hxs hchk K N C hK 41 1 (le_refl _) rfl ([] ++ [v]) t ht
      simpa [chainF] using this) s hs
  refine this.mono (by omega) ?_
  have : chainsCost c 0 42 = chainCost c.lay 0 (dig c 0) + chainsCost c 1 41 := by
    unfold chainsCost; rw [show List.range' 0 42 = 0 :: List.range' 1 41 from rfl]
    simp only [List.map_cons, List.sum_cons]
  rw [this]; simp only [chainCost, if_pos rfl]
  omega

theorem sum_eq_getD (l : List Nat) : l.sum = ((List.range l.length).map (l.getD · 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.sum_cons,
      List.map_map, ih]
    rfl

/-- Sum of the head costs of chains `1 .. 41` of a layer. -/
def headSum (lay : Nat) : Nat := ((List.range' 0 42).map fun j => if j = 0 then 0 else headCost lay j).sum

theorem chainsCost_aux (c : CCtx) : ∀ k i,
    ((List.range' i k).map fun j => chainCost c.lay j (dig c j)).sum + 12 * ((List.range' i k).map (dig c)).sum =
      (87 * k + ((List.range' i k).map fun j => if j = 0 then 0 else headCost c.lay j).sum) := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    have := ih (i + 1)
    have := dig_lt c i
    simp only [List.range'_succ, List.map_cons, List.sum_cons, chainCost] at *
    omega

theorem chainsCost_eq (c : CCtx) (xs : List Nat) (hlen : xs.length = 42)
    (hxs : ∀ i < 42, xs.getD i 0 = dig c i) (hsum : xs.sum = targetSum) :
    chainsCost c 0 42 = 42 * 87 - 12 * targetSum + headSum c.lay := by
  have hs : ((List.range' 0 42).map (dig c)).sum = targetSum := by
    rw [← hsum, sum_eq_getD xs, hlen, List.range_eq_range']
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [hxs i (by simp at hi; omega)]
  have := chainsCost_aux c 42 0
  rw [hs] at this
  unfold chainsCost headSum
  simp only [targetSum] at this ⊢
  omega

end SigGolfCandidate.Verify
