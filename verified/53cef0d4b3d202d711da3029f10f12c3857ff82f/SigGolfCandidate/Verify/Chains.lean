import SigGolfCandidate.Verify.ChainGood

/-! # All 42 chains of a layer -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

def chainF (c : CCtx) (xs : List Nat) (ends : List Val) (i : Nat) : OracleComp HashSpec (List Val) := do
  let v ← chainFrom c.lay c.tau c.e i (xs.getD i 0) (witChain c.wl c.lay i)
  pure (ends ++ [v])

def chainsCost (c : CCtx) (i k : Nat) : Nat :=
  ((List.range' i k).map fun j => chainCost j (dig c j)).sum

theorem chains_good (c : CCtx) (hc : c.ok) (xs : List Nat) (hxs : ∀ i < 42, xs.getD i 0 = dig c i)
    (hchk : ∀ i < 42, chainCheck c.lay i = true) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ ends t, HeadInv c 42 ends t → Good t N C (K ends)) :
    ∀ k i, i + k = 42 → ∀ acc s, HeadInv c i acc s →
      Good s (N + 60 * k) (C + chainsCost c i k)
        (cc ((List.range' i k).foldlM (chainF c xs) acc) K) := by
  intro k
  induction k with
  | zero =>
    intro i hik acc s hs
    obtain rfl : i = 42 := by omega
    simpa [chainsCost] using hK acc s hs
  | succ k ih =>
    intro i hik acc s hs
    rw [List.range'_succ, List.foldlM_cons]
    simp only [chainF, bind_assoc, pure_bind, cc_bind]
    rw [hxs i (by omega)]
    have := chain_good c hc i (by omega) acc (hchk i (by omega))
      (fun ends => cc ((List.range' (i + 1) k).foldlM (chainF c xs) ends) K)
      (N + 60 * k) (C + chainsCost c (i + 1) k)
      (fun v t _ ht => by
        have := ih (i + 1) (by omega) (acc ++ [v]) t ht
        simpa [chainF] using this) s hs
    refine this.mono (by omega) ?_
    simp only [chainsCost, List.range'_succ, List.map_cons, List.sum_cons]
    omega

theorem sum_eq_getD (l : List Nat) : l.sum = ((List.range l.length).map (l.getD · 0)).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.sum_cons, List.sum_cons,
      List.map_map, ih]
    rfl

theorem chainsCost_aux (c : CCtx) : ∀ k i,
    ((List.range' i k).map fun j => chainCost j (dig c j)).sum + 12 * ((List.range' i k).map (dig c)).sum =
      94 * k + ((List.range' i k).map grp).sum := by
  intro k
  induction k with
  | zero => intro i; rfl
  | succ k ih =>
    intro i
    have := ih (i + 1)
    have := dig_lt c i
    simp only [List.range'_succ, List.map_cons, List.sum_cons, chainCost] at *
    omega

theorem grp_sum : ((List.range' 0 42).map grp).sum = 3 := by decide

theorem chainsCost_eq (c : CCtx) (xs : List Nat) (hlen : xs.length = 42)
    (hxs : ∀ i < 42, xs.getD i 0 = dig c i) (hsum : xs.sum = 170) : chainsCost c 0 42 = 1911 := by
  have hs : ((List.range' 0 42).map (dig c)).sum = 170 := by
    rw [← hsum, sum_eq_getD xs, hlen, List.range_eq_range']
    congr 1
    apply List.map_congr_left
    intro i hi
    rw [hxs i (by simp at hi; omega)]
  have := chainsCost_aux c 42 0
  rw [hs, grp_sum] at this
  unfold chainsCost
  omega

end SigGolfCandidate.Verify
