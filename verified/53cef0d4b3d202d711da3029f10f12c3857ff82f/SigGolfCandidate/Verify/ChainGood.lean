import SigGolfCandidate.Verify.ChainSem

/-! # Chains: the simulation judgment for one chain -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

def restFold (c : CCtx) (i mu : Nat) (v : Val) : OracleComp HashSpec Val :=
  (List.range' mu (8 - mu)).foldlM (fun v mu => hash16 (chainInput c.lay c.tau c.e i mu v)) v

def chainCost (i x : Nat) : Nat := 10 + 12 * (7 - x) + grp i

theorem restFold_succ (c : CCtx) (i mu : Nat) (h : mu ≤ 7) (v : Val) :
    restFold c i mu v = hash16 (chainInput c.lay c.tau c.e i mu v) >>= restFold c i (mu + 1) := by
  unfold restFold
  rw [show 8 - mu = (8 - (mu + 1)) + 1 by omega, List.range'_succ, List.foldlM_cons]

theorem restFold_8 (c : CCtx) (i : Nat) (v : Val) : restFold c i 8 v = pure v := rfl

theorem blocks_chain (lay tau e i mu : Nat) (v : Val) (hv : v.length = 16) :
    (pad64 (chainInput lay tau e i mu v)).blocks = 1 := by
  rw [pad64_chainInput _ _ _ _ _ _ hv]; rfl

theorem grp_le (i : Nat) : grp i ≤ 1 := by unfold grp; split <;> omega

theorem steps_good (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ v t, v.length = 16 → HeadInv c (i + 1) (acc ++ [v]) t → Good t N C (K (acc ++ [v]))) :
    ∀ k mu, mu + k = 7 → 2 ≤ mu → ∀ v s, StepInv c i acc mu v s →
      Good s (N + 6 * (8 - mu) + 2 + grp i) (C + 12 * (8 - mu) + 2 + grp i)
        (cc (restFold c i mu v) (fun v => K (acc ++ [v]))) := by
  intro k
  induction k with
  | zero =>
    intro mu hmu h2 v s hs
    have hg := grp_le i
    obtain rfl : mu = 7 := by omega
    have hvl : v.length = 16 := hs.2.2.2.2.2.2.2.2.2.1
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := step_7 c hc i hi acc hchk v s hs
    rw [restFold_succ c i 7 (le_refl _), cc_bind]
    simp only [show 7 + 1 = 8 from rfl, restFold_8, cc_pure]
    have h2 : ∀ a, Good (writeHash t a) (N + (1 + grp i)) (C + (1 + grp i))
        (K (acc ++ [answerBytes 16 a])) := fun a => by
      obtain ⟨t', hst', hH⟩ := chain_end c i hi acc hchk _ _ (hpost a)
      exact Good.steps hst' (hK _ t' (by simp) hH)
    have h3 := Good.hash (K := fun v => K (acc ++ [v])) hf h5 hv hin h2
    rw [blocks_chain _ _ _ _ _ _ hvl] at h3
    exact Good.steps' hst h3 (by omega) (by omega)
  | succ k ih =>
    intro mu hmu h2 v s hs
    have hg := grp_le i
    have hvl : v.length = 16 := hs.2.2.2.2.2.2.2.2.2.1
    obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := step_lt7 c hc i hi acc mu h2 (by omega) hchk v s hs
    rw [restFold_succ c i mu (by omega), cc_bind]
    have h3 := Good.hash (K := fun v => cc (restFold c i (mu + 1) v) (fun v => K (acc ++ [v])))
      hf h5 hv hin (fun a => ih (mu + 1) (by omega) (by omega) _ _ (hpost a))
    rw [blocks_chain _ _ _ _ _ _ hvl] at h3
    exact Good.steps' hst h3 (by omega) (by omega)

theorem dig_lt (c : CCtx) (i : Nat) : dig c i < 8 := by unfold dig; omega

theorem chain_good (c : CCtx) (hc : c.ok) (i : Nat) (hi : i < 42) (acc : List Val)
    (hchk : chainCheck c.lay i = true) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ v t, v.length = 16 → HeadInv c (i + 1) (acc ++ [v]) t → Good t N C (K (acc ++ [v])))
    (s : MachineState) (hs : HeadInv c i acc s) :
    Good s (N + 60) (C + chainCost i (dig c i))
      (cc (chainFrom c.lay c.tau c.e i (dig c i) (witChain c.wl c.lay i)) (fun v => K (acc ++ [v]))) := by
  have hx := dig_lt c i
  have hg := grp_le i
  have hw := length_witChain c hc i hi
  by_cases h7 : dig c i = 7
  · obtain ⟨t, hst, hH⟩ := disp_7 c hc i hi acc h7 hchk s hs
    rw [h7]
    have : chainFrom c.lay c.tau c.e i 7 (witChain c.wl c.lay i) = pure (witChain c.wl c.lay i) := rfl
    rw [this, cc_pure]
    exact Good.steps' hst (hK _ t hw hH) (by omega) (by unfold chainCost; omega)
  · have hcf : chainFrom c.lay c.tau c.e i (dig c i) (witChain c.wl c.lay i) =
        restFold c i (dig c i + 1) (witChain c.wl c.lay i) := by
      unfold chainFrom restFold; congr 2; omega
    rw [hcf, restFold_succ c i _ (by omega), cc_bind]
    by_cases h6 : dig c i = 6
    · obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := disp_6 c hc i hi acc h6 hchk s hs
      simp only [h6, show 6 + 1 + 1 = 8 from rfl, restFold_8, cc_pure]
      have h2 : ∀ a, Good (writeHash t a) (N + (1 + grp i)) (C + (1 + grp i))
          (K (acc ++ [answerBytes 16 a])) := fun a => by
        obtain ⟨t', hst', hH⟩ := chain_end c i hi acc hchk _ _ (hpost a)
        exact Good.steps hst' (hK _ t' (by simp) hH)
      have h3 := Good.hash (K := fun v => K (acc ++ [v])) hf h5 hv hin h2
      rw [blocks_chain _ _ _ _ _ _ hw] at h3
      exact Good.steps' hst h3 (by omega) (by unfold chainCost; omega)
    · obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ :=
        disp_lt6 c hc i hi acc (dig c i) (by omega) rfl hchk s hs
      have h3 := Good.hash (K := fun v => cc (restFold c i (dig c i + 1 + 1) v) (fun v => K (acc ++ [v])))
        hf h5 hv hin (fun a =>
        steps_good c hc i hi acc hchk K N C hK (5 - dig c i) (dig c i + 2) (by omega)
          (by omega) _ _ (hpost a))
      rw [blocks_chain _ _ _ _ _ _ hw] at h3
      exact Good.steps' hst h3 (by omega) (by unfold chainCost; omega)

end SigGolfCandidate.Verify
