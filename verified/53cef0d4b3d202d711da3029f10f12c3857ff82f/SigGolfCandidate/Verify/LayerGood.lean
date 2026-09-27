import SigGolfCandidate.Verify.LeafSem
import SigGolfCandidate.Verify.Chains
import SigGolfCandidate.Verify.ChainCheckAll

/-! # One hypertree layer: the simulation judgment -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

def layerSpec (w : List Byte) (idx lay : Nat) (M : Val) : OracleComp HashSpec (Option Val) := do
  let (e, tau) := route idx lay
  let d ← hash16 (encInput lay tau e M (witCounter w lay))
  match decodeDigits d with
  | none => pure none
  | some x => do
    let leaf ← verifyLeaf w lay tau e x
    let root ← foldPath (nodeInput lay tau) e leaf (witPath w lay)
    pure (some root)

theorem verifyLayers_succ (w : List Byte) (idx lay : Nat) (M : Val) :
    verifyLayers w idx (lay + 1) M = layerSpec w idx lay M >>= fun o => match o with
      | none => pure none
      | some r => verifyLayers w idx lay r := by
  simp only [verifyLayers, layerSpec, bind_assoc]
  congr 1; funext d
  cases h : decodeDigits d <;> simp [h, bind_assoc]

def FoldEndL (L : LCtx) (u : MachineState) : Prop :=
  ∃ s0, FoldEnd (layFC L) s0 u ∧ s0.getReg .x22 = BitVec.ofNat 64 L.idx ∧
    s0.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s0.getMem (BitVec.ofNat 64 0xF8) = 0

def layerCost (lay : Nat) : Nat :=
  encSteps lay + 8 + encPostSteps lay + 1911 + leafSteps lay + 88 + (leafSteps lay - 3) +
    foldCost (layH lay) 0 (layH lay)

theorem blocks_q (n : Nat) (ws : List Word) : (queryOfWords n ws).blocks = n + 1 := rfl

theorem witPath_eq (L : LCtx) (hL : L.ok) : witPath L.wl L.lay = (layFC L).path := by
  simp only [witPath, witSib, FCtx.path, layFC, witLayerOff]
  congr 1

theorem layer_good (L : LCtx) (hL : L.ok) (M : Val) (Kopt : Option Val → OracleComp HashSpec Obs)
    (hnone : Kopt none = pure (false, 0)) (N C : Nat)
    (hK : ∀ a u, FoldEndL L u → Good (writeHash u a) N C (Kopt (some (answerBytes 16 a))))
    (s : MachineState) (hs : LayerIn L M s) :
    Good s (N + 5000) (C + layerCost L.lay) (cc (layerSpec L.wl L.idx L.lay M) Kopt) := by
  have hL' := hL
  obtain ⟨hlay, hidx, hwl⟩ := hL'
  have hMl : M.length = 16 := hs.2.2.2.2.2.1
  obtain ⟨t1, hst1, hf1, h51, hv1, hin1, hpost1⟩ := enc_step L hL M s hs
  unfold layerSpec
  rw [route_eq L.idx L.lay hlay]
  simp only []
  rw [cc_bind]
  have hH := layH_le L.lay
  have hls : leafSteps L.lay ≤ 9 := by unfold leafSteps; split <;> omega
  have heps : encPostSteps L.lay ≤ 31 := by unfold encPostSteps; split <;> omega
  have hfc := layFC_ok L hL
  have H : ∀ a, Good (writeHash t1 a) (N + 4900) (C + layerCost L.lay - encSteps L.lay - 8)
      (cc (match decodeDigits (answerBytes 16 a) with
        | none => pure none
        | some x => do
          let leaf ← verifyLeaf L.wl L.lay L.tau L.e x
          let root ← foldPath (nodeInput L.lay L.tau) L.e leaf (witPath L.wl L.lay)
          pure (some root)) Kopt) := by
    intro a
    obtain ⟨hrej, hacc⟩ := encpost_step L hL a _ (hpost1 a)
    cases hd : decodeDigits (answerBytes 16 a) with
    | none =>
      obtain ⟨k, hk, t, hst, hf, h5, h10⟩ := hrej hd
      simp only [cc_pure, hnone]
      exact Good.steps' hst (Good.reject hf h5 h10) (by omega) (by unfold layerCost; omega)
    | some xs =>
      obtain ⟨t2, hst2, hhead, hxs, hsum, hlen⟩ := hacc xs hd
      simp only [verifyLeaf, bind_assoc, cc_bind]
      set c := L.cctx a with hc
      have hcok : c.ok := ⟨hlay, by simp [hc, LCtx.cctx]; have := tau_lt L.lay L.idx hlay hidx; unfold LCtx.tau; omega,
        by simp [hc, LCtx.cctx]; have := e_lt L hL; omega, hwl⟩
      have hcost := chainsCost_eq c xs hlen hxs hsum
      -- the chains
      have hch := chains_good c hcok xs hxs (fun i hi => chainCheck_at L.lay i hlay hi)
        (fun ends => cc (hash16 (leafInput L.lay L.tau L.e ends)) (fun leaf =>
          cc (foldPath (nodeInput L.lay L.tau) L.e leaf (witPath L.wl L.lay)) (fun root =>
            cc (pure (some root)) Kopt)))
        (N + 2000) (C + 88 + leafSteps L.lay + (leafSteps L.lay - 3) + foldCost (layH L.lay) 0 (layH L.lay))
        (by
          intro ends t hH42
          obtain ⟨t3, hst3, hf3, h53, hv3, hin3, hpost3⟩ := leaf_step L hL a ends t hH42
          have hends : ends.length = 42 := hH42.2.2.2.2.2.2.2.1
          have hvs : ∀ v ∈ ends, v.length = 16 := hH42.2.2.2.2.2.2.2.2.1
          have H3 : ∀ ans, Good (writeHash t3 ans) (N + 1900)
              (C + (leafSteps L.lay - 3) + foldCost (layH L.lay) 0 (layH L.lay))
              (cc (foldPath (nodeInput L.lay L.tau) L.e (answerBytes 16 ans) (witPath L.wl L.lay))
                (fun root => cc (pure (some root)) Kopt)) := by
            intro ans
            obtain ⟨t4, hst4, hfi, h22, hF0, hF8⟩ := fsetup_step L hL _ _ (hpost3 ans)
            rw [nodeInput_eq, witPath_eq L hL,
              show nodeF 3 L.lay L.tau = (layFC L).node from rfl, show L.e = (layFC L).E from rfl,
              foldPath_eq]
            simp only [cc_pure]
            have hfold := fold_good (layFC L) hfc (layFC_check L hL) t4 (fun root => Kopt (some root))
              N C (fun a u hend => hK a u ⟨t4, hend, h22, hF0, hF8⟩) (layH L.lay) 0 (by simp [layFC])
              (by unfold layH; split <;> omega) _ _ hfi
            refine Good.steps' hst4 hfold (by omega) (by simp [layFC]; omega)
          have h3 := Good.hash (K := fun leaf => cc (foldPath (nodeInput L.lay L.tau) L.e leaf
            (witPath L.wl L.lay)) (fun root => cc (pure (some root)) Kopt)) hf3 h53 hv3 hin3 H3
          rw [pad64_leafInput _ _ _ _ hends hvs, blocks_q] at h3
          exact Good.steps' hst3 h3 (by omega) (by omega))
        42 0 rfl [] t2 hhead
      have e1 : List.range nChains = List.range' 0 42 := by rw [List.range_eq_range']; rfl
      rw [e1]
      refine Good.steps' hst2 (hch.congr ?_) (by omega) (by rw [hcost]; unfold layerCost; omega)
      rfl
  have h3 := Good.hash (K := fun d => cc (match decodeDigits d with
        | none => pure none
        | some x => do
          let leaf ← verifyLeaf L.wl L.lay L.tau L.e x
          let root ← foldPath (nodeInput L.lay L.tau) L.e leaf (witPath L.wl L.lay)
          pure (some root)) Kopt) hf1 h51 hv1 hin1 H
  rw [pad64_encInput _ _ _ _ hMl, blocks_q] at h3
  exact Good.steps' hst1 h3 (by unfold encSteps; split <;> split <;> omega)
    (by unfold layerCost; omega)

end SigGolfCandidate.Verify
