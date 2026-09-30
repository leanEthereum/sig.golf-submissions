import SigGolfCandidate.Verify.LeafSem
import SigGolfCandidate.Verify.ChainGood
import SigGolfCandidate.Verify.ChainCheckAll

/-! # Hypertree layers: the simulation judgment for one layer, all layers, and the comparison -/

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
  ∃ s0, FoldEnd (layFC L) s0 u ∧ LeafCarry L s0

def layerCost (lay : Nat) : Nat :=
  stepsA lay + 8 + stepsB lay + (42 * 67 - 9 * targetSum + headSum lay) + 11 + 88 +
    foldCost false (heightL lay) 0 (heightL lay)

theorem blocks_q (n : Nat) (ws : List Word) : (queryOfWords n ws).blocks = n + 1 := rfl

theorem witPath_eq (L : LCtx) (hL : L.lay < 5) : witPath L.wl L.lay = (layFC L).path := by
  unfold witPath FCtx.path layFC
  simp only [heightL_eq _ hL]
  apply List.map_congr_left
  intro l _
  simp [witSib, witLayerOff_eq _ hL]

theorem Good.reject {s : MachineState} (hf : fetch image s = some (.base .ECALL))
    (h5 : s.getReg .x5 = 1) (h10 : s.getReg .x10 = 1) : Good s 1 1 (pure (false, 0)) := by
  have := Good.halt hf h5
  rw [h10] at this
  exact this

theorem layer_good (L : LCtx) (hL : L.ok) (M : Val) (Kopt : Option Val → OracleComp HashSpec Obs)
    (hnone : Kopt none = pure (false, 0)) (N C : Nat)
    (hK : ∀ a u, FoldEndL L u → Good (writeHash u a) N C (Kopt (some (answerBytes 16 a))))
    (s : MachineState) (hs : LayerIn L M s) :
    Good s (N + 5000) (C + layerCost L.lay) (cc (layerSpec L.wl L.idx L.lay M) Kopt) := by
  have hL' := hL
  obtain ⟨hlay, hidx, hwl⟩ := hL'
  have hMl : M.length = 16 := hs.2.2.2.2.2.1
  obtain ⟨t, ht, t1, hst1, hf1, h51, hv1, hin1, hpost1⟩ := enc_step L hL M s hs
  unfold layerSpec
  rw [route_eq L.idx L.lay hlay]
  simp only []
  rw [cc_bind]
  have hfc := layFC_ok L hL
  have hsA : stepsA L.lay ≤ 29 := by unfold stepsA; split_ifs <;> omega
  have hsB : stepsB L.lay ≤ 40 := by unfold stepsB; split_ifs <;> omega
  have H : ∀ a, Good (writeHash t1 a) (N + 4900) (C + layerCost L.lay - stepsA L.lay - 8)
      (cc (match decodeDigits (answerBytes 16 a) with
        | none => pure none
        | some x => do
          let leaf ← verifyLeaf L.wl L.lay L.tau L.e x
          let root ← foldPath (nodeInput L.lay L.tau) L.e leaf (witPath L.wl L.lay)
          pure (some root)) Kopt) := by
    intro a
    obtain ⟨hrej, hacc⟩ := encpost_step L hL t ht a _ (hpost1 a)
    cases hd : decodeDigits (answerBytes 16 a) with
    | none =>
      obtain ⟨k, hk, u, hst, hf, h5, h10⟩ := hrej hd
      simp only [cc_pure, hnone]
      exact Good.steps' hst (Good.reject hf h5 h10) (by omega) (by unfold layerCost; omega)
    | some xs =>
      obtain ⟨t2, hst2, hent, hcok, hxs, hsum, hlen⟩ := hacc xs hd
      simp only [verifyLeaf, bind_assoc, cc_bind]
      set c := L.cctx a with hc
      have hcost : chainsCost c 0 42 = 42 * 67 - 9 * targetSum + headSum L.lay := chainsCost_eq c xs hlen hxs hsum
      have hch := chains_good0 c hcok xs hxs (fun i hi => chainCheck_at L.lay i hlay hi)
        (fun ends => cc (hash16 (leafInput L.lay L.tau L.e ends)) (fun leaf =>
          cc (foldPath (nodeInput L.lay L.tau) L.e leaf (witPath L.wl L.lay)) (fun root =>
            cc (pure (some root)) Kopt)))
        (N + 2000) (C + 88 + 11 + foldCost false (heightL L.lay) 0 (heightL L.lay))
        (by
          intro ends u hH42
          obtain ⟨t3, hst3, hf3, h53, hv3, hin3, hpost3⟩ := leaf_step L hL a ends u hH42
          have hends : ends.length = 42 := hH42.2.2.2.2.2.2.1
          have hvs : ∀ v ∈ ends, v.length = 16 := hH42.2.2.2.2.2.2.2.1
          have H3 : ∀ ans, Good (writeHash t3 ans) (N + 1900) (C + foldCost false (heightL L.lay) 0 (heightL L.lay))
              (cc (foldPath (nodeInput L.lay L.tau) L.e (answerBytes 16 ans) (witPath L.wl L.lay))
                (fun root => cc (pure (some root)) Kopt)) := by
            intro ans
            obtain ⟨hfi, hcar⟩ := hpost3 ans
            rw [nodeInput_eq, witPath_eq L hlay,
              show nodeF 3 L.lay L.tau = (layFC L).node from rfl, show L.e = (layFC L).E from rfl,
              foldPath_eq]
            simp only [cc_pure]
            have hfold := fold_good (layFC L) hfc
              ⟨rfl, by simp [layFC, Nat.mod_eq_of_lt (show L.lay < 256 by omega), heightL_eq _ hlay]⟩
              (layFC_check L hL) _ (fun root => Kopt (some root))
              N C (fun a u hend => hK a u ⟨_, hend, hcar⟩) (heightL L.lay) 0 (by simp [layFC])
              (by have := heightL_le L.lay hlay; omega) _ _ hfi
            exact hfold.mono (by have := heightL_le L.lay hlay; omega) (by simp [layFC])
          have h3 := Good.hashP (x := leafInput L.lay L.tau L.e ends) (K := fun leaf => cc (foldPath (nodeInput L.lay L.tau) L.e leaf
            (witPath L.wl L.lay)) (fun root => cc (pure (some root)) Kopt))
            (fmt_th _ _ _ _ _ _ (by decide)) hf3 h53 hv3 hin3 H3
          rw [pad64_leafInput _ _ _ _ hends hvs, blocks_q] at h3
          exact Good.steps' hst3 h3 (by omega) (by omega))
        t2 hent
      have e1 : List.range nChains = List.range 42 := rfl
      rw [e1]
      refine Good.steps' hst2 (hch.congr ?_) (by omega) (by rw [hcost]; unfold layerCost; omega)
      rfl
  have h3 := Good.hashP (x := encInput L.lay L.tau L.e M (witCounter L.wl L.lay)) (K := fun d => cc (match decodeDigits d with
        | none => pure none
        | some x => do
          let leaf ← verifyLeaf L.wl L.lay L.tau L.e x
          let root ← foldPath (nodeInput L.lay L.tau) L.e leaf (witPath L.wl L.lay)
          pure (some root)) Kopt) (fmt_th _ _ _ _ _ _ (by decide)) hf1 h51 hv1 hin1 H
  rw [pad64_encInput _ _ _ _ hMl, blocks_q] at h3
  exact Good.steps' hst1 h3 (by omega) (by unfold layerCost; omega)

/-! ## Layer transitions -/

theorem foldEnd_layerIn (wl pk : List Byte) (lay idx : Nat) (h1 : 1 ≤ lay) (h7 : lay < 5)
    (u : MachineState) (hu : FoldEndL ⟨wl, pk, lay, idx⟩ u) (a : BitVec 256) :
    LayerIn ⟨wl, pk, lay - 1, idx⟩ (answerBytes 16 a) (writeHash u a) := by
  obtain ⟨s0, ⟨hG, hK, hF, hpc, -, -⟩, ⟨h27, h15, h30, hZ, h48⟩⟩ := hu
  have hdst : (layFC ⟨wl, pk, lay, idx⟩).dst = 0x120 := by simp [layFC]; omega
  have h12 : u.getReg .x12 = BitVec.ofNat 64 0x120 := by
    rw [← hdst]; exact hK (.x12, _) (List.mem_append_right _ (List.mem_singleton_self _))
  have hK1 := (KnownOK_append.mp hK).1
  have kf : ∀ r ∈ fkeep false, (writeHash u a).getReg r = s0.getReg r := fun r hr => by
    rw [writeHash_getReg]; exact hF.1 r hr
  refine ⟨by simpa [LCtx.gk, show lay - 1 ≠ 4 by omega, layFC, FCtx.gk, gkOf] using
      Glob_writeHash hG a _ h12 (by decide), ?_, ?_, ?_, ?_, by simp, fun _ => ⟨?_, ?_⟩, ?_, ?_⟩
  · simp only [LCtx.lay, preK, if_neg (show lay - 1 ≠ 4 by omega), aK, Nat.sub_add_cancel h1]
    intro p hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with hp | hp | hp | hp | hp | hp
    · rw [writeHash_getReg]; exact hK1 p (by simp [fk, gkOf, layFC, hp])
    · subst hp; rw [writeHash_getReg]; exact hK1 _ (by simp [fk, gkOf, layFC])
    · subst hp; rw [writeHash_getReg]; exact hK1 _ (by simp [fk, gkOf, layFC])
    · subst hp; rw [writeHash_getReg]; exact h12
    · subst hp; rw [kf _ (by simp [fkeep])]; exact h27
    · subst hp; rw [kf _ (by simp [fkeep])]; exact h15
  · simp only [routeReg, routeIn, if_neg (show lay - 1 ≠ 4 by omega)]
    rw [kf _ (by simp [fkeep]), h30]
    simp only [LCtx.tau]
    rw [layS_succ (lay - 1) (by omega), Nat.sub_add_cancel h1]
  · rw [writeHash_at0 _ a _ h12 (by omega)]; exact (vw0_answer a).symm
  · rw [show (0x128 : Nat) = 0x120 + 8 from rfl, writeHash_at8 _ a _ h12 (by omega)]
    exact (vw1_answer a).symm
  · rw [writeHash_frame _ a _ _ h12 (by omega) (by omega) (by omega), hF.2 _ (by omega) (by omega)]
    exact hZ.1
  · rw [writeHash_frame _ a _ _ h12 (by omega) (by omega) (by omega), hF.2 _ (by omega) (by omega)]
    exact hZ.2
  · rw [writeHash_frame _ a _ _ h12 (by omega) (by omega) (by omega), hF.2 _ (by omega) (by omega)]
    exact h48
  · refine ⟨bitOf (layFC ⟨wl, pk, lay, idx⟩).E ((layFC ⟨wl, pk, lay, idx⟩).h - 1),
      by simp only [bitOf, nCopy, if_neg (show lay - 1 ≠ 4 by omega)]; omega, ?_⟩
    rw [writeHash_pc, hpc, pcOf_add4]
    simp only [preStart, if_neg (show lay - 1 ≠ 4 by omega), layFC, Nat.sub_add_cancel h1,
      show 3 - (lay - 1) = 4 - lay by omega]

/-! ## The final comparison -/

theorem leNat_inj : ∀ (l1 l2 : List Byte), l1.length = l2.length → leNat l1 = leNat l2 → l1 = l2
  | [], [], _, _ => rfl
  | a :: l1, b :: l2, hl, h => by
    simp only [leNat] at h
    have ha := a.isLt; have hb := b.isLt
    have h1 : a.toNat = b.toNat := by omega
    have h2 : leNat l1 = leNat l2 := by omega
    rw [BitVec.eq_of_toNat_eq h1, leNat_inj l1 l2 (by simpa using hl) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem w64_inj (l1 l2 : List Byte) (h1 : l1.length = 8) (h2 : l2.length = 8) :
    w64 l1 = w64 l2 ↔ l1 = l2 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [w64_toNat _ (by omega), w64_toNat _ (by omega)] at this
    exact leNat_inj _ _ (by omega) this
  · intro h; rw [h]

theorem val_eq_iff (M P : Val) (hM : M.length = 16) (hP : P.length = 16) :
    M = P ↔ vw0 M = w64 (P.take 8) ∧ vw1 M = w64 (P.drop 8) := by
  unfold vw0 vw1
  rw [w64_inj _ _ (by simp; omega) (by simp; omega), w64_inj _ _ (by simp; omega) (by simp; omega)]
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← List.take_append_drop 8 M, ← List.take_append_drop 8 P, h1, h2]

def FinalIn (wl pk : List Byte) (idx : Nat) (M : Val) (s : MachineState) : Prop :=
  ∃ u a, FoldEndL ⟨wl, pk, 0, idx⟩ u ∧ s = writeHash u a ∧ M = answerBytes 16 a

theorem cmp_link (t : Nat) (ht : t < 2) : lvlPc 4 t 0 10 + 6 + 1 = cmpPc t := by
  interval_cases t <;> decide

theorem compare_good (wl pk : List Byte) (hpk : pk.length = 16) (idx : Nat) (M : Val)
    (s : MachineState) (hs : FinalIn wl pk idx M s) : Good s 9 9 (pure (M == pk, 0)) := by
  obtain ⟨u, a, ⟨s0, ⟨hG, hK, hF, hpc, -, -⟩, -⟩, rfl, rfl⟩ := hs
  have hdst : (layFC ⟨wl, pk, 0, idx⟩).dst = 0x180 := by simp [layFC]
  have h12 : u.getReg .x12 = BitVec.ofNat 64 0x180 := by
    rw [← hdst]; exact hK (.x12, _) (List.mem_append_right _ (List.mem_singleton_self _))
  have hG' := Glob_writeHash hG a _ h12 (by decide)
  set tt := bitOf (layFC ⟨wl, pk, 0, idx⟩).E ((layFC ⟨wl, pk, 0, idx⟩).h - 1) with htt
  have htt2 : tt < 2 := by simp [htt, bitOf]; omega
  have hK' : KnownOK cmpK (writeHash u a) := fun p hp => by
    rw [writeHash_getReg]
    simp only [cmpK] at hp
    exact hK p (by simpa [layFC] using hp)
  have hpc' : (writeHash u a).pc = pcOf (cmpPc tt) := by
    rw [writeHash_pc, hpc, pcOf_add4, ← cmp_link tt htt2]
    rfl
  have m0 : (writeHash u a).getMem (BitVec.ofNat 64 384) = vw0 (answerBytes 16 a) :=
    (writeHash_at0 _ a _ h12 (by omega)).trans (vw0_answer a).symm
  have m1 : (writeHash u a).getMem (BitVec.ofNat 64 392) = vw1 (answerBytes 16 a) :=
    (writeHash_at8 _ a 0x180 h12 (by omega)).trans (vw1_answer a).symm
  have p0 : (writeHash u a).getMem (BitVec.ofNat 64 160) = w64 (pk.take 8) := hG'.2.2.1.1
  have p1 : (writeHash u a).getMem (BitVec.ofNat 64 168) = w64 (pk.drop 8) := hG'.2.2.1.2
  have heq := val_eq_iff (answerBytes 16 a) pk (by simp) hpk
  obtain ⟨r1, r2, r3⟩ := (lc_stream (lay := 0) (by omega) htt2).2.2.2.2 rfl
  by_cases e0 : vw0 (answerBytes 16 a) = w64 (pk.take 8)
  · by_cases e1 : vw1 (answerBytes 16 a) = w64 (pk.drop 8)
    · obtain ⟨v, hv⟩ := spec_run r1 _ hpc' hK' (by
        intro b hb
        simp only [specAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;>
          simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, m0, m1, p0, p1, e0, e1, bne_self_eq_false])
      have hb : (answerBytes 16 a == pk) = true := beq_iff_eq.mpr (heq.mpr ⟨e0, e1⟩)
      have := Good.steps hv.steps (Good.halt (hv.ecall rfl) (hv.regs (.x5, cw 1) (by simp [specAcc])))
      rw [hv.regs (.x10, cw 0) (by simp [specAcc])] at this
      rw [hb]; exact this.mono (by simp [specAcc]) (by simp [specAcc])
    · obtain ⟨v, hv⟩ := spec_run r3 _ hpc' hK' (by
        intro b hb
        simp only [specCR2, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, m1, p1]; simpa using e1
        · simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, m0, p0, e0, bne_self_eq_false])
      have hb : (answerBytes 16 a == pk) = false := by
        rw [beq_eq_false_iff_ne]; intro h; exact e1 (heq.mp h).2
      have := Good.steps hv.steps (Good.reject (hv.ecall rfl) (hv.regs (.x5, cw 1) (by simp [specCR2, rejK]))
        (hv.regs (.x10, cw 1) (by simp [specCR2, rejK])))
      rw [hb]; exact this.mono (by simp [specCR2]) (by simp [specCR2])
  · obtain ⟨v, hv⟩ := spec_run r2 _ hpc' hK' (by
      intro b hb
      simp only [specCR1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, m0, p0]; simpa using e0)
    have hb : (answerBytes 16 a == pk) = false := by
      rw [beq_eq_false_iff_ne]; intro h; exact e0 (heq.mp h).1
    have := Good.steps hv.steps (Good.reject (hv.ecall rfl) (hv.regs (.x5, cw 1) (by simp [specCR1, rejK]))
      (hv.regs (.x10, cw 1) (by simp [specCR1, rejK])))
    rw [hb]; exact this.mono (by simp [specCR1]) (by simp [specCR1])

/-! ## All layers -/

def Kfin (pk : List Byte) : Option Val → OracleComp HashSpec Obs
  | none => pure (false, 0)
  | some root => pure (root == pk, 0)

def InLayer (wl pk : List Byte) (idx : Nat) : Nat → Val → MachineState → Prop
  | 0 => FinalIn wl pk idx
  | n + 1 => LayerIn ⟨wl, pk, n, idx⟩

def layersCost : Nat → Nat
  | 0 => 9
  | n + 1 => layersCost n + layerCost n

theorem layers_good (wl pk : List Byte) (hpk : pk.length = 16) (idx : Nat) (hidx : idx < 2 ^ 34)
    (hwl : wl.length = 6348) :
    ∀ n, n ≤ 5 → ∀ M s, InLayer wl pk idx n M s →
      Good s (5000 * n + 9) (layersCost n) (cc (verifyLayers wl idx n M) (Kfin pk)) := by
  intro n
  induction n with
  | zero =>
    intro _ M s hs
    simp only [verifyLayers, cc_pure, Kfin, layersCost]
    exact compare_good wl pk hpk idx M s hs
  | succ n ih =>
    intro hn M s hs
    rw [verifyLayers_succ, cc_bind]
    have hL : (⟨wl, pk, n, idx⟩ : LCtx).ok := ⟨show n < 5 by omega, hidx, hwl⟩
    have := layer_good ⟨wl, pk, n, idx⟩ hL M
      (fun o => cc (match o with
        | none => pure none
        | some r => verifyLayers wl idx n r) (Kfin pk)) (by simp [Kfin])
      (5000 * n + 9) (layersCost n) (by
        intro a u hu
        simp only []
        apply ih (by omega)
        cases n with
        | zero => exact ⟨u, a, hu, rfl, rfl⟩
        | succ m => exact foldEnd_layerIn wl pk (m + 1) idx (by omega) (by omega) u hu a) s hs
    exact this.mono (by omega) (by dsimp only; simp only [layersCost]; omega)

end SigGolfCandidate.Verify
