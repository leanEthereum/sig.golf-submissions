import SigGolfCandidate.Verify.ForsSem
import SigGolfCandidate.Verify.LayerGood

/-! # FORS: the simulation judgment for the trees and the roots hash -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

macro "bvne" : tactic => `(tactic| (intro h; have h' := congrArg BitVec.toNat h; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at h'; omega))

theorem witFtsPath_eq (d : DCtx) (k : Nat) : witFtsPath d.wl k = (forsFC d k).path := by
  show (List.range 10).map (witFtsSib d.wl k) = (List.range 10).map fun l => slice d.wl (32 + 176 * k + 16 * l) 16
  rfl

theorem uSteps_le (k : Nat) : uSteps k ≤ 4 := by
  unfold uSteps; simp only []; split
  · split <;> omega
  · omega

theorem treeRest_good (d : DCtx) (hwl : d.wl.length = 7756) (k : Nat) (hk : k < 14)
    (roots : List Val) (Kr : Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ ans t, ForsIn d (k + 1) (roots ++ [answerBytes 16 ans]) t →
      Good t N C (Kr (answerBytes 16 ans)))
    (v : Val) (s : MachineState) (hs : LeafDoneF d k roots v s) :
    Good s (N + 143) (C + 199) (cc (foldPath (ftsNodeInput k d.idx) (d.u k) v (witFtsPath d.wl k)) Kr) := by
  obtain ⟨t, hst, hfi, hcarry, hlen⟩ := fsetupF_step d k hk roots v s hs
  rw [ftsNodeInput_eq, witFtsPath_eq, show nodeF 10 k d.idx = (forsFC d k).node from rfl,
    show d.u k = (forsFC d k).E from rfl, foldPath_eq]
  have hfold := fold_good (forsFC d k) (forsFC_ok d hwl k hk) (forsFC_check d k hk) t Kr N C
    (fun a u hend => hK a _ (tree_end d k hk roots t u hcarry hlen hend a)) 10 0 (by simp [forsFC])
    (by decide) v t hfi
  refine Good.steps' hst hfold (by simp [forsFC]) ?_
  simp only [forsFC]
  have : foldCost 10 0 10 = 196 := by decide
  omega

def treeCost (k : Nat) : Nat := headSteps k + 8 + 199

theorem tree_good (d : DCtx) (hwl : d.wl.length = 7756) (k : Nat) (hk1 : 1 ≤ k) (hk : k < 14)
    (roots : List Val) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ ans t, ForsIn d (k + 1) (roots ++ [answerBytes 16 ans]) t →
      Good t N C (K (roots ++ [answerBytes 16 ans])))
    (s : MachineState) (hs : ForsIn d k roots s) :
    Good s (N + 200) (C + treeCost k)
      (cc (do
        let r ← ftsRoot k d.idx (d.u k) (witFtsSecret d.wl k) (witFtsPath d.wl k)
        pure (roots ++ [r])) K) := by
  obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := header_step d hwl k hk1 hk roots s hs
  simp only [ftsRoot, bind_assoc, cc_bind, cc_pure]
  have hsl : (witFtsSecret d.wl k).length = 16 := by
    unfold witFtsSecret; apply length_slice16; omega
  have h3 := Good.hash (K := fun v => cc (foldPath (ftsNodeInput k d.idx) (d.u k) v (witFtsPath d.wl k))
      (fun r => K (roots ++ [r]))) hf h5 hv hin
    (fun ans => treeRest_good d hwl k hk roots (fun r => K (roots ++ [r])) N C hK _ _ (hpost ans))
  rw [pad64_ftsLeafInput _ _ _ _ hsl, blocks_q] at h3
  refine Good.steps' hst h3 (by have := uSteps_le k; unfold headSteps; omega)
    (by unfold treeCost; omega)

def forsF (d : DCtx) (roots : List Val) (k : Nat) : OracleComp HashSpec (List Val) := do
  let r ← ftsRoot k d.idx (d.u k) (witFtsSecret d.wl k) (witFtsPath d.wl k)
  pure (roots ++ [r])

def treesCost (i k : Nat) : Nat := ((List.range' i k).map treeCost).sum

theorem trees_good (d : DCtx) (hwl : d.wl.length = 7756) (K : List Val → OracleComp HashSpec Obs)
    (N C : Nat) (hK : ∀ roots t, ForsIn d 14 roots t → Good t N C (K roots)) :
    ∀ m k, k + m = 14 → 1 ≤ k → ∀ roots s, ForsIn d k roots s →
      Good s (N + 200 * m) (C + treesCost k m) (cc ((List.range' k m).foldlM (forsF d) roots) K) := by
  intro m
  induction m with
  | zero =>
    intro k hk _ roots s hs
    obtain rfl : k = 14 := by omega
    simpa [treesCost] using hK roots s hs
  | succ m ih =>
    intro k hk hk1 roots s hs
    rw [List.range'_succ, List.foldlM_cons]
    simp only [forsF, bind_assoc, pure_bind, cc_bind]
    have := tree_good d hwl k hk1 (by omega) roots
      (fun r => cc ((List.range' (k + 1) m).foldlM (forsF d) r) K) (N + 200 * m) (C + treesCost (k + 1) m)
      (fun ans t ht => ih (k + 1) (by omega) (by omega) _ t ht) s hs
    simp only [cc_bind, bind_assoc, cc_pure] at this ⊢
    refine this.mono (by omega) ?_
    simp only [treesCost, List.range'_succ, List.map_cons, List.sum_cons]
    omega

/-! ## The roots hash -/

theorem roots_good (d : DCtx) (roots : List Val) (KM : Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ ans t, LayerIn ⟨d.wl, d.pk, 6, d.idx⟩ (answerBytes 16 ans) t → Good t N C (KM (answerBytes 16 ans)))
    (s : MachineState) (hs : ForsIn d 14 roots s) :
    Good s (N + 11) (C + 42) (cc (hash16 (rootsInput d.idx roots)) KM) := by
  obtain ⟨hG, hK0, ⟨h16, h17, h25, h22, h29, h31, hC0, hC8, hF0, hF8, hRB, hrv, hR0, hR8⟩,
    hlen, hN8, hpc⟩ := hs
  have hrun := top_runs.1
  have hok : resOK rootsExp = true := by decide
  have hkn : knownB (globK ++ [(.x10, 544), (.x11, 256), (.x12, 288)]) rootsExp = true := by decide
  have hpc' : s.pc = pcOf 2085 := by rw [hpc]; rfl
  set r := rootsExp with hr
  obtain ⟨hst, hec, hglob⟩ := run_post hrun hok s hpc' hK0 (by simp [hr, rootsExp])
  have hK' := knownB_ok hkn s
  have h10 : (r.toState s).getReg .x10 = BitVec.ofNat 64 0x220 := hK' (.x10, 544) (by simp)
  have h11 : (r.toState s).getReg .x11 = BitVec.ofNat 64 (64 * (3 + 1)) := hK' (.x11, 256) (by simp)
  have h12 : (r.toState s).getReg .x12 = BitVec.ofNat 64 0x120 := hK' (.x12, 288) (by simp)
  have hidx := d_idx_lt d
  have hmem : r.st.mem = [(⟨none, BitVec.ofNat 64 544⟩, stW0 544 rw0E)] := rfl
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 0x220 →
      (r.toState s).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1
    rw [PRes.toState_getMem, memEval_frame_ofNat _ _ _ hA (by rw [hmem]; simp; omega)]
  have hvs : ∀ v ∈ roots, v.length = 16 := hrv
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have hin : hashInput (r.toState s) = pad64 (rootsInput d.idx roots) := by
    rw [hashInput_ofNat _ 0x220 3 h10 h11 (by decide) (by decide), pad64_rootsInput _ _ hlen hvs]
    congr 1
    rw [show 8 * (3 + 1) = 4 + 28 by rfl, List.range_add, List.map_append]
    congr 1
    · simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
        Nat.mul_zero, List.cons.injEq]
      refine ⟨?_, ?_, ?_, ?_, trivial⟩
      · rw [PRes.toState_getMem, hmem, memEval_cons_eq _ _ _ _ _ rfl]
        apply BitVec.eq_of_toNat_eq
        rw [show (stW0 544 rw0E).eval s = StoreKind.merge .w (s.getMem (BitVec.ofNat 64 544)) 0 (rw0E.eval s)
          from rfl, merge_w0_toNat, rw0E_eval d.idx hidx s h22]
        simp only [BitVec.toNat_ofNat, twLo]
        rw [Nat.div_eq_of_lt hR0]
        have : d.idx / 2 ^ 32 < 4 := by omega
        omega
      · rw [mfr 0x228 (by omega) (by omega), hR8]; congr 1
      · rw [mfr 0x230 (by omega) (by omega)]; exact hP _ (by decide)
      · rw [mfr 0x238 (by omega) (by omega)]; exact hP _ (by decide)
    · apply List.ext_getElem?
      intro m
      rw [List.map_map]
      by_cases hm : m < 28
      · rw [List.getElem?_map, List.getElem?_range hm, flat_get? _ _ _ _ (by rw [hlen]; omega)]
        simp only [Option.map_some, Function.comp, Option.some.injEq]
        rw [mfr _ (by omega) (by omega)]
        obtain ⟨hl0, hl1⟩ := hRB (m / 2) (by rw [hlen]; omega)
        split
        · rw [show 0x220 + 8 * (4 + m) = 0x240 + 16 * (m / 2) by omega]; exact hl0
        · rw [show 0x220 + 8 * (4 + m) = 0x248 + 16 * (m / 2) by omega]; exact hl1
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
          (by rw [length_flat, hlen]; omega)]
  have hpost : ∀ ans, Good (writeHash (r.toState s) ans) N C (KM (answerBytes 16 ans)) := by
    intro ans
    refine hK ans _ ⟨Glob_writeHash (hglob _ _ hG) ans _ h12 (by decide), ?_, ?_, ?_, ?_, by simp, ?_, ?_, ?_⟩
    · intro p hp; rw [writeHash_getReg]; exact hK' p (List.mem_append_left _ hp)
    · rw [writeHash_getReg, PRes.toState_getReg]
      have : r.st.regs.get .x22 = .reg .x22 := rfl
      rw [this]; exact h22
    · exact (writeHash_at0 _ ans _ h12 (by omega)).trans (vw0_answer ans).symm
    · rw [show (0x128 : Nat) = 0x120 + 8 from rfl]
      exact (writeHash_at8 _ ans _ h12 (by omega)).trans (vw1_answer ans).symm
    · rw [writeHash_frame _ ans _ _ h12 (by omega) (by omega) (by omega), mfr 0xF0 (by omega) (by omega)]
      exact hF0
    · rw [writeHash_frame _ ans _ _ h12 (by omega) (by omega) (by omega), mfr 0xF8 (by omega) (by omega)]
      exact hF8
    · rw [writeHash_pc, PRes.toState_pc, show r.pc = pcOf 2095 from rfl, pcOf_add4]; rfl
  have h3 := Good.hash (K := KM) (hec rfl) (hK' (.x5, 0) (by simp [globK]))
    (hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide)) hin hpost
  rw [pad64_rootsInput _ _ hlen hvs, blocks_q] at h3
  exact Good.steps' hst h3 (by simp [hr, rootsExp]) (by simp [hr, rootsExp])

end SigGolfCandidate.Verify
