import SigGolfCandidate.Verify.ForsSem

/-! # FORS: the simulation judgment for the trees and the roots hash -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

theorem witFtsPath_eq (d : DCtx) (k : Nat) : witFtsPath d.wl k = (forsFC d k).path := by
  show (List.range 10).map (witFtsSib d.wl k) = (List.range 10).map fun l => slice d.wl (32 + 176 * k + 16 * l) 16
  rfl

theorem uSteps_le (k : Nat) : uSteps k ≤ 4 := by
  unfold uSteps; simp only []; split
  · split <;> omega
  · omega

theorem foldCost_fors : foldCost 10 0 10 = 178 := by decide

theorem treeRest_good (d : DCtx) (hwl : d.wl.length = 7756) (k : Nat) (hk : k < 14)
    (roots : List Val) (Kr : Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ ans t, ForsIn d (k + 1) (roots ++ [answerBytes 16 ans]) t →
      Good t N C (Kr (answerBytes 16 ans)))
    (v : Val) (s : MachineState) (hs : LeafF d k roots v s) :
    Good s (N + 140) (C + 178) (cc (foldPath (ftsNodeInput k d.idx) (d.u k) v (witFtsPath d.wl k)) Kr) := by
  obtain ⟨hfi, hcarry, hlen⟩ := hs
  rw [ftsNodeInput_eq, witFtsPath_eq, show nodeF 10 k d.idx = (forsFC d k).node from rfl,
    show d.u k = (forsFC d k).E from rfl, foldPath_eq]
  have hfold := fold_good (forsFC d k) (forsFC_ok d hwl k hk) (forsFC_check d k hk) s Kr N C
    (fun a u hend => hK a _ (tree_end d k hk roots s u hcarry hlen hend a)) 10 0 (by simp [forsFC])
    (by decide) v s hfi
  simpa [forsFC, foldCost_fors] using hfold

def treeCost (k : Nat) : Nat := treeSteps k + 8 + 178

theorem tree_good (d : DCtx) (hwl : d.wl.length = 7756) (k : Nat) (hk1 : 1 ≤ k) (hk : k < 14)
    (roots : List Val) (K : List Val → OracleComp HashSpec Obs) (N C : Nat)
    (hK : ∀ ans t, ForsIn d (k + 1) (roots ++ [answerBytes 16 ans]) t →
      Good t N C (K (roots ++ [answerBytes 16 ans])))
    (s : MachineState) (hs : ForsIn d k roots s) :
    Good s (N + 200) (C + treeCost k)
      (cc (do
        let r ← ftsRoot k d.idx (d.u k) (witFtsSecret d.wl k) (witFtsPath d.wl k)
        pure (roots ++ [r])) K) := by
  obtain ⟨t, hst, hf, h5, hv, hin, hpost⟩ := tree_leaf d hwl k hk1 hk roots s hs
  simp only [ftsRoot, bind_assoc, cc_bind, cc_pure]
  have hsl : (witFtsSecret d.wl k).length = 16 := by
    unfold witFtsSecret; apply length_slice16; omega
  have h3 := Good.hash (K := fun v => cc (foldPath (ftsNodeInput k d.idx) (d.u k) v (witFtsPath d.wl k))
      (fun r => K (roots ++ [r]))) hf h5 hv hin
    (fun ans => treeRest_good d hwl k hk roots (fun r => K (roots ++ [r])) N C hK _ _ (hpost ans))
  rw [pad64_ftsLeafInput _ _ _ _ hsl, blocks_q] at h3
  refine Good.steps' hst h3 (by have := uSteps_le k; unfold treeSteps; split <;> omega)
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
    Good s (N + 6) (C + 5 + 32) (cc (hash16 (rootsInput d.idx roots)) KM) := by
  obtain ⟨hG, hK0, ⟨h16, h17, h25, h22, h29, h27, hC0, hC8, hF0, hF8, hRB, hrv, hR0, hR8⟩,
    hlen, hN8, t, ht, hpc⟩ := hs
  have hsp : specB gkF (runAt (fK 13) [] (tEnd 13 t) []) (specRoots t) a6K forsKeep = true := by
    have := rootsCheck_ok
    simp only [rootsCheck, List.all_eq_true, List.mem_range] at this
    exact this t ht
  obtain ⟨u, hu⟩ := spec_run hsp s hpc hK0 (by simp [specRoots])
  have hK' := hu.known
  have h10 : u.getReg .x10 = BitVec.ofNat 64 0x220 := hK' (.x10, 544) (by simp [a6K])
  have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (3 + 1)) := hK' (.x11, 256) (by simp [a6K])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 0xE0 := hK' (.x12, 224) (by simp [a6K])
  have hidx := d_idx_lt d
  have mfr : ∀ A, u.getMem A = s.getMem A := fun A => by rw [hu.mem]; rfl
  have hvs : ∀ v ∈ roots, v.length = 16 := hrv
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have hin : hashInput u = pad64 (rootsInput d.idx roots) := by
    rw [hashInput_ofNat _ 0x220 3 h10 h11 (by decide) (by decide), pad64_rootsInput _ _ hlen hvs]
    congr 1
    rw [show 8 * (3 + 1) = 4 + 28 by rfl, List.range_add, List.map_append]
    congr 1
    · simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
        Nat.mul_zero, List.cons.injEq]
      refine ⟨?_, ?_, ?_, ?_, trivial⟩
      · rw [mfr, hR0]; congr 1; unfold twLo
        have : d.idx / 2 ^ 32 < 4 := by omega
        omega
      · rw [mfr, hR8]; congr 1
      · rw [mfr]; exact hP _ (by decide)
      · rw [mfr]; exact hP _ (by decide)
    · apply List.ext_getElem?
      intro m
      rw [List.map_map]
      by_cases hm : m < 28
      · rw [List.getElem?_map, List.getElem?_range hm, flat_get? _ _ _ _ (by rw [hlen]; omega)]
        simp only [Option.map_some, Function.comp, Option.some.injEq]
        rw [mfr]
        obtain ⟨hl0, hl1⟩ := hRB (m / 2) (by rw [hlen]; omega)
        split
        · rw [show 0x220 + 8 * (4 + m) = 0x240 + 16 * (m / 2) by omega]; exact hl0
        · rw [show 0x220 + 8 * (4 + m) = 0x248 + 16 * (m / 2) by omega]; exact hl1
      · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none
          (by rw [length_flat, hlen]; omega)]
  have hpost : ∀ ans, Good (writeHash u ans) N C (KM (answerBytes 16 ans)) := by
    intro ans
    refine hK ans _ ⟨Glob_writeHash (hu.glob _ _ _ hG) ans _ h12 (by decide), ?_, ?_, ?_, ?_, by simp, ?_⟩
    · intro p hp; rw [writeHash_getReg]; exact hK' p (by simpa [preK] using hp)
    · simp only [routeReg, routeIn, if_true]
      rw [writeHash_getReg, hu.keep .x22 (by simp [forsKeep])]; exact h22
    · exact (writeHash_at0 _ ans _ h12 (by omega)).trans (vw0_answer ans).symm
    · rw [show (0xE8 : Nat) = 0xE0 + 8 from rfl]
      exact (writeHash_at8 _ ans _ h12 (by omega)).trans (vw1_answer ans).symm
    · refine ⟨t, ht, ?_⟩
      rw [writeHash_pc, hu.pc rfl, pcOf_add4]; rfl
  have h3 := Good.hash (K := KM) (hu.ecall rfl) (hK' (.x5, 0) (by simp [a6K, gkF, baseK]))
    (hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega) (by decide)) hin hpost
  rw [pad64_rootsInput _ _ hlen hvs, blocks_q] at h3
  exact Good.steps' hu.steps h3 (by simp [specRoots]) (by simp [specRoots])

end SigGolfCandidate.Verify
