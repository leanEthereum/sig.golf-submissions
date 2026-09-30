import SigGolfCandidate.Budget.Search

/-!
# Budget: the expectation bound for `signRef`

From any random-oracle cache without tweak types `4`, `7`, `12` (e.g. after keygen, which only
queries types `0..3`), the expectation of `z ^ (compressions of signRef)` is at most

  `bD * z ^ (14 * 3071 + 4) * bC ^ 7 * z ^ 72377`,

where `bD` bounds the digest search and `bC` each counter search (`V_signRef`). The deterministic
part is `42998 + 72377 = 115375` blocks.
-/

namespace SigGolfCandidate.Budget
open SigGolf SigGolfCandidate.Ref OracleComp OracleSpec ENNReal OracleComp.EvalDist

/-- Compressions of the trees of layers `0 .. n-1`. -/
def layerCost (n : Nat) : Nat := ∑ l ∈ Finset.range n, treeCost (height l)

theorem layerCost_succ (n : Nat) : layerCost (n + 1) = layerCost n + treeCost (height n) := by
  simp [layerCost, Finset.sum_range_succ]

theorem layerCost_7 : layerCost 7 = 72377 := by decide

/-- Before the layers `n-1 .. 0`: every cached counter query is of a layer `≥ n`. -/
def InvL (n : Nat) (q : Query) : Prop := qbyte q 1 = 4 → n ≤ qbyte q 2

/-- Sign's starting cache: no counter, randomizer or digest queries. -/
def Inv0 (q : Query) : Prop := qbyte q 1 ≠ 4 ∧ qbyte q 1 ≠ 7 ∧ qbyte q 1 ≠ 12

theorem V_signLayers (z bC : ℝ≥0∞) (hz : 1 ≤ z) (hbC : 1 ≤ bC)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC) (S : List Byte) (hS : S.length = 32)
    (idx : Nat) :
    ∀ lay (M : Val) (cache : RCache), lay ≤ 7 → M.length ≤ 16 → CacheInv (InvL lay) cache →
      V z (signLayers S idx lay M) cache ≤ bC ^ lay * z ^ layerCost lay := by
  intro lay
  induction lay with
  | zero => intro M cache _ _ _; simp [signLayers, layerCost]
  | succ lay ih =>
    intro M cache hlay hM hinv
    unfold signLayers
    rcases hr : route idx lay with ⟨e, tau⟩
    dsimp only
    have hfresh : ∀ c', 0 ≤ c' → c' < 2 ^ 32 →
        cache (pad64 (encInput lay tau e M c')) = none := by
      intro c' _ _
      cases hq : cache (pad64 (encInput lay tau e M c')) with
      | none => rfl
      | some u =>
        exfalso
        have h := hinv _ u hq (by unfold encInput; rw [qbyte_tag])
        unfold encInput at h; rw [qbyte_lay] at h; omega
    refine (V_bind_le z _ _ cache (bC ^ lay * z ^ (treeCost (height lay) + layerCost lay))
      fun x hx => ?_).trans ?_
    · have hx' := (spec_searchCounter lay tau e M hM (by omega) cMax 0).support
        (I := InvL lay) (fun q hq h => by rw [hq.2]) cache
        (hinv.mono fun q h h4 => by have := h h4; omega) x hx
      obtain ⟨o, c1⟩ := x
      have hbig : 1 ≤ bC ^ lay * z ^ (treeCost (height lay) + layerCost lay) :=
        one_le_mul (one_le_pow₀ hbC) (one_le_pow₀ hz)
      rcases o with _ | ⟨c, xs⟩
      · simpa using hbig
      · dsimp only
        refine (V_bind_le z _ _ c1 (bC ^ lay * z ^ layerCost lay) fun y hy => ?_).trans ?_
        · have hy' := (spec_buildTree S hS lay tau (height lay) e xs).support
            (I := InvL lay) (fun q hq h => by unfold PT at hq; omega) c1 hx'.2 y hy
          obtain ⟨⟨root, vals, path⟩, c2⟩ := y
          dsimp only
          refine (V_bind_le z _ _ c2 1 fun w _ => ?_).trans ?_
          · obtain ⟨r, _⟩ := w
            rcases r with _ | rest <;> simp
          · rw [mul_one]; exact ih root c2 (by omega) hy'.1 hy'.2
        · rw [pow_add]
          calc V z (buildTree S lay tau (height lay) e xs) c1 * (bC ^ lay * z ^ layerCost lay)
              ≤ z ^ treeCost (height lay) * (bC ^ lay * z ^ layerCost lay) :=
                mul_le_mul' ((spec_buildTree S hS lay tau (height lay) e xs).V_le hz c1) le_rfl
            _ = bC ^ lay * (z ^ treeCost (height lay) * z ^ layerCost lay) := by ring
    · rw [layerCost_succ, pow_succ]
      calc V z (searchCounter lay tau e M 0 cMax) cache *
            (bC ^ lay * z ^ (treeCost (height lay) + layerCost lay))
          ≤ bC * (bC ^ lay * z ^ (treeCost (height lay) + layerCost lay)) :=
            mul_le_mul' (V_searchCounter z bC hz hbC hstepC lay tau e M hM cMax 0 cache
              (by simp [cMax]) hfresh) le_rfl
        _ = bC ^ lay * bC * z ^ (layerCost lay + treeCost (height lay)) := by
            rw [Nat.add_comm]; ring

set_option maxRecDepth 100000 in
/-- The expectation bound for `signList` from a cache satisfying `Inv0`. -/
theorem V_signList (z bD bC : ℝ≥0∞) (hz : 1 ≤ z) (hbD : 1 ≤ bD) (hbC : 1 ≤ bC)
    (hstepD : z ^ 4 * ((epsD + rhoD) * bD + (1 - rhoD)) ≤ bD)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC)
    (S m : List Byte) (hS : S.length = 32) (hm : m.length = 32) (cache : RCache)
    (hinv : CacheInv Inv0 cache) :
    V z (signList S m) cache ≤ bD * (z ^ (14 * 3071 + 4) * (bC ^ 7 * z ^ 72377)) := by
  unfold signList
  have hbig : 1 ≤ z ^ (14 * 3071 + 4) * (bC ^ 7 * z ^ 72377) :=
    one_le_mul (one_le_pow₀ hz) (one_le_mul (one_le_pow₀ hbC) (one_le_pow₀ hz))
  refine (V_bind_le z _ _ cache _ fun x hx => ?_).trans (mul_le_mul' ?_ le_rfl)
  · have hx' := (spec_searchDigest S m hS hm aMax 0).support
      (I := fun q => qbyte q 1 ≠ 4) (fun q hq => by unfold PD at hq; omega) cache
      (hinv.mono fun q h => h.1) x hx
    obtain ⟨o, c1⟩ := x
    rcases o with _ | ⟨rho, N⟩
    · simpa using hbig
    · dsimp only
      refine (V_bind_le z _ _ c1 (z ^ 4 * (bC ^ 7 * z ^ 72377)) fun y hy => ?_).trans ?_
      · have hy' := (spec_signFors S hS N).support (I := fun q => qbyte q 1 ≠ 4)
          (fun q hq => by unfold PF at hq; omega) c1 hx'.2 y hy
        obtain ⟨⟨fors, roots⟩, c2⟩ := y
        dsimp only
        obtain ⟨hp1, hp2⟩ := roots_ok (idxOf N) roots hy'.1.1 hy'.1.2
        refine (V_bind_le z _ _ c2 (bC ^ 7 * z ^ 72377) fun w hw => ?_).trans ?_
        · have hw' := (spec_hash16 (P := PF) (rootsInput (idxOf N) roots) 4 hp1 hp2).support
            (I := fun q => qbyte q 1 ≠ 4) (fun q hq => by unfold PF at hq; omega) c2 hy'.2 w hw
          obtain ⟨M, c3⟩ := w
          refine (V_bind_le z _ _ c3 1 fun r _ => ?_).trans ?_
          · obtain ⟨r, _⟩ := r
            rcases r with _ | lays <;> simp
          · rw [mul_one, ← layerCost_7]
            refine V_signLayers z bC hz hbC hstepC S hS (idxOf N) nLayers M c3 (by decide)
              (by rw [hw'.1]) ?_
            exact hw'.2.mono fun q h h4 => absurd h4 h
        · exact mul_le_mul' ((spec_hash16 (P := PF) _ 4 hp1 hp2).V_le hz c2) le_rfl
      · rw [pow_add, mul_assoc]
        refine mul_le_mul' ?_ le_rfl
        rw [← ftsCost_10]
        exact (spec_signFors S hS N).V_le hz c1
  · refine V_searchDigest z bD hz hbD hstepD S m hS hm aMax 0 cache ∅ (by simp [aMax]) (by simp)
      (fun a' _ _ => ?_) (fun rho _ _ => ?_)
    · cases hq : cache (pad64 (rndInput S m a')) with
      | none => rfl
      | some u =>
        exfalso; have := (hinv _ u hq).2.1; unfold rndInput at this; rw [qbyte_tag] at this
        exact this rfl
    · cases hq : cache (pad64 (digestInput rho m)) with
      | none => rfl
      | some u =>
        exfalso; have := (hinv _ u hq).2.2; unfold digestInput at this; rw [qbyte_tag] at this
        exact this rfl

theorem V_signRef (z bD bC : ℝ≥0∞) (hz : 1 ≤ z) (hbD : 1 ≤ bD) (hbC : 1 ≤ bC)
    (hstepD : z ^ 4 * ((epsD + rhoD) * bD + (1 - rhoD)) ≤ bD)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC)
    (sk m : Bytes 32) (cache : RCache) (hinv : CacheInv Inv0 cache) :
    V z (signRef sk m) cache ≤ bD * (z ^ (14 * 3071 + 4) * (bC ^ 7 * z ^ 72377)) := by
  unfold signRef
  refine (V_bind_le z _ _ cache 1 fun _ _ => by simp).trans ?_
  rw [mul_one]
  exact V_signList z bD bC hz hbD hbC hstepD hstepC _ _ (length_toList sk) (length_toList m)
    cache hinv

end SigGolfCandidate.Budget
