import SigGolfCandidate.Budget.Search

/-!
# Budget: the expectation bound for `signRef` (v4: MAC check, cached top tree)

From any random-oracle cache without tweak types `4`, `7`, `12` (e.g. after keygen, which only
queries types `0..3`, `13`, `14`), and for **every** cache argument, the expectation of
`z ^ (compressions of signRef sk cache m)` is at most

  `z ^ 1025 * (bD * (z ^ (14 * 3071 + 4) * (bC ^ 6 * z ^ (44539 + 239))))`,

where `bD` bounds the digest search and `bC` each of the 6 counter searches (`V_signRef`). The
deterministic part is MAC 1025 + FORS 42998 + layers 1..5 44539 + top layer 239 = 88801 blocks
(top layer: 42 secrets, `targetSum = 186` chain steps, 11 masks).
-/

namespace SigGolfCandidate.Budget
open SigGolf SigGolfCandidate.Ref OracleComp OracleSpec ENNReal OracleComp.EvalDist Finset

/-- Compressions of the trees of layers `1 .. n`. -/
def layerCost (n : Nat) : Nat := ∑ l ∈ Finset.range n, treeCost (height (l + 1))

theorem layerCost_succ (n : Nat) : layerCost (n + 1) = layerCost n + treeCost (height (n + 1)) := by
  simp [layerCost, Finset.sum_range_succ]

theorem layerCost_5 : layerCost 5 = 44539 := by decide

/-- Before the layers `n-1 .. 0`: every cached counter query is of a layer `≥ n`. -/
def InvL (n : Nat) (q : Query) : Prop := qbyte q 1 = 4 → n ≤ qbyte q 2

/-- Sign's starting cache: no counter, randomizer or digest queries. -/
def Inv0 (q : Query) : Prop := qbyte q 1 ≠ 4 ∧ qbyte q 1 ≠ 7 ∧ qbyte q 1 ≠ 12

/-! ## The top layer -/

theorem sum_getD (x : List Nat) : ∑ i ∈ range x.length, x.getD i 0 = x.sum := by
  induction x with
  | nil => simp
  | cons a x ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    omega

theorem spec_chainTo (S : List Byte) (hS : S.length = 32) (lay tau e i x : Nat) :
    Spec (fun _ => True) (fun v : Val => v.length ≤ 16) (1 + x) (chainTo S lay tau e i x) := by
  unfold chainTo
  refine spec_hash16_bind _ trivial (prf_ok S hS lay tau e i).2 (fun v hv => ?_) le_rfl
  refine Spec.foldlM_range'_le (P := fun _ => True) 1 x _ (fun _ (w : Val) => w.length ≤ 16)
    (fun _ => 1) v (by omega) (fun i' _ w hw => ?_) (fun _ h => h) (by simp)
  exact spec_hash16_bind (chainInput lay tau e i (1 + i') w) trivial
    (blocks_fmt_le _ 1 (by simp [chainInput]; omega) le_rfl)
    (fun w' hw' => Spec.pure _ 0 (by omega)) le_rfl

theorem spec_topPath (S cache : List Byte) (hS : S.length = 32) (e : Nat) :
    Spec (fun _ => True) (fun _ => True) 11 (topPath S cache e) := by
  unfold topPath
  rw [topH_eq]
  refine Spec.foldlM_range_le (P := fun _ => True) 11 _ (fun _ (_ : List Val) => True)
    (fun _ => 1) [] trivial (fun l _ acc _ => ?_) (fun _ _ => trivial) (by simp)
  exact spec_hash16_bind _ trivial (mask_ok S hS l _).2 (fun _ _ => Spec.pure _ 0 trivial) le_rfl

/-- Compressions of the top layer after its counter search. -/
def topCost : Nat := 42 + 186 + 11

theorem V_signTop (z bC : ℝ≥0∞) (hz : 1 ≤ z) (hbC : 1 ≤ bC)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC) (S cache : List Byte) (hS : S.length = 32)
    (idx : Nat) (M : Val) (c : RCache) (hM : M.length ≤ 16) (hinv : CacheInv (InvL 1) c) :
    V z (signTop S cache idx M) c ≤ bC * z ^ topCost := by
  unfold signTop
  rcases hr : route idx 0 with ⟨e, tau⟩
  dsimp only
  have hfresh : ∀ c', 0 ≤ c' → c' < 2 ^ 32 → c (fmt (encInput 0 tau e M c')) = none := by
    intro c' _ _
    cases hq : c (fmt (encInput 0 tau e M c')) with
    | none => rfl
    | some u =>
      exfalso
      have h := hinv _ u hq (by unfold encInput; rw [qbyte_tag])
      unfold encInput at h; rw [qbyte_lay] at h; omega
  refine (V_bind_le z _ _ c (z ^ topCost) fun x hx => ?_).trans
    (mul_le_mul' (V_searchCounter z bC hz hbC hstepC 0 tau e M hM cMax 0 c (by simp [cMax])
      hfresh) le_rfl)
  have hx' := (spec_searchCounter 0 tau e M hM (by omega) cMax 0).support
    (I := fun _ => True) (fun _ _ => trivial) c (fun _ _ _ => trivial) x hx
  obtain ⟨o, c1⟩ := x
  rcases o with _ | ⟨cnt, xs⟩
  · simpa using one_le_pow₀ hz
  · dsimp only
    obtain ⟨hlen, hsum⟩ := hx'.1 cnt xs rfl
    refine Spec.V_le (P := fun _ => True) (Post := fun _ => True) ?_ hz c1
    refine Spec.bind' (l := 11) (Spec.foldlM_range (P := fun _ => True) nChains _
      (fun _ (_ : List Val) => True) (fun i => 1 + xs.getD i 0) [] trivial
      (fun i _ acc _ => ?_)) (fun vals _ => ?_) ?_
    · exact (spec_chainTo S hS 0 tau e i (xs.getD i 0)).bind' (l := 0)
        (fun _ _ => Spec.pure _ 0 trivial) (by omega)
    · exact (spec_topPath S cache hS e).bind' (l := 0) (fun _ _ => Spec.pure _ 0 trivial) le_rfl
    · have h42 : nChains = xs.length := by rw [hlen]; rfl
      rw [Finset.sum_add_distrib, h42, sum_getD, hsum]
      simp [topCost, targetSum, hlen]

theorem V_signLayers (z bC : ℝ≥0∞) (hz : 1 ≤ z) (hbC : 1 ≤ bC)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC) (S cache : List Byte) (hS : S.length = 32)
    (idx : Nat) :
    ∀ lay (M : Val) (c : RCache), lay ≤ 5 → M.length ≤ 16 → CacheInv (InvL (lay + 1)) c →
      V z (signLayers S cache idx lay M) c ≤ bC ^ (lay + 1) * z ^ (layerCost lay + topCost) := by
  intro lay
  induction lay with
  | zero =>
    intro M c _ hM hinv
    simp only [signLayers, layerCost, Finset.range_zero, Finset.sum_empty, Nat.zero_add, pow_one]
    exact V_signTop z bC hz hbC hstepC S cache hS idx M c hM hinv
  | succ lay ih =>
    intro M cache' hlay hM hinv
    unfold signLayers
    rcases hr : route idx (lay + 1) with ⟨e, tau⟩
    dsimp only
    have hfresh : ∀ c', 0 ≤ c' → c' < 2 ^ 32 →
        cache' (fmt (encInput (lay + 1) tau e M c')) = none := by
      intro c' _ _
      cases hq : cache' (fmt (encInput (lay + 1) tau e M c')) with
      | none => rfl
      | some u =>
        exfalso
        have h := hinv _ u hq (by unfold encInput; rw [qbyte_tag])
        unfold encInput at h; rw [qbyte_lay] at h; omega
    refine (V_bind_le z _ _ cache' (bC ^ (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost))) fun x hx => ?_).trans ?_
    · have hx' := (spec_searchCounter (lay + 1) tau e M hM (by omega) cMax 0).support
        (I := InvL (lay + 1)) (fun q hq h => by rw [hq.2]) cache'
        (hinv.mono fun q h h4 => by have := h h4; omega) x hx
      obtain ⟨o, c1⟩ := x
      have hbig : 1 ≤ bC ^ (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost)) := one_le_mul (one_le_pow₀ hbC) (one_le_pow₀ hz)
      rcases o with _ | ⟨cnt, xs⟩
      · simpa using hbig
      · dsimp only
        refine (V_bind_le z _ _ c1 (bC ^ (lay + 1) * z ^ (layerCost lay + topCost))
          fun y hy => ?_).trans ?_
        · have hy' := (spec_buildTree S hS (lay + 1) tau (height (lay + 1)) e xs).support
            (I := InvL (lay + 1)) (fun q hq h => by unfold PT at hq; omega) c1 hx'.2 y hy
          obtain ⟨⟨root, vals, path⟩, c2⟩ := y
          dsimp only
          refine (V_bind_le z _ _ c2 1 fun w _ => ?_).trans ?_
          · obtain ⟨r, _⟩ := w
            rcases r with _ | rest <;> simp
          · rw [mul_one]; exact ih root c2 (by omega) hy'.1 hy'.2
        · rw [pow_add z (treeCost (height (lay + 1))) (layerCost lay + topCost)]
          calc V z (buildTree S (lay + 1) tau (height (lay + 1)) e xs) c1 *
                (bC ^ (lay + 1) * z ^ (layerCost lay + topCost))
              ≤ z ^ treeCost (height (lay + 1)) * (bC ^ (lay + 1) * z ^ (layerCost lay + topCost)) :=
                mul_le_mul' ((spec_buildTree S hS (lay + 1) tau (height (lay + 1)) e xs).V_le hz c1)
                  le_rfl
            _ = bC ^ (lay + 1) * (z ^ treeCost (height (lay + 1)) *
                  z ^ (layerCost lay + topCost)) := by ring
    · rw [layerCost_succ]
      calc V z (searchCounter (lay + 1) tau e M 0 cMax) cache' * (bC ^ (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost)))
          ≤ bC * (bC ^ (lay + 1) * z ^ (treeCost (height (lay + 1)) + (layerCost lay + topCost))) :=
            mul_le_mul' (V_searchCounter z bC hz hbC hstepC (lay + 1) tau e M hM cMax 0 cache'
              (by simp [cMax]) hfresh) le_rfl
        _ = bC ^ (lay + 1 + 1) * z ^ (layerCost lay + treeCost (height (lay + 1)) + topCost) := by
            rw [show layerCost lay + treeCost (height (lay + 1)) + topCost =
              treeCost (height (lay + 1)) + (layerCost lay + topCost) by omega]
            ring

theorem spec_H {P : Query → Prop} (x : List Byte) (k : Nat) (hP : P (fmt x))
    (hk : (fmt x).blocks ≤ k) : Spec P (fun _ => True) k (Ref.H x) := by
  rw [← bind_pure (Ref.H x)]
  exact Spec.qry_bind hP (fun u => Spec.pure _ 0 trivial) (by omega)

theorem regionBytes_eq : regionBytes = 65504 := by decide

theorem mac_ok (S cache : List Byte) (hS : S.length = 32) :
    qbyte (fmt (macInput S (cacheRegion cache))) 1 = 14 ∧
      (fmt (macInput S (cacheRegion cache))).blocks ≤ 1025 := by
  refine ⟨by unfold macInput; rw [qbyte_tag], blocks_fmt_le _ 1025 ?_ (by omega)⟩
  have : (cacheRegion cache).length ≤ 65504 := by
    unfold cacheRegion slice; rw [List.length_take, ← regionBytes_eq]; omega
  simp only [macInput, length_thInput, length_tweak, List.length_append, hS]; omega

/-- The signing bound without the MAC check. -/
noncomputable abbrev signBound (z bD bC : ℝ≥0∞) : ℝ≥0∞ :=
  bD * (z ^ (14 * 3071 + 4) * (bC ^ 6 * z ^ (44539 + 239)))

set_option maxRecDepth 100000 in
/-- The expectation bound for the part of `signList` after the MAC check, from `Inv0`. -/
theorem V_signBody (z bD bC : ℝ≥0∞) (hz : 1 ≤ z) (hbD : 1 ≤ bD) (hbC : 1 ≤ bC)
    (hstepD : z ^ 4 * ((epsD + rhoD) * bD + (1 - rhoD)) ≤ bD)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC)
    (S cache m : List Byte) (hS : S.length = 32) (hm : m.length = 32) (c : RCache)
    (hinv : CacheInv Inv0 c) :
    V z (do
      match ← searchDigest S m 0 aMax with
      | none => pure none
      | some (rho, N) =>
        let (fors, roots) ← signFors S N
        let M ← hash16 (rootsInput (idxOf N) roots)
        match ← signLayers S cache (idxOf N) (nLayers - 1) M with
        | none => pure none
        | some lays => pure (some (serialize rho fors lays))) c ≤ signBound z bD bC := by
  have hbig : 1 ≤ z ^ (14 * 3071 + 4) * (bC ^ 6 * z ^ (44539 + 239)) :=
    one_le_mul (one_le_pow₀ hz) (one_le_mul (one_le_pow₀ hbC) (one_le_pow₀ hz))
  refine (V_bind_le z _ _ c _ fun x hx => ?_).trans (mul_le_mul' ?_ le_rfl)
  · have hx' := (spec_searchDigest S m hS hm aMax 0).support
      (I := fun q => qbyte q 1 ≠ 4) (fun q hq => by unfold PD at hq; omega) c
      (hinv.mono fun q h => h.1) x hx
    obtain ⟨o, c1⟩ := x
    rcases o with _ | ⟨rho, N⟩
    · simpa using hbig
    · dsimp only
      refine (V_bind_le z _ _ c1 (z ^ 4 * (bC ^ 6 * z ^ (44539 + 239))) fun y hy => ?_).trans ?_
      · have hy' := (spec_signFors S hS N).support (I := fun q => qbyte q 1 ≠ 4)
          (fun q hq => by unfold PF at hq; omega) c1 hx'.2 y hy
        obtain ⟨⟨fors, roots⟩, c2⟩ := y
        dsimp only
        obtain ⟨hp1, hp2⟩ := roots_ok (idxOf N) roots hy'.1.1 hy'.1.2
        refine (V_bind_le z _ _ c2 (bC ^ 6 * z ^ (44539 + 239)) fun w hw => ?_).trans ?_
        · have hw' := (spec_hash16 (P := PF) (rootsInput (idxOf N) roots) 4 hp1 hp2).support
            (I := fun q => qbyte q 1 ≠ 4) (fun q hq => by unfold PF at hq; omega) c2 hy'.2 w hw
          obtain ⟨M, c3⟩ := w
          refine (V_bind_le z _ _ c3 1 fun r _ => ?_).trans ?_
          · obtain ⟨r, _⟩ := r
            rcases r with _ | lays <;> simp
          · rw [mul_one, ← layerCost_5, show (239 : Nat) = topCost from rfl]
            refine V_signLayers z bC hz hbC hstepC S cache hS (idxOf N) (nLayers - 1) M c3
              (by decide) (by rw [hw'.1]) ?_
            exact hw'.2.mono fun q h h4 => absurd h4 h
        · exact mul_le_mul' ((spec_hash16 (P := PF) _ 4 hp1 hp2).V_le hz c2) le_rfl
      · rw [pow_add z (14 * 3071) 4, mul_assoc]
        refine mul_le_mul' ?_ le_rfl
        rw [← ftsCost_10]
        exact (spec_signFors S hS N).V_le hz c1
  · refine V_searchDigest z bD hz hbD hstepD S m hS hm aMax 0 c ∅ (by simp [aMax]) (by simp)
      (fun a' _ _ => ?_) (fun rho _ _ => ?_)
    · cases hq : c (fmt (rndInput S m a')) with
      | none => rfl
      | some u =>
        exfalso; have := (hinv _ u hq).2.1; unfold rndInput at this; rw [qbyte_tag] at this
        exact this rfl
    · cases hq : c (fmt (digestInput rho m)) with
      | none => rfl
      | some u =>
        exfalso; have := (hinv _ u hq).2.2; unfold digestInput at this; rw [qbyte_tag] at this
        exact this rfl

/-- The expectation bound for `signList` (MAC check first), for every cache argument. -/
theorem V_signList (z bD bC : ℝ≥0∞) (hz : 1 ≤ z) (hbD : 1 ≤ bD) (hbC : 1 ≤ bC)
    (hstepD : z ^ 4 * ((epsD + rhoD) * bD + (1 - rhoD)) ≤ bD)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC)
    (S cache m : List Byte) (hS : S.length = 32) (hm : m.length = 32) (c : RCache)
    (hinv : CacheInv Inv0 c) :
    V z (signList S cache m) c ≤ z ^ 1025 * signBound z bD bC := by
  unfold signList
  obtain ⟨h1, h2⟩ := mac_ok S cache hS
  have hspec := spec_H (P := fun q => qbyte q 1 = 14) (macInput S (cacheRegion cache)) 1025 h1 h2
  refine (V_bind_le z _ _ c _ fun x hx => ?_).trans (mul_le_mul' (hspec.V_le hz c) le_rfl)
  have hx' := hspec.support (I := Inv0) (fun q hq => by unfold Inv0; omega) c hinv x hx
  dsimp only
  split
  · exact V_signBody z bD bC hz hbD hbC hstepD hstepC S cache m hS hm x.2 hx'.2
  · simp only [V_pure]
    exact one_le_mul hbD (one_le_mul (one_le_pow₀ hz) (one_le_mul (one_le_pow₀ hbC)
      (one_le_pow₀ hz)))

theorem V_signRef (z bD bC : ℝ≥0∞) (hz : 1 ≤ z) (hbD : 1 ≤ bD) (hbC : 1 ≤ bC)
    (hstepD : z ^ 4 * ((epsD + rhoD) * bD + (1 - rhoD)) ≤ bD)
    (hstepC : z * (rhoC * bC + (1 - rhoC)) ≤ bC)
    (sk : Bytes 32) (cache : Cache) (m : Bytes 32) (c : RCache) (hinv : CacheInv Inv0 c) :
    V z (signRef sk cache m) c ≤ z ^ 1025 * signBound z bD bC := by
  unfold signRef
  refine (V_bind_le z _ _ c 1 fun _ _ => by simp).trans ?_
  rw [mul_one]
  exact V_signList z bD bC hz hbD hbC hstepD hstepC _ _ _ (length_toList sk) (length_toList m)
    c hinv

end SigGolfCandidate.Budget
