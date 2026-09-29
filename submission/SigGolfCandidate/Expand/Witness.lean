import SigGolfCandidate.Expand.CopyRun
import SigGolfCandidate.Expand.RefFacts

/-!
# `expand`: the witness bytes

`witness_bytes` : the byte view left by the copy phase is `witnessList sig v vs segs`
(`ref.expand`'s witness) on the 6348 witness bytes, given the byte view before the phase
(signature bytes, the segment stream, zero at the unused pi byte).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Ref

theorem getD_app (l1 l2 : List Byte) (i : Nat) :
    (l1 ++ l2).getD i 0 = if i < l1.length then l1.getD i 0 else l2.getD (i - l1.length) 0 := by
  split
  · exact List.getD_append _ _ _ _ (by assumption)
  · exact List.getD_append_right _ _ _ _ (by omega)

theorem getD_slice' (l : List Byte) (off len j : Nat) (hj : j < len) :
    (slice l off len).getD j 0 = l.getD (off + j) 0 := by
  simp only [slice, List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  rw [if_pos hj]

theorem length_slice' (l : List Byte) (off len : Nat) (h : off + len ≤ l.length) :
    (slice l off len).length = len := by
  simp [slice]; omega

/-- The copies read the signature and write the witness only. -/
theorem copyRest_pairwise : copyRest.Pairwise (fun c c' => Disj c.2.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2)) := by
  decide

theorem copyRest_srcdst : ∀ c ∈ copyRest, ∀ c' ∈ copyRest, Disj c.1 (4 * c.2.2) c'.2.1 (4 * c'.2.2) := by
  decide

theorem copy_hit (g : Nat → Byte) (c : Nat × Nat × Nat) (hc : c ∈ copyRest) (x : Nat)
    (h1 : c.2.1 ≤ x) (h2 : x < c.2.1 + 4 * c.2.2) :
    applyCopies copyRest g x = g (x - c.2.1 + c.1) :=
  applyCopies_hit copyRest g copyRest_pairwise copyRest_srcdst c hc x h1 h2

theorem copy_miss (g : Nat → Byte) (x : Nat) (hx : x < 0x820 ∨ (0x910 ≤ x ∧ x < 0x1178)) :
    applyCopies copyRest g x = g x :=
  applyCopies_frame copyRest g x (by
    intro c hc; simp only [copyRest, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp <;> omega)

theorem flatten_slices (l : List Byte) (off len : Nat) :
    ∀ n, ((List.range n).map (fun k => slice l (off + len * k) len)).flatten = slice l off (len * n) := by
  intro n
  induction n with
  | zero => simp [slice]
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.flatten_append, ih]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil, slice]
    rw [show len * (n + 1) = len * n + len by ring, List.take_add, List.drop_drop]

theorem getD_take' (l : List Byte) (n i : Nat) (hi : i < n) : (l.take n).getD i 0 = l.getD i 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take]; rw [if_pos hi]

theorem witness_bytes (sig : List Byte) (hsig : sig.length = 6100) (N : Nat) (A : Nat → Nat)
    (hSK : SortedKeys N A) (hn : (leavesOf N).Nodup) (segs : List Nat) (f0 : Nat → Byte)
    (h1 : ∀ j < 6100, f0 (0x3300 + j) = sig.getD j 0)
    (h2 : ∀ i < 2152, f0 (0x910 + i) = (curStream sig segs 0).getD i 0) (h3 : f0 0x81F = 0) :
    ∀ i < 6348, applyCopies copyRest (piF A 15 (applyCopy (0x3300, 0x800, 4) f0)) (0x800 + i) =
      (witnessList sig (leavesOf N) (vsOf A) segs).getD i 0 := by
  intro i hi
  set g := piF A 15 (applyCopy (0x3300, 0x800, 4) f0) with hg
  -- the signature under the copies
  have hgs : ∀ j < 6100, g (0x3300 + j) = sig.getD j 0 := by
    intro j hj; simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]; exact h1 j hj
  -- the witness as one concatenation with explicit lengths
  have eS : ((List.range porsK).map (sigItem sig)).flatten = slice sig 16 240 := by
    have := flatten_slices sig 16 16 15
    simp only [show 16 * 15 = 240 from rfl] at this
    rw [← this]; unfold porsK sigItem; rfl
  have eB : ((List.range nLayers).map (sigLayerBody sig)).flatten =
      slice sig 2180 848 ++ (slice sig 3032 768 ++ (slice sig 3804 768 ++ (slice sig 4576 768 ++
        slice sig 5348 752))) := by
    simp only [nLayers, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.append_assoc]
    unfold sigLayerBody
    rw [show sigLayerOff 0 = 2176 by decide, show sigLayerOff 1 = 3028 by decide,
      show sigLayerOff 2 = 3800 by decide, show sigLayerOff 3 = 4572 by decide,
      show sigLayerOff 4 = 5344 by decide, show sigLayerBytes 0 = 852 by decide,
      show sigLayerBytes 1 = 772 by decide, show sigLayerBytes 2 = 772 by decide,
      show sigLayerBytes 3 = 772 by decide, show sigLayerBytes 4 = 756 by decide]
  have eC : ((List.range nLayers).map (sigCounterBytes sig)).flatten =
      slice sig 2176 4 ++ (slice sig 3028 4 ++ (slice sig 3800 4 ++ (slice sig 4572 4 ++
        slice sig 5344 4))) := by
    simp only [nLayers, List.range_succ, List.range_zero, List.map_append, List.map_cons, List.map_nil,
      List.nil_append, List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
      List.append_assoc]
    unfold sigCounterBytes
    rw [show sigLayerOff 0 = 2176 by decide, show sigLayerOff 1 = 3028 by decide,
      show sigLayerOff 2 = 3800 by decide, show sigLayerOff 3 = 4572 by decide,
      show sigLayerOff 4 = 5344 by decide]
  have lr : (sigRho sig).length = 16 := length_slice' _ _ _ (by omega)
  have lp : ((vsOf A).map (fun x => byte (8 * (leavesOf N).idxOf x))).length = 15 := by simp [vsOf]
  have lz : (zeros (wSec - wPi - porsK)).length = 1 := by simp [zeros, wSec, wPi, porsK]
  have ls : (slice sig 16 240).length = 240 := length_slice' _ _ _ (by omega)
  have lt : ((segStream sig segs ++ zeros streamBytes).take streamBytes).length = 2152 := by
    rw [List.length_take, List.length_append, streamBytes_eq]; simp only [zeros, List.length_replicate]; omega
  have l0 : (slice sig 2180 848).length = 848 := length_slice' _ _ _ (by omega)
  have l1 : (slice sig 3032 768).length = 768 := length_slice' _ _ _ (by omega)
  have l2 : (slice sig 3804 768).length = 768 := length_slice' _ _ _ (by omega)
  have l3 : (slice sig 4576 768).length = 768 := length_slice' _ _ _ (by omega)
  have l4 : (slice sig 5348 752).length = 752 := length_slice' _ _ _ (by omega)
  have k0 : (slice sig 2176 4).length = 4 := length_slice' _ _ _ (by omega)
  have k1 : (slice sig 3028 4).length = 4 := length_slice' _ _ _ (by omega)
  have k2 : (slice sig 3800 4).length = 4 := length_slice' _ _ _ (by omega)
  have k3 : (slice sig 4572 4).length = 4 := length_slice' _ _ _ (by omega)
  have k4 : (slice sig 5344 4).length = 4 := length_slice' _ _ _ (by omega)
  unfold witnessList
  rw [eS, eB, eC]
  simp only [List.append_assoc]
  simp only [getD_app, lr, lp, lz, ls, lt, l0, l1, l2, l3, l4, k0, k1, k2, k3, k4, List.length_nil]
  -- a copied region: `x = 0x800 + i` in `[dst, dst + 4 n)` reads `sig[x - dst + src - 0x3300]`
  have cp : ∀ c ∈ copyRest, c.2.1 ≤ 0x800 + i → 0x800 + i < c.2.1 + 4 * c.2.2 → 0x3300 ≤ c.1 →
      c.1 + 4 * c.2.2 ≤ 0x3300 + 6100 →
      applyCopies copyRest g (0x800 + i) = sig.getD (0x800 + i - c.2.1 + c.1 - 0x3300) 0 := by
    intro c hc h1 h2 h3 h4
    rw [copy_hit g c hc _ h1 h2]
    have := hgs (0x800 + i - c.2.1 + c.1 - 0x3300) (by omega)
    rwa [show 0x3300 + (0x800 + i - c.2.1 + c.1 - 0x3300) = 0x800 + i - c.2.1 + c.1 by omega] at this
  by_cases r0 : i < 16
  · rw [if_pos r0, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_pos (by omega)]
    rw [show 0x800 + i - 0x800 + 0x3300 = 0x3300 + i by omega, h1 i (by omega), sigRho, getD_slice' _ _ _ _ r0,
      Nat.zero_add]
  rw [if_neg r0]
  by_cases r1 : i - 16 < 15
  · rw [if_pos r1, copy_miss g _ (by omega)]
    simp only [hg, piF]; rw [if_pos (by omega)]
    rw [List.getD_eq_getElem?_getD, List.getElem?_map]
    simp only [vsOf, List.getElem?_map, List.getElem?_range r1, Option.map_some, Option.getD_some]
    rw [← idxOf_lv hSK hn (i - 16) r1, show 0x800 + i - 0x810 = i - 16 by omega]
    unfold byte; apply BitVec.eq_of_toNat_eq; simp
  rw [if_neg r1]
  by_cases r2 : i - 16 - 15 < 1
  · rw [if_pos r2, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega), show 0x800 + i = 0x81F by omega, h3]
    simp [zeros, List.getD_eq_getElem?_getD]
  rw [if_neg r2]
  by_cases r3 : i - 16 - 15 - 1 < 240
  · rw [if_pos r3, cp (0x3310, 0x820, 60) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ r3]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg r3]
  by_cases r4 : i - 16 - 15 - 1 - 240 < 2152
  · rw [if_pos r4, copy_miss g _ (by omega)]
    simp only [hg, piF, applyCopy]; rw [if_neg (by omega), if_neg (by omega)]
    rw [show 0x800 + i = 0x910 + (i - 16 - 15 - 1 - 240) by omega, h2 _ r4, getD_take' _ _ _ (by rw [streamBytes_eq]; exact r4)]
    unfold curStream items
    simp only [List.range_zero, List.map_nil, List.flatten_nil, List.append_nil]
    rw [getD_app, getD_app]
    split
    · rfl
    · rw [getD_zeros, getD_zeros]
  rw [if_neg r4]
  by_cases q0 : i - 16 - 15 - 1 - 240 - 2152 < 848
  · rw [if_pos q0, cp (0x3B84, 0x1178, 212) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q0]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q0]
  by_cases q1 : i - 16 - 15 - 1 - 240 - 2152 - 848 < 768
  · rw [if_pos q1, cp (0x3ED8, 0x14C8, 192) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q1]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q1]
  by_cases q2 : i - 16 - 15 - 1 - 240 - 2152 - 848 - 768 < 768
  · rw [if_pos q2, cp (0x41DC, 0x17C8, 192) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q2]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q2]
  by_cases q3 : i - 16 - 15 - 1 - 240 - 2152 - 848 - 768 - 768 < 768
  · rw [if_pos q3, cp (0x44E0, 0x1AC8, 192) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q3]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q3]
  by_cases q4 : i - 16 - 15 - 1 - 240 - 2152 - 848 - 768 - 768 - 768 < 752
  · rw [if_pos q4, cp (0x47E4, 0x1DC8, 188) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q4]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q4]
  by_cases q5 : i - 16 - 15 - 1 - 240 - 2152 - 848 - 768 - 768 - 768 - 752 < 4
  · rw [if_pos q5, cp (0x3B80, 0x20B8, 1) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q5]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q5]
  by_cases q6 : i - 16 - 15 - 1 - 240 - 2152 - 848 - 768 - 768 - 768 - 752 - 4 < 4
  · rw [if_pos q6, cp (0x3ED4, 0x20BC, 1) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q6]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q6]
  by_cases q7 : i - 16 - 15 - 1 - 240 - 2152 - 848 - 768 - 768 - 768 - 752 - 4 - 4 < 4
  · rw [if_pos q7, cp (0x41D8, 0x20C0, 1) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q7]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q7]
  by_cases q8 : i - 16 - 15 - 1 - 240 - 2152 - 848 - 768 - 768 - 768 - 752 - 4 - 4 - 4 < 4
  · rw [if_pos q8, cp (0x44DC, 0x20C4, 1) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
      getD_slice' _ _ _ _ q8]
    exact congrArg (fun j => sig.getD j 0) (by simp; omega)
  rw [if_neg q8]
  rw [cp (0x47E0, 0x20C8, 1) (by decide) (by simp; omega) (by simp; omega) (by simp) (by simp),
    getD_slice' _ _ _ _ (by omega)]
  exact congrArg (fun j => sig.getD j 0) (by simp; omega)

end SigGolfCandidate.Expand
