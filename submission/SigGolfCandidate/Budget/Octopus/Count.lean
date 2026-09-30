import SigGolfCandidate.Budget.Octopus.Split
import Mathlib.Algebra.BigOperators.ModEq
import Mathlib.Data.Nat.Choose.Bounds

/-!
# PORS+FP admissibility: the exact number of admissible sets

`packedCount` (kernel-evaluated in `Defs.lean`) is the DP of `Q_{H+1} = 2 y Q_H + Q_H^2` on the
rows `j ≤ 15`, with `y = 2^224`, modulo `M = y^121`, and then row 15 modulo `y - 1`:

* `rep_piter`: the DP computes `(Q y 14).coeff 15 mod M = (∑_{|S| = 15} y^(oc S)) mod y^121`;
* `mod_pow_sum`: modulo `y^121` exactly the sets with `oc S ≤ 120` survive (there are fewer than
  `y` sets, so no carries);
* `sum_pow_mod_pred`: modulo `y - 1` every `y^(oc S)` is `1`, so what is left is their number.

Result: `card_admissibleSets` (the number of 15-subsets of `[0, 2^14)` with octopus size `≤ 120`
is `Nadm`).
-/

namespace SigGolfCandidate.Budget.Octopus
open Finset Polynomial

theorem list_sum_map_range' (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, sum_range_succ]; simp

theorem getD_pstep (K y M : ℕ) (T : List ℕ) {j : ℕ} (hj : j ≤ K) :
    (pstep K y M T).getD j 0 =
      (2 * y * T.getD j 0 + ∑ i ∈ range (j + 1), T.getD i 0 * T.getD (j - i) 0) % M := by
  unfold pstep
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (by omega)]
  simp [list_sum_map_range']

/-- `T` holds the coefficients `0..K` of `Q y H` modulo `M`. -/
def Rep (K y M H : ℕ) (T : List ℕ) : Prop := ∀ j ≤ K, T.getD j 0 = (Q y H).coeff j % M

theorem rep_pstep {K y M H : ℕ} {T : List ℕ} (h : Rep K y M H T) :
    Rep K y M (H + 1) (pstep K y M T) := by
  intro j hj
  rw [getD_pstep K y M T hj, coeff_Q_succ]
  show Nat.ModEq M _ _
  apply Nat.ModEq.add
  · exact Nat.ModEq.mul_left _ (by rw [h j hj]; exact Nat.mod_modEq _ _)
  · refine Nat.ModEq.sum fun i hi => ?_
    have hi' : i ≤ K := by rw [mem_range] at hi; omega
    rw [h i hi', h (j - i) (by omega)]
    exact (Nat.mod_modEq _ _).mul (Nat.mod_modEq _ _)

theorem rep_piter {K y M : ℕ} : ∀ (k H : ℕ) (T : List ℕ), Rep K y M H T →
    Rep K y M (H + k) (piter K y M k T)
  | 0, _, _, h => h
  | k + 1, H, T, h => by
    have := rep_piter k (H + 1) _ (rep_pstep h)
    rwa [show H + 1 + k = H + (k + 1) by omega] at this

theorem rep_zero (K y M : ℕ) (hM : 1 < M) : Rep K y M 0 [0, 1] := by
  intro j _
  rw [Q_zero, coeff_X]
  rcases j with _ | _ | j
  · simp
  · simp [Nat.mod_eq_of_lt hM]
  · simp

/-- Modulo `y^n`, only the terms with exponent `< n` survive (fewer than `y` terms). -/
theorem mod_pow_sum {y n : ℕ} (hn : 0 < n) (P : Finset (Finset ℕ)) (g : Finset ℕ → ℕ)
    (hP : P.card < y) :
    (∑ S ∈ P, y ^ g S) % y ^ n = ∑ S ∈ P.filter (g · < n), y ^ g S := by
  rw [← sum_filter_add_sum_filter_not P (g · < n)]
  obtain ⟨c, hc⟩ : y ^ n ∣ ∑ S ∈ P.filter (fun S => ¬ g S < n), y ^ g S :=
    dvd_sum fun S hS => pow_dvd_pow y (not_lt.mp (mem_filter.mp hS).2)
  rw [hc, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  have hy : 1 ≤ y := by omega
  calc ∑ S ∈ P.filter (g · < n), y ^ g S
      ≤ ∑ _S ∈ P.filter (g · < n), y ^ (n - 1) :=
        sum_le_sum fun S hS => Nat.pow_le_pow_right hy (by have := (mem_filter.mp hS).2; omega)
    _ = (P.filter (g · < n)).card * y ^ (n - 1) := by rw [sum_const, smul_eq_mul]
    _ ≤ P.card * y ^ (n - 1) := Nat.mul_le_mul_right _ (card_filter_le _ _)
    _ < y * y ^ (n - 1) := Nat.mul_lt_mul_of_pos_right hP (by positivity)
    _ = y ^ n := by rw [← pow_succ']; congr 1; omega

/-- Modulo `y - 1`, every power of `y` is `1`. -/
theorem sum_pow_mod_pred {y : ℕ} (hy : 3 ≤ y) (F : Finset (Finset ℕ)) (g : Finset ℕ → ℕ) :
    (∑ S ∈ F, y ^ g S) % (y - 1) = F.card % (y - 1) := by
  have hmod : y % (y - 1) = 1 := by
    calc y % (y - 1) = (y - 1 + 1) % (y - 1) := by rw [Nat.sub_add_cancel (by omega)]
      _ = 1 % (y - 1) := Nat.add_mod_left _ _
      _ = 1 := Nat.mod_eq_of_lt (by omega)
  rw [sum_nat_mod]
  rw [sum_congr rfl fun S _ => by rw [Nat.pow_mod, hmod, one_pow]]
  simp

/-- **The exact number of admissible sets**: 15-subsets of `[0, 2^14)` whose octopus size (the
`ref.octopus_size` formula on the sorted list) is at most 120. -/
theorem card_admissibleSets :
    ((powersetCard 15 (range (2 ^ 14))).filter fun S => octH 14 S.sort ≤ 120).card = Nadm := by
  rw [← packedCount_eq]
  unfold packedCount
  have hM : (2 : ℕ) ^ (pB * 121) = (2 ^ pB) ^ 121 := pow_mul 2 pB 121
  have hy3 : 3 ≤ (2 : ℕ) ^ pB := by unfold pB; norm_num
  have hcard : (powersetCard 15 (range (2 ^ 14))).card < 2 ^ pB - 1 := by
    rw [card_powersetCard, card_range]
    exact lt_of_le_of_lt (Nat.choose_le_pow _ _) (by rw [← pow_mul]; unfold pB; norm_num)
  have h15 := rep_piter (K := 15) (y := 2 ^ pB) (M := 2 ^ (pB * 121)) 14 0 [0, 1]
    (rep_zero 15 _ _ (Nat.one_lt_two_pow (by unfold pB; norm_num))) 15 le_rfl
  rw [Nat.zero_add] at h15
  rw [h15, coeff_Q _ _ _ (by norm_num), hM, mod_pow_sum (by norm_num) _ _ (by omega),
    sum_pow_mod_pred hy3, Nat.mod_eq_of_lt (lt_of_le_of_lt (card_filter_le _ _) hcard)]
  exact congrArg card (filter_congr fun S _ => by simp only [oc]; omega)

end SigGolfCandidate.Budget.Octopus
