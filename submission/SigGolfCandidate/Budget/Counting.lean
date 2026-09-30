import SigGolfCandidate.Budget.Loops

/-!
# Budget: the acceptance probabilities of one fresh answer

For a uniform answer `u : BitVec 256`:

* the digest is admissible with probability exactly `2^-10` (`probEvent_not_admissible`);
* the randomizer lands in a set `R` of values with probability at most `|R| / 2^128`
  (`probEvent_answerBytes_mem_le`);
* the encoding decodes with probability exactly `codeCount / 2^128`, where
  `codeCount = 693523430046796437145478038506044352` is the number of pairs of 21-digit octal
  words with digit sum 170 (`probEvent_decode_none`). The count is a generating-function identity
  evaluated by the kernel (`codeCount_eq`), as in the leanVM completeness proof.
-/

namespace SigGolfCandidate.Budget
open SigGolf SigGolfCandidate.Ref OracleComp Finset ENNReal

/-! ## Counting over ranges -/

theorem sum_range_mul {M : Type} [AddCommMonoid M] (f : Nat → M) (A B : Nat) :
    ∑ k ∈ range (A * B), f k = ∑ b ∈ range B, ∑ a ∈ range A, f (a + A * b) := by
  induction B with
  | zero => simp
  | succ B ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.add_comm]

theorem card_bitVec_filter (n : Nat) (P : Nat → Prop) [DecidablePred P] :
    (univ.filter fun u : BitVec n => P u.toNat).card = ((range (2 ^ n)).filter P).card := by
  refine Finset.card_nbij' (fun u => u.toNat) (fun k => BitVec.ofNat n k) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, mem_range] at hu ⊢
    exact ⟨u.isLt, hu⟩
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_univ, true_and] at hk ⊢
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hk.1]; exact hk.2
  · intro u _; simp
  · intro k hk
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hk
    simp [Nat.mod_eq_of_lt hk.1]

theorem probEvent_uniform_toNat (P : Nat → Prop) [DecidablePred P] :
    Pr[fun u : BitVec 256 => P u.toNat | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      (((range (2 ^ 256)).filter P).card : ℝ≥0∞) / (2 ^ 256 : ℝ≥0∞) := by
  rw [probEvent_uniformSample, card_bitVec_filter, Fintype.card_bitVec, Nat.cast_pow,
    Nat.cast_ofNat]

/-- Indicator sums. -/
theorem card_filter_range (P : Nat → Prop) [DecidablePred P] (n : Nat) :
    ((range n).filter P).card = ∑ k ∈ range n, if P k then 1 else 0 :=
  Finset.card_filter _ _

/-! ## Admissibility -/

theorem count_split (A B : Nat) (P Q : Nat → Prop) [DecidablePred P] [DecidablePred Q]
    (hPQ : ∀ a, a < A → ∀ b, (P (a + A * b) ↔ Q b)) :
    (∑ k ∈ range (A * B), if P k then 1 else 0) = A * ∑ b ∈ range B, if Q b then 1 else 0 := by
  rw [sum_range_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_congr rfl fun a ha => by rw [if_congr (hPQ a (mem_range.mp ha) b) rfl rfl]]
  by_cases hb : Q b <;> simp [hb]

theorem count_mod (m t : Nat) (hm : 0 < m) :
    (∑ b ∈ range (m * t), if b % m = 0 then 1 else 0) = t := by
  rw [sum_range_mul]
  have : ∀ s ∈ range t, (∑ r ∈ range m, if (r + m * s) % m = 0 then 1 else 0) = 1 := by
    intro s _
    rw [Finset.sum_congr rfl fun r hr => by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp hr)]]
    rw [Finset.sum_ite_eq' (range m) 0 (fun _ => 1)]
    simp [hm]
  rw [Finset.sum_congr rfl this]
  simp

theorem admissible_split (a b : Nat) (ha : a < 2 ^ 174) :
    admissible ((a + 2 ^ 174 * b) % 2 ^ 184) = true ↔ b % 2 ^ 10 = 0 := by
  unfold admissible uOf
  simp only [totalH, ftsA]
  have h1 : (2 : Nat) ^ 184 = 2 ^ 174 * 2 ^ 10 := by rw [← pow_add]
  rw [h1, Nat.mod_mul_right_div_self, Nat.add_mul_div_left _ _ (by positivity),
    Nat.div_eq_of_lt ha, Nat.zero_add]
  simp

theorem count_admissible_gen (T : Nat) :
    (∑ k ∈ range (2 ^ 174 * (2 ^ 10 * T)), if admissible (k % 2 ^ 184) = true then 1 else 0)
      = 2 ^ 174 * T := by
  rw [count_split _ _ _ (fun b => b % 2 ^ 10 = 0) (fun a ha b => admissible_split a b ha),
    count_mod _ _ (by positivity)]

theorem count_admissible :
    ((range (2 ^ 256)).filter fun k => admissible (k % 2 ^ 184) = true).card = 2 ^ 246 := by
  have e : (2 : Nat) ^ 256 = 2 ^ 174 * (2 ^ 10 * 2 ^ 72) := by rw [← pow_add, ← pow_add]
  rw [card_filter_range, e, count_admissible_gen, ← pow_add]

/-- A fresh digest is rejected with probability `1 - 2^-10`. -/
theorem probEvent_not_admissible :
    Pr[fun u : BitVec 256 => ¬ admissible (u.toNat % 2 ^ 184) = true |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = 1 - (2 ^ 246 : ℝ≥0∞) / 2 ^ 256 := by
  have hc := probEvent_compl ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    (fun u : BitVec 256 => admissible (u.toNat % 2 ^ 184) = true)
  have hfail : Pr[⊥ | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = 0 := by simp
  rw [hfail, tsub_zero] at hc
  rw [ENNReal.eq_sub_of_add_eq probEvent_ne_top ((add_comm _ _).trans hc),
    probEvent_uniform_toNat (fun k => admissible (k % 2 ^ 184) = true), count_admissible,
    Nat.cast_pow, Nat.cast_ofNat]

/-! ## Answer bytes -/

theorem leBytes_add (a b v : Nat) :
    leBytes (a + b) v = leBytes a v ++ leBytes b (v / 256 ^ a) := by
  unfold leBytes
  rw [List.range_add, List.map_append, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Function.comp_apply, Nat.pow_add, Nat.div_div_eq_div_mul]

theorem answerBytes_eq (k : Nat) (u : BitVec 256) (hk : k ≤ 32) :
    answerBytes k u = leBytes k u.toNat := by
  unfold answerBytes leBytes
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have := extractByte_ofNat 256 u.toNat i (by omega)
  simpa using this

theorem leNat_answerBytes16 (u : BitVec 256) : leNat (answerBytes 16 u) = u.toNat % 2 ^ 128 := by
  rw [answerBytes_eq 16 u (by omega), leNat_leBytes]; norm_num

theorem count_mod_eq_le (A B r : Nat) :
    (∑ k ∈ range (A * B), if k % A = r then 1 else 0) ≤ B := by
  rw [sum_range_mul]
  calc (∑ b ∈ range B, ∑ a ∈ range A, if (a + A * b) % A = r then 1 else 0)
      ≤ ∑ _b ∈ range B, 1 := by
        refine Finset.sum_le_sum fun b _ => ?_
        rw [Finset.sum_congr rfl fun a ha => by
          rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp ha)]]
        rw [Finset.sum_ite_eq' (range A) r (fun _ => 1)]
        split <;> simp
    _ = B := by simp

/-- The randomizer is in `R` with probability at most `|R| / 2^128`. -/
theorem probEvent_answerBytes_mem_le (R : Finset Val) :
    Pr[fun u : BitVec 256 => answerBytes 16 u ∈ R | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤
      (R.card : ℝ≥0∞) / 2 ^ 128 := by
  classical
  rw [probEvent_uniformSample]
  have hsub : (univ.filter fun u : BitVec 256 => answerBytes 16 u ∈ R) ⊆
      R.biUnion fun ρ => univ.filter fun u : BitVec 256 => u.toNat % 2 ^ 128 = leNat ρ := by
    intro u hu
    simp only [mem_filter, mem_univ, true_and] at hu
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    exact ⟨_, hu, by rw [leNat_answerBytes16]⟩
  have hone : ∀ r : Nat,
      (univ.filter fun u : BitVec 256 => u.toNat % 2 ^ 128 = r).card ≤ 2 ^ 128 := by
    intro r
    rw [card_bitVec_filter 256 (fun k => k % 2 ^ 128 = r), card_filter_range,
      show (2 : Nat) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add]]
    exact count_mod_eq_le _ _ r
  have hcard : (univ.filter fun u : BitVec 256 => answerBytes 16 u ∈ R).card ≤ R.card * 2 ^ 128 :=
    (card_le_card hsub).trans (card_biUnion_le.trans (by
      calc ∑ ρ ∈ R, (univ.filter fun u : BitVec 256 => u.toNat % 2 ^ 128 = leNat ρ).card
          ≤ ∑ _ρ ∈ R, 2 ^ 128 := Finset.sum_le_sum fun ρ _ => hone _
        _ = R.card * 2 ^ 128 := by simp))
  have hc : (Fintype.card (BitVec 256) : ℝ≥0∞) = 2 ^ 128 * 2 ^ 128 := by
    rw [Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat, ← pow_add]
  rw [hc]
  calc ((univ.filter fun u : BitVec 256 => answerBytes 16 u ∈ R).card : ℝ≥0∞) / (2 ^ 128 * 2 ^ 128)
      ≤ ((R.card * 2 ^ 128 : Nat) : ℝ≥0∞) / (2 ^ 128 * 2 ^ 128) := by
        gcongr
    _ = (R.card : ℝ≥0∞) / 2 ^ 128 := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat,
          ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

/-! ## Decoding -/

/-- Octal digit sum of the low `n` digits. -/
def ds (n a : Nat) : Nat := ∑ r ∈ range n, a / 8 ^ r % 8

theorem list_sum_map_range (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ r ∈ range n, f r := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

theorem sum_digitsOfWord (d : Nat) : (digitsOfWord d).sum = ds 21 d := by
  unfold digitsOfWord ds
  exact list_sum_map_range _ 21

theorem ds_succ (n d b : Nat) (hd : d < 8) : ds (n + 1) (d + 8 * b) = d + ds n b := by
  unfold ds
  rw [Finset.sum_range_succ']
  simp only [pow_zero, Nat.div_one]
  rw [show (d + 8 * b) % 8 = d by omega, Nat.add_comm]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pow_succ', ← Nat.div_div_eq_div_mul, show (d + 8 * b) / 8 = b by omega]

theorem ds_le (n a : Nat) : ds n a ≤ 7 * n := by
  unfold ds
  calc ∑ r ∈ range n, a / 8 ^ r % 8 ≤ ∑ _r ∈ range n, 7 :=
        Finset.sum_le_sum fun r _ => Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
    _ = 7 * n := by simp [Nat.mul_comm]

/-- The digit generating polynomial `1 + X + ... + X^7`. -/
def gfDigit (X : Nat) : Nat := ∑ d ∈ range 8, X ^ d

theorem gf_ds (X n : Nat) : ∑ a ∈ range (8 ^ n), X ^ ds n a = gfDigit X ^ n := by
  induction n with
  | zero => simp [ds]
  | succ n ih =>
    rw [pow_succ', sum_range_mul, pow_succ, ← ih, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [gfDigit, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [ds_succ n d b (mem_range.mp hd), pow_add, Nat.mul_comm]

/-- Pairs of `n`-digit octal words with digit sum `s`. -/
def npair (n s : Nat) : Nat :=
  ∑ a1 ∈ range (8 ^ n), ∑ a0 ∈ range (8 ^ n), if ds n a0 + ds n a1 = s then 1 else 0

theorem gf_pairs (X n : Nat) :
    ∑ s ∈ range (14 * n + 1), npair n s * X ^ s = gfDigit X ^ (2 * n) := by
  have hr : gfDigit X ^ (2 * n) =
      ∑ a1 ∈ range (8 ^ n), ∑ a0 ∈ range (8 ^ n), X ^ (ds n a0 + ds n a1) := by
    rw [Nat.two_mul, pow_add, ← gf_ds, Finset.sum_mul_sum, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a1 _ => Finset.sum_congr rfl fun a0 _ => ?_
    rw [pow_add]
  rw [hr]
  unfold npair
  simp only [Finset.sum_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a1 _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a0 _ => ?_
  rw [Finset.sum_ite_eq (range (14 * n + 1)) (ds n a0 + ds n a1) (fun s => X ^ s), if_pos]
  have := ds_le n a0; have := ds_le n a1
  rw [mem_range]; omega

theorem npair_le (n s : Nat) : npair n s ≤ 8 ^ n * 8 ^ n := by
  unfold npair
  calc (∑ a1 ∈ range (8 ^ n), ∑ a0 ∈ range (8 ^ n), if ds n a0 + ds n a1 = s then 1 else 0)
      ≤ ∑ _a1 ∈ range (8 ^ n), ∑ _a0 ∈ range (8 ^ n), 1 :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => by split <;> simp
    _ = 8 ^ n * 8 ^ n := by simp

theorem digit_of_sum (B : Nat) (hB : 0 < B) (c : Nat → Nat) (hc : ∀ s, c s < B) :
    ∀ (n k : Nat), k < n → (∑ s ∈ range n, c s * B ^ s) / B ^ k % B = c k := by
  intro n
  induction n generalizing c with
  | zero => intro k hk; exact absurd hk (Nat.not_lt_zero k)
  | succ n ih =>
      intro k hk
      have hsplit : ∑ s ∈ range (n + 1), c s * B ^ s
          = c 0 + B * ∑ s ∈ range n, c (s + 1) * B ^ s := by
        rw [Finset.sum_range_succ', Finset.mul_sum]
        simp only [pow_zero, mul_one, pow_succ]
        rw [Nat.add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro s _
        ring
      cases k with
      | zero =>
          rw [hsplit, pow_zero, Nat.div_one, Nat.add_mul_mod_self_left,
            Nat.mod_eq_of_lt (hc 0)]
      | succ k =>
          rw [hsplit, pow_succ']
          rw [← Nat.div_div_eq_div_mul]
          rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt (hc 0), Nat.zero_add]
          exact ih (fun s => c (s + 1)) (fun s => hc (s + 1)) k (Nat.lt_of_succ_lt_succ hk)

theorem npair_coeff (n s X : Nat) (hX : 8 ^ n * 8 ^ n < X) (hs : s < 14 * n + 1) :
    npair n s = gfDigit X ^ (2 * n) / X ^ s % X := by
  rw [← gf_pairs]
  exact (digit_of_sum X (by omega) (npair n) (fun s => (npair_le n s).trans_lt hX) _ s hs).symm

/-- The number of accepted encodings (pairs of 21-digit words with digit sum 170). -/
def codeCount : Nat := 693523430046796437145478038506044352

theorem gfDigit_eq (X : Nat) : gfDigit X = 1 + X + X ^ 2 + X ^ 3 + X ^ 4 + X ^ 5 + X ^ 6 + X ^ 7 := by
  simp [gfDigit, Finset.sum_range_succ]

theorem npair_170 : npair 21 170 = codeCount := by
  rw [npair_coeff 21 170 (2 ^ 128) (by norm_num) (by norm_num), gfDigit_eq]
  decide

/-- The decoding condition on the low 128 bits `k`. -/
def Dok (k : Nat) : Prop :=
  k % 2 ^ 64 < 2 ^ 63 ∧ k / 2 ^ 64 % 2 ^ 64 < 2 ^ 63 ∧
    ds 21 (k % 2 ^ 64) + ds 21 (k / 2 ^ 64 % 2 ^ 64) = 170

instance : DecidablePred Dok := fun k => by unfold Dok; infer_instance

theorem Dok_high (a b : Nat) : Dok (a + 2 ^ 128 * b) ↔ Dok a := by
  have e : 2 ^ 128 * b = 2 ^ 64 * (2 ^ 64 * b) := by rw [← Nat.mul_assoc, ← pow_add]
  have h1 : (a + 2 ^ 128 * b) % 2 ^ 64 = a % 2 ^ 64 := by rw [e, Nat.add_mul_mod_self_left]
  have h2 : (a + 2 ^ 128 * b) / 2 ^ 64 % 2 ^ 64 = a / 2 ^ 64 % 2 ^ 64 := by
    rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left]
  unfold Dok; rw [h1, h2]

theorem Dok_split (a0 a1 : Nat) (h0 : a0 < 2 ^ 64) (h1 : a1 < 2 ^ 64) :
    Dok (a0 + 2 ^ 64 * a1) ↔ (a0 < 2 ^ 63 ∧ a1 < 2 ^ 63 ∧ ds 21 a0 + ds 21 a1 = 170) := by
  have e1 : (a0 + 2 ^ 64 * a1) % 2 ^ 64 = a0 := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h0]
  have e2 : (a0 + 2 ^ 64 * a1) / 2 ^ 64 % 2 ^ 64 = a1 := by
    rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt h0, Nat.zero_add,
      Nat.mod_eq_of_lt h1]
  unfold Dok; rw [e1, e2]

theorem sum_half (M : Nat) (f : Nat → Nat) (P : Nat → Prop) [DecidablePred P] :
    (∑ x ∈ range (M + M), if x < M ∧ P x then f x else 0) = ∑ x ∈ range M, if P x then f x else 0 := by
  rw [Finset.sum_range_add]
  have : ∀ x ∈ range M, (if M + x < M ∧ P (M + x) then f (M + x) else 0) = 0 := by
    intro x _; rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl this, Finset.sum_const_zero, Nat.add_zero]
  refine Finset.sum_congr rfl fun x hx => ?_
  have := mem_range.mp hx
  by_cases hp : P x <;> simp [hp, this]

theorem Dok_split' (M a0 a1 : Nat) (hM : M = 2 ^ 63) (h0 : a0 < M + M) (h1 : a1 < M + M) :
    Dok (a0 + (M + M) * a1) ↔ (a0 < M ∧ a1 < M ∧ ds 21 a0 + ds 21 a1 = 170) := by
  have hMM : M + M = 2 ^ 64 := by subst hM; norm_num
  rw [hMM] at h0 h1 ⊢
  rw [Dok_split a0 a1 h0 h1, hM]

theorem count_Dok_low (M : Nat) (hM : M = 2 ^ 63) :
    (∑ a ∈ range ((M + M) * (M + M)), if Dok a then 1 else 0) =
      ∑ a1 ∈ range M, ∑ a0 ∈ range M, if ds 21 a0 + ds 21 a1 = 170 then 1 else 0 := by
  rw [sum_range_mul]
  have step : ∀ a1 ∈ range (M + M),
      (∑ a0 ∈ range (M + M), if Dok (a0 + (M + M) * a1) then 1 else 0)
      = if a1 < M then ∑ a0 ∈ range M, (if ds 21 a0 + ds 21 a1 = 170 then 1 else 0) else 0 := by
    intro a1 ha1
    rw [Finset.sum_congr rfl fun a0 ha0 => by
      rw [if_congr (Dok_split' M a0 a1 hM (mem_range.mp ha0) (mem_range.mp ha1)) rfl rfl]]
    by_cases h : a1 < M
    · rw [if_pos h]
      have := sum_half M (fun _ => 1) (fun a0 => ds 21 a0 + ds 21 a1 = 170)
      rw [← this]
      refine Finset.sum_congr rfl fun a0 _ => ?_
      by_cases h' : a0 < M <;> simp [h, h']
    · rw [if_neg h]
      exact Finset.sum_eq_zero fun a0 _ => by simp [h]
  rw [Finset.sum_congr rfl step]
  have := sum_half M (fun a1 => ∑ a0 ∈ range M, if ds 21 a0 + ds 21 a1 = 170 then 1 else 0)
    (fun _ => True)
  simp only [and_true, if_true] at this
  exact this

theorem count_Dok (W T : Nat) (hW : W = 2 ^ 128) :
    (∑ k ∈ range (W * T), if Dok k then 1 else 0) = T * ∑ a ∈ range W, if Dok a then 1 else 0 := by
  rw [sum_range_mul]
  have : ∀ b ∈ range T, (∑ a ∈ range W, if Dok (a + W * b) then 1 else 0) =
      ∑ a ∈ range W, if Dok a then 1 else 0 := fun b _ =>
    Finset.sum_congr rfl fun a _ => by rw [hW]; exact if_congr (Dok_high a _) rfl rfl
  rw [Finset.sum_congr rfl this, Finset.sum_const, card_range, smul_eq_mul]

theorem count_Dok_256 :
    ((range (2 ^ 256)).filter Dok).card = 2 ^ 128 * codeCount := by
  have h1 := count_Dok ((2 ^ 63 + 2 ^ 63) * (2 ^ 63 + 2 ^ 63)) (2 ^ 128) (by norm_num)
  have h2 := count_Dok_low (2 ^ 63) rfl
  have h3 : npair 21 170 = ∑ a1 ∈ range (2 ^ 63), ∑ a0 ∈ range (2 ^ 63),
      if ds 21 a0 + ds 21 a1 = 170 then 1 else 0 := by
    unfold npair; rw [show (8 : Nat) ^ 21 = 2 ^ 63 by norm_num]
  have e : (2 : Nat) ^ 256 = (2 ^ 63 + 2 ^ 63) * (2 ^ 63 + 2 ^ 63) * 2 ^ 128 := by norm_num
  rw [card_filter_range, e, h1, h2, ← h3, npair_170]

theorem slice_leBytes16 (v : Nat) :
    slice (leBytes 16 v) 0 8 = leBytes 8 v ∧ slice (leBytes 16 v) 8 8 = leBytes 8 (v / 256 ^ 8) := by
  rw [show 16 = 8 + 8 from rfl, leBytes_add]
  unfold slice
  constructor
  · simp
  · simp

theorem decode_none_iff (u : BitVec 256) :
    decodeDigits (answerBytes 16 u) = none ↔ ¬ Dok u.toNat := by
  rw [answerBytes_eq 16 u (by omega)]
  obtain ⟨h1, h2⟩ := slice_leBytes16 u.toNat
  unfold decodeDigits
  simp only [h1, h2, leNat_leBytes, List.sum_append, sum_digitsOfWord, target]
  have e1 : (256 : Nat) ^ 8 = 2 ^ 64 := by norm_num
  rw [e1]
  unfold Dok
  split_ifs with ha hb <;> simp_all

/-- A fresh encoding is rejected with probability `1 - codeCount / 2^128`. -/
theorem probEvent_decode_none :
    Pr[fun u : BitVec 256 => decodeDigits (answerBytes 16 u) = none |
      ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      1 - (2 ^ 128 * codeCount : Nat) / (2 ^ 256 : ℝ≥0∞) := by
  have hc := probEvent_compl ($ᵗ BitVec 256 : ProbComp (BitVec 256))
    (fun u : BitVec 256 => Dok u.toNat)
  have hfail : Pr[⊥ | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = 0 := by simp
  rw [hfail, tsub_zero] at hc
  have hcongr : (fun u : BitVec 256 => decodeDigits (answerBytes 16 u) = none) =
      fun u => ¬ Dok u.toNat := funext fun u => propext (decode_none_iff u)
  rw [hcongr, ENNReal.eq_sub_of_add_eq probEvent_ne_top ((add_comm _ _).trans hc),
    probEvent_uniform_toNat Dok, count_Dok_256]

end SigGolfCandidate.Budget
