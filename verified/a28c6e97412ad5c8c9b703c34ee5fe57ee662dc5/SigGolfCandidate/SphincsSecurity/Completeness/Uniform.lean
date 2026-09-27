import SigGolfCandidate.SphincsSecurity.Scheme

/-!
# What one uniform answer shows

A trial of either search reads a few low bits of a uniform `256`-bit answer: the counter search its
low `128` bits, the randomizer search the last `10`-bit index group of its low `184`. Splitting a
bit vector into its low and high bits is a bijection, so a condition on the low bits holds for
exactly the share of answers the condition has among the low bits alone. This file counts both.
-/

open OracleComp ENNReal Finset

namespace SphincsSecurity.Completeness

/-- A bit vector as its low `w` bits and the rest. -/
def splitBits (n w : Nat) (x : BitVec n) : BitVec w × BitVec (n - w) :=
  (x.extractLsb' 0 w, x.extractLsb' w (n - w))

theorem splitBits_injective {n w : Nat} (hw : w ≤ n) : Function.Injective (splitBits n w) := by
  intro x y h
  simp only [splitBits, Prod.mk.injEq] at h
  obtain ⟨hlow, hhigh⟩ := h
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  by_cases hiw : i < w
  · have := congrArg (fun b : BitVec w => b.getLsbD i) hlow
    simpa [BitVec.getLsbD_extractLsb', hiw] using this
  · have := congrArg (fun b : BitVec (n - w) => b.getLsbD (i - w)) hhigh
    simpa [BitVec.getLsbD_extractLsb', show i - w < n - w by omega,
      show w + (i - w) = i by omega] using this

theorem splitBits_bijective {n w : Nat} (hw : w ≤ n) : Function.Bijective (splitBits n w) := by
  refine (Fintype.bijective_iff_injective_and_card _).2 ⟨splitBits_injective hw, ?_⟩
  rw [Fintype.card_prod, Fintype.card_bitVec, Fintype.card_bitVec, Fintype.card_bitVec, ← pow_add]
  congr 1
  omega

/-- A condition on the two halves holds for as many vectors as pairs. -/
theorem card_filter_splitBits {n w : Nat} (hw : w ≤ n) (P : BitVec w × BitVec (n - w) → Prop)
    [DecidablePred P] :
    (univ.filter fun x : BitVec n => P (splitBits n w x)).card = (univ.filter P).card := by
  refine Finset.card_bij (fun x _ => splitBits n w x) ?_ ?_ ?_
  · intro x hx
    simpa using hx
  · intro x _ y _ h
    exact splitBits_injective hw h
  · intro p hp
    obtain ⟨x, hx⟩ := (splitBits_bijective hw).2 p
    exact ⟨x, by simpa [hx] using hp, hx⟩

/-- A condition on the low `w` bits holds for its count of low parts, times every high part. -/
theorem card_filter_low {n w : Nat} (hw : w ≤ n) (Q : BitVec w → Prop) [DecidablePred Q] :
    (univ.filter fun x : BitVec n => Q (x.extractLsb' 0 w)).card
      = (univ.filter Q).card * 2 ^ (n - w) := by
  have h := card_filter_splitBits hw (fun p => Q p.1)
  rw [show (univ.filter fun p : BitVec w × BitVec (n - w) => Q p.1) = (univ.filter Q) ×ˢ univ by
      ext p; simp, Finset.card_product, Finset.card_univ, Fintype.card_bitVec] at h
  exact h

/-- `card_filter_low` for a condition only equivalent to one on the low bits. -/
theorem card_filter_low' {n w : Nat} (hw : w ≤ n) (P : BitVec n → Prop) [DecidablePred P]
    (Q : BitVec w → Prop) [DecidablePred Q] (hPQ : ∀ x, P x ↔ Q (x.extractLsb' 0 w)) :
    (univ.filter P).card = (univ.filter Q).card * 2 ^ (n - w) := by
  rw [Finset.filter_congr (fun x _ => hPQ x)]
  exact card_filter_low hw Q

/-- A condition on the high `n - w` bits holds for its count of high parts, times every low part. -/
theorem card_filter_high {n w : Nat} (hw : w ≤ n) (Q : BitVec (n - w) → Prop) [DecidablePred Q] :
    (univ.filter fun x : BitVec n => Q (x.extractLsb' w (n - w))).card
      = 2 ^ w * (univ.filter Q).card := by
  have h := card_filter_splitBits hw (fun p => Q p.2)
  rw [show (univ.filter fun p : BitVec w × BitVec (n - w) => Q p.2) = univ ×ˢ (univ.filter Q) by
      ext p; simp, Finset.card_product, Finset.card_univ, Fintype.card_bitVec] at h
  exact h

theorem probEvent_uniform (P : HashOutput → Prop) [DecidablePred P] :
    Pr[P | ($ᵗ HashOutput : ProbComp HashOutput)]
      = ((univ.filter P).card : ℝ≥0∞) / (2 : ℝ≥0∞) ^ hashOutputBits := by
  rw [probEvent_uniformSample, Fintype.card_bitVec, Nat.cast_pow, Nat.cast_ofNat]

/-- A uniform answer's truncation lands in a set of digests with the set's share of `2 ^ 128`. -/
theorem probEvent_truncateHash_mem (targets : Finset Digest) :
    Pr[fun u : HashOutput => truncateHash u ∈ targets | ($ᵗ HashOutput : ProbComp HashOutput)]
      = (targets.card : ℝ≥0∞) / (2 : ℝ≥0∞) ^ digestBits := by
  rw [probEvent_uniform]
  have hcard := card_filter_low' (n := hashOutputBits) (w := digestBits) (by decide)
    (fun u : HashOutput => truncateHash u ∈ targets) (fun d => d ∈ targets) (fun _ => Iff.rfl)
  rw [Finset.filter_univ_mem] at hcard
  have hsplit : (2 : ℝ≥0∞) ^ hashOutputBits = 2 ^ digestBits * 2 ^ (hashOutputBits - digestBits) := by
    rw [← pow_add]; congr 1
  rw [hcard, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, hsplit,
    ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

/-- The admissibility test reads bits `174 .. 183` of the digest, the high part past `174`. -/
theorem admissible_iff (d : MessageDigest) :
    Concrete.Admissible d ↔ d.extractLsb' 174 (messageDigestBits - 174) = 0 := by
  change (d.extractLsb' 174 10).toFin = 0 ↔ d.extractLsb' 174 10 = 0
  exact ⟨fun h => BitVec.eq_of_toFin_eq h, fun h => by rw [h]; rfl⟩

/-- A uniform answer's digest is admissible with probability `1 / 1024`. -/
theorem probEvent_admissible :
    Pr[fun u : HashOutput => Concrete.Admissible (truncateMessageDigest u) |
      ($ᵗ HashOutput : ProbComp HashOutput)] = (1024 : ℝ≥0∞)⁻¹ := by
  rw [probEvent_uniform]
  have hinner : (univ.filter fun d : BitVec messageDigestBits => Concrete.Admissible d).card
      = 2 ^ 174 := by
    simp_rw [admissible_iff]
    rw [card_filter_high (n := messageDigestBits) (w := 174) (by decide) (fun b => b = 0),
      Finset.filter_eq' univ 0, if_pos (Finset.mem_univ _), Finset.card_singleton, mul_one]
  have hcard := card_filter_low' (n := hashOutputBits) (w := messageDigestBits) (by decide)
    (fun u : HashOutput => Concrete.Admissible (truncateMessageDigest u))
    (fun d => Concrete.Admissible d) (fun _ => Iff.rfl)
  have hsplit : (2 : ℝ≥0∞) ^ hashOutputBits
      = 2 ^ (174 + (hashOutputBits - messageDigestBits)) * 2 ^ 10 := by
    rw [← pow_add]; congr 1
  rw [hcard, hinner, ← pow_add, Nat.cast_pow, Nat.cast_ofNat, hsplit]
  have hA0 : (2 : ℝ≥0∞) ^ (174 + (hashOutputBits - messageDigestBits)) ≠ 0 := by simp
  have hAt : (2 : ℝ≥0∞) ^ (174 + (hashOutputBits - messageDigestBits)) ≠ ⊤ := by simp
  generalize (2 : ℝ≥0∞) ^ (174 + (hashOutputBits - messageDigestBits)) = A at hA0 hAt ⊢
  calc A / (A * 2 ^ 10) = A * 1 / (A * 2 ^ 10) := by rw [mul_one]
    _ = 1 / 2 ^ 10 := ENNReal.mul_div_mul_left _ _ hA0 hAt
    _ = (1024 : ℝ≥0∞)⁻¹ := by norm_num

end SphincsSecurity.Completeness
