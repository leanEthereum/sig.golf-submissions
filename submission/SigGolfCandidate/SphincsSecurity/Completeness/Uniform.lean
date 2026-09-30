import SigGolfCandidate.SphincsSecurity.Scheme
import SigGolfCandidate.SphincsSecurity.Completeness.Octopus.Prob

/-!
# What one uniform answer shows

A trial of either search reads a few low bits of a uniform `256`-bit answer: the counter search its
low `128` bits, the randomizer search its leaf indices, bits `34 .. 243`. Splitting a bit vector into
its low and high bits is a bijection, so a condition on the low bits holds for exactly the share of
answers the condition has among the low bits alone. The admissible share is counted in `Octopus/`.
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

/-! ## Admissibility

The signer keeps a digest when its `15` leaf indices (bits `34 .. 243`) are distinct and their octopus
has at most `120` nodes. `Octopus/` counts those digests exactly, on natural numbers
(`Octopus.admissible`); the two tests agree. -/

theorem sortedLeaves_eq_sortLeaves (leaves : IndexGroup → FtsLeaf) :
    Concrete.sortedLeaves leaves = Octopus.sortLeaves (Octopus.valList leaves) := by
  unfold Concrete.sortedLeaves Concrete.sortedSlots Octopus.sortLeaves Octopus.valList
  rw [List.ofFn_eq_map]
  exact List.map_insertionSort (fun r r' : IndexGroup => (leaves r).val ≤ (leaves r').val)
    (fun a b : Nat => a ≤ b) _ _ (fun _ _ _ _ => Iff.rfl)

theorem valList_digestLeaves (d : MessageDigest) :
    Octopus.valList (Concrete.digestLeaves d) = Octopus.leavesOf d.toNat := by
  unfold Octopus.valList Octopus.leavesOf Octopus.leafOf Concrete.digestLeaves
  apply List.ext_getElem (by simp [ftsOpenings])
  intro r h1 _
  simp [Nat.shiftRight_eq_div_pow, totalHeight, ftsTreeHeight]

/-- The scheme's admissibility is the counted one. -/
theorem admissible_iff (u : HashOutput) :
    Concrete.Admissible (truncateMessageDigest u) ↔ Octopus.admissible u.toNat = true := by
  have htrunc : (truncateMessageDigest u).toNat = u.toNat := by
    simp [truncateMessageDigest, messageDigestBits, hashOutputBits]
    exact Nat.mod_eq_of_lt u.isLt
  unfold Concrete.Admissible Concrete.AdmissibleLeaves Octopus.admissible
  rw [sortedLeaves_eq_sortLeaves, valList_digestLeaves, htrunc, ← Octopus.valList_nodup,
    valList_digestLeaves, htrunc]
  simp [ftsAuthCapacity]

/-- A uniform answer's digest is admissible with probability at least `2⁻¹⁰` (exactly
`15! · N / 2²¹⁰ ≈ 2^-9.76`). -/
theorem probEvent_admissible_ge :
    (1024 : ℝ≥0∞)⁻¹ ≤ Pr[fun u : HashOutput => Concrete.Admissible (truncateMessageDigest u) |
      ($ᵗ HashOutput : ProbComp HashOutput)] := by
  have h := Octopus.probEvent_admissibleDigest_ge
  rw [show (1 : ℝ≥0∞) / 2 ^ 10 = (1024 : ℝ≥0∞)⁻¹ by norm_num] at h
  refine h.trans (le_of_eq ?_)
  exact probEvent_congr' (fun u _ => (admissible_iff u).symm) rfl

end SphincsSecurity.Completeness
