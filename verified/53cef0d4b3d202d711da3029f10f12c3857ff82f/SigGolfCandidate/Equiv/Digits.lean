import SigGolfCandidate.Equiv.Basic

/-!
# Digest splitting and target-sum decoding

* `decodeDigits_dv`: the reference decoder on the bytes of a digest is the abstract
  `TargetSum.decodeDigest`, digits read as numbers;
* message digest: `N = a mod 2^184` and its index / leaf groups (`idxOf`, `uOf`, `admissible`)
  are the abstract `digestIndex`, `digestLeaves`, `Admissible`.
-/

namespace SigGolfCandidate.Equiv

open SigGolf (Byte Bytes)
open SphincsSecurity (Digest Encoding)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

theorem leNat_take_dv (d : Digest) (k : Nat) (hk : k ≤ 16) :
    Ref.leNat ((dv d).take k) = d.toNat % 2 ^ (8 * k) := by
  have h := Ref.toList_eq_map (n := 16) d
  simp only [dv]
  rw [h, ← List.map_take, List.take_range, Nat.min_eq_left hk, Ref.leNat_map_range]
  rw [Nat.pow_mul]

theorem leNat_slice_dv (d : Digest) :
    Ref.leNat (Ref.slice (dv d) 8 8) = d.toNat / 2 ^ 64 := by
  have h := Ref.toList_eq_map (n := 16) d
  simp only [dv, Ref.slice]
  rw [h, ← List.map_drop]
  have hr : (List.range 16).drop 8 = (List.range 8).map (· + 8) := by decide
  rw [hr, List.map_map, List.take_of_length_le (by simp)]
  have e : ((fun i => Ref.byte (d.toNat / 256 ^ i)) ∘ fun x => x + 8) =
      fun i => Ref.byte (d.toNat / 2 ^ 64 / 256 ^ i) := by
    funext i
    simp only [Function.comp]
    congr 1
    rw [Nat.div_div_eq_div_mul, show (256 : Nat) ^ (i + 8) = 2 ^ 64 * 256 ^ i by
      rw [Nat.pow_add]; norm_num; ring]
  rw [e, Ref.leNat_map_range]
  apply Nat.mod_eq_of_lt
  have := d.isLt
  simp only [SphincsSecurity.digestBits] at this
  rw [Nat.div_lt_iff_lt_mul (by norm_num)]
  norm_num at this ⊢; omega

theorem digitOffset_lt (i : SphincsSecurity.ChainIndex) : i.val < 21 →
    SphincsSecurity.TargetSum.digitOffset i = 3 * i.val := by
  intro h
  simp [SphincsSecurity.TargetSum.digitOffset, SphincsSecurity.TargetSum.digitsPerHalf,
    SphincsSecurity.winternitzBits, SphincsSecurity.numChains, h]

theorem digestEncoding_val (d : Digest) (i : SphincsSecurity.ChainIndex) :
    (SphincsSecurity.TargetSum.digestEncoding d i).val =
      d.toNat / 2 ^ (SphincsSecurity.TargetSum.digitOffset i) % 8 := by
  simp [SphincsSecurity.TargetSum.digestEncoding, Nat.shiftRight_eq_div_pow,
    SphincsSecurity.winternitzBits]

/-- The 42 digits of the reference decoder are the abstract digits. -/
theorem digits_eq (d : Digest) :
    Ref.digitsOfWord (d.toNat % 2 ^ 64) ++ Ref.digitsOfWord (d.toNat / 2 ^ 64) =
      List.ofFn fun i => (SphincsSecurity.TargetSum.digestEncoding d i).val := by
  unfold Ref.digitsOfWord
  apply List.ext_getElem (by simp [SphincsSecurity.numChains])
  intro i h1 h2'
  simp only [List.getElem_ofFn]
  rw [digestEncoding_val]
  have h2 : i < 42 := by simpa [SphincsSecurity.numChains] using h2'
  by_cases hi : i < 21
  · rw [List.getElem_append_left (by simp [hi])]
    simp only [List.getElem_map, List.getElem_range]
    rw [digitOffset_lt ⟨i, h2'⟩ hi]
    rw [show (8 : Nat) ^ i = 2 ^ (3 * i) by rw [Nat.pow_mul]]
    rw [show (2 : Nat) ^ 64 = 2 ^ (3 * i) * 2 ^ (64 - 3 * i) by rw [← Nat.pow_add]; congr 1; omega,
      Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow_iff_le_right'.mpr
        (show 3 ≤ 64 - 3 * i by omega) |> fun h => by
          rw [show (8 : Nat) = 2 ^ 3 by norm_num]; exact h)]
  · rw [List.getElem_append_right (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range, List.length_map, List.length_range]
    have ho : SphincsSecurity.TargetSum.digitOffset ⟨i, h2'⟩ = 64 + 3 * (i - 21) := by
      simp [SphincsSecurity.TargetSum.digitOffset, SphincsSecurity.TargetSum.digitsPerHalf,
        SphincsSecurity.winternitzBits, SphincsSecurity.numChains, hi]; omega
    rw [ho, Nat.pow_add, ← Nat.div_div_eq_div_mul, show (8 : Nat) ^ (i - 21) = 2 ^ (3 * (i - 21)) by
      rw [Nat.pow_mul]]

theorem bit63 (d : Digest) : d.getLsbD 63 = false ↔ d.toNat % 2 ^ 64 < 2 ^ 63 := by
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_false_iff_not]
  norm_num
  omega

theorem bit127 (d : Digest) : d.getLsbD 127 = false ↔ d.toNat / 2 ^ 64 < 2 ^ 63 := by
  have h := d.isLt
  simp only [SphincsSecurity.digestBits] at h
  rw [BitVec.getLsbD, Nat.testBit_eq_decide_div_mod_eq]
  simp only [decide_eq_false_iff_not]
  norm_num at h ⊢
  omega

/-- **Target-sum decoding**: the reference decoder is the abstract one. -/
theorem decodeDigits_dv (d : Digest) :
    Ref.decodeDigits (dv d) =
      (SphincsSecurity.TargetSum.decodeDigest d).map (fun enc => List.ofFn fun i => (enc i).val) := by
  unfold Ref.decodeDigits SphincsSecurity.TargetSum.decodeDigest
  have h0 : Ref.slice (dv d) 0 8 = (dv d).take 8 := by simp [Ref.slice]
  simp only [h0, leNat_take_dv d 8 (by omega), leNat_slice_dv]
  simp only [show 8 * 8 = 64 from rfl]
  rw [digits_eq]
  by_cases hb : d.toNat % 2 ^ 64 < 2 ^ 63 ∧ d.toNat / 2 ^ 64 < 2 ^ 63
  · rw [if_pos hb]
    have hs : (List.ofFn fun i => (SphincsSecurity.TargetSum.digestEncoding d i).val).sum =
        SphincsSecurity.TargetSum.sum (SphincsSecurity.TargetSum.digestEncoding d) := by
      rw [List.sum_ofFn]; rfl
    rw [hs]
    by_cases hv : SphincsSecurity.TargetSum.Valid (SphincsSecurity.TargetSum.digestEncoding d)
    · rw [if_pos (by exact hv), if_pos ⟨(bit63 d).mpr hb.1, (bit127 d).mpr hb.2, hv⟩]; rfl
    · rw [if_neg (by exact hv), if_neg (fun h => hv h.2.2)]; rfl
  · rw [if_neg hb, if_neg (fun h => hb ⟨(bit63 d).mp h.1, (bit127 d).mp h.2.1⟩)]; rfl

/-! ## The message digest -/

open SphincsSecurity (MessageDigest IndexGroup FtsLeaf)

/-- The leaf groups of a digest as the reference reads them (zero past the last group). -/
def uFun (leaves : IndexGroup → FtsLeaf) (k : Nat) : Nat :=
  if h : k < SphincsSecurity.ftsTrees then (leaves ⟨k, h⟩).val else 0

theorem truncateMessageDigest_toNat (a : BitVec 256) :
    (SphincsSecurity.truncateMessageDigest a).toNat = a.toNat % 2 ^ 184 := by
  simp [SphincsSecurity.truncateMessageDigest, SphincsSecurity.messageDigestBits,
    SphincsSecurity.totalHeight, SphincsSecurity.ftsTrees, SphincsSecurity.ftsTreeHeight]

theorem idxOf_eq (d : MessageDigest) : Ref.idxOf d.toNat = (SphincsSecurity.Concrete.digestIndex d).val := by
  simp [Ref.idxOf, SphincsSecurity.Concrete.digestIndex, Ref.totalH, SphincsSecurity.totalHeight]

theorem uOf_eq (d : MessageDigest) : Ref.uOf d.toNat = uFun (SphincsSecurity.Concrete.digestLeaves d) := by
  funext k
  unfold uFun Ref.uOf
  split_ifs with hk
  · simp [SphincsSecurity.Concrete.digestLeaves, Ref.totalH, SphincsSecurity.totalHeight, Ref.ftsA,
      SphincsSecurity.ftsTreeHeight, Nat.shiftRight_eq_div_pow]
  · have h := d.isLt
    simp only [SphincsSecurity.messageDigestBits, SphincsSecurity.totalHeight, SphincsSecurity.ftsTrees,
      SphincsSecurity.ftsTreeHeight] at h hk
    simp only [Ref.totalH, Ref.ftsA]
    have h2 : d.toNat < 2 ^ (34 + 10 * k) :=
      lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega))
    rw [Nat.div_eq_of_lt h2]
    rfl

theorem admissible_eq (d : MessageDigest) :
    Ref.admissible d.toNat = decide (SphincsSecurity.Concrete.Admissible d) := by
  unfold Ref.admissible
  rw [uOf_eq]
  have e : uFun (SphincsSecurity.Concrete.digestLeaves d) 14 =
      (SphincsSecurity.Concrete.digestLeaves d SphincsSecurity.Concrete.lastIndexGroup).val :=
    dif_pos (by decide)
  rw [e, Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff]
  show _ ↔ SphincsSecurity.Concrete.digestLeaves d SphincsSecurity.Concrete.lastIndexGroup = 0
  exact ⟨fun h => Fin.ext h, fun h => by rw [h]; rfl⟩

end SigGolfCandidate.Equiv
