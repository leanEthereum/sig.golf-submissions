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

/-! ## The message digest (PORS+FP: the full 256-bit answer) -/

open SphincsSecurity (MessageDigest IndexGroup FtsLeaf SlotCode)

theorem truncateMessageDigest_toNat (a : BitVec 256) :
    (SphincsSecurity.truncateMessageDigest a).toNat = a.toNat := by
  simp [SphincsSecurity.truncateMessageDigest, SphincsSecurity.messageDigestBits]

theorem idxOf_eq (d : MessageDigest) :
    Ref.idxOf d.toNat = (SphincsSecurity.Concrete.digestIndex d).val := by
  simp [Ref.idxOf, SphincsSecurity.Concrete.digestIndex, Ref.totalH, SphincsSecurity.totalHeight]

theorem leafOf_eq (d : MessageDigest) (r : IndexGroup) :
    Ref.leafOf d.toNat r.val = (SphincsSecurity.Concrete.digestLeaves d r).val := by
  simp [Ref.leafOf, SphincsSecurity.Concrete.digestLeaves, Ref.totalH, SphincsSecurity.totalHeight,
    Ref.porsH, SphincsSecurity.ftsTreeHeight, Nat.shiftRight_eq_div_pow]

/-- The reference's leaf list is the abstract slot map, slot by slot. -/
theorem leavesOf_eq (d : MessageDigest) :
    Ref.leavesOf d.toNat = List.ofFn fun r => (SphincsSecurity.Concrete.digestLeaves d r).val := by
  unfold Ref.leavesOf
  rw [map_range_eq_ofFn]
  exact List.ofFn_inj.mpr (funext fun r => leafOf_eq d r)

/-- The verifier's leaf value of a slot code (`IND = v ++ [2^14]`) is `slotValue`. -/
theorem slotValue_eq (leaves : IndexGroup → FtsLeaf) (c : SlotCode) :
    ((List.ofFn fun r => (leaves r).val) ++ [Ref.porsT]).getD c.val 0 =
      SphincsSecurity.Concrete.slotValue leaves c := by
  unfold SphincsSecurity.Concrete.slotValue
  split
  · next h =>
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simpa using h)]
    simp [h]
  · next h =>
    have hc := c.isLt
    simp only [SphincsSecurity.ftsOpenings] at h hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [SphincsSecurity.ftsOpenings]; omega)]
    have : c.val = 15 := by omega
    rw [this]
    rfl

theorem bitLen_eq : Ref.bitLen = SphincsSecurity.Concrete.bitLength := rfl

theorem octopusSize_eq : Ref.octopusSize = SphincsSecurity.Concrete.octopusSize := rfl

/-- Sorting the leaf values is sorting the slots by value, then reading the values. -/
theorem sortLeaves_eq (leaves : IndexGroup → FtsLeaf) :
    Ref.sortLeaves (List.ofFn fun r => (leaves r).val) =
      SphincsSecurity.Concrete.sortedLeaves leaves := by
  unfold Ref.sortLeaves SphincsSecurity.Concrete.sortedLeaves SphincsSecurity.Concrete.sortedSlots
  rw [List.ofFn_eq_map]
  exact (List.map_insertionSort (fun r r' : IndexGroup => (leaves r).val ≤ (leaves r').val)
    (fun a b : Nat => a ≤ b) (fun r => (leaves r).val) _ (fun a _ b _ => Iff.rfl)).symm

theorem admissible_eq (d : MessageDigest) :
    Ref.admissible d.toNat = decide (SphincsSecurity.Concrete.Admissible d) := by
  unfold Ref.admissible SphincsSecurity.Concrete.Admissible SphincsSecurity.Concrete.AdmissibleLeaves
  rw [leavesOf_eq, sortLeaves_eq, octopusSize_eq]
  have hn : (List.ofFn fun r => (SphincsSecurity.Concrete.digestLeaves d r).val).Nodup ↔
      Function.Injective (SphincsSecurity.Concrete.digestLeaves d) := by
    rw [List.nodup_ofFn]
    exact ⟨fun h a b e => h (congrArg Fin.val e), fun h a b e => h (Fin.ext e)⟩
  by_cases h1 : Function.Injective (SphincsSecurity.Concrete.digestLeaves d) <;>
    by_cases h2 : SphincsSecurity.Concrete.octopusSize
      (SphincsSecurity.Concrete.sortedLeaves (SphincsSecurity.Concrete.digestLeaves d)) ≤ 120 <;>
    simp [hn, h1, h2, Ref.porsM, SphincsSecurity.ftsAuthCapacity]

end SigGolfCandidate.Equiv
