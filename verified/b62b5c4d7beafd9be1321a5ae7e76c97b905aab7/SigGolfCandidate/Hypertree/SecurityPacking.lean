import SigGolfCandidate.Hypertree.Reference
import Mathlib.Data.Nat.Digits.Lemmas

namespace SigGolfCandidate.Hypertree.SecurityPacking
open SigGolf Reference
set_option maxRecDepth 4096

theorem packValue_eq (data : List Byte) :
    packValue data = Nat.ofDigits 256 (data.map BitVec.toNat) := by
  unfold packValue
  rw [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_zipIdx_map, List.zipIdx_map,
    List.map_map, List.sum_eq_foldl, List.foldl_map]
  congr 1
  funext acc entry
  simp only [Function.comp_def, Prod.map_fst, Prod.map_snd, id_eq]
  rw [pow_mul]
  rfl

theorem packValue_lt (data : List Byte) : packValue data < 2 ^ (8 * data.length) := by
  have h := Nat.ofDigits_lt_base_pow_length (b := 256) (by decide)
    (l := data.map BitVec.toNat) (by
      intro value hv
      obtain ⟨byte, _, rfl⟩ := List.mem_map.mp hv
      exact byte.isLt)
  rw [packValue_eq]
  simpa [List.length_map, pow_mul] using h

theorem packValue_append (first second : List Byte) :
    packValue (first ++ second) = packValue first + 2 ^ (8 * first.length) * packValue second := by
  rw [packValue_eq, packValue_eq, packValue_eq, List.map_append, Nat.ofDigits_append, List.length_map,
    pow_mul]
  rfl

/-- Equal-length byte strings with one little-endian number are equal. -/
theorem packValue_injective {first second : List Byte} (length : first.length = second.length)
    (same : packValue first = packValue second) : first = second := by
  rw [packValue_eq, packValue_eq] at same
  have hmap := Nat.ofDigits_inj_of_len_eq (by decide : 1 < 256)
    (by simpa using length)
    (by intro value hv; obtain ⟨byte, _, rfl⟩ := List.mem_map.mp hv; exact byte.isLt)
    (by intro value hv; obtain ⟨byte, _, rfl⟩ := List.mem_map.mp hv; exact byte.isLt) same
  exact (List.map_injective_iff.mpr (fun _ _ h => BitVec.eq_of_toNat_eq h)) hmap

@[simp] theorem packed_blocks (data : List Byte) : (packed data).1 = (data.length - 1) / 64 := rfl

/-- Zero padding to whole blocks keeps every input byte: the packed number is exact. -/
theorem packed_toNat (data : List Byte) : (packed data).2.toNat = packValue data := by
  change (BitVec.ofNat _ (packValue data)).toNat = packValue data
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
  calc packValue data < 2 ^ (8 * data.length) := packValue_lt data
    _ ≤ 2 ^ (8 * (64 * ((data.length - 1) / 64 + 1))) := Nat.pow_le_pow_right (by decide) (by omega)

theorem packed_value {first second : List Byte} (same : packed first = packed second) :
    packValue first = packValue second := by
  have h := congrArg (fun query : Query => query.2.toNat) same
  simpa only [packed_toNat] using h

/-- One packed input determines each byte string of a fixed length. Different lengths are
told apart by their domains, not by the zero padding. -/
theorem packed_injective {first second : List Byte} (same : packed first = packed second)
    (length : first.length = second.length) : first = second :=
  packValue_injective length (packed_value same)

/-- One packed input determines every fixed-length prefix, whatever follows it. -/
theorem packed_prefix {first second rest rest' : List Byte}
    (same : packed (first ++ rest) = packed (second ++ rest'))
    (length : first.length = second.length) : first = second := by
  have h := packed_value same
  rw [packValue_append, packValue_append, ← length] at h
  have m := congrArg (· % 2 ^ (8 * first.length)) h
  simp only [Nat.add_mul_mod_self_left] at m
  have second_lt : packValue second < 2 ^ (8 * first.length) := by
    rw [length]
    exact packValue_lt second
  rw [Nat.mod_eq_of_lt (packValue_lt first), Nat.mod_eq_of_lt second_lt] at m
  exact packValue_injective length m

@[simp] theorem chainPayload_length (value : Digest) : (chainPayload value).length = 32 := by
  simp [chainPayload, bytes]

/-- The organizer's little-endian byte encoding is injective at every fixed width. -/
theorem bytes_injective (n : Nat) : Function.Injective (bytes (n := n)) := by
  intro first second heq
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hbyte : i / 8 < n := (Nat.div_lt_iff_lt_mul (by decide)).mpr (by omega)
  have hv := congrArg (fun data : List Byte => data[i / 8]?) heq
  simp [bytes, hbyte] at hv
  have hb := congrArg (fun byte : Byte => byte.getLsbD (i % 8)) hv
  have hm : i % 8 < 8 := Nat.mod_lt _ (by decide)
  simp only [BitVec.getLsbD_extractLsb', hm, decide_true, Bool.true_and] at hb
  have hidx : 8 * (i / 8) + i % 8 = i := by omega
  simpa [hidx] using hb

/-- The chain-step payload repeats its value, so it names exactly one value. -/
theorem chainPayload_injective : Function.Injective chainPayload := by
  intro first second same
  exact bytes_injective 16 (List.append_inj_left same (by simp [bytes]))

end SigGolfCandidate.Hypertree.SecurityPacking
