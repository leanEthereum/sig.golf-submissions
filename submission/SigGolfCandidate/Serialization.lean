import SigGolfCandidate.Memory
import SigGolfCandidate.Hypertree.Reference

namespace SigGolfCandidate.Serialization
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64

theorem zipIdx_eq_range (data : List Byte) :
    data.zipIdx = (List.range data.length).map (fun i => (getByteAt data i, i)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range]
    have index : i < data.length := by simpa using hi
    simp [getByteAt, index]

/-- A query is determined by its block count and numeric contents. -/
theorem query_eq (first second : Query) (length : first.1 = second.1)
    (value : first.2.toNat = second.2.toNat) : first = second := by
  rcases first with ⟨n, first⟩
  rcases second with ⟨m, second⟩
  dsimp only at length value
  subst m
  exact congrArg (fun v : Bytes (64 * (n + 1)) => (⟨n, v⟩ : Query)) (BitVec.eq_of_toNat_eq value)

/-- Zero bytes past the end of the data add nothing to the little-endian number. -/
private theorem fold_zero_tail (g : Nat → Nat) (n k initial : Nat)
    (zero : ∀ i, n ≤ i → i < n + k → g i = 0) :
    (List.range (n + k)).foldl (fun acc i => acc + g i * 2 ^ (8 * i)) initial =
      (List.range n).foldl (fun acc i => acc + g i * 2 ^ (8 * i)) initial := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, List.range_succ, List.foldl_append,
      ih (fun i low high => zero i low (by omega))]
    simp [zero (n + k) (by omega) (by omega)]

/-- A buffer holding these bytes, and zero bytes up to the next block boundary, produces precisely
the reference scheme's oracle query. -/
theorem hashInput_of_padded (s : MachineState) (base : Nat) (data : List Byte)
    (source : s.getReg .x10 = BitVec.ofNat 64 base)
    (length : (s.getReg .x11).toNat = 64 * ((data.length - 1) / 64 + 1))
    (h : ∀ i, (hi : i < data.length) → s.getByte (BitVec.ofNat 64 (base + i)) = data[i]'hi)
    (zero : ∀ i, data.length ≤ i → i < 64 * ((data.length - 1) / 64 + 1) →
      s.getByte (BitVec.ofNat 64 (base + i)) = 0) :
    hashInput s = Hypertree.Reference.packed data := by
  have blocks : (s.getReg .x11).toNat / 64 - 1 = (data.length - 1) / 64 := by omega
  apply query_eq
  · exact blocks
  · dsimp only [hashInput, Hypertree.Reference.packed, Hypertree.Reference.packValue]
    simp only [BitVec.toNat_ofNat]
    rw [blocks]
    congr 1
    have same : (List.range (64 * ((data.length - 1) / 64 + 1))).foldl (fun acc i =>
        acc + (s.getByte (s.getReg .x10 + BitVec.ofNat 64 i)).toNat * 2 ^ (8 * i)) 0 =
        (List.range (64 * ((data.length - 1) / 64 + 1))).foldl (fun acc i =>
          acc + (getByteAt data i).toNat * 2 ^ (8 * i)) 0 := by
      apply Memory.foldl_eq_on
      intro i hi acc
      have bound : i < 64 * ((data.length - 1) / 64 + 1) := by simpa using hi
      rw [source, ← BitVec.ofNat_add]
      by_cases inside : i < data.length
      · rw [h i inside]
        simp [getByteAt, inside]
      · rw [zero i (by omega) bound]
        simp [getByteAt, inside]
    rw [same, show 64 * ((data.length - 1) / 64 + 1) = data.length +
      (64 * ((data.length - 1) / 64 + 1) - data.length) by omega,
      fold_zero_tail (fun i => (getByteAt data i).toNat) data.length _ 0 (by
        intro i low _
        simp [getByteAt, show ¬i < data.length by omega]),
      zipIdx_eq_range, List.foldl_map]

/-- A buffer of whole blocks with these bytes produces precisely the reference scheme's oracle query. -/
theorem hashInput_of_list (s : MachineState) (base : Nat) (data : List Byte)
    (source : s.getReg .x10 = BitVec.ofNat 64 base)
    (length : (s.getReg .x11).toNat = data.length)
    (whole : data.length % 64 = 0) (nonempty : 0 < data.length)
    (h : ∀ i, (hi : i < data.length) → s.getByte (BitVec.ofNat 64 (base + i)) = data[i]'hi) :
    hashInput s = Hypertree.Reference.packed data :=
  hashInput_of_padded s base data source (by omega) h (fun i low high => by omega)

/-- info: 'SigGolfCandidate.Serialization.hashInput_of_padded' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms hashInput_of_padded

end SigGolfCandidate.Serialization
