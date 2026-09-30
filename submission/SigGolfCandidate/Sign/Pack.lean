import SigGolfCandidate.Sign.Bytes
import SigGolfCandidate.Sign.TreeBuildNode
import SigGolfCandidate.Sign.PackRun

/-!
# `sign`: the pack (instructions 614 .. 3394)

`pack_bytes` : after the pack, the signature layer region `SIG + 2480 ..` holds the staged bytes
in signature order: layer `l` = the 4 counter bytes at `STG + 856 l`, then its body at
`STG + 856 l + 8`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option maxRecDepth 100000

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem packTab_length : packTab.length = 491 := by decide +kernel

/-- Table sanity (checked by the kernel). -/
theorem packTab_ok : packTab.all (fun e => decide (e.1 ≤ 2) &&
    (if e.1 = 0 then decide (e.2.1 % 8 = 0) else decide (e.2.1 % 4 = 0 ∧ e.2.2 % 4 = 0)) &&
    decide (e.2.1 + 8 < 0x3300 ∧ e.2.2 + 8 < 0x3300)) = true := by decide +kernel

/-- The stage address of byte `i` of the dword of entry `e`. -/
def srcA (e : Nat × Nat × Nat) (i : Nat) : Nat :=
  if e.1 = 0 then e.2.1 + i else if i < 4 then e.2.1 + i else e.2.2 + (i - 4)

theorem packDW_byte (t : MachineState) (e : Nat × Nat × Nat) (he : e ∈ packTab) (i : Nat) (hi : i < 8)
    (h2 : e.1 = 2 → i < 4) :
    extractByte (packDW t e) i = t.getByte (BitVec.ofNat 64 (srcA e i)) := by
  have hok := List.all_eq_true.mp packTab_ok e he
  obtain ⟨k, lo, hi'⟩ := e
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨hk, hal⟩, hlo, hhi⟩ := hok
  have hbo : ∀ a, a % 4 = 0 → a + 8 < 2 ^ 64 → byteOffset (BitVec.ofNat 64 a) = 0 ∨
      byteOffset (BitVec.ofNat 64 a) = 4 := by
    intro a ha hb; rw [byteOffset_ofNat (by omega)]; omega
  have hgb : ∀ a j, a % 4 = 0 → a + 8 < 0x3300 → j < 4 →
      extractByte (t.getMem (alignToDword (BitVec.ofNat 64 a))) (byteOffset (BitVec.ofNat 64 a) + j) =
        t.getByte (BitVec.ofNat 64 (a + j)) := by
    intro a j ha hb hj
    rw [byteOffset_ofNat (by omega), show alignToDword (BitVec.ofNat 64 a) = BitVec.ofNat 64 (a / 8 * 8) by
      apply BitVec.eq_of_toNat_eq; rw [alignToDword_toNat]; simp; omega]
    rw [← getByte_aligned' t (a / 8 * 8) (a % 8 + j) (by omega) (by omega) (by omega)]
    congr 2; omega
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · simp only [packDW, srcA, if_true, decide_eq_true_eq] at hal ⊢
    rw [getByte_aligned' t lo i hal hi (by omega)]
  · simp only [packDW, srcA, if_neg (show (1 : Nat) ≠ 0 by decide), decide_eq_true_eq] at hal ⊢
    rw [extractByte_pair _ _ _ _ i (hbo lo hal.1 (by omega)) (hbo hi' hal.2 (by omega)) hi]
    split
    · exact hgb lo i hal.1 hlo (by omega)
    · exact hgb hi' (i - 4) hal.2 hhi (by omega)
  · simp only [packDW, srcA, if_neg (show (2 : Nat) ≠ 0 by decide), decide_eq_true_eq] at hal ⊢
    have := h2 rfl
    rw [extractByte_lwuW _ _ i (hbo lo hal.1 (by omega)) hi, if_pos this, if_pos this]
    exact hgb lo i hal.1 hlo this

theorem packTab_kind2_ok : (packTab.take 490).all (fun e => decide (e.1 ≠ 2)) = true := by
  decide +kernel

theorem packTab_kind2 : ∀ j < 490, (packTab.getD j (0, 0, 0)).1 ≠ 2 := by
  intro j hj
  rw [getD_of_lt (by rw [packTab_length]; omega)]
  have hm : packTab[j]'(by rw [packTab_length]; omega) ∈ packTab.take 490 :=
    List.mem_iff_getElem.mpr ⟨j, by simp [packTab_length]; omega, by simp⟩
  simpa using List.all_eq_true.mp packTab_kind2_ok _ hm

/-- **Pack**: the signature layer region after the pack, as stage bytes. -/
theorem pack_bytes (t u : MachineState)
    (hw : u.readWords (BitVec.ofNat 64 (0x3300 + 2176)) 491 = packTab.map (packDW t)) :
    bytesAt u (0x3300 + 2176) 3924 =
      (List.range 3924).map (fun p =>
        t.getByte (BitVec.ofNat 64 (srcA (packTab.getD (p / 8) (0, 0, 0)) (p % 8)))) := by
  apply List.ext_getElem (by simp)
  intro p h1 h2
  simp only [length_bytesAt] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range]
  rw [show 0x3300 + 2176 + p = (0x3300 + 2176 + 8 * (p / 8)) + p % 8 by omega,
    getByte_aligned' _ _ _ (by omega) (by omega) (by omega),
    getMem_of_readWords _ 491 _ (p / 8) _ hw (by omega)]
  have hmem : packTab.getD (p / 8) (0, 0, 0) ∈ packTab := by
    rw [getD_of_lt (by rw [packTab_length]; omega)]; exact List.getElem_mem _
  rw [show (packTab.map (packDW t)).getD (p / 8) 0 = packDW t (packTab.getD (p / 8) (0, 0, 0)) by
    rw [getD_of_lt (by simp [packTab_length]; omega), getD_of_lt (by rw [packTab_length]; omega)]
    simp]
  apply packDW_byte t _ hmem _ (by omega)
  intro h
  by_cases hp : p / 8 < 490
  · exact absurd h (packTab_kind2 _ hp)
  · omega

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

/-- The source addresses of the table entries, 8 per entry. -/
def blocks8 (T : List (Nat × Nat × Nat)) : List Nat := T.flatMap (fun e => (List.range 8).map (srcA e))

theorem length_blocks8 (T : List (Nat × Nat × Nat)) : (blocks8 T).length = 8 * T.length := by
  induction T with
  | nil => rfl
  | cons e T ih => simp only [blocks8, List.flatMap_cons, List.length_append, List.length_map,
      List.length_range] at ih ⊢; rw [ih, List.length_cons]; ring

theorem getElem_blocks8 (T : List (Nat × Nat × Nat)) (p : Nat) (hp : p < (blocks8 T).length) :
    (blocks8 T)[p] = srcA (T.getD (p / 8) (0, 0, 0)) (p % 8) := by
  induction T generalizing p with
  | nil => simp [blocks8] at hp
  | cons e T ih =>
    simp only [blocks8, List.flatMap_cons] at hp ⊢
    by_cases h8 : p < 8
    · rw [List.getElem_append_left (by simp; omega)]
      simp [Nat.div_eq_of_lt h8, Nat.mod_eq_of_lt h8]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_map, List.length_range]
      have hp' : p - 8 < (blocks8 T).length := by
        simp only [List.length_append, List.length_map, List.length_range] at hp
        exact (by unfold blocks8; omega)
      refine (ih (p - 8) hp').trans ?_
      rw [show p / 8 = (p - 8) / 8 + 1 by omega, show p % 8 = (p - 8) % 8 by omega]
      rfl

/-- The pack's source addresses, layer by layer (checked by the kernel, linear size). -/
theorem blocks8_packTab : (blocks8 packTab).take 3924 =
    (List.range 5).flatMap (fun l => (List.range 4).map (fun i => 0x900 + 856 * l + i) ++
      (List.range (672 + 16 * height l)).map (fun i => 0x900 + 856 * l + 8 + i)) := by
  decide +kernel

theorem pack_addrs : (List.range 3924).map (fun p => srcA (packTab.getD (p / 8) (0, 0, 0)) (p % 8)) =
    (List.range 5).flatMap (fun l => (List.range 4).map (fun i => 0x900 + 856 * l + i) ++
      (List.range (672 + 16 * height l)).map (fun i => 0x900 + 856 * l + 8 + i)) := by
  rw [← blocks8_packTab]
  apply List.ext_getElem (by simp [length_blocks8, packTab_length])
  intro p h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  rw [getElem_blocks8]

theorem pack_layers (t u : MachineState)
    (hw : u.readWords (BitVec.ofNat 64 (0x3300 + 2176)) 491 = packTab.map (packDW t)) :
    bytesAt u (0x3300 + 2176) 3924 =
      (List.range 5).flatMap (fun l => bytesAt t (0x900 + 856 * l) 4 ++
        bytesAt t (0x900 + 856 * l + 8) (672 + 16 * height l)) := by
  rw [pack_bytes t u hw]
  have h := congrArg (List.map (fun a => t.getByte (BitVec.ofNat 64 a))) pack_addrs
  simp only [List.map_map, List.map_flatMap, List.map_append] at h
  rw [show (fun p => t.getByte (BitVec.ofNat 64 (srcA (packTab.getD (p / 8) (0, 0, 0)) (p % 8)))) =
    ((fun a => t.getByte (BitVec.ofNat 64 a)) ∘ fun p => srcA (packTab.getD (p / 8) (0, 0, 0)) (p % 8))
    from rfl, h]
  rfl

end SigGolfCandidate.Sign
