import SigGolfCandidate.Sign.Init

/-!
# The cache MAC: hash input and tag comparison (byte ↔ dword lemmas)

* `words_macInput` : the padded MAC input as dwords (`tw_mac | P | S | region | 0^32`).
* `answerBytes_32` / `toList_tag` : a 256-bit answer as four dwords.
* `tag_eq_iff` : a 32-byte tag equals the answer iff the four dwords agree.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Sign
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem words_macInput (S region : List Byte) (hS : S.length = 32) (hR : region.length = 65504) :
    padBlocks (macInput S region).length = 1024 ∧
    wordsOf (padTo64 (macInput S region)) =
      twWords 14 0 0 0 0 ++ [0, 0] ++ wordsOf S ++ wordsOf region ++ [0, 0, 0, 0] := by
  obtain ⟨h1, h2⟩ := padTo64_eq (macInput S region) 1024 (by simp [macInput, hS, hR])
    (by simp [macInput, hS, hR])
  refine ⟨h1, ?_⟩
  rw [h2, macInput, wordsOf_thInput_pad]
  simp only [length_thInput, length_tweak, List.length_append, hS, hR]
  rw [List.append_assoc S, wordsOf_append _ _ (by omega), wordsOf_append _ _ (by omega),
    show 64 * (1024 + 1) - (16 + 16 + (32 + 65504)) = 8 * 4 from rfl, wordsOf_zeros]
  simp

theorem answerBytes_32 (a : BitVec 256) :
    answerBytes 32 a = bytesOfWord (a.extractLsb' 0 64) ++ bytesOfWord (a.extractLsb' 64 64) ++
      bytesOfWord (a.extractLsb' 128 64) ++ bytesOfWord (a.extractLsb' 192 64) := by
  unfold answerBytes bytesOfWord
  simp only [List.range_succ, List.range_zero, List.map_cons, List.map_nil,
    List.nil_append, List.cons_append, List.map_append, List.append_assoc]
  simp only [extractLsb'_extractLsb' _ _ _ (by norm_num : (0 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (1 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (2 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (3 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (4 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (5 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (6 : Nat) < 8),
    extractLsb'_extractLsb' _ _ _ (by norm_num : (7 : Nat) < 8)]

theorem toList_tag (a : BitVec 256) :
    toList (n := 32) a = bytesOfWord (a.extractLsb' 0 64) ++ bytesOfWord (a.extractLsb' 64 64) ++
      bytesOfWord (a.extractLsb' 128 64) ++ bytesOfWord (a.extractLsb' 192 64) :=
  answerBytes_32 a

theorem bytesOfWord_inj {w w' : Word} (h : bytesOfWord w = bytesOfWord w') : w = w' := by
  apply BitVec.eq_of_toNat_eq
  rw [← leNat_bytesOfWord, ← leNat_bytesOfWord, h]

/-- An 8-byte list is the bytes of its dword. -/
theorem bytesOfWord_leNat (l : List Byte) (hl : l.length = 8) :
    bytesOfWord (BitVec.ofNat 64 (leNat l)) = l := by
  apply List.ext_getElem (by simp [hl])
  intro j hj1 hj2
  simp only [bytesOfWord, List.getElem_map, List.getElem_range]
  rw [extractByte_ofNat _ _ _ (by simp at hj1; omega)]
  apply BitVec.eq_of_toNat_eq
  rw [byte_toNat, leNat_div_mod, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj2]; rfl

/-- A 32-byte list from its four dwords. -/
theorem eq_of_words4 (l : List Byte) (hl : l.length = 32) (c0 c1 c2 c3 : Word)
    (hw : wordsOf l = [c0, c1, c2, c3]) :
    l = bytesOfWord c0 ++ bytesOfWord c1 ++ bytesOfWord c2 ++ bytesOfWord c3 := by
  have e : l = l.take 8 ++ (l.drop 8).take 8 ++ ((l.drop 8).drop 8).take 8 ++ ((l.drop 8).drop 8).drop 8 := by
    simp only [List.append_assoc, List.take_append_drop]
  rw [e, wordsOf_append _ _ (by simp; omega), wordsOf_append _ _ (by simp; omega),
    wordsOf_append _ _ (by simp; omega), wordsOf_eight _ (by simp; omega), wordsOf_eight _ (by simp; omega),
    wordsOf_eight _ (by simp; omega), wordsOf_eight _ (by simp; omega)] at hw
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at hw
  obtain ⟨h0, h1, h2, h3⟩ := hw
  rw [e, ← h0, ← h1, ← h2, ← h3, bytesOfWord_leNat _ (by simp; omega), bytesOfWord_leNat _ (by simp; omega),
    bytesOfWord_leNat _ (by simp; omega), bytesOfWord_leNat _ (by simp; omega)]

theorem append4_inj {a0 a1 a2 a3 b0 b1 b2 b3 : Word}
    (h : bytesOfWord a0 ++ bytesOfWord a1 ++ bytesOfWord a2 ++ bytesOfWord a3 =
      bytesOfWord b0 ++ bytesOfWord b1 ++ bytesOfWord b2 ++ bytesOfWord b3) :
    a0 = b0 ∧ a1 = b1 ∧ a2 = b2 ∧ a3 = b3 := by
  simp only [List.append_assoc] at h
  obtain ⟨h0, h⟩ := List.append_inj h (by simp)
  obtain ⟨h1, h⟩ := List.append_inj h (by simp)
  obtain ⟨h2, h3⟩ := List.append_inj h (by simp)
  exact ⟨bytesOfWord_inj h0, bytesOfWord_inj h1, bytesOfWord_inj h2, bytesOfWord_inj h3⟩

/-- The tag comparison, dword by dword. -/
theorem tag_eq_iff (a : BitVec 256) (l : List Byte) (hl : l.length = 32) (c0 c1 c2 c3 : Word)
    (hw : wordsOf l = [c0, c1, c2, c3]) :
    toList (n := 32) a = l ↔ a.extractLsb' 0 64 = c0 ∧ a.extractLsb' 64 64 = c1 ∧
      a.extractLsb' 128 64 = c2 ∧ a.extractLsb' 192 64 = c3 := by
  rw [toList_tag, eq_of_words4 l hl c0 c1 c2 c3 hw]
  constructor
  · exact append4_inj
  · rintro ⟨rfl, rfl, rfl, rfl⟩; rfl

end SigGolfCandidate.Sign
