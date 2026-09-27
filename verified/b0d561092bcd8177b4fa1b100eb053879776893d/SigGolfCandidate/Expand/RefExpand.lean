import SigGolfCandidate.Expand.Witness
import SigGolfCandidate.Expand.Pad

/-!
# `expandOf` (the pure part of `expandRef`) in the machine's terms
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Expand
open SigGolf SigGolfCandidate.Ref

theorem sigAuth_zero_iff (sig : List Byte) (hsig : sig.length = 6100) (i : Nat) (hi : i < 120) :
    sigAuth sig i = zeros 16 ↔ ∀ k < 16, sig.getD (256 + 16 * i + k) 0 = 0 := by
  have hl := length_sigAuth sig hsig i hi
  constructor
  · intro h k hk; rw [← getD_sigAuth sig hsig i k hi hk, h, getD_zeros]
  · intro h
    apply List.ext_getElem (by rw [hl]; simp [zeros])
    intro k h1 h2
    have := h k (by omega)
    rw [← getD_sigAuth sig hsig i k hi (by omega), List.getD_eq_getElem _ _ h1] at this
    rw [this]; exact (List.getElem_replicate _).symm

theorem all_iff_padOK (sig : List Byte) (hsig : sig.length = 6100) (n : Nat) (hn : n ≤ 120) :
    (List.range' n (porsM - n)).all (fun i => sigAuth sig i == zeros 16) = true ↔ PadOK sig n := by
  rw [List.all_eq_true]
  simp only [List.mem_range', beq_iff_eq, porsM]
  constructor
  · intro h j hj hj'
    have := (sigAuth_zero_iff sig hsig ((j - 256) / 16) (by omega)).mp
      (h ((j - 256) / 16) ⟨(j - 256) / 16 - n, by omega, by omega⟩) ((j - 256) % 16) (by omega)
    rwa [show 256 + 16 * ((j - 256) / 16) + (j - 256) % 16 = j by omega] at this
  · rintro h i ⟨k, hk, rfl⟩
    rw [sigAuth_zero_iff sig hsig _ (by omega)]
    intro k' hk'
    exact h _ (by omega) (by omega)

theorem expandOf_none {sig : List Byte} {N : Nat}
    (h : ¬ ((leavesOf N).Nodup ∧ octopusSize (sortLeaves (leavesOf N)) ≤ porsM)) : expandOf sig N = none := by
  unfold expandOf
  dsimp only
  by_cases h1 : (leavesOf N).Nodup
  · rw [if_neg (by simp [h1]), if_pos (Nat.lt_of_not_le fun h2 => h ⟨h1, h2⟩)]
  · rw [if_pos (by simp [h1])]

theorem expandOf_eq {sig : List Byte} {N : Nat} (h1 : (leavesOf N).Nodup)
    (h2 : octopusSize (sortLeaves (leavesOf N)) ≤ porsM) :
    expandOf sig N =
      if (List.range' (schedule (sortLeaves (leavesOf N))).2.length
          (porsM - (schedule (sortLeaves (leavesOf N))).2.length)).all (fun i => sigAuth sig i == zeros 16)
      then some (witnessList sig (leavesOf N) (sortLeaves (leavesOf N)) (schedule (sortLeaves (leavesOf N))).1)
      else none := by
  unfold expandOf
  dsimp only
  rw [if_neg (by simp [h1]), if_neg (by omega)]
  generalize schedule (sortLeaves (leavesOf N)) = p
  obtain ⟨segs, reads⟩ := p
  dsimp only
  cases h : (List.range' reads.length (porsM - reads.length)).all (fun i => sigAuth sig i == zeros 16) <;> rfl

end SigGolfCandidate.Expand
