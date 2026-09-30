import SigGolfCandidate.Expand.Base
import Mathlib.Data.List.GetD

/-!
# The segment stream as it is being written

`curStream sig segs cnt` : the stream bytes after the completed segments `segs` and `cnt` items
of the current segment: `segStream sig segs`, an (unwritten, zero) 8-byte header, then the items.
The machine writes the header byte when the segment ends (`curStream_emit`) and appends items one
by one (`curStream_succ`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Expand
open SigGolf SigGolfCandidate.Ref

/-- The number of auth items consumed by the segments `segs`. -/
def nsum (segs : List Nat) : Nat := (segs.map (· % 16)).sum

/-- `n` auth items from item `r0` on. -/
def items (sig : List Byte) (r0 n : Nat) : List Byte :=
  ((List.range n).map fun i => sigAuth sig (r0 + i)).flatten

def curStream (sig : List Byte) (segs : List Nat) (cnt : Nat) : List Byte :=
  segStream sig segs ++ zeros 8 ++ items sig (nsum segs) cnt

theorem streamFold_snd (sig : List Byte) (segs : List Nat) :
    (segs.foldl (streamStep sig) ([], 0)).2 = nsum segs := by
  suffices h : ∀ (p : List Byte × Nat), (segs.foldl (streamStep sig) p).2 = p.2 + nsum segs by
    simpa using h ([], 0)
  induction segs with
  | nil => intro p; simp [nsum]
  | cons b segs ih =>
    intro p; rw [List.foldl_cons, ih]; simp [streamStep, nsum]; omega

theorem segStream_snoc (sig : List Byte) (segs : List Nat) (b : Nat) :
    segStream sig (segs ++ [b]) =
      segStream sig segs ++ [byte b] ++ zeros 7 ++ items sig (nsum segs) (b % 16) := by
  unfold segStream
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
  simp only [streamStep, items]
  rw [streamFold_snd]

theorem nsum_snoc (segs : List Nat) (b : Nat) : nsum (segs ++ [b]) = nsum segs + b % 16 := by
  simp [nsum]

theorem items_succ (sig : List Byte) (r0 n : Nat) :
    items sig r0 (n + 1) = items sig r0 n ++ sigAuth sig (r0 + n) := by
  simp [items, List.range_succ]

theorem curStream_succ (sig : List Byte) (segs : List Nat) (cnt : Nat) :
    curStream sig segs (cnt + 1) = curStream sig segs cnt ++ sigAuth sig (nsum segs + cnt) := by
  simp [curStream, items_succ]

theorem getD_zeros (k i : Nat) : (zeros k).getD i 0 = 0 := by
  unfold zeros; rw [List.getD_eq_getElem?_getD]; simp

theorem length_sigAuth (sig : List Byte) (hsig : sig.length = 6100) (r : Nat) (hr : r < 120) :
    (sigAuth sig r).length = 16 := by
  simp [sigAuth, sigItem, slice, porsK, hsig]; omega

theorem getD_sigAuth (sig : List Byte) (hsig : sig.length = 6100) (r k : Nat) (hr : r < 120) (hk : k < 16) :
    (sigAuth sig r).getD k 0 = sig.getD (256 + 16 * r + k) 0 := by
  simp only [sigAuth, sigItem, slice, porsK, List.getD_eq_getElem?_getD, List.getElem?_take,
    List.getElem?_drop]
  rw [if_pos hk]; congr 2; ring

theorem length_items (sig : List Byte) (hsig : sig.length = 6100) (r0 n : Nat) (hr : r0 + n ≤ 120) :
    (items sig r0 n).length = 16 * n := by
  induction n with
  | zero => simp [items]
  | succ n ih => rw [items_succ, List.length_append, ih (by omega), length_sigAuth sig hsig _ (by omega)]; ring

theorem length_segStream (sig : List Byte) (hsig : sig.length = 6100) :
    ∀ segs : List Nat, nsum segs ≤ 120 → (segStream sig segs).length = 8 * segs.length + 16 * nsum segs := by
  intro segs
  induction segs using List.reverseRecOn with
  | nil => intro _; simp [segStream, nsum]
  | append_singleton segs b ih =>
    intro h
    rw [nsum_snoc] at h
    rw [segStream_snoc, List.length_append, List.length_append, List.length_append, ih (by omega),
      length_items sig hsig _ _ (by omega), nsum_snoc]
    simp [zeros]; ring

theorem getD_append_zeros (l : List Byte) (n k : Nat) : (l ++ zeros n).getD k 0 = l.getD k 0 := by
  by_cases h : k < l.length
  · exact List.getD_append _ _ _ _ h
  · rw [List.getD_append_right _ _ _ _ (by omega), getD_zeros, List.getD_eq_default _ _ (by omega)]

/-- Emitting the header byte `b` of the current segment (with `b % 16 = cnt` items). -/
theorem curStream_emit (sig : List Byte) (segs : List Nat) (b cnt : Nat) (hb : b % 16 = cnt) (i : Nat) :
    (curStream sig (segs ++ [b]) 0).getD i 0 =
      if i = (segStream sig segs).length then byte b else (curStream sig segs cnt).getD i 0 := by
  have hl : curStream sig (segs ++ [b]) 0 =
      segStream sig segs ++ ([byte b] ++ zeros 7 ++ items sig (nsum segs) cnt ++ zeros 8) := by
    simp only [curStream, segStream_snoc, hb, nsum_snoc, items, List.range_zero, List.map_nil,
      List.flatten_nil, List.append_nil, List.append_assoc]
  have hr : curStream sig segs cnt = segStream sig segs ++ (zeros 8 ++ items sig (nsum segs) cnt) := by
    simp only [curStream, List.append_assoc]
  rw [hl, hr]
  set P := segStream sig segs
  set I := items sig (nsum segs) cnt
  simp only [List.append_assoc]
  by_cases h1 : i < P.length
  · rw [if_neg (by omega), List.getD_append P _ _ _ h1, List.getD_append P _ _ _ h1]
  · rw [List.getD_append_right P _ _ _ (by omega), List.getD_append_right P _ _ _ (by omega)]
    by_cases h2 : i = P.length
    · subst h2; simp
    · rw [if_neg h2]
      obtain ⟨k, hk⟩ : ∃ k, i - P.length = k + 1 := ⟨i - P.length - 1, by omega⟩
      rw [hk, List.cons_append, List.nil_append, List.getD_cons_succ,
        show zeros 8 = 0 :: zeros 7 from rfl, List.cons_append, List.getD_cons_succ,
        ← List.append_assoc, show (0 : Byte) :: zeros 7 = zeros 8 from rfl, getD_append_zeros]

end SigGolfCandidate.Expand
