import Mathlib.Data.List.Sort
import Mathlib.Tactic
import SigGolfCandidate.Sign.SchedMath

/-!
# The digest analysis as the machine performs it (pure model)

`digest_analysis` (sign instructions 78 .. 136) on the digest `N`:
* keys `keyOf N r = v_r * 256 + 8 r` (`v_r = fieldOf N r`, the 14-bit leaf index of slot `r`);
* an insertion sort of the 15 keys (`sortKeys`, the machine's in-place shifting insertion);
* a pass over the sorted keys: reject a duplicate leaf index, else sum the bit lengths of
  `v_s xor v_{s+1}` and accept iff the sum is `≤ 134` (`admissibleM`).

Facts proved here: the sorted keys are a strictly increasing permutation of the keys
(`sortKeys_perm`, `sortKeys_sorted`).
-/

namespace SigGolfCandidate.Sign

/-- Leaf index of digest slot `r`: bits `34 + 14 r .. 34 + 14 r + 13` of `N`. -/
def fieldOf (N r : Nat) : Nat := N / 2 ^ (34 + 14 * r) % 2 ^ 14

/-- The machine's sort key of slot `r`. -/
def keyOf (N r : Nat) : Nat := fieldOf N r * 256 + 8 * r

/-- The 15 keys in slot order. -/
def keys0 (N : Nat) : List Nat := (List.range 15).map (keyOf N)

/-- The machine's insertion of `x` into the sorted prefix (`rpre` = the prefix reversed, the
hole after it, `post` = the elements after the hole): shift while `x < y`, then place `x`. -/
def insRes (x : Nat) : List Nat → List Nat → List Nat
  | [], post => x :: post
  | y :: r, post => if x < y then insRes x r (y :: post) else (y :: r).reverse ++ x :: post

/-- Outer sort step `i`: insert element `i` into the prefix `0 .. i-1`. -/
def sortStep (l : List Nat) (i : Nat) : List Nat :=
  insRes (l.getD i 0) (l.take i).reverse (l.drop (i + 1))

/-- The first `n` outer steps (`i = 1 .. n`). -/
def sortN (l : List Nat) : Nat → List Nat
  | 0 => l
  | n + 1 => sortStep (sortN l n) (n + 1)

/-- The machine's sort of 15 keys. -/
def sortKeys (l : List Nat) : List Nat := sortN l 14

/-- Python's `int.bit_length`. -/
abbrev blen (x : Nat) : Nat := SigGolfCandidate.Ref.bitLen x

/-- The leaf index of a key. -/
def keyV (k : Nat) : Nat := k / 256

/-- Pass: no duplicate leaf index among neighbours `s, s + 1` (`s < 14`). -/
def passOk (l : List Nat) : Bool :=
  (List.range 14).all fun s => keyV (l.getD s 0) != keyV (l.getD (s + 1) 0)

/-- Pass: the sum of the bit lengths of the neighbour xors. -/
def passSum (l : List Nat) : Nat :=
  ((List.range 14).map fun s => blen (keyV (l.getD s 0) ^^^ keyV (l.getD (s + 1) 0))).sum

/-- The machine's decision. -/
def admissibleM (N : Nat) : Bool :=
  passOk (sortKeys (keys0 N)) && decide (passSum (sortKeys (keys0 N)) ≤ 134)

/-! ## Sorting facts -/

theorem insRes_perm (x : Nat) : ∀ (r post : List Nat), (insRes x r post).Perm (r.reverse ++ x :: post)
  | [], post => by simp [insRes]
  | y :: r, post => by
    unfold insRes
    split
    · refine (insRes_perm x r (y :: post)).trans ?_
      simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
      exact List.Perm.append_left _ (List.Perm.swap y x post)
    · exact List.Perm.refl _

theorem insRes_sorted (x : Nat) : ∀ (r post : List Nat), r.reverse.Pairwise (· < ·) → x ∉ r →
    ∃ M, insRes x r post = M ++ post ∧ M.Pairwise (· < ·) ∧ M.Perm (x :: r.reverse)
  | [], post, _, _ => ⟨[x], by simp [insRes], by simp, by simp⟩
  | y :: r, post, hs, hx => by
    have hs' : (r.reverse ++ [y]).Pairwise (· < ·) := by simpa using hs
    rw [List.pairwise_append] at hs'
    obtain ⟨hr, -, hry⟩ := hs'
    have hxy : x ≠ y := fun h => hx (h ▸ List.mem_cons_self)
    have hxr : x ∉ r := fun h => hx (List.mem_cons_of_mem _ h)
    unfold insRes
    split
    · rename_i hlt
      obtain ⟨M, hM, hMs, hMp⟩ := insRes_sorted x r (y :: post) hr hxr
      refine ⟨M ++ [y], by rw [hM]; simp, ?_, ?_⟩
      · rw [List.pairwise_append]
        refine ⟨hMs, by simp, fun a ha b hb => ?_⟩
        simp at hb; rw [hb]
        rcases List.mem_cons.mp (hMp.subset ha) with h | h
        · rw [h]; exact hlt
        · exact hry a h y List.mem_cons_self
      · refine (List.Perm.append_right _ hMp).trans ?_
        simp
    · rename_i hge
      have hyx : y < x := by omega
      refine ⟨(y :: r).reverse ++ [x], by simp, ?_, ?_⟩
      · rw [List.pairwise_append]
        refine ⟨by simpa using hs, by simp, fun a ha b hb => ?_⟩
        simp at hb; subst hb
        simp only [List.reverse_cons, List.mem_append, List.mem_reverse, List.mem_singleton] at ha
        rcases ha with h | h
        · exact lt_trans (hry a (List.mem_reverse.mpr h) y List.mem_cons_self) hyx
        · subst h; exact hyx
      · exact List.perm_append_singleton _ _

theorem length_insRes (x : Nat) : ∀ (r post : List Nat), (insRes x r post).length = r.length + 1 + post.length
  | r, post => by rw [(insRes_perm x r post).length_eq]; simp; omega

theorem length_sortN (l : List Nat) (hl : l.length = 15) : ∀ n, n ≤ 14 → (sortN l n).length = 15
  | 0, _ => hl
  | n + 1, h => by
    have ih := length_sortN l hl n (by omega)
    simp only [sortN, sortStep, length_insRes, List.length_reverse, List.length_take, List.length_drop, ih]
    omega

theorem getD_drop_take (l : List Nat) (i : Nat) (hi : i < l.length) :
    l = l.take i ++ l.getD i 0 :: l.drop (i + 1) := by
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- Invariant of the outer sort: a permutation of the keys whose first `n + 1` elements are sorted. -/
theorem sortN_inv (l : List Nat) (hl : l.length = 15) (hnd : l.Nodup) : ∀ n, n ≤ 14 →
    (sortN l n).Perm l ∧ ((sortN l n).take (n + 1)).Pairwise (· < ·)
  | 0, _ => ⟨List.Perm.refl _, by
      rcases l with _ | ⟨a, l⟩
      · simp at hl
      · simp [sortN]⟩
  | n + 1, h => by
    obtain ⟨hp, hs⟩ := sortN_inv l hl hnd n (by omega)
    have hlen := length_sortN l hl n (by omega)
    set L := sortN l n with hL
    have hsplit := getD_drop_take L (n + 1) (by omega)
    have hndL : L.Nodup := hp.nodup_iff.mpr hnd
    have hx : L.getD (n + 1) 0 ∉ (L.take (n + 1)).reverse := by
      intro hm
      rw [List.mem_reverse] at hm
      rw [hsplit] at hndL
      rw [List.nodup_append] at hndL
      exact hndL.2.2 _ hm _ List.mem_cons_self rfl
    obtain ⟨M, hM, hMs, hMp⟩ := insRes_sorted (L.getD (n + 1) 0) (L.take (n + 1)).reverse
      (L.drop (n + 1 + 1)) (by rw [List.reverse_reverse]; exact hs) hx
    have hMlen : M.length = n + 2 := by
      rw [hMp.length_eq]; simp [List.length_take, hlen]; omega
    refine ⟨?_, ?_⟩
    · show (sortStep L (n + 1)).Perm l
      unfold sortStep
      refine ((insRes_perm _ _ _).trans ?_).trans hp
      rw [List.reverse_reverse, ← hsplit]
    · show ((sortStep L (n + 1)).take (n + 1 + 1)).Pairwise (· < ·)
      unfold sortStep
      rw [hM, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      exact hMs

theorem sortKeys_perm (l : List Nat) (hl : l.length = 15) (hnd : l.Nodup) : (sortKeys l).Perm l :=
  (sortN_inv l hl hnd 14 (le_refl _)).1

theorem sortKeys_sorted (l : List Nat) (hl : l.length = 15) (hnd : l.Nodup) :
    (sortKeys l).Pairwise (· < ·) := by
  have h := (sortN_inv l hl hnd 14 (le_refl _)).2
  rwa [List.take_of_length_le (by rw [length_sortN l hl 14 (le_refl _)])] at h

theorem length_sortKeys (l : List Nat) (hl : l.length = 15) : (sortKeys l).length = 15 :=
  length_sortN l hl 14 (le_refl _)

/-! ## The machine's decision is `Ref.admissible` -/

section AnRef
open SigGolfCandidate.Ref

theorem fieldOf_eq (N r : Nat) : fieldOf N r = leafOf N r := rfl

theorem keyV_keyOf (N r : Nat) (hr : r < 32) : keyV (keyOf N r) = leafOf N r := by
  unfold keyV keyOf; rw [← fieldOf_eq]; unfold fieldOf; omega

theorem keys0_map (N : Nat) : (keys0 N).map keyV = leavesOf N := by
  unfold keys0 leavesOf porsK
  rw [List.map_map]
  apply List.map_congr_left
  intro r hr
  exact keyV_keyOf N r (by simp at hr; omega)

theorem keyOf_mod' (N r : Nat) (hr : r < 32) : keyOf N r % 256 = 8 * r := by
  unfold keyOf; omega

theorem keys0_nodup' (N : Nat) : (keys0 N).Nodup := by
  unfold keys0
  refine List.Nodup.map_on (fun a ha b hb hab => ?_) List.nodup_range
  have h1 := keyOf_mod' N a (by simp at ha; omega)
  have h2 := keyOf_mod' N b (by simp at hb; omega)
  rw [hab] at h1; omega

/-- The sorted leaf indices are the key values of the machine's sorted keys. -/
theorem sortLeaves_eq (N : Nat) : sortLeaves (leavesOf N) = (sortKeys (keys0 N)).map keyV := by
  have hl : (keys0 N).length = 15 := by simp [keys0]
  have hp := sortKeys_perm (keys0 N) hl (keys0_nodup' N)
  have hs := sortKeys_sorted (keys0 N) hl (keys0_nodup' N)
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·))
  · exact List.pairwise_insertionSort _ _
  · exact List.Pairwise.map _ (fun a b h => by unfold keyV; omega) hs
  · refine (List.perm_insertionSort _ _).trans ?_
    rw [← keys0_map]; exact (hp.map keyV).symm

theorem length_sortKeys_keys0 (N : Nat) : (sortKeys (keys0 N)).length = 15 :=
  length_sortKeys _ (by simp [keys0])

/-- For a list sorted by `≤`, no duplicates iff neighbours differ. -/
theorem nodup_iff_adj (vs : List Nat) (hs : vs.Pairwise (· ≤ ·)) :
    vs.Nodup ↔ ∀ j, j + 1 < vs.length → vs.getD j 0 ≠ vs.getD (j + 1) 0 := by
  constructor
  · intro hn j hj heq
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hj] at heq
    have := (hn.getElem_inj_iff (hi := by omega) (hj := hj)).mp heq
    omega
  · intro hadj
    have hlt : vs.Pairwise (· < ·) := by
      rw [List.pairwise_iff_getElem] at hs ⊢
      intro i j hi hj hij
      have h1 := hs i (i + 1) hi (by omega) (by omega)
      have h2 : vs[i + 1] ≤ vs[j] := by
        rcases Nat.eq_or_lt_of_le (show i + 1 ≤ j by omega) with h | h
        · subst h; exact le_refl _
        · exact hs (i + 1) j (by omega) hj h
      have h3 := hadj i (by omega)
      rw [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ (by omega)] at h3
      omega
    exact hlt.imp (fun h => Nat.ne_of_lt h)

theorem getD_map_keyV (L : List Nat) (j : Nat) : (L.map keyV).getD j 0 = keyV (L.getD j 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases L[j]? <;> rfl

theorem octo_eq (L : List Nat) (hlen : L.length = 15) :
    octopusSize (L.map keyV) = 16 + passSum L - 30 := by
  unfold octopusSize
  rw [SchedMath.zipWith_tail, List.length_map, hlen]
  have : (List.map (fun j => bitLen ((L.map keyV).getD j 0 ^^^ (L.map keyV).getD (j + 1) 0))
      (List.range (15 - 1))) = List.map (fun s => blen (keyV (L.getD s 0) ^^^ keyV (L.getD (s + 1) 0)))
      (List.range 14) := by
    apply List.map_congr_left
    intro j _
    rw [getD_map_keyV, getD_map_keyV]
  rw [this]
  unfold passSum porsH
  omega

theorem passOk_eq (L : List Nat) (hlen : L.length = 15) (hs : (L.map keyV).Pairwise (· ≤ ·)) :
    passOk L = decide (L.map keyV).Nodup := by
  rw [Bool.eq_iff_iff, decide_eq_true_eq, nodup_iff_adj _ hs, List.length_map, hlen]
  simp only [passOk, List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq]
  constructor
  · intro h j hj; rw [getD_map_keyV, getD_map_keyV]; exact h j (by omega)
  · intro h j hj; have := h j (by omega); rw [getD_map_keyV, getD_map_keyV] at this; exact this

theorem admissibleM_eq (N : Nat) : admissibleM N = admissible N := by
  have hvs := sortLeaves_eq N
  have hlen := length_sortKeys_keys0 N
  have hsorted : (sortLeaves (leavesOf N)).Pairwise (· ≤ ·) := List.pairwise_insertionSort _ _
  have hperm : (sortLeaves (leavesOf N)).Perm (leavesOf N) := List.perm_insertionSort _ _
  unfold admissibleM admissible
  have hnd : decide (leavesOf N).Nodup = decide (sortLeaves (leavesOf N)).Nodup := by
    simp only [decide_eq_decide]; exact hperm.nodup_iff.symm
  rw [hnd]
  simp only [hvs]
  rw [hvs] at hsorted
  generalize sortKeys (keys0 N) = L at hlen hsorted ⊢
  rw [passOk_eq L hlen hsorted, octo_eq L hlen]
  have : decide (passSum L ≤ 134) = decide (16 + passSum L - 30 ≤ porsM) := by
    rw [decide_eq_decide]; unfold porsM; omega
  rw [this]

end AnRef

end SigGolfCandidate.Sign
