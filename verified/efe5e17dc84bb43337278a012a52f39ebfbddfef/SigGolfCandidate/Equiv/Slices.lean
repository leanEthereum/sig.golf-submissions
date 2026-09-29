import SigGolfCandidate.Equiv.Basic

/-!
# Byte-list slices

Generic lemmas on `Ref.slice` of concatenations, used by the cache, witness and signature layouts.
-/

namespace SigGolfCandidate.Equiv

open SigGolfCandidate.Legacy (Byte Bytes)
open SphincsSecurity (Digest)

set_option linter.unusedSimpArgs false

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

section slices


theorem slice_append_left (A B : List Byte) (off len : Nat) (h : off + len ≤ A.length) :
    Ref.slice (A ++ B) off len = Ref.slice A off len := by
  unfold Ref.slice
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem slice_append_right (A B : List Byte) (off off' len : Nat) (h : off = A.length + off') :
    Ref.slice (A ++ B) off len = Ref.slice B off' len := by
  unfold Ref.slice
  subst h
  rw [List.drop_append, List.drop_eq_nil_of_le (by omega)]
  simp

theorem slice_full (A : List Byte) (len : Nat) (h : A.length = len) : Ref.slice A 0 len = A := by
  unfold Ref.slice; subst h; simp

theorem slice_split (l : List Byte) (a b c : Nat) :
    Ref.slice l a (b + c) = Ref.slice l a b ++ Ref.slice l (a + b) c := by
  simp [Ref.slice, List.take_add, List.drop_drop, Nat.add_comm]

theorem slice_flatten_ofFn {n : Nat} (f : Fin n → List Byte) (k : Nat) (i : Fin n) (r len off : Nat)
    (hf : ∀ j : Fin n, j.val < i.val → (f j).length = k) (hr : r + len ≤ (f i).length)
    (hoff : off = k * i.val + r) :
    Ref.slice (List.ofFn f).flatten off len = Ref.slice (f i) r len := by
  induction n generalizing off with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons]
    cases i using Fin.cases with
    | zero =>
      simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add] at hoff
      subst hoff
      exact slice_append_left _ _ _ _ hr
    | succ i =>
      have h0 := hf 0 (by simp)
      rw [slice_append_right _ _ _ (k * i.val + r) _ (by simp [Fin.val_succ] at hoff; rw [h0, hoff]; ring)]
      exact ih (f := fun j => f j.succ) (i := i) (off := k * i.val + r)
        (hf := fun j hj => hf j.succ (by simp; omega)) (hr := hr) (hoff := rfl)

theorem flatten_ofFn_slices (l : List Byte) (a k n : Nat) :
    (List.ofFn fun i : Fin n => Ref.slice l (a + k * i.val) k).flatten = Ref.slice l a (k * n) := by
  induction n with
  | zero => simp [Ref.slice]
  | succ n ih =>
    rw [List.ofFn_succ_last, List.flatten_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih, ← slice_split, Nat.mul_succ]

theorem length_slice (l : List Byte) (a len : Nat) (h : a + len ≤ l.length) :
    (Ref.slice l a len).length = len := by
  simp [Ref.slice]; omega

end slices

theorem length_flatten_ofFn {n : Nat} (f : Fin n → List Byte) (k : Nat) (hf : ∀ j, (f j).length = k) :
    (List.ofFn f).flatten.length = k * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.flatten_cons, List.length_append, hf 0,
      ih (fun j => f j.succ) (fun j => hf j.succ), Nat.mul_succ]; ring

theorem slice_flatten_take (L : List (List Byte)) (i r len : Nat) (hi : i < L.length)
    (h : r + len ≤ (L.getD i []).length) :
    Ref.slice L.flatten ((L.take i).flatten.length + r) len = Ref.slice (L.getD i []) r len := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    cases i with
    | zero =>
      simp only [List.take_zero, List.flatten_nil, List.length_nil, Nat.zero_add, List.flatten_cons,
        List.getD_cons_zero] at h ⊢
      exact slice_append_left _ _ _ _ h
    | succ i =>
      simp only [List.take_succ_cons, List.flatten_cons, List.length_append, List.getD_cons_succ] at h ⊢
      rw [slice_append_right _ _ _ ((L.take i).flatten.length + r) _ (by omega)]
      exact ih i (by simp at hi; omega) h

theorem dv_ofList_slice (l : List Byte) (a : Nat) (h : a + 16 ≤ l.length) :
    dv (Ref.ofList 16 (Ref.slice l a 16)) = Ref.slice l a 16 :=
  Ref.toList_ofList 16 _ (length_slice l a 16 h)

theorem flatten_ofFn_slices_var (l : List Byte) (a : Nat) {n : Nat} (w : Nat → Nat) :
    (List.ofFn fun j : Fin n => Ref.slice l (a + ((List.range j).map w).sum) (w j)).flatten =
      Ref.slice l a ((List.range n).map w).sum := by
  induction n with
  | zero => simp [Ref.slice]
  | succ n ih =>
    rw [List.ofFn_succ_last, List.flatten_append]
    simp only [Fin.val_castSucc, Fin.val_last, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [ih, ← slice_split, List.range_succ, List.map_append, List.sum_append]
    simp

end SigGolfCandidate.Equiv
