import SigGolfCandidate.SphincsSecurity.Scheme
import SigGolfCandidate.Ref
import SigGolfCandidate.Bridge.Basic

/-!
# Byte-level reference vs abstract scheme: basic tools

* `toB` (abstract `List UInt8` ↦ organizer `List Byte`) and `padQ = pad64 ∘ toB`, the oracle
  relabelling;
* byte encodings: `toB_bytesLE`, `leBytes_eq_toList`, `tweak_eq` (the 16-byte tweak);
* hashing through `relabel padQ`: `relabel_oracleHash`, `hash16_eq`;
* generic loop lemmas: `relabel_sequenceFin`, `foldlM_range_seq` (a `List.range` fold whose
  state update is pure, against `sequenceFin`), `map_fst_foldlM`.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolf (Byte Bytes Query)
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map relabel_query)

/-- Abstract hash inputs as organizer bytes. -/
def toB (x : List UInt8) : List Byte := x.map UInt8.toBitVec

/-- The oracle relabelling: zero padding of the organizer bytes. -/
def padQ (x : List UInt8) : Query := Ref.pad64 (toB x)

@[simp] theorem toB_append (x y : List UInt8) : toB (x ++ y) = toB x ++ toB y := by
  simp [toB]

@[simp] theorem toB_nil : toB [] = [] := rfl

@[simp] theorem toB_cons (a : UInt8) (x : List UInt8) : toB (a :: x) = a.toBitVec :: toB x := rfl

@[simp] theorem length_toB (x : List UInt8) : (toB x).length = x.length := by simp [toB]

theorem toB_injective : Function.Injective toB := by
  intro x y h
  exact List.map_injective_iff.mpr (fun a b h => UInt8.toBitVec_inj.mp h) h

/-! ## Byte encodings -/

theorem toB_bytesLE (n : Nat) (v : BitVec (8 * n)) :
    toB (SphincsSecurity.bytesLE n v) = Ref.toList v := by
  simp only [toB, SphincsSecurity.bytesLE, Ref.toList, SigGolf.bytes, List.map_ofFn]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem leBytes_eq_toList (k v : Nat) : Ref.leBytes k v = Ref.toList (BitVec.ofNat (8 * k) v) := by
  simp only [Ref.leBytes, Ref.toList, SigGolf.bytes]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  rw [Ref.extractByte_ofNat _ _ _ (by omega)]

theorem toB_bytesLE_ofNat (k v : Nat) :
    toB (SphincsSecurity.bytesLE k (BitVec.ofNat (8 * k) v)) = Ref.leBytes k v := by
  rw [toB_bytesLE, leBytes_eq_toList]

theorem toList_zero (n : Nat) : Ref.toList (0 : Bytes n) = Ref.zeros n := by
  simp only [Ref.toList, SigGolf.bytes, Ref.zeros]
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

theorem length_toList {n : Nat} (x : Bytes n) : (Ref.toList x).length = n := Ref.length_toList x


theorem extract_hi (tau : Nat) :
    (BitVec.ofNat 40 tau).extractLsb' 32 8 = BitVec.ofNat (8 * 1) (tau / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  rw [show (2 : Nat) ^ 40 = 2 ^ 32 * 2 ^ 8 by norm_num, Nat.mod_mul_right_div_self]
  norm_num

theorem extract_lo (tau : Nat) :
    (BitVec.ofNat 40 tau).extractLsb' 0 32 = BitVec.ofNat (8 * 4) (tau % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  rw [Nat.mod_mod_of_dvd _ (by norm_num), Nat.mod_mod_of_dvd _ (by norm_num)]

/-- The 16 tweak bytes of the abstract scheme are the reference tweak. -/
theorem toB_tweakFields (t lay tau p j : Nat) :
    toB (SphincsSecurity.fieldBytes (SphincsSecurity.tweakFields t lay tau p j)) =
      Ref.tweak t lay tau p j := by
  simp only [SphincsSecurity.fieldBytes, SphincsSecurity.tweakFields, toB_append]
  rw [extract_hi, extract_lo]
  rw [show (BitVec.ofNat 8 t : BitVec 8) = BitVec.ofNat (8 * 1) t from rfl,
    show (BitVec.ofNat 8 lay : BitVec 8) = BitVec.ofNat (8 * 1) lay from rfl,
    show (BitVec.ofNat 32 p : BitVec 32) = BitVec.ofNat (8 * 4) p from rfl,
    show (BitVec.ofNat 32 j : BitVec 32) = BitVec.ofNat (8 * 4) j from rfl]
  simp only [toB_bytesLE_ofNat]
  simp [Ref.tweak, Ref.le32, Ref.leBytes, SphincsSecurity.protocolDomainSep, Ref.byte]


/-! ## Hashing through the relabelling -/

/-- The abstract hash oracle, as the Bridge types it. -/
abbrev AHash := List UInt8 →ₒ BitVec 256

theorem relabel_oracleHash (x : List UInt8) :
    relabel padQ (SphincsSecurity.Concrete.oracleHash (m := OracleComp SphincsSecurity.HashSpec) x) =
      Ref.H (toB x) := by
  simp [SphincsSecurity.Concrete.oracleHash, Ref.H, padQ]
  rfl


set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-- Abstract computations. -/
abbrev AComp := OracleComp SphincsSecurity.HashSpec

/-- A 16-byte abstract value as reference bytes. -/
def dv (d : SphincsSecurity.Digest) : Ref.Val := Ref.toList (n := 16) d

@[simp] theorem length_dv (d : SphincsSecurity.Digest) : (dv d).length = 16 := Ref.length_toList (n := 16) d

theorem dv_injective : Function.Injective dv := by
  intro a b h
  have h2 : Ref.ofList 16 (Ref.toList (n := 16) a) = Ref.ofList 16 (Ref.toList (n := 16) b) :=
    congrArg (Ref.ofList 16) h
  rwa [Ref.ofList_toList, Ref.ofList_toList] at h2

theorem answerBytes_eq (a : BitVec 256) :
    Ref.answerBytes 16 a = dv (SphincsSecurity.truncateHash a) := by
  simp only [Ref.answerBytes, dv, Ref.toList, SigGolf.bytes, SphincsSecurity.truncateHash]
  apply List.map_congr_left
  intro i hi
  rw [List.mem_range] at hi
  apply BitVec.eq_of_toNat_eq
  simp only [SphincsSecurity.hashOutputBits, SphincsSecurity.digestBits] at *
  rw [BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
  simp only [Nat.shiftRight_eq_div_pow, Nat.pow_zero, Nat.div_one]
  rw [show (2 : Nat) ^ 128 = 2 ^ (8 * i) * 2 ^ (128 - 8 * i) by
    rw [← Nat.pow_add]; congr 1; omega]
  rw [Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 (by omega))]

theorem hash16_eq (y : List Byte) :
    Ref.hash16 y = (fun a => dv (SphincsSecurity.truncateHash a)) <$> Ref.H y := by
  simp only [Ref.hash16, answerBytes_eq]
  rw [map_eq_bind_pure_comp]; rfl

/-- A reference `Th` call is the relabelled abstract tweakable hash, when the inputs agree. -/
theorem hash16_tweakable (P : SphincsSecurity.PublicParameter) (dom : SphincsSecurity.HashDomain)
    (payload : List UInt8) (y : List Byte)
    (hy : toB (SphincsSecurity.tweakableHashInput P dom payload) = y) :
    Ref.hash16 y = dv <$> relabel padQ
      (SphincsSecurity.Concrete.tweakableHash (m := AComp) P dom payload) := by
  subst hy
  simp only [SphincsSecurity.Concrete.tweakableHash, relabel_bind, relabel_oracleHash, hash16_eq,
    relabel_pure]
  rw [map_bind]
  simp only [map_pure]
  rw [map_eq_bind_pure_comp]; rfl

/-! ## Generic loop lemmas -/

section loops

theorem relabel_sequenceFin {ι ι' R α : Type} (f : ι → ι') {n : Nat}
    (c : Fin n → OracleComp (ι →ₒ R) α) :
    relabel f (SphincsSecurity.Concrete.sequenceFin c) =
      SphincsSecurity.Concrete.sequenceFin (fun j => relabel f (c j)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [SphincsSecurity.Concrete.sequenceFin, relabel_bind, relabel_pure]
    congr 1; funext h
    rw [ih]

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- A fold over `0 .. n-1` whose state update is pure, against `sequenceFin`. -/
theorem foldlM_range_seq {α β σ : Type} {n : Nat} (c : Fin n → m α) (b : Nat → m β) (g : α → β)
    (hb : ∀ j (h : j < n), b j = g <$> c ⟨j, h⟩) (upd : σ → Nat → β → σ) (s : σ) :
    (List.range n).foldlM (fun st j => do let v ← b j; pure (upd st j v)) s =
      (fun f => (List.finRange n).foldl (fun st j => upd st j.val (g (f j))) s) <$>
        SphincsSecurity.Concrete.sequenceFin c := by
  induction n generalizing s b upd with
  | zero => simp [SphincsSecurity.Concrete.sequenceFin]
  | succ n ih =>
    rw [List.range_succ_eq_map, List.foldlM_cons]
    simp only [List.foldlM_map]
    rw [hb 0 (by omega)]
    simp only [SphincsSecurity.Concrete.sequenceFin, map_bind, bind_map_left, map_pure, bind_assoc,
      pure_bind]
    congr 1; funext h
    have := ih (fun j => c j.succ) (fun j => b (j + 1)) (fun j hj => hb (j + 1) (by omega))
      (fun st j v => upd st (j + 1) v) (upd s 0 (g h))
    simp only [Nat.succ_eq_add_one] at this ⊢
    rw [this, map_eq_bind_pure_comp]
    congr 1; funext t
    simp [List.finRange_succ, List.foldl_map]

theorem map_fst_foldlM {α β γ δ : Type} (l : List γ) (body : α → γ → m δ) (g : α → γ → δ → α)
    (k : α × β → γ → δ → β) (s : α × β) :
    Prod.fst <$> l.foldlM (fun st x => do let r ← body st.1 x; pure (g st.1 x r, k st x r)) s =
      l.foldlM (fun a x => do let r ← body a x; pure (g a x r)) s.1 := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldlM_cons, map_bind, bind_assoc, pure_bind]
    congr 1; funext r
    exact ih _

end loops

/-! ## Pure folds -/

theorem foldl_finRange_append {β : Type} {n : Nat} (F : Fin n → β) (init : List β) :
    (List.finRange n).foldl (fun acc j => acc ++ [F j]) init = init ++ List.ofFn F := by
  induction n generalizing init with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
    have := ih (fun j => F j.succ) (init ++ [F 0])
    rw [this, List.ofFn_succ]; simp

theorem foldl_keep {β γ : Type} (l : List γ) (s : β) : l.foldl (fun acc _ => acc) s = s := by
  induction l <;> simp [*]

theorem foldl_finRange_capture {β : Type} {n : Nat} (F : Fin n → β) (cap : Nat) (s : β) :
    (List.finRange n).foldl (fun acc j => if j.val = cap then F j else acc) s =
      if h : cap < n then F ⟨cap, h⟩ else s := by
  induction n generalizing s cap with
  | zero => simp
  | succ n ih =>
    rw [List.finRange_succ, List.foldl_cons, List.foldl_map]
    cases cap with
    | zero =>
      simp only [Fin.val_succ, Nat.add_one_ne_zero, if_false, foldl_keep]
      simp
    | succ c =>
      simp only [Fin.val_succ, Nat.add_right_cancel_iff]
      rw [ih (fun j => F j.succ) c]
      simp only [Fin.val_zero, Nat.zero_ne_add_one, if_false]
      by_cases hl : c < n
      · rw [dif_pos hl, dif_pos (by omega)]; rfl
      · rw [dif_neg hl, dif_neg (by omega)]

theorem foldl_prod {α β γ : Type} (l : List γ) (u1 : α → γ → α) (u2 : β → γ → β) (a : α) (b : β) :
    l.foldl (fun st j => (u1 st.1 j, u2 st.2 j)) (a, b) = (l.foldl u1 a, l.foldl u2 b) := by
  induction l generalizing a b with
  | nil => rfl
  | cons x l ih => simp [ih]

end SigGolfCandidate.Equiv
