import SigGolfCandidate.SphincsSecurity
import SigGolfCandidate.Final.Refine
import SigGolfCandidate.Final.RO
import Mathlib.Data.Set.Finite.List

/-!
# Completeness

`submission_complete`: for every secret key, all `2^256` honest pipelines, run against one shared
lazy random oracle, succeed with probability at least `1 - 2^-256`.

1. The `allSucceed` bit of `allMessages` is the conjunction fold (`foldAll`) of the success bits
   of the honest pipelines (`allSucceed_allMessages`).
2. Each success bit is the abstract honest game relabelled by `padQ` (`success_honest_eq_game`).
3. The abstract game only makes `Honest` queries; there are finitely many. Restricted to that
   finite domain `HD`, the whole fold is a relabelling by the injective `padQ ∘ val`, so the
   organizer's lazy oracle on `Query` is the lazy oracle on `HD` (`run'_relabel`).
4. On a finite domain the lazy oracle is the eager one; a union bound over messages then bounds the
   failure probability by the sum of the per-message failure probabilities
   (`probOutput_false_foldAll_le`), each of which is that of the seeded completeness experiment.
5. Per-seed completeness (`sphincs_is_complete_for_every_seed`) bounds the sum by `2^-256`.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Final
open SigGolf
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map relabel_relabel)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits

/-! ## The fold -/

theorem allSucceed_foldlM (P : Message → OracleComp HashSpec HonestResult) (L : List Message)
    (s : HonestSummary) :
    HonestSummary.allSucceed <$> L.foldlM (fun summary message => do
        let result ← P message
        return (⟨summary.allSucceed && result.success,
          fun phase => max (summary.maxCosts phase) (result.costs phase)⟩ : HonestSummary)) s =
      foldAll L (fun m => HonestResult.success <$> P m) s.allSucceed := by
  induction L generalizing s with
  | nil => simp [foldAll]
  | cons m L ih =>
    rw [List.foldlM_cons, foldAll_cons, map_bind, bind_assoc, bind_map_left]
    refine bind_congr fun r => ?_
    rw [pure_bind, ih]

theorem allSucceed_allMessages (sub : Submission) (sk : SecretKey) :
    HonestSummary.allSucceed <$> sub.allMessages sk =
      foldAll (Finset.univ : Finset Message).toList
        (fun m => HonestResult.success <$> sub.honest sk m) true := by
  unfold Submission.allMessages
  exact allSucceed_foldlM _ _ {}

theorem foldAll_relabel {ι ι' R κ : Type} (f : ι → ι') (L : List κ)
    (P : κ → OracleComp (ι →ₒ R) Bool) (b : Bool) :
    foldAll L (fun k => relabel f (P k)) b = relabel f (foldAll L P b) := by
  induction L generalizing b with
  | nil => rfl
  | cons k L ih =>
    rw [foldAll_cons, foldAll_cons, relabel_bind]
    exact bind_congr fun c => ih _

/-! ## The finite honest domain -/

/-- Honest abstract hash inputs. -/
abbrev HD := {x : List UInt8 // Equiv.Honest x}

theorem honest_length_le (x : List UInt8) (h : Equiv.Honest x) : x.length ≤ 704 := by
  rw [h.2]
  unfold Equiv.tagLen
  split <;> omega

instance : Finite HD :=
  ((List.finite_length_le UInt8 704).subset fun x hx => honest_length_le x hx).to_subtype

noncomputable instance : Fintype HD := Fintype.ofFinite HD

theorem honest_witness : Equiv.Honest (1 :: List.replicate 63 0) := by
  refine ⟨rfl, ?_⟩
  rfl

/-- Restrict an abstract input to the honest domain (a fixed honest input otherwise). -/
noncomputable def toHD (x : List UInt8) : HD := by
  classical
  exact if h : Equiv.Honest x then ⟨x, h⟩ else ⟨_, honest_witness⟩

theorem val_toHD (x : List UInt8) (h : Equiv.Honest x) : (toHD x).val = x := by
  unfold toHD
  rw [dif_pos h]

/-- The organizer query of an honest input. -/
def encHD (x : HD) : Query := Equiv.padQ x.val

theorem encHD_injective : Function.Injective encHD := by
  intro x y h
  exact Subtype.ext (Equiv.padQ_injOn x.2 y.2 h)

/-- The abstract honest game on the honest domain. -/
noncomputable def gameHD (sk : SecretKey) (m : Message) :
    OracleComp (HD →ₒ SphincsSecurity.HashOutput) Bool :=
  relabel toHD (game sk m)

theorem relabel_val_gameHD (sk : SecretKey) (m : Message) :
    relabel Subtype.val (gameHD sk m) = game sk m := by
  unfold gameHD
  rw [relabel_relabel]
  exact Bridge.relabel_eq_self_of_allQ Equiv.Honest _ (fun x hx => val_toHD x hx) (hq_game sk m)

/-! ## Probabilities -/

theorem withRandomOracle_map {α β : Type} (f : α → β) (oa : OracleComp HashSpec α) :
    withRandomOracle (f <$> oa) = f <$> withRandomOracle oa := by
  unfold withRandomOracle
  rw [simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
    Functor.map_map]

theorem probOutput_gameHD (sk : SecretKey) (m : Message) (b : Bool) :
    Pr[= b | (simulateQ randomOracle (gameHD sk m)).run' ∅] =
      Pr[= b | SphincsSecurity.Completeness.seededExperiment sk m] := by
  rw [seededExperiment_eq, run'_relabel Subtype.val Subtype.val_injective (gameHD sk m) ∅ ∅
    (fun _ => rfl), relabel_val_gameHD]

/-! ## Completeness -/

/-- The organizer's `allSucceed` bit is the conjunction fold of the abstract games on the honest
domain, relabelled by `encHD`. -/
theorem allSucceed_eq_relabel (hS : SignRefinementStatement) (hV : VerifyRefinementStatement)
    (sk : SecretKey) :
    HonestSummary.allSucceed <$> submission.allMessages sk =
      relabel encHD (foldAll (Finset.univ : Finset Message).toList (gameHD sk) true) := by
  rw [allSucceed_allMessages, ← foldAll_relabel]
  congr 1
  funext m
  rw [success_honest_eq_game hS hV, ← relabel_val_gameHD, relabel_relabel]
  rfl

theorem failure_eq : FAILURE = ((2 ^ 256 : Nat) : ENNReal)⁻¹ := by
  rw [FAILURE, one_div, Nat.cast_pow, Nat.cast_ofNat]

/-- **Completeness** of the submission, given the sign and verify refinements. -/
theorem submission_complete (hS : SignRefinementStatement) (hV : VerifyRefinementStatement) :
    submission.Complete := by
  intro sk
  set L := (Finset.univ : Finset Message).toList
  set F := foldAll L (gameHD sk) true
  have hP : Pr[fun summary => summary.allSucceed = true |
        withRandomOracle (submission.allMessages sk)] =
      Pr[= true | (simulateQ randomOracle F).run' ∅] := by
    have e1 : Pr[fun summary => summary.allSucceed = true |
          withRandomOracle (submission.allMessages sk)] =
        Pr[= true | withRandomOracle (HonestSummary.allSucceed <$> submission.allMessages sk)] := by
      rw [withRandomOracle_map, ← probEvent_eq_eq_probOutput, probEvent_map]
      rfl
    rw [e1, allSucceed_eq_relabel hS hV]
    unfold withRandomOracle
    rw [← run'_relabel encHD encHD_injective F ∅ ∅ (fun _ => rfl)]
  have hF : Pr[= false | (simulateQ randomOracle F).run' ∅] ≤ FAILURE := by
    refine (probOutput_false_foldAll_le L (gameHD sk)).trans ?_
    simp_rw [probOutput_gameHD]
    rw [Finset.sum_map_toList, failure_eq]
    rw [← tsum_fintype (L := SummationFilter.unconditional Message)]
    exact SphincsSecurity.sphincs_is_complete_for_every_seed sk
  have h1 : Pr[= true | (simulateQ randomOracle F).run' ∅] +
      Pr[= false | (simulateQ randomOracle F).run' ∅] = 1 := by
    simp
  rw [hP, tsub_le_iff_right, ← h1]
  exact add_le_add le_rfl hF

end SigGolfCandidate.Final
