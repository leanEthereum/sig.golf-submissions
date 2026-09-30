import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.SignCharge
import SigGolfCandidate.SphincsSecurity.Proof.Base.QueryCap
/-!
# The visibly capped adversary

The adversary cannot see how many digest trials a signing request cost, but every request costs at
least `signCharge` hash calls (the forest and the trees below the top layer, or a failed search). The
capped adversary charges one per own hash query and `signCharge` per signing request, and stops before the charge would exceed its limit. On a run
of the original adversary that stays within the budget the cap never fires. At the end it makes
one marker query, a message-class input of even length whose payload length records how many
nonmessage hash queries it made.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec

/-- The visible charge of a query: nothing for sampling, one per hash query, and the least cost
of a signing request. -/
def visWeight : (OracleWorld + SigningSpec).Domain → Nat
  | .inl (.inl _) => 0
  | .inl (.inr _) => 1
  | .inr _ => signCharge

/-- Run a computation while the remaining charge covers each query; stop before one it does not. -/
noncomputable def weightCap {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) :
    Nat → OracleComp (OracleWorld + SigningSpec) (Option α) :=
  OracleComp.construct (fun result _ => pure (some result))
    (fun input _ next budget =>
      if visWeight input ≤ budget then
        liftM ((OracleWorld + SigningSpec).query input) >>= fun answer => next answer (budget - visWeight input)
      else pure none) computation

theorem weightCap_pure {α : Type} (value : α) (budget : Nat) :
    weightCap (pure value : OracleComp (OracleWorld + SigningSpec) α) budget = pure (some value) := rfl

theorem weightCap_query_bind {α : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (budget : Nat) :
    weightCap (liftM ((OracleWorld + SigningSpec).query input) >>= next) budget =
      if visWeight input ≤ budget then
        liftM ((OracleWorld + SigningSpec).query input) >>= fun answer => weightCap (next answer) (budget - visWeight input)
      else pure none := rfl

/-- A weighted structural bound: along every path the visible charges sum to at most `budget`. -/
def WeightBound {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : Nat) : Prop :=
  computation.IsQueryBound budget (fun input remaining => visWeight input ≤ remaining)
    (fun input remaining => remaining - visWeight input)

theorem weightBound_pure {α : Type} (value : α) (budget : Nat) :
    WeightBound (pure value : OracleComp (OracleWorld + SigningSpec) α) budget := trivial

theorem weightBound_query_bind_iff {α : Type} (input : (OracleWorld + SigningSpec).Domain)
    (next : (OracleWorld + SigningSpec).Range input → OracleComp (OracleWorld + SigningSpec) α) (budget : Nat) :
    WeightBound (liftM ((OracleWorld + SigningSpec).query input) >>= next) budget ↔
      visWeight input ≤ budget ∧ ∀ answer, WeightBound (next answer) (budget - visWeight input) :=
  Iff.rfl

theorem WeightBound.mono {α : Type} {computation : OracleComp (OracleWorld + SigningSpec) α} {budget budget' : Nat}
    (h : WeightBound computation budget) (hle : budget ≤ budget') : WeightBound computation budget' := by
  induction computation using OracleComp.inductionOn generalizing budget budget' with
  | pure value => trivial
  | query_bind input next ih =>
      rw [weightBound_query_bind_iff] at h ⊢
      exact ⟨h.1.trans hle, fun answer => ih answer (h.2 answer) (by omega)⟩

theorem weightBound_bind {α β : Type} {first : OracleComp (OracleWorld + SigningSpec) α}
    {next : α → OracleComp (OracleWorld + SigningSpec) β} {budget budget' : Nat}
    (hfirst : WeightBound first budget) (hnext : ∀ value, WeightBound (next value) budget') :
    WeightBound (first >>= next) (budget + budget') := by
  induction first using OracleComp.inductionOn generalizing budget with
  | pure value => exact (hnext value).mono (Nat.le_add_left _ _)
  | query_bind input continuation ih =>
      rw [weightBound_query_bind_iff] at hfirst
      rw [bind_assoc, weightBound_query_bind_iff]
      refine ⟨hfirst.1.trans (Nat.le_add_right _ _), fun answer => ?_⟩
      exact (ih answer (hfirst.2 answer)).mono (by omega)

theorem weightBound_map {α β : Type} {computation : OracleComp (OracleWorld + SigningSpec) α} (f : α → β)
    {budget : Nat} (h : WeightBound computation budget) : WeightBound (f <$> computation) budget := by
  rw [map_eq_bind_pure_comp]
  exact (weightBound_bind h (fun value => weightBound_pure (f value) 0) : WeightBound _ (budget + 0))

theorem weightCap_weightBound {α : Type} (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : Nat) :
    WeightBound (weightCap computation budget) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind input next ih =>
      rw [weightCap_query_bind]
      split_ifs with h
      · exact (weightBound_query_bind_iff _ _ _).mpr ⟨h, fun answer => ih answer _⟩
      · trivial

theorem counted_weightBound {α : Type} (selected : (OracleWorld + SigningSpec).Domain → Prop) [DecidablePred selected]
    (computation : OracleComp (OracleWorld + SigningSpec) α) (budget : Nat) (h : WeightBound computation budget) :
    WeightBound (QueryCap.counted selected computation) budget := by
  induction computation using OracleComp.inductionOn generalizing budget with
  | pure value => trivial
  | query_bind input next ih =>
      rw [weightBound_query_bind_iff] at h
      rw [QueryCap.counted_query_bind, weightBound_query_bind_iff]
      refine ⟨h.1, fun answer => ?_⟩
      simpa only [Nat.add_zero] using weightBound_bind (ih answer _ (h.2 answer))
        (fun value => weightBound_pure (value.1, (if selected input then 1 else 0) + value.2) 0)

/-! ### The marker -/

/-- The prefix every message-class input starts with. -/
def messagePrefix (parameter : PublicParameter) : HashInput :=
  tweakBytes .message ++ bytesLE 16 parameter

/-- A computable test for message-class inputs. -/
def isMessageInput (parameter : PublicParameter) (input : HashInput) : Bool :=
  (messagePrefix parameter).isPrefixOf input

/-- The nonmessage hash queries, which the marker counts. -/
def NonmessageQuery (parameter : PublicParameter) : (OracleWorld + SigningSpec).Domain → Prop
  | .inl (.inr input) => isMessageInput parameter input = false
  | _ => False

instance (parameter : PublicParameter) : DecidablePred (NonmessageQuery parameter) := by
  intro input
  rcases input with (input | input) | input
  · exact isFalse id
  · exact inferInstanceAs (Decidable (isMessageInput parameter input = false))
  · exact isFalse id

/-- The marker: a message-class input whose payload has odd length `2 * count + 1`. -/
def markerInput (parameter : PublicParameter) (count : Nat) : HashInput :=
  tweakableHashInput parameter .message (List.replicate (2 * count + 1) 0)

/-- A forgery returned when the cap fires. -/
def dummyForgery : Forgery :=
  ⟨0, ⟨0, fun _ => 0, fun _ _ => 0, fun _ => ⟨0, fun _ => 0, fun _ => 0⟩⟩⟩

/-- The capped adversary for total budget `budget`: key generation takes `keygenHashCost`, the marker
one call, and the cap covers the rest. -/
noncomputable def visAdversary (adversary : Adversary) (budget : Nat) : Adversary where
  main pk := do
    let result ← QueryCap.counted (NonmessageQuery pk.parameter)
      (weightCap (adversary.main pk) (budget - keygenHashCost - 1))
    let _ ← (liftM ((OracleWorld + SigningSpec).query (.inl (.inr (markerInput pk.parameter result.2)))) :
      OracleComp (OracleWorld + SigningSpec) HashOutput)
    pure (result.1.getD dummyForgery)

theorem visAdversary_weightBound (adversary : Adversary) (budget : Nat) (pk : PublicKey)
    (hbudget : keygenHashCost + 1 ≤ budget) :
    WeightBound ((visAdversary adversary budget).main pk) (budget - keygenHashCost) := by
  have hcap := counted_weightBound (NonmessageQuery pk.parameter) _ _
    (weightCap_weightBound (adversary.main pk) (budget - keygenHashCost - 1))
  have hmarker : ∀ result : Option Forgery × Nat,
      WeightBound (liftM ((OracleWorld + SigningSpec).query (.inl (.inr (markerInput pk.parameter result.2)))) >>=
        fun _ => (pure (result.1.getD dummyForgery) : OracleComp (OracleWorld + SigningSpec) Forgery)) 1 :=
    fun result => (weightBound_query_bind_iff _ _ _).mpr ⟨le_rfl, fun _ => trivial⟩
  have h := weightBound_bind hcap hmarker
  refine h.mono ?_
  omega

end SphincsSecurity.Concrete.EventSmall
