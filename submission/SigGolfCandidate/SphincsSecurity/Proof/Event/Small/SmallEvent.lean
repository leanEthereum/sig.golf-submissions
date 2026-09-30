import SigGolfCandidate.SphincsSecurity.Proof.Event.Small.Closing
/-!
# The small-budget event bound

Below `budgetSplit` the event bound follows from the coupling with the capped adversary and its
small-budget bound. Below `keygenHashCost` the event is empty: key generation alone makes that many
hash calls.
-/

namespace SphincsSecurity.Concrete.EventSmall

open _root_.OracleComp OracleSpec ENNReal
set_option backward.isDefEq.respectTransparency false

theorem forgeEventAdvantage_le_forgeAdvantage (adversary : Adversary) (q : Nat) :
    forgeEventAdvantage scheme adversary q ≤ forgeAdvantage scheme adversary := by
  have hforget := congrArg (fun computation : OracleComp OracleWorld Bool => (simulateQ romImpl computation).run' ∅)
    (QueryCap.counted_forget (fun input : OracleWorld.Domain => input matches .inr _) (gameCore scheme adversary))
  simp only [simulateQ_map, StateT.run'_map'] at hforget
  rw [forgeAdvantage, ← hforget, ← probEvent_eq_eq_probOutput, probEvent_map, forgeEventAdvantage,
    ← simulateQ_countHashQueries]
  exact probEvent_mono fun result _ hresult => hresult.1

theorem boundaryGameCore_hashCalls_ge (adversary : Adversary) (result : Bool × SigningBoundaryTrace)
    (hresult : result ∈ support ((simulateQ romImpl (boundaryGameCore adversary)).run' ∅)) :
    keygenHashCost ≤ result.2.hashCalls := by
  classical
  let inputs := hashInputs (boundaryGameCore adversary)
  let _ : SampleableType (inputs → HashOutput) := SampleableType.ofFintype _
  have heq := evalDist_romRun_eq_finiteHash (boundaryGameCore adversary) inputs (Finset.Subset.refl _) ∅
  have hs : result ∈ support (do
      let table ← ($ᵗ (inputs → HashOutput) : ProbComp _)
      simulateQ (fixedHashWorld (finiteHashAnswer ∅ inputs table)) (boundaryGameCore adversary)) := by
    rw [mem_support_iff, probOutput_def, ← heq, ← probOutput_def, ← mem_support_iff]
    exact hresult
  rw [mem_support_bind_iff] at hs
  obtain ⟨table, _, hs⟩ := hs
  rw [fixed_boundaryGameCore] at hs
  simp only [mem_support_bind_iff] at hs
  obtain ⟨parameter, _, otsSecret, _, ftsSecret, _, hs⟩ := hs
  rw [fixed_gameAfterSecrets] at hs
  dsimp only at hs
  rw [support_map] at hs
  obtain ⟨final, _, rfl⟩ := hs
  simp only [SigningBoundaryTrace.hashCalls_mul, SigningBoundaryTrace.hashCalls_pow_none]
  exact Nat.le_add_right _ _

theorem forgeEventAdvantage_eq_zero (adversary : Adversary) (q : Nat) (hq : q < keygenHashCost) :
    forgeEventAdvantage scheme adversary q = 0 := by
  rw [forgeEventAdvantage_eq_boundary, probEvent_eq_zero_iff]
  intro result hresult hevent
  have := boundaryGameCore_hashCalls_ge adversary result hresult
  omega

/-- **The small-budget event bound.** -/
theorem security127_event_of_small_budget (q : Nat) (hsmall : q + 1 ≤ budgetSplit) (adversary : Adversary) :
    forgeEventAdvantage scheme adversary q ≤ (q : ENNReal) / 2 ^ 127 := by
  by_cases hq : keygenHashCost ≤ q
  · calc
      _ ≤ forgeEventAdvantage scheme (visAdversary adversary (q + 1)) (q + 1) :=
        forgeEventAdvantage_le_visAdversary adversary q
      _ ≤ forgeAdvantage scheme (visAdversary adversary (q + 1)) := forgeEventAdvantage_le_forgeAdvantage _ _
      _ ≤ visSmallBound (q + 1) :=
        forgeAdvantage_visAdversary_le fixedReferenceDummy (fun _ _ _ => fixedReferenceDummyWord_valid) adversary (q + 1)
          (by omega) hsmall
      _ ≤ _ := visSmallBound_le q hq hsmall
  · rw [forgeEventAdvantage_eq_zero adversary q (by omega)]
    exact zero_le

end SphincsSecurity.Concrete.EventSmall
