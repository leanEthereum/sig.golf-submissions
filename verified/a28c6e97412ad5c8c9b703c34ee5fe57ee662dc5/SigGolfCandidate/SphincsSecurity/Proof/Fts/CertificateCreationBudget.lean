import SigGolfCandidate.SphincsSecurity.Proof.Fts.CertificateMonitor
import SigGolfCandidate.SphincsSecurity.Proof.Fts.FewTimeFreshMass
/-!
# The monitor's creation mass never exceeds its budget

A live monitor charges a request only when the request's macro cost fits into what remains of the
budget, and the creation mass it adds is at most that macro cost. So the creation mass stays below the
budget on every path, whatever the adversary does afterwards: the bound needs no query bound on the
adversary.
-/
namespace SphincsSecurity.Concrete

open _root_.OracleComp OracleSpec ENNReal
attribute [local instance] Classical.propDecidable

def CreationBudget (budget : Nat) (monitor : CertificateMonitor) : Prop :=
  monitor.creationMass ≤ (budget : ENNReal) ∧ (monitor.stopped = false → monitor.creationMass ≤ (monitor.spent : ENNReal))

theorem creationBudget_initial (budget spent : Nat) (stopped : Bool) :
    CreationBudget budget (initialCertificateMonitor spent stopped) :=
  ⟨zero_le, fun _ => zero_le⟩

theorem targetCreationMultiplier_le_macro (key : SecretKey) (cache : QueryCache HashSpec)
    (input : (OracleWorld + SigningSpec).Domain) :
    targetCreationMultiplier key cache input ≤ (signingMacroHashCost input : ENNReal) := by
  cases input with
  | inl world =>
      cases world with
      | inl sample => simp [targetCreationMultiplier, freshWorldTargetHashCost, signingMacroHashCost]
      | inr hash =>
          simp only [targetCreationMultiplier, freshWorldTargetHashCost, signingMacroHashCost]
          split_ifs <;> norm_num
  | inr message =>
      simp only [targetCreationMultiplier, signingMacroHashCost]
      calc
        _ ≤ ((2 ^ ftsTreeHeight : Nat) : ENNReal) * 1 :=
          mul_le_mul' le_rfl (freshDigestSelectionProbability_le_one key message cache)
        _ = _ := by rw [mul_one]

theorem creationBudget_update (key : SecretKey) (budget : Nat) (required : Finset FtsTree) (stopAfter : CertificateStopRule)
    (input : (OracleWorld + SigningSpec).Domain) (state : CertificateMonitorState) (length : Nat)
    (record : ProposalExecutionRecord input) (hbefore : CreationBudget budget state.2)
    (hmass : targetCreationMultiplier key state.1 input ≤ record.trace.hashCalls) :
    CreationBudget budget (certificateMonitorUpdate key budget required stopAfter input state length record) := by
  by_cases hactive : CertificateMonitorActive key budget input state
  · have hlive : state.2.stopped = false := hactive.1
    have hspent : state.2.spent ≤ budget := hactive.2.1.2.2
    have hmacro := hactive.2.2.2
    have hcm := hbefore.2 hlive
    have hsum : state.2.creationMass + targetCreationMultiplier key state.1 input ≤ (budget : ENNReal) := by
      calc
        _ ≤ (state.2.spent : ENNReal) + (signingMacroHashCost input : ENNReal) :=
          add_le_add hcm (targetCreationMultiplier_le_macro key state.1 input)
        _ = ((state.2.spent + signingMacroHashCost input : Nat) : ENNReal) := by push_cast; rfl
        _ ≤ _ := Nat.cast_le.mpr (by omega)
    rw [certificateMonitorUpdate, if_pos hactive]
    refine ⟨hsum, fun _ => ?_⟩
    change state.2.creationMass + targetCreationMultiplier key state.1 input ≤
      ((state.2.spent + record.trace.hashCalls : Nat) : ENNReal)
    rw [Nat.cast_add]
    exact add_le_add hcm hmass
  · rw [certificateMonitorUpdate_inactive _ _ _ _ _ _ _ _ hactive]
    exact ⟨hbefore.1, fun h => by cases h⟩

theorem creationBudget_stop (budget : Nat) (monitor : CertificateMonitor) (h : CreationBudget budget monitor) :
    CreationBudget budget { monitor with stopped := true } :=
  ⟨h.1, fun h => by cases h⟩

end SphincsSecurity.Concrete
