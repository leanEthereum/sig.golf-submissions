import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualTerminalCoverage
import SigGolfCandidate.SphincsSecurity.Proof.Residual.RetainedResidualCreationBudget
/-!
# Terminal coverage without a query bound

The terminal-coverage bound only needs the creation mass to stay within the budget, which the monitor
guarantees on every path. The message side is left as the expected creation mass, which the event
potential pays.
-/
namespace SphincsSecurity.Concrete.RetainedResidual

open _root_.OracleComp OracleSpec ENNReal CanonicalProbeRouting
open AdaptiveResidualLabels hiding World State Environment
open FtsProbeSimulation (unloggedRetainedRestComputation)
attribute [local instance] Classical.propDecidable
attribute [local irreducible] hashInputs sourceInputs canonicalEncodingInputs canonicalGraphInputs instFintypePosition
set_option backward.isDefEq.respectTransparency false

theorem initialMonitoredSource_creationMass_le_budget
    (key : SecretKey) (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (q : Nat) (required : Finset IndexGroup) (stopAfter : CertificateStopRule) (stopped : Bool)
    (result : Option (Forgery × Bool) × MonitoredState (gameInputs adversary))
    (hresult : initialMonitoredSource key adversary encoding dummy exposed high q required stopAfter stopped result ≠ 0) :
    result.2.2.creationMass ≤ (q : ENNReal) :=
  (monitoredRun_creationBudget key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q required stopAfter
    (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩)
    (initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed,
      initialCertificateMonitor keygenHashCost stopped)
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
    (sourceInputs_unlogged_subset_gameInputs adversary key) (creationBudget_initial q keygenHashCost stopped) result hresult).1

theorem expected_initialMonitoredSource_full_unit_count_le_mass
    (key : SecretKey) (adversary : Adversary) (encoding : ReferenceEncodingAuxiliary) (dummy : OtsReferenceWords)
    (exposed : InitialPublicLabels (referenceFamilyWords encoding.selections dummy)) (high : CanonicalGraphHighHalves)
    (q : Nat) (stopAfter : CertificateStopRule) (stopped : Bool) (hbudget : q ≤ 2 ^ 127) :
    (∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] *
      certificateBankCount result.2.2.bank) ≤
        (2 ^ 128 : ENNReal)⁻¹ *
          (∑' result, Pr[= result | initialMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] *
            result.2.2.creationMass) + (q : ENNReal) * fullCertificateExcessRate := by
  let state : ProposalState (gameInputs adversary) :=
    ([], initialState (gameInputs adversary) (referenceFamilyWords encoding.selections dummy) exposed, initialCertificateMonitor keygenHashCost stopped)
  let law := proposalRun key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
    (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q Finset.univ (proposalStop stopAfter)
    (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) state
  have hvalid : MonitoredValid (gameInputs adversary) state.2 :=
    ⟨initialAllowed_nonempty _ exposed, initialState_rowsCovered _ _ exposed⟩
  have hinv : ProposalInvariant key fixedProposalLength state :=
    certificateProposalInvariant_initial key fixedProposalLength keygenHashCost _ stopped (fun _ => le_rfl)
  have hproject : Prod.map id Prod.snd <$> law =
      initialMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped :=
    proposalRun_erasure key (gameInputs adversary) (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter)
      (referenceFamilyWords encoding.selections dummy)
      (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
      encoding.selections encoding.rows q Finset.univ (proposalStop stopAfter) _ state
  have herase (weight : Option (Forgery × Bool) × MonitoredState (gameInputs adversary) → ENNReal) :
      (∑' result, Pr[= result | law] * weight (Prod.map id Prod.snd result)) =
        ∑' result, Pr[= result |
          initialMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] * weight result := by
    have h := congrArg (fun p => ∑' result, Pr[= result | p] * weight result) hproject
    rw [tsum_probOutput_map_mul] at h
    exact h
  have hmass : ∀ result, law result ≠ 0 → result.2.2.2.creationMass ≤ (q : ENNReal) := by
    intro result hresult
    have h := map_nonzero law (Prod.map id Prod.snd) result hresult
    rw [hproject] at h
    exact initialMonitoredSource_creationMass_le_budget key adversary encoding dummy exposed high q Finset.univ
      (proposalStop stopAfter) stopped _ h
  have hcost := expected_proposalRun_creationCost_le_mass_terminalPotential key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q Finset.univ stopAfter fixedProposalLength
    (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) state hvalid
    (sourceInputs_unlogged_subset_gameInputs adversary key) hbudget hinv
  have huniform := expected_proposalRun_terminalPotential key (gameInputs adversary)
    (canonicalEncodingInputs_subset_retainedGameInputs adversary key.parameter) (referenceFamilyWords encoding.selections dummy)
    (coordinateGraphLabels (initialKnown (referenceFamilyWords encoding.selections dummy) exposed) high)
    encoding.selections encoding.rows q Finset.univ (proposalStop stopAfter)
    (unloggedRetainedRestComputation adversary ⟨key.root, key.parameter⟩) state hvalid
    (sourceInputs_unlogged_subset_gameInputs adversary key) fixedProposalLength
    (fun word => terminalCertificatePrice Finset.univ word - (2 ^ 128 : ENNReal)⁻¹)
  change (∑' result, Pr[= result | law] * terminalProposalPotential (PMF.uniformOfFintype Index) fixedProposalLength
    (fun word => terminalCertificatePrice Finset.univ word - (2 ^ 128 : ENNReal)⁻¹) result.2.1) = _ at huniform
  have hzero : state.2.2.creationCost = 0 := rfl
  rw [hzero, zero_add] at hcost
  have hempty : state.1 = [] := rfl
  rw [hempty, terminalProposalPotential_empty] at huniform
  calc
    _ ≤ ∑' result, Pr[= result |
        initialMonitoredSource key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped] * result.2.2.creationCost :=
      expected_initialMonitoredSource_count_le_creationCost key adversary encoding dummy exposed high q Finset.univ (proposalStop stopAfter) stopped
    _ = ∑' result, Pr[= result | law] * result.2.2.2.creationCost := (herase (fun result => result.2.2.creationCost)).symm
    _ ≤ ∑' result, Pr[= result | law] * (result.2.2.2.creationMass *
        terminalProposalPotential (PMF.uniformOfFintype Index) fixedProposalLength (terminalCertificatePrice Finset.univ) result.2.1) := hcost
    _ ≤ (2 ^ 128 : ENNReal)⁻¹ * (∑' result, Pr[= result | law] * result.2.2.2.creationMass) +
        (q : ENNReal) * ∑' result, Pr[= result | law] * terminalProposalPotential (PMF.uniformOfFintype Index) fixedProposalLength
          (fun word => terminalCertificatePrice Finset.univ word - (2 ^ 128 : ENNReal)⁻¹) result.2.1 :=
      expected_weighted_terminalPotential_le law (fun result => result.2.1) (fun result => result.2.2.2.creationMass)
        q (2 ^ 128 : ENNReal)⁻¹ hmass fixedProposalLength (terminalCertificatePrice Finset.univ)
    _ ≤ _ := by
      rw [huniform]
      have hm := herase (fun result => result.2.2.creationMass)
      dsimp only [Prod.map] at hm
      rw [hm]
      exact add_le_add le_rfl (mul_le_mul' le_rfl uniformWordAverage_full_price_excess_le)

end SphincsSecurity.Concrete.RetainedResidual
