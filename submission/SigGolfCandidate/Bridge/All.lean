import SigGolfCandidate.Bridge.Main
import SigGolfCandidate.Bridge.Convenience

/-! # The security bridge: entry points -/

namespace SigGolfCandidate.Bridge

/-- The bridge with (C) in zero-padding form. -/
theorem ZeroPadAssumptions.secure {sub : SigGolf.Submission} (Z : ZeroPadAssumptions sub) :
    sub.Secure :=
  Z.toAssumptions.secure

end SigGolfCandidate.Bridge

/-- info: 'SigGolfCandidate.Bridge.Assumptions.secure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.Bridge.Assumptions.secure

/-- info: 'SigGolfCandidate.Bridge.ZeroPadAssumptions.secure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.Bridge.ZeroPadAssumptions.secure

/-- info: 'SigGolfCandidate.Bridge.run'_relabelW' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.Bridge.run'_relabelW
