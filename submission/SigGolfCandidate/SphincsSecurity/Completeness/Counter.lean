import SigGolfCandidate.SphincsSecurity.Completeness.Search

/-!
# The counter search

`encodingSearch` is the search of `Search.lean` run over the encoding inputs: the counter rides in
the hashed bytes, so the inputs below the `2 ^ 32` wrap are distinct, and the trial budget
`C_max = 2 ^ 20` stays below it.
What remains to bound its failure is the share of answers the target-sum code rejects.
-/

open OracleComp OracleSpec ENNReal

set_option maxRecDepth 10000

namespace SphincsSecurity.Completeness

open Concrete

/-- The input the counter search hashes at counter `c`. -/
def encodeInput (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (message : Digest) (c : Nat) : HashInput :=
  tweakableHashInput parameter (.encoding lay tree leaf)
    (bytesLE 16 message ++ bytesLE 4 (BitVec.ofNat counterBits c))

theorem encodeInput_inj (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) {c c' : Nat}
    (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : encodeInput parameter lay tree leaf message c
      = encodeInput parameter lay tree leaf message c') : c = c' := by
  simp only [encodeInput, tweakableHashInput, List.append_assoc] at h
  have hpayload := List.append_cancel_left h
  have hpayload' := List.append_cancel_left hpayload
  exact counter_bytes_inj hc hc' (List.append_cancel_left hpayload')

/-- The counter search exhausts its budget with probability at most the rejection share to the budget. -/
theorem probEvent_encodingSearch (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (leaf : LeafIndex) (message : Digest) (cache : QueryCache HashSpec)
    (hfresh : ∀ c, c < encodingAttemptLimit →
      cache (encodeInput parameter lay tree leaf message c) = none) :
    Pr[fun r => r.1 = none | (simulateQ randomOracle
        (encodingSearch parameter lay tree leaf message encodingAttemptLimit 0
          : OracleComp HashSpec (Option (Counter × Encoding)))).run cache]
      ≤ failMass (fun out => TargetSum.decodeDigest (truncateHash out)) ^ encodingAttemptLimit := by
  have hwrap : encodingAttemptLimit ≤ 2 ^ 32 := by rw [encodingAttemptLimit]; norm_num
  rw [encodingSearch_eq_searchLoop]
  exact probEvent_searchLoop _ _ _ encodingAttemptLimit
    (fun s s' hs hs' heq => encodeInput_inj parameter lay tree leaf message (by omega) (by omega) heq)
    encodingAttemptLimit 0 (by simp) cache (fun s _ hsb => hfresh s hsb)

end SphincsSecurity.Completeness
