import SigGolfCandidate.Equiv.Verify
import SigGolfCandidate.Equiv.Keygen
import SigGolfCandidate.Equiv.Honest
import SigGolfCandidate.Bridge.All
import SigGolfCandidate.Submission

/-!
# The bridge assumptions from the bytecode refinements

Given the four RISC-V refinement theorems (the programs compute the reference spec, with the call
count), the Bridge's implementation equations (D) hold, and together with the equivalence of the
reference spec and the abstract scheme this discharges every field of `ZeroPadAssumptions` except
(A) security.
-/

open OracleComp OracleSpec

namespace SigGolfCandidate.Equiv

open SigGolf (Byte Bytes Query)
open SigGolfCandidate.Bridge (relabel relabel_pure relabel_bind relabel_map relabel_query AllQ)

set_option allowUnsafeReducibility true in
attribute [local reducible] SphincsSecurity.hashOutputBits SphincsSecurity.digestBits
  SphincsSecurity.messageBits SphincsSecurity.publicParameterBits SphincsSecurity.counterBits
  SigGolfCandidate.submission

theorem countCalls_eq {α : Type} (oa : OracleComp SigGolf.HashSpec α) :
    Ref.countCalls oa = SigGolfCandidate.Bridge.countCalls oa := rfl

theorem countCalls_map {α β : Type} (f : α → β) (oa : OracleComp SigGolf.HashSpec α) :
    Ref.countCalls (f <$> oa) = (fun p => (f p.1, p.2)) <$> Ref.countCalls oa := by
  unfold Ref.countCalls Ref.countWith
  rw [simulateQ_map, StateT.run_map]

/-- The keys produced by the abstract key generation. -/
theorem keygen_support (seed : SphincsSecurity.MasterSeed)
    (kp : SphincsSecurity.PublicKey × SphincsSecurity.TopCache × SphincsSecurity.Seeded.SecretKey)
    (h : kp ∈ support (SphincsSecurity.Seeded.keygenFromSeed seed)) :
    kp.2.2.seed = seed ∧ kp.2.2.parameter = 0 ∧ kp.1 = ⟨kp.2.2.root, 0⟩ := by
  unfold SphincsSecurity.Seeded.keygenFromSeed at h
  simp only [support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at h
  obtain ⟨x, _, y, _, z, _, rfl⟩ := h
  exact ⟨rfl, rfl, rfl⟩

/-! ## The bytecode refinements, as hypotheses -/

/-- The four RISC-V refinement theorems: each program's value and call count are those of the
reference spec (`SigGolfCandidate/{Keygen,Sign,Expand,Verify}` prove them). -/
structure Refinements : Prop where
  keygen : ∀ sk, (fun r => (r.value, r.hashCalls)) <$> submission.run .keygen sk =
    (fun p => (some p.1, p.2)) <$> Ref.countCalls (Ref.keygenRef sk)
  sign : ∀ sk cache m, (fun r => (r.value, r.hashCalls)) <$> submission.run .sign (sk, cache, m) =
    (fun p => (p.1, p.2)) <$> Ref.countCalls (Ref.signRef sk cache m)
  expand : ∀ m pk σ, (fun r => (r.value, r.hashCalls)) <$> submission.run .expand (m, pk, σ) =
    pure (some (Ref.expandRef σ), 0)
  verify : ∀ m pk w, (fun r => (r.value, r.hashCalls)) <$> submission.run .verify (m, pk, w) =
    (fun p => (if p.1 then some () else none, p.2)) <$> Ref.countCalls (Ref.verifyRef m pk w)

/-- The published key: the root. -/
def pkEnc (pk : SphincsSecurity.PublicKey) : SigGolf.PublicKey := pk.root

/-- **The Bridge's assumptions**, except (A) security, from the bytecode refinements and the
equivalence of the reference spec with the abstract scheme. -/
noncomputable def zeroPadAssumptions (security : SigGolfCandidate.Bridge.EventSecurity)
    (R : Refinements) : SigGolfCandidate.Bridge.ZeroPadAssumptions submission where
  security := security
  seedOf := id
  seedOf_dist := SigGolfCandidate.Bridge.seedOf_id_dist
  msgOf := fun m => m
  msgOf_injective := fun _ _ h => h
  sigCodec := sigCodec
  expandFn := Ref.expandRef
  witDec := witDec
  witDec_expandFn := witDec_expandRef
  pkEnc := pkEnc
  cacheEnc := cacheEnc
  cacheDec := cacheDec
  pad := fmtQ
  Honest := Honest
  pad_injOn := fmtQ_injOn
  honest_head := honest_head
  qEnc := SigGolfCandidate.Bridge.defaultQEnc
  qEnc_injective := SigGolfCandidate.Bridge.defaultQEnc_injective
  keygen_eq (sk : Bytes 32) := by
    have e1 : Ref.countCalls (Ref.keygenRef sk) =
        (fun p => (((p.1.1.root : Bytes 16), cacheEnc p.1.2.1), p.2)) <$>
          Ref.countCalls (relabel fmtQ (SphincsSecurity.Seeded.keygenFromSeed sk)) := by
      rw [keygenRef_eq, countCalls_map]
    rw [R.keygen sk, e1, Functor.map_map]
    rfl
  keygen_honest seed := hq_keygen seed
  sign_eq sk pk cache' sk' h cache m := by
    obtain ⟨hs, hP, -⟩ := keygen_support _ _ h
    have hs' : sk'.seed = sk := hs
    have e1 : Ref.countCalls (Ref.signRef sk cache m) =
        (fun p => (Option.map sigCodec.symm p.1, p.2)) <$>
          Ref.countCalls (relabel fmtQ
            (SphincsSecurity.Seeded.sign (m := AComp) sk' (cacheDec cache) m)) := by
      rw [← hs', signRef_eq sk' hP cache m, countCalls_map]
    rw [R.sign, e1, Functor.map_map]
    rfl
  sign_honest seed pk cache' sk' h cache m := hq_sign sk' (keygen_support _ _ h).2.1 cache m
  expand_eq m pk σ := R.expand m pk σ
  verify_eq seed pk cache' sk' h m (w : Bytes 6404) := by
    obtain ⟨-, -, hpk⟩ := keygen_support _ _ h
    have hpk' : pk = ⟨sk'.root, 0⟩ := hpk
    have e : (⟨pkEnc pk, 0⟩ : SphincsSecurity.PublicKey) = pk := by
      rw [hpk']; rfl
    have e2 : Ref.countCalls (Ref.verifyRef m (pkEnc pk) w) =
        Ref.countCalls (relabel fmtQ (SphincsSecurity.Concrete.verify (m := AComp) pk m (witDec w))) := by
      rw [verifyRef_eq, e]
    rw [R.verify m (pkEnc pk) w, e2]
    rfl
  verify_honest seed pk cache' sk' h m σ := by
    obtain ⟨-, -, hpk⟩ := keygen_support _ _ h
    exact hq_verify pk (by rw [show pk = _ from hpk]) m σ

/-- **Security of the submission**, from (A) abstract security and the four bytecode refinement
theorems. -/
theorem submission_secure (security : SigGolfCandidate.Bridge.EventSecurity) (R : Refinements) :
    submission.Secure :=
  (zeroPadAssumptions security R).secure

end SigGolfCandidate.Equiv
