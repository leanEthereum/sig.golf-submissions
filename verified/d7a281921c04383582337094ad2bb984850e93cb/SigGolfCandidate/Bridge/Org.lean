import SigGolfCandidate.Bridge.Setup

/-!
# The organizer experiment, relabelled onto the abstract oracle

`orgK` is the organizer's `interact` loop with every hash input renamed by `unpad`.
With the implementation equations (D) it unfolds into the abstract algorithms.
-/

open OracleSpec OracleComp SigGolf

namespace SigGolfCandidate.Bridge

variable {sub : Submission} (B : Assumptions sub)

lemma relabel_unpad_countCalls {α : Type} (X : OracleComp AHash α) (hX : AllQ B.Honest X) :
    relabel B.unpad (countCalls (relabel B.pad X)) = countCalls X := by
  rw [relabel_countCalls, relabel_relabel]
  congr 1
  exact relabel_eq_self_of_allQ B.Honest _ (fun x hx => B.unpad_pad x hx) hX

lemma relabelW_liftM_proj {α β γ : Type} (Y : OracleComp SigGolf.HashSpec α) (proj : α → β)
    (K' : β → OracleComp World γ) (K : α → OracleComp World γ) (hK : ∀ r, K r = K' (proj r)) :
    relabelW B.unpad ((liftM Y : OracleComp World α) >>= K) =
      (liftM (relabel B.unpad (proj <$> Y)) : OracleComp AW β) >>= fun p => relabelW B.unpad (K' p) := by
  rw [relabelW_bind, relabelW_liftM_hash, relabel_map, liftM_map, bind_map_left]
  simp only [hK]

lemma bind_eq_of_proj {ι : Type} {spec : OracleSpec ι} {α β γ : Type} (Y : OracleComp spec α)
    (proj : α → β) (K' : β → OracleComp spec γ) (K : α → OracleComp spec γ)
    (hK : ∀ r, K r = K' (proj r)) : Y >>= K = (proj <$> Y) >>= K' := by
  rw [bind_map_left]; exact bind_congr hK

lemma liftM_map_bind {ι : Type} {spec : OracleSpec ι} {α β γ : Type} (X : OracleComp spec α)
    (f : α → β) (K : β → OracleComp (unifSpec + spec) γ) :
    (liftM (f <$> X) : OracleComp (unifSpec + spec) β) >>= K =
      (liftM X : OracleComp (unifSpec + spec) α) >>= fun x => K (f x) := by
  rw [liftM_map, bind_map_left]

/-- `Transcript.record` only reads the value and hash-call count of the signing result. -/
def recordVC {sizes : Sizes} (T : Transcript sizes) (message : Message)
    (value : Option (Bytes sizes.signature)) (calls : ℕ) : Transcript sizes :=
  { signed := match value with
      | none => T.signed
      | some signature => (message, signature) :: T.signed
    signingRequests := T.signingRequests + 1
    hashCalls := T.hashCalls + calls }

lemma record_eq_recordVC {sizes : Sizes} (T : Transcript sizes) (message : Message)
    (r : RunResult (Bytes sizes.signature)) :
    T.record message r = recordVC T message r.value r.hashCalls := rfl

variable (A : Adversary sub.sizes) (sk : SecretKey) (pk : SphincsSecurity.PublicKey)

/-- The organizer interaction against the public key `pkEnc pk`, relabelled by `unpad`. -/
def orgK (n : ℕ) (s : A.State) (T : Transcript sub.sizes) : OracleComp AW AttackResult :=
  relabelW B.unpad (sub.interact A sk (B.pkEnc pk) n s T)

variable {A sk pk}

lemma orgK_zero (s : A.State) (T : Transcript sub.sizes) :
    orgK B A sk pk 0 s T = pure ⟨false, T.hashCalls⟩ := rfl

lemma orgK_hash {n : ℕ} {s : A.State} {T : Transcript sub.sizes} {y : Query}
    {resume : BitVec 256 → A.State} (h : A.step s = .hash y resume) :
    orgK B A sk pk (n + 1) s T =
      (AW.query (Sum.inr (B.unpad y)) : OracleComp AW _) >>= fun a =>
        orgK B A sk pk n (resume a) { T with hashCalls := T.hashCalls + 1 } := by
  simp only [orgK, Submission.interact, h]
  rw [relabelW_bind]
  rfl

lemma orgK_sample {n : ℕ} {s : A.State} {T : Transcript sub.sizes} {m : ℕ}
    {resume : Fin (m + 1) → A.State} (h : A.step s = .sample m resume) :
    orgK B A sk pk (n + 1) s T =
      (AW.query (Sum.inl m) : OracleComp AW _) >>= fun a =>
        orgK B A sk pk n (resume a) T := by
  simp only [orgK, Submission.interact, h]
  rw [relabelW_bind]
  rfl

lemma orgK_step {n : ℕ} {s s' : A.State} {T : Transcript sub.sizes} (h : A.step s = .step s') :
    orgK B A sk pk (n + 1) s T = orgK B A sk pk n s' T := by
  simp only [orgK, Submission.interact, h]

lemma orgK_sign_ge {n : ℕ} {s : A.State} {T : Transcript sub.sizes} {req : SigningRequest}
    {resume : Option (Bytes sub.sizes.signature) → A.State} (h : A.step s = .sign req resume)
    (hk : ¬ T.signingRequests < LIFETIME) :
    orgK B A sk pk (n + 1) s T = pure ⟨false, T.hashCalls⟩ := by
  simp only [orgK, Submission.interact, h, hk, if_false]
  rfl

lemma orgK_sign_lt {sk' : SphincsSecurity.Seeded.SecretKey}
    (hkey : (pk, sk') ∈ support (aKeygen (B.seedOf sk)))
    {n : ℕ} {s : A.State} {T : Transcript sub.sizes} {req : SigningRequest}
    {resume : Option (Bytes sub.sizes.signature) → A.State} (h : A.step s = .sign req resume)
    (hk : T.signingRequests < LIFETIME) :
    orgK B A sk pk (n + 1) s T =
      (liftM (countCalls (aSign sk' (B.msgOf req.message))) : OracleComp AW _) >>= fun p =>
        orgK B A sk pk n (resume (p.1.map B.sigCodec.symm))
          (recordVC T req.message (p.1.map B.sigCodec.symm) p.2) := by
  simp only [orgK, Submission.interact, h, hk, if_true, Submission.signingOracle,
    record_eq_recordVC]
  refine (relabelW_liftM_proj B (sub.run .sign (sk, req.cache, req.message))
    (fun r => (r.value, r.hashCalls))
    (fun p => sub.interact A sk (B.pkEnc pk) n (resume p.1) (recordVC T req.message p.1 p.2))
    _ (fun _ => rfl)).trans ?_
  rw [B.sign_eq sk pk sk' hkey]
  erw [relabel_map]
  rw [relabel_unpad_countCalls B _ (B.sign_honest _ pk sk' hkey _)]
  erw [liftM_map, bind_map_left]

/-- The witness-form checker, relabelled. -/
lemma relabel_verify {sk' : SphincsSecurity.Seeded.SecretKey}
    (hkey : (pk, sk') ∈ support (aKeygen (B.seedOf sk)))
    (m : Message) (w : Bytes sub.sizes.witness) (fresh : Bool) (calls : ℕ) :
    relabel B.unpad ((sub.run .verify (m, B.pkEnc pk, w)) >>= fun verify =>
        (pure (⟨verify.value.isSome && fresh, calls + verify.hashCalls⟩ : AttackResult) :
          OracleComp SigGolf.HashSpec AttackResult)) =
      (fun p => (⟨p.1 && fresh, calls + p.2⟩ : AttackResult)) <$>
        countCalls (aVerify pk (B.msgOf m) (B.witDec w)) := by
  have e : ((sub.run .verify (m, B.pkEnc pk, w)) >>= fun verify =>
        (pure (⟨verify.value.isSome && fresh, calls + verify.hashCalls⟩ : AttackResult) :
          OracleComp SigGolf.HashSpec AttackResult)) =
      (fun p => (⟨p.1.isSome && fresh, calls + p.2⟩ : AttackResult)) <$>
        ((fun r => (r.value, r.hashCalls)) <$> sub.run .verify (m, B.pkEnc pk, w)) := by
    rw [Functor.map_map, map_eq_bind_pure_comp]
    rfl
  rw [e, B.verify_eq _ pk sk' hkey]
  erw [Functor.map_map, relabel_map]
  rw [relabel_unpad_countCalls B _ (B.verify_honest _ pk sk' hkey _ _)]
  refine congrArg (· <$> _) ?_
  funext a
  rcases a with ⟨b, c⟩
  cases b <;> rfl

lemma orgK_submit_witness {sk' : SphincsSecurity.Seeded.SecretKey}
    (hkey : (pk, sk') ∈ support (aKeygen (B.seedOf sk)))
    {n : ℕ} {s : A.State} {T : Transcript sub.sizes} {m : Message} {w : Bytes sub.sizes.witness}
    (h : A.step s = .submit (.witness m w)) :
    orgK B A sk pk (n + 1) s T =
      (liftM ((fun p => (⟨p.1 && T.freshMessage m, T.hashCalls + p.2⟩ : AttackResult)) <$>
        countCalls (aVerify pk (B.msgOf m) (B.witDec w))) : OracleComp AW _) := by
  simp only [orgK, Submission.interact, h, relabelW_liftM_hash]
  rw [← relabel_verify B hkey m w]
  rfl

lemma orgK_submit_signature {sk' : SphincsSecurity.Seeded.SecretKey}
    (hkey : (pk, sk') ∈ support (aKeygen (B.seedOf sk)))
    {n : ℕ} {s : A.State} {T : Transcript sub.sizes} {m : Message}
    {σ : Bytes sub.sizes.signature}
    (h : A.step s = .submit (.signature m σ)) :
    orgK B A sk pk (n + 1) s T =
      (liftM ((fun p => (⟨p.1 && T.freshSignature m σ, T.hashCalls + 0 + p.2⟩ : AttackResult)) <$>
        countCalls (aVerify pk (B.msgOf m) (B.sigCodec σ))) : OracleComp AW _) := by
  simp only [orgK, Submission.interact, h, relabelW_liftM_hash]
  congr 1
  rw [← B.witDec_expandFn σ, ← relabel_verify B hkey m (B.expandFn σ)]
  congr 1
  simp only [Submission.checkForgery]
  refine (bind_eq_of_proj (sub.run .expand (m, B.pkEnc pk, σ)) (fun r => (r.value, r.hashCalls))
    (fun (p : Option (Bytes sub.sizes.witness) × ℕ) =>
          (match p.1 with
          | none => pure ⟨false, T.hashCalls + p.2⟩
          | some witness => (do
              let verify ← sub.run .verify (m, B.pkEnc pk, witness)
              pure ⟨verify.value.isSome && T.freshSignature m σ,
                T.hashCalls + p.2 + verify.hashCalls⟩) : OracleComp SigGolf.HashSpec AttackResult))
    _ ?hK).trans ?_
  case hK =>
    intro r
    rcases r with ⟨v, f, c, h, hc⟩
    cases v <;> rfl
  erw [B.expand_eq m (B.pkEnc pk) σ]
  rfl

variable (A)

/-- The organizer experiment, with hash inputs renamed onto the abstract oracle and the
implementation of key generation substituted. -/
noncomputable def orgGame (rounds : ℕ) : OracleComp AW AttackResult := do
  let sk ← (liftM sampleSecretKey : OracleComp AW _)
  let p ← (liftM (countCalls (aKeygen (B.seedOf sk))) : OracleComp AW _)
  orgK B A sk p.1.1 rounds (A.initial (B.pkEnc p.1.1) (B.cacheOf p.1.1)) { hashCalls := p.2 }

lemma unpad_injective : Function.Injective B.unpad := fun x y h => by
  rw [← B.pad_unpad x, ← B.pad_unpad y, h]

theorem securityExperiment_eq (rounds : ℕ) :
    sub.securityExperiment A rounds =
      (simulateQ (roImpl (List UInt8) (BitVec 256)) (orgGame B A rounds)).run' ∅ := by
  unfold Submission.securityExperiment withRandomness
  refine (run'_relabelW (R := BitVec 256) B.unpad (unpad_injective B) _ ∅ ∅ (fun _ => rfl)).trans ?_
  refine congrArg (fun P => (simulateQ (roImpl (List UInt8) (BitVec 256)) P).run' ∅) ?_
  unfold orgGame
  rw [relabelW_bind, relabelW_liftM_unif]
  refine bind_congr fun sk => ?_
  refine (relabelW_liftM_proj B (sub.run .keygen sk) (fun r => (r.value, r.hashCalls))
    (fun (p : Option (PublicKey × Cache) × ℕ) =>
      (match p.1 with
      | some (pk, cache) => sub.interact A sk pk rounds (A.initial pk cache) { hashCalls := p.2 }
      | none => pure ⟨false, p.2⟩ : OracleComp World AttackResult)) _ ?hK).trans ?_
  case hK =>
    intro r
    rcases r with ⟨v, f, c, h, hc⟩
    rcases v with _ | ⟨pk, cache⟩ <;> rfl
  rw [B.keygen_eq sk]
  erw [relabel_map]
  rw [relabel_unpad_countCalls B _ (B.keygen_honest _)]
  refine (liftM_map_bind _ _ _).trans ?_
  refine bind_congr fun p => ?_
  rfl

end SigGolfCandidate.Bridge
