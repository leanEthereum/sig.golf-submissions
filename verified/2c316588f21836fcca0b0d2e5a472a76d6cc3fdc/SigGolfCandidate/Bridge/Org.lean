import SigGolfCandidate.Bridge.Setup

/-!
# The organizer experiment, relabelled onto the abstract oracle

`orgK` is the organizer's `interact` loop with every hash input renamed by `unpad`.
With the implementation equations (D) it unfolds into the abstract algorithms.
-/

open OracleSpec OracleComp SigGolfCandidate.Legacy

namespace SigGolfCandidate.Bridge

variable {sub : Submission} (B : Assumptions sub)

lemma relabel_unpad_countCalls {α : Type} (X : OracleComp AHash α) (hX : AllQ B.Honest X) :
    relabel B.unpad (countCalls (relabel B.pad X)) = countCalls X := by
  rw [relabel_countCalls, relabel_relabel]
  congr 1
  exact relabel_eq_self_of_allQ B.Honest _ (fun x hx => B.unpad_pad x hx) hX

lemma relabelW_liftM_proj {α β γ : Type} (Y : OracleComp SigGolfCandidate.Legacy.HashSpec α) (proj : α → β)
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

lemma orgK_sign_ge {n : ℕ} {s : A.State} {T : Transcript sub.sizes} {req : SigningRequest sub.sizes}
    {resume : Option (Bytes sub.sizes.signature) → A.State} (h : A.step s = .sign req resume)
    (hk : ¬ T.signingRequests < LIFETIME) :
    orgK B A sk pk (n + 1) s T = pure ⟨false, T.hashCalls⟩ := by
  simp only [orgK, Submission.interact, h, hk, if_false]
  rfl

lemma orgK_sign_lt {cache' : SphincsSecurity.TopCache} {sk' : SphincsSecurity.Seeded.SecretKey}
    (hkey : (pk, cache', sk') ∈ support (aKeygen (B.seedOf sk)))
    {n : ℕ} {s : A.State} {T : Transcript sub.sizes} {req : SigningRequest sub.sizes}
    {resume : Option (Bytes sub.sizes.signature) → A.State} (h : A.step s = .sign req resume)
    (hk : T.signingRequests < LIFETIME) :
    orgK B A sk pk (n + 1) s T =
      (liftM (countCalls (aSign sk' (B.cacheDec req.cache) (B.msgOf req.message))) :
          OracleComp AW _) >>= fun p =>
        orgK B A sk pk n (resume (p.1.map B.compress))
          (recordVC T req.message (p.1.map B.compress) p.2) := by
  simp only [orgK, Submission.interact, h, hk, if_true, Submission.signingOracle,
    record_eq_recordVC]
  refine (relabelW_liftM_proj B (sub.run .sign (sk, req.cache, req.message))
    (fun r => (r.value, r.hashCalls))
    (fun p => sub.interact A sk (B.pkEnc pk) n (resume p.1) (recordVC T req.message p.1 p.2))
    _ (fun _ => rfl)).trans ?_
  rw [B.sign_eq sk pk cache' sk' hkey]
  erw [relabel_map]
  rw [relabel_unpad_countCalls B _ (B.sign_honest _ pk cache' sk' hkey _ _)]
  erw [liftM_map, bind_map_left]

/-- The witness-form checker, relabelled. -/
lemma relabel_verify {cache' : SphincsSecurity.TopCache}
    {sk' : SphincsSecurity.Seeded.SecretKey}
    (hkey : (pk, cache', sk') ∈ support (aKeygen (B.seedOf sk)))
    (m : Message) (w : Bytes sub.sizes.witness) (fresh : Bool) (calls : ℕ) :
    relabel B.unpad ((sub.run .verify (m, B.pkEnc pk, w)) >>= fun verify =>
        (pure (⟨verify.value.isSome && fresh, calls + verify.hashCalls⟩ : AttackResult) :
          OracleComp SigGolfCandidate.Legacy.HashSpec AttackResult)) =
      (fun p => (⟨p.1 && fresh, calls + p.2⟩ : AttackResult)) <$>
        countCalls (aVerify pk (B.msgOf m) (B.witDec w)) := by
  have e : ((sub.run .verify (m, B.pkEnc pk, w)) >>= fun verify =>
        (pure (⟨verify.value.isSome && fresh, calls + verify.hashCalls⟩ : AttackResult) :
          OracleComp SigGolfCandidate.Legacy.HashSpec AttackResult)) =
      (fun p => (⟨p.1.isSome && fresh, calls + p.2⟩ : AttackResult)) <$>
        ((fun r => (r.value, r.hashCalls)) <$> sub.run .verify (m, B.pkEnc pk, w)) := by
    rw [Functor.map_map, map_eq_bind_pure_comp]
    rfl
  rw [e, B.verify_eq _ pk cache' sk' hkey]
  erw [Functor.map_map, relabel_map]
  rw [relabel_unpad_countCalls B _ (B.verify_honest _ pk cache' sk' hkey _ _)]
  refine congrArg (· <$> _) ?_
  funext a
  rcases a with ⟨b, c⟩
  cases b <;> rfl

lemma orgK_submit_witness {cache' : SphincsSecurity.TopCache}
    {sk' : SphincsSecurity.Seeded.SecretKey}
    (hkey : (pk, cache', sk') ∈ support (aKeygen (B.seedOf sk)))
    {n : ℕ} {s : A.State} {T : Transcript sub.sizes} {m : Message} {w : Bytes sub.sizes.witness}
    (h : A.step s = .submit (.witness m w)) :
    orgK B A sk pk (n + 1) s T =
      (liftM ((fun p => (⟨p.1 && T.freshMessage m, T.hashCalls + p.2⟩ : AttackResult)) <$>
        countCalls (aVerify pk (B.msgOf m) (B.witDec w))) : OracleComp AW _) := by
  simp only [orgK, Submission.interact, h, relabelW_liftM_hash]
  rw [← relabel_verify B hkey m w]
  rfl

/-- The organizer's final check of a signature-form forgery: the counted abstract expansion,
then (on success) the counted abstract verification of the decoded witness. -/
lemma orgK_submit_signature {cache' : SphincsSecurity.TopCache}
    {sk' : SphincsSecurity.Seeded.SecretKey}
    (hkey : (pk, cache', sk') ∈ support (aKeygen (B.seedOf sk)))
    {n : ℕ} {s : A.State} {T : Transcript sub.sizes} {m : Message}
    {σ : Bytes sub.sizes.signature}
    (h : A.step s = .submit (.signature m σ)) :
    orgK B A sk pk (n + 1) s T =
      (liftM (countCalls (B.aExpand (B.msgOf m) pk σ)) : OracleComp AW _) >>= fun p =>
        match p.1 with
        | none => pure ⟨false, T.hashCalls + p.2⟩
        | some w =>
          (liftM ((fun q => (⟨q.1 && T.freshSignature m σ, T.hashCalls + p.2 + q.2⟩ :
              AttackResult)) <$> countCalls (aVerify pk (B.msgOf m) (B.witDec w))) :
            OracleComp AW _) := by
  simp only [orgK, Submission.interact, h, relabelW_liftM_hash, Submission.checkForgery]
  have hE : relabel B.unpad ((fun r => (r.value, r.hashCalls)) <$>
      sub.run .expand (m, B.pkEnc pk, σ)) = countCalls (B.aExpand (B.msgOf m) pk σ) := by
    erw [B.expand_eq _ pk cache' sk' hkey m σ]
    exact relabel_unpad_countCalls B _ (B.expand_honest _ pk cache' sk' hkey _ _)
  refine (congrArg (fun X => (liftM (relabel B.unpad X) : OracleComp AW AttackResult))
    (bind_eq_of_proj (sub.run .expand (m, B.pkEnc pk, σ)) (fun r => (r.value, r.hashCalls))
      (fun (p : Option (Output sub.sizes .expand) × ℕ) =>
          (match p.1 with
          | none => pure ⟨false, T.hashCalls + p.2⟩
          | some witness => (do
              let verify ← sub.run .verify (m, B.pkEnc pk, witness)
              pure ⟨verify.value.isSome && T.freshSignature m σ,
                T.hashCalls + p.2 + verify.hashCalls⟩) : OracleComp SigGolfCandidate.Legacy.HashSpec AttackResult))
      _ (fun r => by rcases r with ⟨v, f, c, h, hc⟩; cases v <;> rfl))).trans ?_
  refine (congrArg liftM (relabel_bind B.unpad _ _)).trans ?_
  refine (liftM_bind _ _).trans ?_
  rw [hE]
  refine bind_congr fun p => ?_
  rcases p with ⟨_ | w, c⟩
  · rfl
  · exact congrArg _ (relabel_verify B hkey m w _ _)

variable (A)

/-- The organizer experiment, with hash inputs renamed onto the abstract oracle and the
implementation of key generation substituted. -/
noncomputable def orgGame (rounds : ℕ) : OracleComp AW AttackResult := do
  let sk ← (liftM sampleSecretKey : OracleComp AW _)
  let p ← (liftM (countCalls (aKeygen (B.seedOf sk))) : OracleComp AW _)
  orgK B A sk p.1.1 rounds (A.initial (B.pkEnc p.1.1) (B.cacheEnc p.1.2.1)) { hashCalls := p.2 }

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
    (fun (p : Option (PublicKey × Bytes sub.sizes.cache) × ℕ) =>
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
