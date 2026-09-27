import SigGolfCandidate.Bridge.Org

/-!
# The reduction adversary and the abstract experiment

`reduction B A rounds` runs the organizer adversary `A` inside the abstract SUF-CMA game.
-/

open OracleSpec OracleComp SigGolf

namespace SigGolfCandidate.Bridge

open SphincsSecurity (SigningSpec)

/-- The abstract adversary's oracle world. -/
abbrev ASpec := AW + SigningSpec

variable {sub : Submission} (B : Assumptions sub) (A : Adversary sub.sizes)

/-- A fixed forgery returned when the organizer adversary never submits. -/
def dummyForgery : SphincsSecurity.Forgery := ⟨B.msgOf 0, B.sigCodec 0⟩

/-- Replay of the organizer interaction: fuel, adversary state, number of signing requests. -/
def advLoop : ℕ → A.State → ℕ → OracleComp ASpec SphincsSecurity.Forgery
  | 0, _, _ => pure (dummyForgery B)
  | n + 1, s, k =>
    match A.step s with
    | .submit (.witness m w) => pure ⟨B.msgOf m, B.witDec w⟩
    | .submit (.signature m σ) => pure ⟨B.msgOf m, B.sigCodec σ⟩
    | .hash y resume => do
        let a ← (liftM (ASpec.query (Sum.inl (Sum.inr (B.unpad y)))) : OracleComp ASpec (BitVec 256))
        advLoop n (resume a) k
    | .sign req resume =>
        if k < LIFETIME then do
          let r ← (liftM (ASpec.query (Sum.inr (B.msgOf req.message))) :
            OracleComp ASpec (Option SphincsSecurity.Signature))
          advLoop n (resume (r.map B.sigCodec.symm)) (k + 1)
        else pure (dummyForgery B)
    | .sample m resume => do
        let u ← (liftM (ASpec.query (Sum.inl (Sum.inl m))) : OracleComp ASpec (Fin (m + 1)))
        advLoop n (resume u) k
    | .step next => advLoop n next k

/-- The reduction: an abstract SUF-CMA adversary built from an organizer adversary. -/
def reduction (rounds : ℕ) : SphincsSecurity.Security.Adversary where
  main pk := advLoop B A rounds (A.initial (B.pkEnc pk) (B.cacheOf pk)) 0

/-- Logged signing, typed over `AW`. -/
def aSigningOracle (sk : SphincsSecurity.Seeded.SecretKey) :
    QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp AW)) :=
  QueryImpl.withLogging fun (request : SphincsSecurity.Message) =>
    (liftM (aSign sk request) : OracleComp AW _)

/-- The adversary's handler in the abstract game. -/
def advImpl (sk : SphincsSecurity.Seeded.SecretKey) :
    QueryImpl ASpec (WriterT (QueryLog SigningSpec) (OracleComp AW)) :=
  QueryImpl.add (QueryImpl.ofLift AW (WriterT (QueryLog SigningSpec) (OracleComp AW)))
    (aSigningOracle sk)

/-- `Security.gameCore`, typed over `AW`. -/
noncomputable def aGameCore (adversary : SphincsSecurity.Security.Adversary) : OracleComp AW Bool := do
  let seed ← (liftM SphincsSecurity.sampleMasterSeed : OracleComp AW _)
  let (pk, sk) ← (liftM (aKeygen seed) : OracleComp AW _)
  let ((forgery, log) : SphincsSecurity.Forgery × QueryLog SigningSpec) ←
    (simulateQ (advImpl sk) (adversary.main pk)).run
  let verified ← (liftM (aVerify pk forgery.message forgery.signature) : OracleComp AW _)
  return decide (SphincsSecurity.SigningTranscript.Valid log ∧ ¬SphincsSecurity.SigningTranscript.Contains log forgery) && verified

/-- Hash calls cost one, uniform sampling is free. -/
def costW : (AW).Domain → ℕ
  | .inl _ => 0
  | .inr _ => 1

theorem experiment_eq (adversary : SphincsSecurity.Security.Adversary) :
    SphincsSecurity.Security.experiment adversary =
      (simulateQ ((roImpl (List UInt8) (BitVec 256)).withAddCost costW)
        (aGameCore adversary)).run.run' ∅ := rfl

/-- Run the adversary against the logged signing oracle. -/
def advRun (sk : SphincsSecurity.Seeded.SecretKey) {α : Type} (X : OracleComp ASpec α) :
    OracleComp AW (α × QueryLog SigningSpec) :=
  (simulateQ (advImpl sk) X).run

lemma advRun_pure (sk : SphincsSecurity.Seeded.SecretKey) {α : Type} (x : α) :
    advRun sk (pure x : OracleComp ASpec α) = pure (x, []) := rfl

lemma advRun_inl_bind (sk : SphincsSecurity.Seeded.SecretKey) {α : Type} (t : AW.Domain)
    (f : AW.Range t → OracleComp ASpec α) :
    advRun sk ((liftM (ASpec.query (Sum.inl t)) : OracleComp ASpec _) >>= f) =
      (AW.query t : OracleComp AW _) >>= fun a => advRun sk (f a) := by
  simp only [advRun, advImpl, simulateQ_bind, simulateQ_spec_query, WriterT.run_bind]
  have e : ((QueryImpl.add (QueryImpl.ofLift AW (WriterT (QueryLog SigningSpec) (OracleComp AW)))
      (aSigningOracle sk)) (Sum.inl t)).run =
      (fun a => (a, [])) <$> (AW.query t : OracleComp AW _) := rfl
  rw [e, bind_map_left]
  simp

lemma advRun_inr_bind (sk : SphincsSecurity.Seeded.SecretKey) {α : Type} (m : SphincsSecurity.Message)
    (f : Option SphincsSecurity.Signature → OracleComp ASpec α) :
    advRun sk ((liftM (ASpec.query (Sum.inr m)) : OracleComp ASpec _) >>= f) =
      (liftM (aSign sk m) : OracleComp AW _) >>= fun u =>
        (fun p => (p.1, [⟨m, u⟩] ++ p.2)) <$> advRun sk (f u) := by
  simp [advRun, advImpl, aSigningOracle, WriterT.run_bind, QueryImpl.add]

/-- The rest of the abstract game after key generation, counted from `c`, with signing log
prefix `lg`. -/
noncomputable def absK (sk : SphincsSecurity.Seeded.SecretKey) (pk : SphincsSecurity.PublicKey)
    (n : ℕ) (s : A.State) (k : ℕ) (lg : QueryLog SigningSpec) (c : ℕ) :
    OracleComp AW (Bool × ℕ) :=
  countFrom costW (do
    let ((forgery, log) : SphincsSecurity.Forgery × QueryLog SigningSpec) ←
      advRun sk (advLoop B A n s k)
    let verified ← (liftM (aVerify pk forgery.message forgery.signature) : OracleComp AW _)
    return decide (SphincsSecurity.SigningTranscript.Valid (lg ++ log) ∧
      ¬SphincsSecurity.SigningTranscript.Contains (lg ++ log) forgery) && verified) c

theorem abs_top (rounds : ℕ) :
    countFrom costW (aGameCore (reduction B A rounds)) 0 =
      (liftM SphincsSecurity.sampleMasterSeed : OracleComp AW _) >>= fun seed =>
        (liftM (countFrom (fun _ => 1) (aKeygen seed) 0) : OracleComp AW _) >>= fun p =>
          absK B A p.1.2 p.1.1 rounds (A.initial (B.pkEnc p.1.1) (B.cacheOf p.1.1)) 0 [] p.2 := by
  unfold aGameCore
  rw [countFrom_bind, countFrom_liftM_unif _ (fun _ => rfl), bind_map_left]
  refine bind_congr fun seed => ?_
  rw [countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  refine bind_congr fun p => ?_
  rcases p with ⟨⟨pk, sk⟩, c⟩
  simp only [absK, List.nil_append]
  rfl

variable {B A}
variable {sk : SphincsSecurity.Seeded.SecretKey} {pk : SphincsSecurity.PublicKey}

lemma absK_hash {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog SigningSpec} {c : ℕ} {y : Query}
    {resume : BitVec 256 → A.State} (h : A.step s = .hash y resume) :
    absK B A sk pk (n + 1) s k lg c =
      (AW.query (Sum.inr (B.unpad y)) : OracleComp AW _) >>= fun a =>
        absK B A sk pk n (resume a) k lg (c + 1) := by
  unfold absK
  simp only [advLoop, h]
  rw [advRun_inl_bind, bind_assoc, countFrom_query_bind]
  rfl

lemma absK_sample {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog SigningSpec} {c : ℕ} {m : ℕ}
    {resume : Fin (m + 1) → A.State} (h : A.step s = .sample m resume) :
    absK B A sk pk (n + 1) s k lg c =
      (AW.query (Sum.inl m) : OracleComp AW _) >>= fun a =>
        absK B A sk pk n (resume a) k lg c := by
  unfold absK
  simp only [advLoop, h]
  rw [advRun_inl_bind, bind_assoc, countFrom_query_bind]
  rfl

lemma absK_step {n : ℕ} {s s' : A.State} {k : ℕ} {lg : QueryLog SigningSpec} {c : ℕ}
    (h : A.step s = .step s') :
    absK B A sk pk (n + 1) s k lg c = absK B A sk pk n s' k lg c := by
  unfold absK
  simp only [advLoop, h]

lemma absK_sign_lt {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog SigningSpec} {c : ℕ}
    {req : SigningRequest} {resume : Option (Bytes sub.sizes.signature) → A.State}
    (h : A.step s = .sign req resume) (hk : k < LIFETIME) :
    absK B A sk pk (n + 1) s k lg c =
      (liftM (countFrom (fun _ => 1) (aSign sk (B.msgOf req.message)) c) : OracleComp AW _) >>=
        fun p => absK B A sk pk n (resume (p.1.map B.sigCodec.symm)) (k + 1)
          (lg ++ [⟨B.msgOf req.message, p.1⟩]) p.2 := by
  unfold absK
  simp only [advLoop, h, hk, if_true]
  rw [advRun_inr_bind, bind_assoc, countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  refine bind_congr fun p => ?_
  rw [bind_map_left]
  simp only [List.append_assoc]

lemma absK_submit_witness {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog SigningSpec} {c : ℕ}
    {m : Message} {w : Bytes sub.sizes.witness} (h : A.step s = .submit (.witness m w)) :
    absK B A sk pk (n + 1) s k lg c =
      (fun p => (decide (SphincsSecurity.SigningTranscript.Valid lg ∧
          ¬SphincsSecurity.SigningTranscript.Contains lg ⟨B.msgOf m, B.witDec w⟩) && p.1, p.2)) <$>
        (liftM (countFrom (fun _ => 1) (aVerify pk (B.msgOf m) (B.witDec w)) c) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h, advRun_pure, pure_bind, List.append_nil]
  rw [map_eq_bind_pure_comp, countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  rfl

lemma absK_submit_signature {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog SigningSpec} {c : ℕ}
    {m : Message} {σ : Bytes sub.sizes.signature} (h : A.step s = .submit (.signature m σ)) :
    absK B A sk pk (n + 1) s k lg c =
      (fun p => (decide (SphincsSecurity.SigningTranscript.Valid lg ∧
          ¬SphincsSecurity.SigningTranscript.Contains lg ⟨B.msgOf m, B.sigCodec σ⟩) && p.1, p.2)) <$>
        (liftM (countFrom (fun _ => 1) (aVerify pk (B.msgOf m) (B.sigCodec σ)) c) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h, advRun_pure, pure_bind, List.append_nil]
  rw [map_eq_bind_pure_comp, countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  rfl

end SigGolfCandidate.Bridge
