import SigGolfCandidate.Bridge.Org

/-!
# The reduction adversary and the abstract experiment

`reduction B A rounds` runs the organizer adversary `A` inside the abstract SUF-CMA game. A signing
request `(m, cache bytes)` becomes the abstract request `⟨msgOf m, cacheDec bytes⟩`. A
signature-form submission `(m, σ)` is expanded by the adversary itself: it runs `aExpand (msgOf m)
pk σ` through its own hash oracle (so these queries are counted exactly as the organizer counts
expansion's queries) and submits `⟨msgOf m, witDec w⟩` on success.
-/

open OracleSpec OracleComp SigGolf

namespace SigGolfCandidate.Bridge

open SphincsSecurity (RequestSpec)

/-- The abstract adversary's oracle world. -/
abbrev ASpec := AW + RequestSpec

variable {sub : Submission} (B : Assumptions sub) (A : Adversary sub.sizes)

/-- A fixed forgery returned when the organizer adversary never submits (or its signature fails
to expand). -/
def dummyForgery : SphincsSecurity.Forgery := ⟨B.msgOf 0, B.witDec 0⟩

/-- The abstract forgery for a signature-form submission, from the result of the simulated
expansion. -/
def sigForgery (m : Message) : Option (Bytes sub.sizes.witness) → SphincsSecurity.Forgery
  | none => dummyForgery B
  | some w => ⟨B.msgOf m, B.witDec w⟩

/-- Run an `AHash` computation through the adversary's hash oracle. -/
def liftH {α : Type} (X : OracleComp AHash α) : OracleComp ASpec α :=
  simulateQ (fun t => (liftM (ASpec.query (Sum.inl (Sum.inr t))) : OracleComp ASpec (BitVec 256))) X

/-- Replay of the organizer interaction against the abstract public key `pk`: fuel, adversary
state, number of signing requests. A signature-form submission is expanded by running the
abstract expansion through the adversary's own hash oracle. -/
def advLoop (pk : SphincsSecurity.PublicKey) :
    ℕ → A.State → ℕ → OracleComp ASpec SphincsSecurity.Forgery
  | 0, _, _ => pure (dummyForgery B)
  | n + 1, s, k =>
    match A.step s with
    | .submit (.witness m w) => pure ⟨B.msgOf m, B.witDec w⟩
    | .submit (.signature m σ) => do
        let r ← liftH (B.aExpand (B.msgOf m) pk σ)
        pure (sigForgery B m r)
    | .hash y resume => do
        let a ← (liftM (ASpec.query (Sum.inl (Sum.inr (B.unpad y)))) : OracleComp ASpec (BitVec 256))
        advLoop pk n (resume a) k
    | .sign req resume =>
        if k < LIFETIME then do
          let r ← (liftM (ASpec.query
              (Sum.inr ⟨B.msgOf req.message, B.cacheDec req.cache⟩)) :
            OracleComp ASpec (Option SphincsSecurity.Signature))
          advLoop pk n (resume (r.map B.compress)) (k + 1)
        else pure (dummyForgery B)
    | .sample m resume => do
        let u ← (liftM (ASpec.query (Sum.inl (Sum.inl m))) : OracleComp ASpec (Fin (m + 1)))
        advLoop pk n (resume u) k
    | .step next => advLoop pk n next k

/-- The reduction: an abstract SUF-CMA adversary built from an organizer adversary. -/
def reduction (rounds : ℕ) : SphincsSecurity.Security.Adversary where
  main pk cache := advLoop B A pk rounds (A.initial (B.pkEnc pk) (B.cacheEnc cache)) 0

/-- Logged signing, typed over `AW`. -/
def aSigningOracle (sk : SphincsSecurity.Seeded.SecretKey) :
    QueryImpl RequestSpec (WriterT (QueryLog RequestSpec) (OracleComp AW)) :=
  QueryImpl.withLogging fun (request : SphincsSecurity.SigningRequest) =>
    (liftM (aSign sk request.cache request.message) : OracleComp AW _)

/-- The adversary's handler in the abstract game. -/
def advImpl (sk : SphincsSecurity.Seeded.SecretKey) :
    QueryImpl ASpec (WriterT (QueryLog RequestSpec) (OracleComp AW)) :=
  QueryImpl.add (QueryImpl.ofLift AW (WriterT (QueryLog RequestSpec) (OracleComp AW)))
    (aSigningOracle sk)

/-- `Security.gameCore`, typed over `AW`. -/
noncomputable def aGameCore (adversary : SphincsSecurity.Security.Adversary) : OracleComp AW Bool := do
  let seed ← (liftM SphincsSecurity.sampleMasterSeed : OracleComp AW _)
  let (pk, cache, sk) ← (liftM (aKeygen seed) : OracleComp AW _)
  let ((forgery, log) : SphincsSecurity.Forgery × QueryLog RequestSpec) ←
    (simulateQ (advImpl sk) (adversary.main pk cache)).run
  let verified ← (liftM (aVerify pk forgery.message forgery.signature) : OracleComp AW _)
  return decide (SphincsSecurity.RequestTranscript.Valid log ∧ ¬SphincsSecurity.RequestTranscript.Contains log forgery) && verified

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
    OracleComp AW (α × QueryLog RequestSpec) :=
  (simulateQ (advImpl sk) X).run

lemma advRun_pure (sk : SphincsSecurity.Seeded.SecretKey) {α : Type} (x : α) :
    advRun sk (pure x : OracleComp ASpec α) = pure (x, []) := rfl

lemma advRun_inl_bind (sk : SphincsSecurity.Seeded.SecretKey) {α : Type} (t : AW.Domain)
    (f : AW.Range t → OracleComp ASpec α) :
    advRun sk ((liftM (ASpec.query (Sum.inl t)) : OracleComp ASpec _) >>= f) =
      (AW.query t : OracleComp AW _) >>= fun a => advRun sk (f a) := by
  simp only [advRun, advImpl, simulateQ_bind, simulateQ_spec_query, WriterT.run_bind]
  have e : ((QueryImpl.add (QueryImpl.ofLift AW (WriterT (QueryLog RequestSpec) (OracleComp AW)))
      (aSigningOracle sk)) (Sum.inl t)).run =
      (fun a => (a, [])) <$> (AW.query t : OracleComp AW _) := rfl
  rw [e, bind_map_left]
  simp

lemma advRun_inr_bind (sk : SphincsSecurity.Seeded.SecretKey) {α : Type}
    (req : SphincsSecurity.SigningRequest)
    (f : Option SphincsSecurity.Signature → OracleComp ASpec α) :
    advRun sk ((liftM (ASpec.query (Sum.inr req)) : OracleComp ASpec _) >>= f) =
      (liftM (aSign sk req.cache req.message) : OracleComp AW _) >>= fun u =>
        (fun p => (p.1, [⟨req, u⟩] ++ p.2)) <$> advRun sk (f u) := by
  simp [advRun, advImpl, aSigningOracle, WriterT.run_bind, QueryImpl.add]

lemma advRun_liftH_bind (sk : SphincsSecurity.Seeded.SecretKey) {α β : Type}
    (X : OracleComp AHash α) (f : α → OracleComp ASpec β) :
    advRun sk (liftH X >>= f) =
      (liftM X : OracleComp AW _) >>= fun a => advRun sk (f a) := by
  induction X using OracleComp.inductionOn with
  | pure x => simp [liftH]
  | query_bind t k ih =>
    have e : (liftM (AHash.query t : OracleComp AHash _) : OracleComp AW _) =
        (AW.query (Sum.inr t) : OracleComp AW _) := rfl
    simp only [liftH, simulateQ_bind, simulateQ_spec_query, bind_assoc] at ih ⊢
    rw [advRun_inl_bind, liftM_bind, e, bind_assoc]
    exact bind_congr fun u => ih u

/-- The rest of the abstract game after key generation, counted from `c`, with signing log
prefix `lg`. -/
noncomputable def absK (sk : SphincsSecurity.Seeded.SecretKey) (pk : SphincsSecurity.PublicKey)
    (n : ℕ) (s : A.State) (k : ℕ) (lg : QueryLog RequestSpec) (c : ℕ) :
    OracleComp AW (Bool × ℕ) :=
  countFrom costW (do
    let ((forgery, log) : SphincsSecurity.Forgery × QueryLog RequestSpec) ←
      advRun sk (advLoop B A pk n s k)
    let verified ← (liftM (aVerify pk forgery.message forgery.signature) : OracleComp AW _)
    return decide (SphincsSecurity.RequestTranscript.Valid (lg ++ log) ∧
      ¬SphincsSecurity.RequestTranscript.Contains (lg ++ log) forgery) && verified) c

theorem abs_top (rounds : ℕ) :
    countFrom costW (aGameCore (reduction B A rounds)) 0 =
      (liftM SphincsSecurity.sampleMasterSeed : OracleComp AW _) >>= fun seed =>
        (liftM (countFrom (fun _ => 1) (aKeygen seed) 0) : OracleComp AW _) >>= fun p =>
          absK B A p.1.2.2 p.1.1 rounds (A.initial (B.pkEnc p.1.1) (B.cacheEnc p.1.2.1)) 0 [] p.2 := by
  unfold aGameCore
  rw [countFrom_bind, countFrom_liftM_unif _ (fun _ => rfl), bind_map_left]
  refine bind_congr fun seed => ?_
  rw [countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  refine bind_congr fun p => ?_
  rcases p with ⟨⟨pk, cache, sk⟩, c⟩
  simp only [absK, List.nil_append]
  rfl

variable {B A}
variable {sk : SphincsSecurity.Seeded.SecretKey} {pk : SphincsSecurity.PublicKey}

lemma absK_hash {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog RequestSpec} {c : ℕ} {y : Query}
    {resume : BitVec 256 → A.State} (h : A.step s = .hash y resume) :
    absK B A sk pk (n + 1) s k lg c =
      (AW.query (Sum.inr (B.unpad y)) : OracleComp AW _) >>= fun a =>
        absK B A sk pk n (resume a) k lg (c + 1) := by
  unfold absK
  simp only [advLoop, h]
  rw [advRun_inl_bind, bind_assoc, countFrom_query_bind]
  rfl

lemma absK_sample {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog RequestSpec} {c : ℕ} {m : ℕ}
    {resume : Fin (m + 1) → A.State} (h : A.step s = .sample m resume) :
    absK B A sk pk (n + 1) s k lg c =
      (AW.query (Sum.inl m) : OracleComp AW _) >>= fun a =>
        absK B A sk pk n (resume a) k lg c := by
  unfold absK
  simp only [advLoop, h]
  rw [advRun_inl_bind, bind_assoc, countFrom_query_bind]
  rfl

lemma absK_step {n : ℕ} {s s' : A.State} {k : ℕ} {lg : QueryLog RequestSpec} {c : ℕ}
    (h : A.step s = .step s') :
    absK B A sk pk (n + 1) s k lg c = absK B A sk pk n s' k lg c := by
  unfold absK
  simp only [advLoop, h]

lemma absK_sign_lt {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog RequestSpec} {c : ℕ}
    {req : SigningRequest sub.sizes} {resume : Option (Bytes sub.sizes.signature) → A.State}
    (h : A.step s = .sign req resume) (hk : k < LIFETIME) :
    absK B A sk pk (n + 1) s k lg c =
      (liftM (countFrom (fun _ => 1) (aSign sk (B.cacheDec req.cache) (B.msgOf req.message)) c) :
          OracleComp AW _) >>=
        fun p => absK B A sk pk n (resume (p.1.map B.compress)) (k + 1)
          (lg ++ [⟨⟨B.msgOf req.message, B.cacheDec req.cache⟩, p.1⟩]) p.2 := by
  unfold absK
  simp only [advLoop, h, hk, if_true]
  rw [advRun_inr_bind, bind_assoc, countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  refine bind_congr fun p => ?_
  rw [bind_map_left]
  simp only [List.append_assoc]

lemma absK_submit_witness {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog RequestSpec} {c : ℕ}
    {m : Message} {w : Bytes sub.sizes.witness} (h : A.step s = .submit (.witness m w)) :
    absK B A sk pk (n + 1) s k lg c =
      (fun p => (decide (SphincsSecurity.RequestTranscript.Valid lg ∧
          ¬SphincsSecurity.RequestTranscript.Contains lg ⟨B.msgOf m, B.witDec w⟩) && p.1, p.2)) <$>
        (liftM (countFrom (fun _ => 1) (aVerify pk (B.msgOf m) (B.witDec w)) c) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h, advRun_pure, pure_bind, List.append_nil]
  rw [map_eq_bind_pure_comp, countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  rfl

lemma absK_submit_signature {n : ℕ} {s : A.State} {k : ℕ} {lg : QueryLog RequestSpec} {c : ℕ}
    {m : Message} {σ : Bytes sub.sizes.signature} (h : A.step s = .submit (.signature m σ)) :
    absK B A sk pk (n + 1) s k lg c =
      (liftM (countFrom (fun _ => 1) (B.aExpand (B.msgOf m) pk σ) c) : OracleComp AW _) >>= fun p =>
        (fun q => (decide (SphincsSecurity.RequestTranscript.Valid lg ∧
            ¬SphincsSecurity.RequestTranscript.Contains lg (sigForgery B m p.1)) && q.1, q.2)) <$>
          (liftM (countFrom (fun _ => 1) (aVerify pk (sigForgery B m p.1).message
            (sigForgery B m p.1).signature) p.2) : OracleComp AW _) := by
  unfold absK
  simp only [advLoop, h]
  rw [advRun_liftH_bind, bind_assoc, countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  refine bind_congr fun p => ?_
  simp only [advRun_pure, pure_bind, List.append_nil]
  rw [map_eq_bind_pure_comp, countFrom_bind, countFrom_liftM_hash _ (fun _ => rfl)]
  rfl

end SigGolfCandidate.Bridge
