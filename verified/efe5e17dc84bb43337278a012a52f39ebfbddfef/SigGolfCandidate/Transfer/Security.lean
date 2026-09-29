import SigGolfCandidate.Transfer.Basic

/-!
# Security transfers from the legacy contract to the current one

`security_of_legacy`: if a submission's runs agree with those of its legacy view (`RunAgrees`)
and the legacy view is `Legacy.Submission.Secure`, then the submission satisfies the current
`SigGolf.Submission.Security`. Nothing here depends on the scheme.

Proof. A current adversary is an `OracleComp` over coins, `H` and signing. The legacy adversary
`advOf adv` keeps the remaining computation as its state and turns each query into one legacy
action (coin → `sample`, hash → `hash`, signing → `sign`), a final forgery into `submit`, and
giving up into idling (`step`) until the round budget runs out, which loses. The round budget is
one more than the height of the query tree (`depth`), maximized over the public key and cache;
it is finite because every oracle range is finite.

Both experiments are then compared as `OracleComp World` programs run against the same lazy
random oracle (`so`). The current experiment's oracle-side count is moved into the program
(`countQ`, `experiment_eq`), and `Dom p q A B` says that from every oracle table the probability
of `p` after `A` is at most that of `q` after `B`. Along the adversary's tree (`main_dom`):

* coins and hash queries are the same queries on both sides; a hash query costs 1 on both sides
  (the legacy transcript adds 1, `countQ` charges 1);
* a signing request runs the same legacy `sign` run on both sides (`RunAgrees`), and its hash
  calls are counted identically, since the legacy `hashCalls` field is exactly the number of
  hash queries a legacy run makes (`countQ_legacyRun`); the current log and the legacy
  transcript record the same requests, failed ones included, and the same returned pairs
  (`Rel`);
* the legacy game refuses a request once `LIFETIME` requests were made and loses; the current
  game answers it, but its log then exceeds `LIFETIME`, so it loses on every path
  (`contN_alwaysFalse`);
* the final check runs the same `expand`/`verify` runs with the same freshness conditions and
  the same hash-call total (`check_dom`).

Key sampling (`$ᵗ SecretKey`, free coins on both sides) and key generation (charged on both
sides, a failure losing on both) are common prefixes (`game_dom`). So the current win-within-`Q`
probability is at most (in fact equal to) the legacy one for `advOf adv`, which `Secure` bounds.
-/

namespace SigGolfCandidate.Transfer.Sec
open OracleComp OracleSpec SigGolf

def countImpl : QueryImpl World (AddWriterT ℕ (OracleComp World)) :=
  (QueryImpl.ofLift World (OracleComp World)).withAddCost hashCost

def countQ {α : Type} (x : OracleComp World α) : OracleComp World (α × ℕ) :=
  (fun z => (z.1, Multiplicative.toAdd z.2)) <$> (simulateQ countImpl x).run

variable {α β : Type}

@[simp] theorem countQ_pure (a : α) : countQ (pure a : OracleComp World α) = pure (a, 0) := by
  simp [countQ]

theorem countQ_bind (x : OracleComp World α) (f : α → OracleComp World β) :
    countQ (x >>= f) = countQ x >>= fun z => (fun w => (w.1, z.2 + w.2)) <$> countQ (f z.1) := by
  simp [countQ, WriterT.run_bind]

theorem countQ_map (x : OracleComp World α) (f : α → β) :
    countQ (f <$> x) = (fun z => (f z.1, z.2)) <$> countQ x := by
  simp [countQ]

/-- A hash query, as the legacy and current programs lift it into `World`. -/
abbrev hashQ (t : Query) : OracleComp World (BitVec 256) := liftM (World.query (Sum.inr t))

theorem countQ_hashQ (t : Query) : countQ (hashQ t) = (fun u => (u, 1)) <$> hashQ t := by
  simp [countQ, countImpl, hashCost]

theorem countQ_legacyHash (t : Legacy.Query) :
    countQ (liftM (liftM (Legacy.HashSpec.query t) : OracleComp Legacy.HashSpec _) :
      OracleComp World (BitVec 256)) =
    (fun u => (u, 1)) <$> (liftM (liftM (Legacy.HashSpec.query t) : OracleComp Legacy.HashSpec _) :
      OracleComp World (BitVec 256)) :=
  countQ_hashQ t

/-- The legacy interpreter's hash-call counter is the number of hash queries it makes. -/
theorem countQ_execute (fuel : ℕ) (image : Legacy.Riscv.Image) (state : RiscvZkvm.Rv64.MachineState) :
    countQ (liftM (Legacy.Riscv.execute fuel image state) : OracleComp World _) =
      (fun e => (e, e.hashCalls)) <$> liftM (Legacy.Riscv.execute fuel image state) := by
  induction fuel generalizing state with
  | zero => simp [Legacy.Riscv.execute]
  | succ fuel ih =>
    rw [Legacy.Riscv.execute]
    split
    · simp
    · split_ifs
      · simp only [liftM_bind]
        rw [countQ_bind, countQ_legacyHash]
        simp [countQ_map, ih, Legacy.Riscv.Execution.charge, Nat.add_comm]
      all_goals simp
    · split
      · simp
      · simp [countQ_map, ih, Legacy.Riscv.Execution.charge]

theorem countQ_legacyRun (old : Legacy.Submission) (phase : Legacy.Phase)
    (input : Legacy.Input old.sizes phase) :
    countQ (liftM (old.run phase input) : OracleComp World _) =
      (fun r => (r, r.hashCalls)) <$> liftM (old.run phase input) := by
  unfold Legacy.Submission.run
  split
  · simp
  · simp only [liftM_bind, liftM_pure, countQ_bind, countQ_execute]
    simp

/-- A coin query in `World`. -/
abbrev coinQ (n : ℕ) : OracleComp World (Fin (n + 1)) := liftM (World.query (Sum.inl n))

theorem countQ_coinQ (n : ℕ) : countQ (coinQ n) = (fun u => (u, 0)) <$> coinQ n := by
  simp [countQ, countImpl, hashCost]

theorem countQ_unifQ (n : ℕ) :
    countQ (liftM (liftM (unifSpec.query n) : ProbComp _) : OracleComp World (Fin (n + 1))) =
      (fun u => (u, 0)) <$> (liftM (liftM (unifSpec.query n) : ProbComp _) :
        OracleComp World (Fin (n + 1))) :=
  countQ_coinQ n

theorem countQ_liftProb (x : ProbComp α) :
    countQ (liftM x : OracleComp World α) = (fun a => (a, 0)) <$> liftM x := by
  induction x using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp only [liftM_bind, countQ_bind, ih, countQ_unifQ]
    simp

abbrev so : QueryImpl World (StateT (QueryCache HashSpec) ProbComp) :=
  unifFwdImpl HashSpec + HashSpec.randomOracle

theorem simulate_countImpl (G : OracleComp World α) :
    simulateQ so ((simulateQ countImpl G).run) = (simulateQ (so.withAddCost hashCost) G).run := by
  induction G using OracleComp.inductionOn with
  | pure a => simp
  | query_bind t k ih =>
    simp [countImpl] at ih ⊢
    simp [ih]

/-! ### Domination of events after running both sides against the same oracle -/

/-- `Dom p q A B`: from every oracle table, `A` satisfies `p` at most as often as `B`
satisfies `q`. -/
def Dom {α β : Type} (p : α → Prop) (q : β → Prop) (A : OracleComp World α)
    (B : OracleComp World β) : Prop :=
  ∀ σ, Pr[p | (simulateQ so A).run' σ] ≤ Pr[q | (simulateQ so B).run' σ]

namespace Dom
variable {γ α' β' : Type} {p p' : α → Prop} {q q' : β → Prop}
  {A : OracleComp World α} {B : OracleComp World β}

theorem bind (x : OracleComp World γ) {f : γ → OracleComp World α} {g : γ → OracleComp World β}
    (h : ∀ c, Dom p q (f c) (g c)) : Dom p q (x >>= f) (x >>= g) := by
  intro σ
  simp only [simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun z => mul_le_mul_right ?_ _
  have := h z.1 z.2
  simpa only [StateT.run'_eq] using this

theorem map_left {f : α' → α} {A : OracleComp World α'} (h : Dom (p ∘ f) q A B) :
    Dom p q (f <$> A) B := by
  intro σ
  simpa [simulateQ_map, StateT.run'_eq, probEvent_map, Function.comp_def] using h σ

theorem map_right {f : β' → β} {B : OracleComp World β'} (h : Dom p (q ∘ f) A B) :
    Dom p q A (f <$> B) := by
  intro σ
  simpa [simulateQ_map, StateT.run'_eq, probEvent_map, Function.comp_def] using h σ

theorem mono_left (hp : ∀ z, p' z → p z) (h : Dom p q A B) : Dom p' q A B :=
  fun σ => le_trans (probEvent_mono fun z _ => hp z) (h σ)

theorem mono_right (hq : ∀ z, q z → q' z) (h : Dom p q A B) : Dom p q' A B :=
  fun σ => le_trans (h σ) (probEvent_mono fun z _ => hq z)

theorem of_false (hp : ∀ z, ¬ p z) : Dom p q A B := by
  intro σ
  have : Pr[p | (simulateQ so A).run' σ] = 0 := by
    rw [probEvent_eq_zero_iff]; intro z _; exact hp z
  rw [this]; exact zero_le

theorem pure_pure {a : α} {b : β} (h : p a → q b) :
    Dom p q (pure a) (pure b) := by
  intro σ
  classical
  simp only [simulateQ_pure, StateT.run'_eq, StateT.run_pure, map_pure, probEvent_pure]
  by_cases ha : p a
  · simp [ha, h ha]
  · simp [ha]

end Dom

/-! ### The simulating legacy adversary -/

/-- The height of a computation's query tree; finite since every range is finite. -/
noncomputable def depth {ι : Type} {spec : OracleSpec ι} [spec.Fintype] {α : Type} :
    OracleComp spec α → ℕ
  | .pure _ => 0
  | .queryBind _ k => (Finset.univ.sup fun u => depth (k u)) + 1

theorem depth_lt {ι : Type} {spec : OracleSpec ι} [spec.Fintype] {α : Type} {t : spec.Domain}
    (k : spec.Range t → OracleComp spec α) (u : spec.Range t) :
    depth (k u) < depth (OracleComp.queryBind t k) := by
  show depth (k u) < (Finset.univ.sup fun u => depth (k u)) + 1
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun u => depth (k u)) (Finset.mem_univ u))

abbrev NewComp (S : Sizes) := OracleComp (World + SigningSpec S) (Option (Forgery S))

def forgeryOf {S : Sizes} : Forgery S → Legacy.Forgery (sizesOf S)
  | .witness m w => .witness m w
  | .signature m s => .signature m s

def requestOf {S : Sizes} (r : SigningRequest S) : Legacy.SigningRequest (sizesOf S) :=
  ⟨r.message, r.cache⟩

/-- One legacy action per query of the current adversary; giving up idles forever. -/
def stepOf {S : Sizes} : NewComp S → Legacy.Action (sizesOf S) (Option (NewComp S))
  | .pure (some f) => .submit (forgeryOf f)
  | .pure none => .step none
  | .queryBind (.inl (.inl n)) k => .sample n (fun u => some (k u))
  | .queryBind (.inl (.inr x)) k => .hash x (fun h => some (k h))
  | .queryBind (.inr r) k => .sign (requestOf r) (fun o => some (k o))

def advOf {S : Sizes} (adv : Adversary S) : Legacy.Adversary (sizesOf S) where
  State := Option (NewComp S)
  initial pk cache := some (adv pk cache)
  step
    | none => .step none
    | some c => stepOf c

example {S : Sizes} (n : ℕ) (k : Fin (n+1) → NewComp S) :
    stepOf (OracleComp.queryBind (Sum.inl (Sum.inl n)) k) = .sample n (fun u => some (k u)) := rfl

/-! ### The current game, continuation form -/

section New
variable (sub : Submission)

abbrev implN (sk : SecretKey) :
    QueryImpl (World + SigningSpec sub.sizes) (WriterT (SigningLog sub.sizes) (OracleComp World)) :=
  QueryImpl.ofLift World (WriterT (SigningLog sub.sizes) (OracleComp World)) +
    sub.signingOracle sk

def tailN (pk : PublicKey) (log : SigningLog sub.sizes) :
    Option (Forgery sub.sizes) → OracleComp World Bool
  | none => pure false
  | some forgery => do
      let forged ← liftM (sub.checkForgery pk log forgery)
      pure (decide log.WithinLifetime && forged)

def contN (sk : SecretKey) (pk : PublicKey) (c : NewComp sub.sizes) (L : SigningLog sub.sizes) :
    OracleComp World Bool :=
  (simulateQ (implN sub sk) c).run >>= fun z => tailN sub pk (L ++ z.2) z.1

theorem game_eq (adv : Adversary sub.sizes) :
    sub.game adv = (do
      let sk ← liftM ($ᵗ SecretKey : ProbComp SecretKey)
      let keygen ← liftM (sub.run .keygen sk)
      match keygen.output with
      | none => pure false
      | some (pk, cache) => contN sub sk pk (adv pk cache) []) := by
  unfold Submission.game
  congr 1; funext sk; congr 1; funext keygen
  rcases keygen.output with _ | ⟨pk, cache⟩
  · rfl
  · simp only [contN, Submission.interact]
    congr 1; funext z
    rcases z with ⟨_ | f, log⟩ <;> simp [tailN]

variable {sub}

theorem contN_pure (sk : SecretKey) (pk : PublicKey) (x : Option (Forgery sub.sizes))
    (L : SigningLog sub.sizes) : contN sub sk pk (pure x) L = tailN sub pk L x := by
  simp [contN]

theorem contN_queryBind (sk : SecretKey) (pk : PublicKey) (t : (World + SigningSpec sub.sizes).Domain)
    (k : (World + SigningSpec sub.sizes).Range t → NewComp sub.sizes) (L : SigningLog sub.sizes) :
    contN sub sk pk (OracleComp.queryBind t k) L =
      (implN sub sk t).run >>= fun z => contN sub sk pk (k z.1) (L ++ z.2) := by
  rw [show OracleComp.queryBind t k = (liftM ((World + SigningSpec sub.sizes).query t) >>= k) from rfl]
  simp only [contN, simulateQ_bind, simulateQ_spec_query, WriterT.run_bind', bind_assoc]
  congr 1; funext z
  simp [List.append_assoc]

theorem implN_coin (sk : SecretKey) (n : ℕ) :
    (implN sub sk (Sum.inl (Sum.inl n))).run = (fun u => (u, [])) <$> coinQ n := rfl

theorem implN_hash (sk : SecretKey) (x : Query) :
    (implN sub sk (Sum.inl (Sum.inr x))).run = (fun u => (u, [])) <$> hashQ x := rfl

theorem withLogging_run {S : Sizes} (so : QueryImpl (SigningSpec S) (OracleComp World))
    (r : SigningRequest S) :
    (so.withLogging r).run = (fun u => (u, [⟨r, u⟩])) <$> so r := by
  rw [QueryImpl.withLogging_apply]
  simp

theorem implN_sign (sk : SecretKey) (r : SigningRequest sub.sizes) :
    (implN sub sk (Sum.inr r)).run = (fun run => (run.output, [⟨r, run.output⟩])) <$>
      (liftM (sub.run .sign (sk, r.cache, r.message)) : OracleComp World _) := by
  simp only [implN]
  rw [QueryImpl.add_apply_inr, Submission.signingOracle]
  refine (withLogging_run _ r).trans ?_
  generalize (liftM (sub.run .sign (sk, r.cache, r.message)) : OracleComp World _) = x
  simp only [bind_pure_comp]
  exact Functor.map_map _ _ _

end New

/-! ### Transcripts -/

section Rel
variable {S : Sizes}

/-- The legacy transcript records the same requests as the current log. -/
structure Rel (L : SigningLog S) (T : Legacy.Transcript (sizesOf S)) : Prop where
  count : T.signingRequests = L.length
  lifetime : L.length ≤ LIFETIME
  signed : ∀ m s, (m, s) ∈ T.signed ↔ L.Contains m s

theorem Rel.nil (n : ℕ) : Rel ([] : SigningLog S) ({ hashCalls := n } : Legacy.Transcript _) :=
  ⟨rfl, Nat.zero_le _, by simp [SigningLog.Contains]⟩

theorem Rel.freshMessage {L : SigningLog S} {T} (h : Rel L T) (m : Message) :
    T.freshMessage m = !decide (L.Signed m) := by
  unfold Legacy.Transcript.freshMessage
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨m', s⟩, hmem, rfl⟩
    obtain ⟨e, he, hm, hs⟩ := (h.signed _ _).1 hmem
    refine ⟨e, he, hm, ?_⟩
    rw [hs]; rfl
  · rintro ⟨e, he, hm, hs⟩
    obtain ⟨s, hs'⟩ := Option.isSome_iff_exists.1 hs
    exact ⟨(m, s), (h.signed _ _).2 ⟨e, he, hm, hs'⟩, rfl⟩

theorem Rel.freshSignature {L : SigningLog S} {T} (h : Rel L T) (m : Message) (s) :
    T.freshSignature m s = !decide (L.Contains m s) := by
  unfold Legacy.Transcript.freshSignature
  congr 1
  rw [Bool.eq_iff_iff]
  simp only [List.contains_iff_mem, decide_eq_true_eq]
  exact h.signed m s

theorem Rel.record {L : SigningLog S} {T} (h : Rel L T)
    (hlt : T.signingRequests < Legacy.LIFETIME) (r : SigningRequest S)
    (result : Legacy.RunResult (Legacy.Bytes (sizesOf S).signature)) :
    Rel (L ++ [⟨r, result.value⟩]) (T.record r.message result) := by
  constructor
  · simp [Legacy.Transcript.record, h.count]
  · have := h.count ▸ hlt
    simp only [List.length_append, List.length_singleton]
    exact this
  · intro m s
    have hc : (L ++ [⟨r, result.value⟩] : SigningLog S).Contains m s ↔
        L.Contains m s ∨ (r.message = m ∧ result.value = some s) := by
      simp only [SigningLog.Contains, List.mem_append, List.mem_singleton]
      constructor
      · rintro ⟨e, he | rfl, hm, hs⟩
        · exact Or.inl ⟨e, he, hm, hs⟩
        · exact Or.inr ⟨hm, hs⟩
      · rintro (⟨e, he, hm, hs⟩ | ⟨hm, hs⟩)
        · exact ⟨e, Or.inl he, hm, hs⟩
        · exact ⟨_, Or.inr rfl, hm, hs⟩
    rw [hc, ← h.signed]
    unfold Legacy.Transcript.record
    rcases hv : result.value with _ | sig
    · simp
    · simp only [List.mem_cons, Prod.mk.injEq, Option.some.injEq]
      constructor
      · rintro (⟨rfl, rfl⟩ | h') <;> simp_all
      · rintro (h' | ⟨rfl, rfl⟩) <;> simp_all

end Rel

/-! ### The legacy interaction, one step at a time -/

section Old
variable (sub : Submission) (adv : Adversary sub.sizes) (sk : SecretKey) (pk : PublicKey)

theorem old_none (T : Legacy.Transcript (sizesOf sub.sizes)) (rounds : ℕ) :
    (legacyOf sub).interact (advOf adv) sk pk rounds none T = pure ⟨false, T.hashCalls⟩ := by
  induction rounds with
  | zero => rfl
  | succ r ih => exact ih

theorem old_pure_none (T : Legacy.Transcript (sizesOf sub.sizes)) (r : ℕ) :
    (legacyOf sub).interact (advOf adv) sk pk (r + 1) (some (pure none)) T = pure ⟨false, T.hashCalls⟩ := by
  exact old_none sub adv sk pk T r

theorem old_pure_some (T : Legacy.Transcript (sizesOf sub.sizes)) (r : ℕ) (f : Forgery sub.sizes) :
    (legacyOf sub).interact (advOf adv) sk pk (r + 1) (some (pure (some f))) T =
      liftM ((legacyOf sub).checkForgery pk T (forgeryOf f)) := by
  rfl

theorem old_coin (T : Legacy.Transcript (sizesOf sub.sizes)) (r : ℕ) (n : ℕ)
    (k : Fin (n + 1) → NewComp sub.sizes) :
    (legacyOf sub).interact (advOf adv) sk pk (r + 1)
      (some (OracleComp.queryBind (Sum.inl (Sum.inl n)) k)) T =
      coinQ n >>= fun u => (legacyOf sub).interact (advOf adv) sk pk r (some (k u)) T := by
  rfl

theorem old_hash (T : Legacy.Transcript (sizesOf sub.sizes)) (r : ℕ) (x : Query)
    (k : BitVec 256 → NewComp sub.sizes) :
    (legacyOf sub).interact (advOf adv) sk pk (r + 1)
      (some (OracleComp.queryBind (Sum.inl (Sum.inr x)) k)) T =
      hashQ x >>= fun u => (legacyOf sub).interact (advOf adv) sk pk r (some (k u))
        { T with hashCalls := T.hashCalls + 1 } := by
  rfl

theorem old_sign (T : Legacy.Transcript (sizesOf sub.sizes)) (r : ℕ) (req : SigningRequest sub.sizes)
    (k : Option (Bytes sub.sizes.signature) → NewComp sub.sizes) :
    (legacyOf sub).interact (advOf adv) sk pk (r + 1)
      (some (OracleComp.queryBind (Sum.inr req) k)) T =
      if T.signingRequests < Legacy.LIFETIME then
        (liftM ((legacyOf sub).run .sign (sk, req.cache, req.message)) : OracleComp World _) >>=
          fun result => (legacyOf sub).interact (advOf adv) sk pk r (some (k result.value))
            (T.record req.message result)
      else pure ⟨false, T.hashCalls⟩ := by
  rfl

end Old

/-! ### The comparison -/

theorem map_map_eq_bind {γ δ ε : Type} (x : OracleComp World γ) (g : γ → δ) (f : δ → ε) :
    f <$> (g <$> x) = x >>= fun r => pure (f (g r)) := by
  simp [map_eq_bind_pure_comp]

section Main
variable {sub : Submission} (hrun : RunAgrees sub)
include hrun

omit hrun in
@[simp] theorem resultOf_isSome {S : Sizes} (p : Program)
    (r : Legacy.RunResult (Legacy.Output (sizesOf S) (phaseOf p))) :
    (resultOf p r).output.isSome = r.value.isSome := by
  simp [resultOf]

theorem countQ_run (p : Program) (input : Input sub.sizes p) :
    countQ (liftM (sub.run p input) : OracleComp World _) =
      (liftM ((legacyOf sub).run (phaseOf p) (inputOf p input)) : OracleComp World _) >>=
        fun r => pure (resultOf p r, r.hashCalls) := by
  have h : (liftM (sub.run p input) : OracleComp World _) = resultOf p <$>
      (liftM ((legacyOf sub).run (phaseOf p) (inputOf p input) : OracleComp HashSpec _) :
        OracleComp World _) := by
    rw [hrun p input]; exact liftM_map _ _
  rw [h]
  erw [countQ_map]
  erw [countQ_legacyRun]
  exact map_map_eq_bind _ _ _

omit hrun in
theorem Dom.pure_left {α β : Type} {p : α → Prop} {q : β → Prop} {a : α} {B : OracleComp World β}
    (h : ¬ p a) : Dom p q (pure a) B := by
  intro σ
  classical
  simp [probEvent_pure, h]

theorem check_dom (pk : PublicKey) (Q : ℕ) (L : SigningLog sub.sizes)
    (T : Legacy.Transcript (sizesOf sub.sizes)) (hrel : Rel L T) (f : Forgery sub.sizes) :
    Dom (fun z : Bool × ℕ => z.1 = true ∧ T.hashCalls + z.2 ≤ Q)
      (fun r : Legacy.AttackResult => r.won = true ∧ r.hashCalls ≤ Q)
      (countQ (tailN sub pk L (some f)))
      (liftM ((legacyOf sub).checkForgery pk T (forgeryOf f))) := by
  have hlt : decide L.WithinLifetime = true := by simpa using hrel.lifetime
  cases f with
  | witness m w =>
    simp only [tailN, forgeryOf, Submission.checkForgery, Legacy.Submission.checkForgery, hlt,
      Bool.true_and, liftM_bind, liftM_pure, countQ_bind]
    erw [countQ_run hrun]
    simp only [countQ_pure, bind_assoc, pure_bind, map_pure]
    refine Dom.bind _ fun r => Dom.pure_pure ?_
    erw [resultOf_isSome, hrel.freshMessage]
    intro h; simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
      decide_eq_false_iff_not] at h ⊢
    exact h
  | signature m s =>
    simp only [tailN, forgeryOf, Submission.checkForgery, Legacy.Submission.checkForgery, hlt,
      Bool.true_and, liftM_bind, countQ_bind]
    erw [countQ_run hrun]
    simp only [countQ_pure, bind_assoc, pure_bind, map_pure]
    refine Dom.bind _ fun r => ?_
    rcases hv : r.value with _ | wit
    · have ho : (resultOf Program.expand r).output = none := by
        simp only [resultOf, hv]; rfl
      erw [ho]
      simp only [liftM_pure, countQ_pure, map_pure, pure_bind]
      exact Dom.pure_left (by simp)
    · have ho : (resultOf Program.expand r).output = some wit := by
        simp only [resultOf, hv]; rfl
      erw [ho]
      simp only [liftM_bind, liftM_pure, countQ_bind]
      erw [countQ_run hrun]
      simp only [countQ_pure, bind_assoc, pure_bind, map_pure, map_bind]
      refine Dom.bind _ fun r' => Dom.pure_pure ?_
      erw [resultOf_isSome, hrel.freshSignature]
      intro h
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
        decide_eq_false_iff_not, Nat.add_zero] at h ⊢
      exact ⟨h.1, by omega⟩

omit hrun in
theorem alwaysFalse_bind {γ : Type} (x : OracleComp World γ) {f : γ → OracleComp World Bool}
    (h : ∀ c, (fun _ => false) <$> f c = f c) :
    (fun _ => false) <$> (x >>= f) = x >>= f := by
  rw [map_bind]; congr 1; funext c; exact h c

omit hrun in
theorem tailN_alwaysFalse (pk : PublicKey) (L : SigningLog sub.sizes) (hL : LIFETIME < L.length)
    (f : Option (Forgery sub.sizes)) :
    (fun _ => false) <$> tailN sub pk L f = tailN sub pk L f := by
  have : decide L.WithinLifetime = false := by simp; omega
  rcases f with _ | f
  · simp [tailN]
  · simp only [tailN, this, Bool.false_and, map_bind, map_pure]

omit hrun in
theorem contN_alwaysFalse (sk : SecretKey) (pk : PublicKey) (c : NewComp sub.sizes)
    (L : SigningLog sub.sizes) (hL : LIFETIME < L.length) :
    (fun _ => false) <$> contN sub sk pk c L = contN sub sk pk c L :=
  alwaysFalse_bind _ fun z => tailN_alwaysFalse pk _ (by simp; omega) _

omit hrun in
theorem Dom.of_alwaysFalse {β : Type} {P : ℕ → Prop} {q : β → Prop} {A : OracleComp World Bool}
    {B : OracleComp World β} (h : (fun _ => false) <$> A = A) :
    Dom (fun z : Bool × ℕ => z.1 = true ∧ P z.2) q (countQ A) B := by
  rw [← h, countQ_map]
  exact Dom.map_left (Dom.of_false (by simp))

theorem main_dom (adv : Adversary sub.sizes) (sk : SecretKey) (pk : PublicKey) (Q : ℕ)
    (c : NewComp sub.sizes) :
    ∀ (L : SigningLog sub.sizes) (T : Legacy.Transcript (sizesOf sub.sizes)) (rounds : ℕ),
      depth c < rounds → Rel L T →
      Dom (fun z : Bool × ℕ => z.1 = true ∧ T.hashCalls + z.2 ≤ Q)
        (fun r : Legacy.AttackResult => r.won = true ∧ r.hashCalls ≤ Q)
        (countQ (contN sub sk pk c L))
        ((legacyOf sub).interact (advOf adv) sk pk rounds (some c) T) := by
  induction c using OracleComp.recOn with
  | pure x =>
    intro L T rounds hd hrel
    obtain ⟨r, rfl⟩ : ∃ r, rounds = r + 1 := ⟨rounds - 1, by omega⟩
    erw [contN_pure]
    rcases x with _ | f
    · simp only [tailN, countQ_pure]
      exact Dom.pure_left (by simp)
    · erw [old_pure_some]
      exact check_dom hrun pk Q L T hrel f
  | queryBind t k ih =>
    intro L T rounds hd hrel
    obtain ⟨r, rfl⟩ : ∃ r, rounds = r + 1 := ⟨rounds - 1, by omega⟩
    have hk : ∀ u, depth (k u) < r := fun u => by have := depth_lt k u; omega
    rw [contN_queryBind]
    rcases t with (n | x) | req
    · erw [implN_coin, old_coin]
      rw [bind_map_left, countQ_bind, countQ_coinQ, bind_map_left]
      refine Dom.bind _ fun u => Dom.map_left ?_
      simp only [List.append_nil]
      refine Dom.mono_left ?_ (ih u L T r (hk u) hrel)
      intro z hz; simpa using hz
    · erw [implN_hash, old_hash]
      rw [bind_map_left, countQ_bind, countQ_hashQ, bind_map_left]
      refine Dom.bind _ fun u => Dom.map_left ?_
      simp only [List.append_nil]
      have hrel' : Rel L { T with hashCalls := T.hashCalls + 1 } :=
        ⟨hrel.count, hrel.lifetime, hrel.signed⟩
      refine Dom.mono_left ?_ (ih u L { T with hashCalls := T.hashCalls + 1 } r (hk u) hrel')
      intro z hz
      simp only [Function.comp] at hz ⊢
      exact ⟨hz.1, by omega⟩
    · erw [implN_sign, old_sign]
      split_ifs with hlt
      · erw [bind_map_left]
        erw [countQ_bind, countQ_run hrun]
        simp only [bind_assoc, pure_bind]
        refine Dom.bind _ fun res => Dom.map_left ?_
        have ho : (resultOf Program.sign res).output = res.value := by
          simp only [resultOf]; cases res.value <;> rfl
        erw [ho]
        refine Dom.mono_left ?_ (ih res.value _ _ r (hk _) (hrel.record hlt req res))
        intro z hz
        simp only [Function.comp, Legacy.Transcript.record] at hz ⊢
        exact ⟨hz.1, by omega⟩
      · have hL : LIFETIME ≤ L.length := by
          have := hrel.count; simp only [Legacy.LIFETIME] at hlt; simp only [LIFETIME]; omega
        refine Dom.of_alwaysFalse (P := fun n => T.hashCalls + n ≤ Q) ?_
        erw [bind_map_left]
        exact alwaysFalse_bind _ fun run =>
          contN_alwaysFalse sk pk _ _ (by simp; omega)

theorem game_dom (adv : Adversary sub.sizes) (Q rounds : ℕ)
    (hrounds : ∀ pk cache, depth (adv pk cache) < rounds) :
    Dom (fun z : Bool × ℕ => z.1 = true ∧ z.2 ≤ Q)
      (fun r : Legacy.AttackResult => r.won = true ∧ r.hashCalls ≤ Q)
      (countQ (sub.game adv))
      (do
        let secretKey ← liftM Legacy.sampleSecretKey
        let keygen ← liftM ((legacyOf sub).run .keygen secretKey)
        let some (pk, cache) := keygen.value | return ⟨false, keygen.hashCalls⟩
        (legacyOf sub).interact (advOf adv) secretKey pk rounds ((advOf adv).initial pk cache)
          { hashCalls := keygen.hashCalls }) := by
  rw [game_eq, countQ_bind, countQ_liftProb, bind_map_left]
  refine Dom.bind _ fun sk => Dom.map_left ?_
  erw [countQ_bind, countQ_run hrun]
  simp only [bind_assoc, pure_bind]
  refine Dom.bind _ fun res => Dom.map_left ?_
  rcases hv : res.value with _ | ⟨pk, cache⟩
  · have ho : (resultOf Program.keygen res).output = none := by
      simp only [resultOf, hv]; rfl
    erw [ho]
    exact Dom.pure_left (by simp)
  · have ho : (resultOf Program.keygen res).output = some (pk, cache) := by
      simp only [resultOf, hv]; rfl
    erw [ho]
    refine Dom.mono_left ?_ (main_dom hrun adv sk pk Q (adv pk cache) [] { hashCalls := res.hashCalls }
      rounds (hrounds pk cache) (Rel.nil _))
    intro z hz
    simp only [Function.comp] at hz ⊢
    exact ⟨hz.1, by omega⟩

end Main

theorem experiment_eq (sub : Submission) (adv : Adversary sub.sizes) :
    sub.securityExperiment adv = (simulateQ so (countQ (sub.game adv))).run' ∅ := by
  unfold Submission.securityExperiment countQ
  rw [simulateQ_map, simulate_countImpl]
  simp only [StateT.run'_eq, StateT.run_map, Functor.map_map]
  rfl

theorem security_of_legacy (sub : Submission) (hrun : RunAgrees sub)
    (hsec : (legacyOf sub).Secure) : sub.Security := by
  intro adv Q hQ
  let rounds := (Finset.univ.sup fun pc : PublicKey × Bytes sub.sizes.cache =>
    depth (adv pc.1 pc.2)) + 1
  have hrounds : ∀ pk cache, depth (adv pk cache) < rounds := fun pk cache =>
    Nat.lt_succ_of_le (Finset.le_sup (f := fun pc : PublicKey × Bytes sub.sizes.cache =>
      depth (adv pc.1 pc.2)) (Finset.mem_univ (pk, cache)))
  have hold := hsec (advOf adv) rounds Q hQ
  have hnew := game_dom hrun adv Q rounds hrounds ∅
  rw [experiment_eq]
  refine le_trans (le_of_eq ?_) (le_trans hnew (le_of_eq_of_le ?_ hold))
  · rfl
  · unfold Legacy.Submission.securityExperiment Legacy.withRandomness
    congr 3
    congr 1
    funext sk
    congr 1
    funext keygen
    obtain ⟨_ | ⟨pk, cache⟩, _, _, _, _⟩ := keygen
    · rfl
    · rfl

end SigGolfCandidate.Transfer.Sec

namespace SigGolfCandidate.Transfer

/-- **Security transfer.** A submission whose runs agree with its legacy view inherits the
current contract's `Security` from the legacy contract's `Secure`. -/
theorem security_of_legacy (sub : SigGolf.Submission) (hrun : RunAgrees sub)
    (hsec : (legacyOf sub).Secure) : sub.Security :=
  Sec.security_of_legacy sub hrun hsec

end SigGolfCandidate.Transfer
