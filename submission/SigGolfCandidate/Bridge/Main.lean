import SigGolfCandidate.Bridge.Abs

/-!
# The security bridge

`Assumptions.secure`: under the bridge assumptions, the submission satisfies the organizer's
`Submission.Secure`.
-/

open OracleSpec OracleComp SigGolf ENNReal

namespace SigGolfCandidate.Bridge

open SphincsSecurity (SigningSpec)

variable {sub : Submission} (B : Assumptions sub)

/-- The invariant linking the organizer transcript to the abstract signing log and counter. -/
def Inv (T : Transcript sub.sizes) (k : ℕ) (lg : QueryLog SigningSpec) (c : ℕ) : Prop :=
  T.hashCalls = c ∧ T.signingRequests = k ∧ lg.length = k ∧ k ≤ LIFETIME ∧
    ∀ e ∈ lg, ∀ σ, e.2 = some σ → ∃ mo, B.msgOf mo = e.1 ∧ (mo, B.sigCodec.symm σ) ∈ T.signed

/-- An organizer win transfers to an abstract win with the same number of hash calls. -/
def RFin (r : AttackResult) (b : Bool × ℕ) : Prop :=
  r.won = true → b.1 = true ∧ b.2 = r.hashCalls

lemma rfin_false (h : ℕ) (b : Bool × ℕ) : RFin ⟨false, h⟩ b := fun h => by cases h

variable {B}

lemma valid_of_inv {T : Transcript sub.sizes} {k : ℕ} {lg : QueryLog SigningSpec} {c : ℕ}
    (hI : Inv B T k lg c) : SphincsSecurity.SigningTranscript.Valid lg := by
  obtain ⟨-, -, hlen, hk, -⟩ := hI
  unfold SphincsSecurity.SigningTranscript.Valid
  rw [hlen]
  exact hk.trans B.lifetime_le

lemma not_contains_witness {T : Transcript sub.sizes} {k : ℕ} {lg : QueryLog SigningSpec} {c : ℕ}
    (hI : Inv B T k lg c) {m : Message} (σ : SphincsSecurity.Signature)
    (hfresh : T.freshMessage m = true) :
    ¬SphincsSecurity.SigningTranscript.Contains lg ⟨B.msgOf m, σ⟩ := by
  rintro ⟨e, he, h1, h2⟩
  obtain ⟨mo, hmo, hmem⟩ := hI.2.2.2.2 e he σ h2
  have : mo = m := B.msgOf_injective (hmo.trans h1)
  subst this
  unfold Transcript.freshMessage at hfresh
  simp only [Bool.not_eq_true', List.any_eq_false, beq_iff_eq] at hfresh
  exact hfresh _ hmem rfl

lemma not_contains_signature {T : Transcript sub.sizes} {k : ℕ} {lg : QueryLog SigningSpec}
    {c : ℕ} (hI : Inv B T k lg c) {m : Message} {σ : Bytes sub.sizes.signature}
    (hfresh : T.freshSignature m σ = true) :
    ¬SphincsSecurity.SigningTranscript.Contains lg ⟨B.msgOf m, B.sigCodec σ⟩ := by
  rintro ⟨e, he, h1, h2⟩
  obtain ⟨mo, hmo, hmem⟩ := hI.2.2.2.2 e he _ h2
  have : mo = m := B.msgOf_injective (hmo.trans h1)
  subst this
  rw [Equiv.symm_apply_apply] at hmem
  unfold Transcript.freshSignature at hfresh
  simp only [Bool.not_eq_true'] at hfresh
  have : T.signed.contains (mo, σ) = true := List.contains_iff_mem.mpr hmem
  rw [this] at hfresh
  cases hfresh

lemma inv_record {T : Transcript sub.sizes} {k : ℕ} {lg : QueryLog SigningSpec} {c : ℕ}
    (hI : Inv B T k lg c) (hk : k < LIFETIME) (m : Message)
    (r : Option SphincsSecurity.Signature) (calls : ℕ) :
    Inv B (recordVC T m (r.map B.sigCodec.symm) calls) (k + 1) (lg ++ [⟨B.msgOf m, r⟩])
      (c + calls) := by
  obtain ⟨hc, hs, hlen, -, hent⟩ := hI
  refine ⟨by simp [recordVC, hc], by simp [recordVC, hs], by simp [hlen], hk, ?_⟩
  intro e he σ hσ
  rw [List.mem_append] at he
  rcases he with he | he
  · obtain ⟨mo, hmo, hmem⟩ := hent e he σ hσ
    refine ⟨mo, hmo, ?_⟩
    cases r <;> simp [recordVC, hmem]
  · rw [List.mem_singleton] at he
    subst he
    refine ⟨m, rfl, ?_⟩
    change r = some σ at hσ
    subst hσ
    simp [recordVC]

variable (B) (A : Adversary sub.sizes)

theorem rel_main {sk : SecretKey} {pk : SphincsSecurity.PublicKey}
    {sk' : SphincsSecurity.Seeded.SecretKey}
    (hkey : (pk, sk') ∈ support (aKeygen (B.seedOf sk))) :
    ∀ (n : ℕ) (s : A.State) (T : Transcript sub.sizes) (k : ℕ) (lg : QueryLog SigningSpec) (c : ℕ),
      Inv B T k lg c → Rel (orgK B A sk pk n s T) (absK B A sk' pk n s k lg c) RFin := by
  intro n
  induction n with
  | zero =>
    intro s T k lg c _
    rw [orgK_zero]
    exact Rel.pure_left _ _ (rfin_false _)
  | succ n ih =>
    intro s T k lg c hI
    cases hstep : A.step s with
    | submit f =>
      cases f with
      | witness m w =>
        rw [orgK_submit_witness B hkey hstep, absK_submit_witness hstep, countFrom_shift,
          liftM_map, liftM_map, Functor.map_map]
        unfold countCalls
        refine Rel.of_map _ _ _ fun z => ?_
        intro hwon
        simp only [Bool.and_eq_true] at hwon
        refine ⟨?_, ?_⟩
        · simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨valid_of_inv hI, not_contains_witness hI _ hwon.2⟩, hwon.1⟩
        · simp [hI.1]
      | signature m σ =>
        rw [orgK_submit_signature B hkey hstep, absK_submit_signature hstep, countFrom_shift,
          liftM_map, liftM_map, Functor.map_map]
        unfold countCalls
        refine Rel.of_map _ _ _ fun z => ?_
        intro hwon
        simp only [Bool.and_eq_true] at hwon
        refine ⟨?_, ?_⟩
        · simp only [Bool.and_eq_true, decide_eq_true_eq]
          exact ⟨⟨valid_of_inv hI, not_contains_signature hI hwon.2⟩, hwon.1⟩
        · simp [hI.1]
    | hash y resume =>
      rw [orgK_hash B hstep, absK_hash hstep]
      refine Rel.bind_eq _ fun a => ih _ _ _ _ _ ?_
      obtain ⟨hc, hs, hlen, hk, hent⟩ := hI
      exact ⟨by simp [hc], hs, hlen, hk, hent⟩
    | sample m resume =>
      rw [orgK_sample B hstep, absK_sample hstep]
      exact Rel.bind_eq _ fun a => ih _ _ _ _ _ hI
    | step next =>
      rw [orgK_step B hstep, absK_step hstep]
      exact ih _ _ _ _ _ hI
    | sign req resume =>
      by_cases hk : T.signingRequests < LIFETIME
      · have hk' : k < LIFETIME := hI.2.1 ▸ hk
        rw [orgK_sign_lt B hkey hstep hk, absK_sign_lt hstep hk', countFrom_shift, liftM_map,
          bind_map_left]
        unfold countCalls
        refine Rel.bind_eq _ fun p => ih _ _ _ _ _ ?_
        exact inv_record hI hk' req.message p.1 p.2
      · rw [orgK_sign_ge B hstep hk]
        exact Rel.pure_left _ _ (rfin_false _)

lemma mem_support_liftM_countFrom {α : Type} {X : OracleComp AHash α} {a : α × ℕ}
    (ha : a ∈ support (liftM (countFrom (fun _ => 1) X 0) : OracleComp AW _)) : a.1 ∈ support X := by
  have h1 : a ∈ support (countFrom (fun _ => 1) X 0) := by
    rw [← liftComp_eq_liftM, support_liftComp] at ha
    exact ha
  rw [← fst_map_countFrom (fun _ => 1) X 0, support_map]
  exact ⟨a, h1, rfl⟩

lemma probEvent_bind_le {α β γ : Type} (mx : ProbComp α) {f : α → ProbComp β}
    {g : α → ProbComp γ} {E₁ : β → Prop} {E₂ : γ → Prop}
    (h : ∀ x, Pr[E₁ | f x] ≤ Pr[E₂ | g x]) : Pr[E₁ | mx >>= f] ≤ Pr[E₂ | mx >>= g] := by
  rw [probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  exact ENNReal.tsum_le_tsum fun x => by gcongr; exact h x

lemma seed_swap {β : Type} (G : SphincsSecurity.MasterSeed → ProbComp β) (E : β → Prop) :
    Pr[E | sampleSecretKey >>= fun sk => G (B.seedOf sk)] =
      Pr[E | SphincsSecurity.sampleMasterSeed >>= G] := by
  rw [← bind_map_left B.seedOf, probEvent_bind_eq_tsum, probEvent_bind_eq_tsum]
  simp only [B.seedOf_dist]

/-- The key inequality: the organizer's event is dominated by the abstract event for the
reduction. -/
theorem probEvent_le (rounds Q : ℕ) :
    Pr[fun r => r.won = true ∧ r.hashCalls ≤ Q | sub.securityExperiment A rounds] ≤
      Pr[fun r => r.1 = true ∧ r.2 ≤ Q |
        SphincsSecurity.Security.experiment (reduction B A rounds)] := by
  have hR : Pr[fun b : Bool × ℕ => b.1 = true ∧ b.2 ≤ Q |
      (simulateQ (roImpl (List UInt8) (BitVec 256))
        (countFrom costW (aGameCore (reduction B A rounds)) 0)).run' ∅] =
      Pr[fun r => r.1 = true ∧ r.2 ≤ Q |
        SphincsSecurity.Security.experiment (reduction B A rounds)] := by
    rw [experiment_eq, probEvent_countFrom_eq]
    rfl
  rw [← hR, securityExperiment_eq B A rounds, abs_top]
  unfold orgGame
  rw [simulateQ_bind, simulateQ_bind, roSim.run'_liftM_bind, roSim.run'_liftM_bind]
  calc _ ≤ Pr[fun b : Bool × ℕ => b.1 = true ∧ b.2 ≤ Q |
        sampleSecretKey >>= fun sk => (simulateQ (roImpl (List UInt8) (BitVec 256))
          ((liftM (countFrom (fun _ => 1) (aKeygen (B.seedOf sk)) 0) : OracleComp AW _) >>= fun p =>
            absK B A p.1.2 p.1.1 rounds (A.initial (B.pkEnc p.1.1) (B.cacheOf p.1.1)) 0 [] p.2)).run'
            ∅] := by
        refine probEvent_bind_le _ fun sk => ?_
        refine Rel.probEvent_le (R := RFin) (roImpl (List UInt8) (BitVec 256)) ?_ _ _ ?_ ∅
        · refine Rel.bind_eq_of_support _ fun a ha => ?_
          have hkey : (a.1.1, a.1.2) ∈ support (aKeygen (B.seedOf sk)) :=
            mem_support_liftM_countFrom ha
          exact rel_main B A hkey rounds _ _ 0 [] a.2
            ⟨rfl, rfl, rfl, Nat.zero_le _, by simp⟩
        · intro r b hR hE
          obtain ⟨h1, h2⟩ := hR hE.1
          exact ⟨h1, h2 ▸ hE.2⟩
    _ = _ := seed_swap B (fun seed => (simulateQ (roImpl (List UInt8) (BitVec 256))
          ((liftM (countFrom (fun _ => 1) (aKeygen seed) 0) : OracleComp AW _) >>= fun p =>
            absK B A p.1.2 p.1.1 rounds (A.initial (B.pkEnc p.1.1) (B.cacheOf p.1.1)) 0 [] p.2)).run'
            ∅) _

/-- **The security bridge.** A submission satisfying the bridge assumptions — in particular the
abstract event-form 127-bit security of the scheme it implements — is organizer-secure. -/
theorem Assumptions.secure (B : Assumptions sub) : sub.Secure := by
  intro A rounds Q hQ
  calc _ ≤ _ := probEvent_le B A rounds Q
    _ ≤ (Q : ℝ≥0∞) / 2 ^ 127 := B.security Q hQ _
    _ = (Q : ℝ≥0∞) / 2 ^ SECURITY_BITS := rfl

end SigGolfCandidate.Bridge

/-- info: 'SigGolfCandidate.Bridge.Assumptions.secure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms SigGolfCandidate.Bridge.Assumptions.secure
