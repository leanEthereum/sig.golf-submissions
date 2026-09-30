import SigGolfCandidate.Budget.Counting

/-!
# Budget: the two searches

Under the lazy random oracle each trial of a search queries fresh inputs, so it succeeds with a
fixed probability (up to randomizer collisions for the digest search). If one trial costs `w`
(as a factor `w = z ^ blocks`) and fails with probability at most `ρ`, a bound `b ≥ 1` with
`w * (ρ * b + (1 - ρ)) ≤ b` bounds the whole search (`V_searchCounter`, `V_searchDigest`): this is
the geometric bound `E[w^N] ≤ (1-ρ) w / (1 - ρ w)` by induction on the fuel.
-/

namespace SigGolfCandidate.Budget
open SigGolf SigGolfCandidate.Ref OracleComp OracleSpec ENNReal OracleComp.EvalDist

theorem hash16_bind_eq {β : Type} (x : List Byte) (f : Val → OracleComp HashSpec β) :
    Ref.hash16 x >>= f = qry (pad64 x) >>= fun a => f (answerBytes 16 a) := by
  simp only [Ref.hash16, Ref.H, bind_assoc, pure_bind]

theorem digest_bind_eq {β : Type} (rho m : List Byte) (f : Nat → OracleComp HashSpec β) :
    digest rho m >>= f = qry (pad64 (digestInput rho m)) >>= fun a => f (a.toNat % 2 ^ 184) := by
  simp only [digest, Ref.H, bind_assoc, pure_bind]

/-- Averaging a function bounded by a two-valued one. -/
theorem ev_ite_le (P : BitVec 256 → Prop) [DecidablePred P] (x y : ℝ≥0∞)
    (g : BitVec 256 → ℝ≥0∞) (hg : ∀ u, g u ≤ if P u then x else y) :
    expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256)) g ≤
      Pr[P | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] * x +
        Pr[fun u => ¬ P u | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] * y := by
  calc expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256)) g
      ≤ expectedValue ($ᵗ BitVec 256 : ProbComp (BitVec 256))
          (fun u => (if P u then 1 else 0) * x + (if ¬ P u then 1 else 0) * y) :=
        expectedValue_mono _ fun u => (hg u).trans (by by_cases h : P u <;> simp [h])
    _ = _ := by
        rw [expectedValue_add, expectedValue_mul_const, expectedValue_mul_const,
          expectedValue_ite_one, expectedValue_ite_one]

theorem probEvent_not_uniform (P : BitVec 256 → Prop) [DecidablePred P] :
    Pr[fun u => ¬ P u | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] =
      1 - Pr[P | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] := by
  have hc := probEvent_compl ($ᵗ BitVec 256 : ProbComp (BitVec 256)) P
  have hfail : Pr[⊥ | ($ᵗ BitVec 256 : ProbComp (BitVec 256))] = 0 := by simp
  rw [hfail, tsub_zero] at hc
  exact ENNReal.eq_sub_of_add_eq probEvent_ne_top ((add_comm _ _).trans hc)

/-! ## Counter search -/

theorem enc_inj (lay tau e : Nat) (M : Val) {c c' : Nat} (hc : c < 2 ^ 32) (hc' : c' < 2 ^ 32)
    (h : pad64 (encInput lay tau e M c) = pad64 (encInput lay tau e M c')) : c = c' := by
  have h2 := pad64_inj (by simp [encInput]) h
  simp only [encInput, thInput, List.append_assoc, List.append_cancel_left_eq] at h2
  exact le32_inj hc hc' h2

/-- The rejection probability of one fresh encoding. -/
noncomputable def rhoC : ℝ≥0∞ :=
  Pr[fun u : BitVec 256 => decodeDigits (answerBytes 16 u) = none |
    ($ᵗ BitVec 256 : ProbComp (BitVec 256))]

theorem V_searchCounter (z b : ℝ≥0∞) (hz : 1 ≤ z) (hb : 1 ≤ b)
    (hstep : z * (rhoC * b + (1 - rhoC)) ≤ b)
    (lay tau e : Nat) (M : Val) (hM : M.length ≤ 16) :
    ∀ fuel c (cache : RCache), c + fuel ≤ 2 ^ 32 →
      (∀ c', c ≤ c' → c' < 2 ^ 32 → cache (pad64 (encInput lay tau e M c')) = none) →
      V z (searchCounter lay tau e M c fuel) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero => intro c cache _ _; simp [searchCounter, hb]
  | succ n ih =>
    intro c cache hbound hfresh
    unfold searchCounter
    rw [hash16_bind_eq, V_query,
      expectedValue_ro_fresh _ _ (hfresh c le_rfl (by omega))]
    have hbl : (pad64 (encInput lay tau e M c)).blocks ≤ 1 :=
      blocks_pad64_le _ 1 (by simp [encInput]; omega) le_rfl
    have hz1 : z ^ (pad64 (encInput lay tau e M c)).blocks ≤ z := by
      calc z ^ (pad64 (encInput lay tau e M c)).blocks ≤ z ^ 1 := pow_le_pow_right₀ hz hbl
        _ = z := pow_one z
    refine le_trans (mul_le_mul' hz1 (ev_ite_le
      (fun u => decodeDigits (answerBytes 16 u) = none) b 1 _ fun u => ?_)) ?_
    · dsimp only
      cases hd : decodeDigits (answerBytes 16 u) with
      | some x => simp
      | none =>
        simp only [if_true]
        refine ih (c + 1) _ (by omega) fun c' hc' hc'b => ?_
        rw [QueryCache.cacheQuery_of_ne]
        · exact hfresh c' (by omega) hc'b
        · intro heq
          have := enc_inj lay tau e M hc'b (by omega) heq
          omega
    · rw [probEvent_not_uniform, mul_one]
      exact hstep

/-! ## Digest search -/

theorem rnd_inj (S m : List Byte) {a a' : Nat} (ha : a < 2 ^ 32) (ha' : a' < 2 ^ 32)
    (h : pad64 (rndInput S m a) = pad64 (rndInput S m a')) : a = a' := by
  have h2 := pad64_inj (by simp [rndInput]) h
  simp only [rndInput, thInput] at h2
  have h3 := List.append_inj_left' (List.append_inj_left' h2 rfl) (by simp)
  exact tweak_p_inj ha ha' h3

theorem rnd_ne_dig (S m rho m' : List Byte) (a : Nat) :
    pad64 (rndInput S m a) ≠ pad64 (digestInput rho m') := by
  intro h
  have := congrArg (fun q => qbyte q 1) h
  simp only [rndInput, digestInput, qbyte_tag] at this
  omega

theorem dig_inj (m : List Byte) {rho rho' : List Byte} (hr : rho.length = 16)
    (hr' : rho'.length = 16)
    (h : pad64 (digestInput rho m) = pad64 (digestInput rho' m)) : rho = rho' := by
  have h2 := pad64_inj (by simp [digestInput, hr, hr']) h
  simp only [digestInput, thInput, List.append_assoc, List.append_cancel_left_eq] at h2
  exact List.append_inj_left' h2 rfl

/-- The rejection probability of one fresh digest. -/
noncomputable def rhoD : ℝ≥0∞ :=
  Pr[fun u : BitVec 256 => ¬ admissible (u.toNat % 2 ^ 184) = true |
    ($ᵗ BitVec 256 : ProbComp (BitVec 256))]

/-- The collision allowance per digest trial (at most `2^20` earlier randomizers). -/
noncomputable def epsD : ℝ≥0∞ := (2 : ℝ≥0∞) ^ 20 / 2 ^ 128

theorem V_searchDigest (z b : ℝ≥0∞) (hz : 1 ≤ z) (hb : 1 ≤ b)
    (hstep : z ^ 4 * ((epsD + rhoD) * b + (1 - rhoD)) ≤ b)
    (S m : List Byte) (hS : S.length = 32) (hm : m.length = 32) :
    ∀ fuel a (cache : RCache) (R : Finset Val), a + fuel ≤ 2 ^ 20 → R.card ≤ a →
      (∀ a', a ≤ a' → a' < 2 ^ 32 → cache (pad64 (rndInput S m a')) = none) →
      (∀ rho, rho.length = 16 → rho ∉ R → cache (pad64 (digestInput rho m)) = none) →
      V z (searchDigest S m a fuel) cache ≤ b := by
  intro fuel
  induction fuel with
  | zero => intro a cache R _ _ _ _; simp [searchDigest, hb]
  | succ n ih =>
    intro a cache R hbound hcard hrnd hdig
    unfold searchDigest
    rw [hash16_bind_eq, V_query, expectedValue_ro_fresh _ _ (hrnd a le_rfl (by omega))]
    obtain ⟨-, hb1⟩ := rnd_ok S m hS hm a
    have hz2 : ∀ q : Query, q.blocks ≤ 2 → z ^ q.blocks ≤ z ^ 2 := fun q hq =>
      pow_le_pow_right₀ hz hq
    -- the continuation after the randomizer `u`
    have hcont : ∀ u : BitVec 256,
        V z (digest (answerBytes 16 u) m >>= fun N =>
            if admissible N = true then pure (some (answerBytes 16 u, N))
            else searchDigest S m (a + 1) n)
          ((cache.cacheQuery (pad64 (rndInput S m a)) u)) ≤
        if answerBytes 16 u ∈ R then z ^ 2 * b else z ^ 2 * (rhoD * b + (1 - rhoD)) := by
      intro u
      set rho := answerBytes 16 u with hrho_def
      have hrho : rho.length = 16 := by simp [rho]
      have hc1rnd : ∀ a', a + 1 ≤ a' → a' < 2 ^ 32 → (cache.cacheQuery (pad64 (rndInput S m a)) u) (pad64 (rndInput S m a')) = none := by
        intro a' ha' ha'b
        rw [QueryCache.cacheQuery_of_ne]
        · exact hrnd a' (by omega) ha'b
        · intro h; have := rnd_inj S m ha'b (by omega) h; omega
      have hc1dig : ∀ rho', (cache.cacheQuery (pad64 (rndInput S m a)) u) (pad64 (digestInput rho' m)) = cache (pad64 (digestInput rho' m)) :=
        fun rho' => QueryCache.cacheQuery_of_ne _ _ fun h => rnd_ne_dig S m rho' m a h.symm
      obtain ⟨-, hb2⟩ := dig_ok rho m hrho hm
      rw [digest_bind_eq, V_query]
      -- after the digest query: continuation bound from any state keeping the invariants
      have hk : ∀ (R' : Finset Val) (c2 : RCache), R'.card ≤ a + 1 →
          (∀ a', a + 1 ≤ a' → a' < 2 ^ 32 → c2 (pad64 (rndInput S m a')) = none) →
          (∀ rho', rho'.length = 16 → rho' ∉ R' → c2 (pad64 (digestInput rho' m)) = none) →
          ∀ v : BitVec 256,
          V z (if admissible (v.toNat % 2 ^ 184) = true then
              pure (some (rho, v.toNat % 2 ^ 184)) else searchDigest S m (a + 1) n) c2 ≤
            if admissible (v.toNat % 2 ^ 184) = true then 1 else b := by
        intro R' c2 hR' h1 h2 v
        split
        · simp
        · exact ih (a + 1) c2 R' (by omega) hR' h1 h2
      by_cases hmem : rho ∈ R
      · rw [if_pos hmem]
        refine mul_le_mul' (hz2 _ hb2) ?_
        refine expectedValue_le_of_support fun y hy => ?_
        refine (hk R y.2 (by omega) ?_ ?_ y.1).trans (by split <;> simp [hb])
        · rcases mem_support_ro _ _ y hy with ⟨_, h⟩ | ⟨_, h⟩
          · rw [h]; exact hc1rnd
          · rw [h]; intro a' ha' ha'b
            try dsimp only
            rw [QueryCache.cacheQuery_of_ne _ _ (fun h' => rnd_ne_dig S m rho m a' h')]
            exact hc1rnd a' ha' ha'b
        · rcases mem_support_ro _ _ y hy with ⟨_, h⟩ | ⟨_, h⟩
          · rw [h]; intro rho' hl hn; rw [hc1dig]; exact hdig rho' hl hn
          · rw [h]; intro rho' hl hn
            rw [QueryCache.cacheQuery_of_ne _ _ (fun h' => hn (dig_inj m hl hrho h' ▸ hmem)),
              hc1dig]
            exact hdig rho' hl hn
      · rw [if_neg hmem]
        have hfresh : (cache.cacheQuery (pad64 (rndInput S m a)) u) (pad64 (digestInput rho m)) = none := by
          rw [hc1dig]; exact hdig rho hrho hmem
        rw [expectedValue_ro_fresh _ _ hfresh]
        refine mul_le_mul' (hz2 _ hb2) ?_
        refine (ev_ite_le (fun v : BitVec 256 => ¬ admissible (v.toNat % 2 ^ 184) = true) b 1 _
          fun v => ?_).trans ?_
        · refine (hk (insert rho R) _ ((Finset.card_insert_le _ _).trans (by omega)) ?_ ?_ v).trans
            (by split <;> simp_all)
          · intro a' ha' ha'b
            try dsimp only
            rw [QueryCache.cacheQuery_of_ne _ _ (fun h' => rnd_ne_dig S m rho m a' h')]
            exact hc1rnd a' ha' ha'b
          · intro rho' hl hn
            rw [Finset.mem_insert, not_or] at hn
            dsimp only
            rw [QueryCache.cacheQuery_of_ne _ _ (fun h' => hn.1 (dig_inj m hl hrho h')), hc1dig]
            exact hdig rho' hl hn.2
        · rw [probEvent_not_uniform (fun v : BitVec 256 => ¬ admissible (v.toNat % 2 ^ 184) = true),
            mul_one]
          exact le_rfl
    -- average over the randomizer
    refine le_trans (mul_le_mul' (hz2 _ hb1) (ev_ite_le (fun u => answerBytes 16 u ∈ R) _ _ _
      hcont)) ?_
    have hcoll : Pr[fun u : BitVec 256 => answerBytes 16 u ∈ R |
        ($ᵗ BitVec 256 : ProbComp (BitVec 256))] ≤ epsD := by
      refine (probEvent_answerBytes_mem_le R).trans ?_
      unfold epsD
      gcongr
      exact_mod_cast (show R.card ≤ 2 ^ 20 by omega)
    calc z ^ 2 * (Pr[fun u : BitVec 256 => answerBytes 16 u ∈ R |
            ($ᵗ BitVec 256 : ProbComp (BitVec 256))] * (z ^ 2 * b) +
          Pr[fun u : BitVec 256 => ¬ answerBytes 16 u ∈ R |
            ($ᵗ BitVec 256 : ProbComp (BitVec 256))] * (z ^ 2 * (rhoD * b + (1 - rhoD))))
        ≤ z ^ 2 * (epsD * (z ^ 2 * b) + 1 * (z ^ 2 * (rhoD * b + (1 - rhoD)))) := by
          gcongr; exact probEvent_le_one
      _ = z ^ 4 * ((epsD + rhoD) * b + (1 - rhoD)) := by ring
      _ ≤ b := hstep

end SigGolfCandidate.Budget
