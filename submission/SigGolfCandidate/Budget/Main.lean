import SigGolfCandidate.Budget.Numeric
import SigGolfCandidate.Submission

/-!
# Budget: `Submission.CompressionBounds` from refinement hypotheses

`compressionBounds_of_refinement`: any submission whose programs have the compressions of the
reference spec satisfies the organizer's `CompressionBounds`. The hypotheses are about the
`OracleComp`s of the programs (their query trees), mapped to what is needed:

* keygen: `(value, hashCompressions)` is `countBlocks (keygenRef sk)` with the value some function
  `G` of the public key;
* sign: `hashCompressions` is `countBlocks (signRef sk m)`'s count, for every cache input;
* expand: `hashCompressions` is `0`.

These follow from bytecode refinement theorems of the form
`(fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run phase input = ...` by
mapping (`Functor.map_map`).
-/

namespace SigGolfCandidate.Budget
open SigGolf SigGolfCandidate.Ref OracleComp OracleSpec ENNReal OracleComp.EvalDist

/-! ## `honest`, split after each phase -/

section Tails
variable (sub : Submission)

def tailE (m : Message) (pk : PublicKey) (costs : Phase → Nat)
    (expand : RunResult (Output sub.sizes .expand)) : OracleComp HashSpec HonestResult :=
  let costs := recordCost costs .expand expand.hashCompressions
  match expand.value with
  | some witness => do
    let verify ← sub.run .verify (m, pk, witness)
    let costs := recordCost costs .verify verify.hashCompressions
    pure ⟨verify.value.isSome, costs, verify.cycles + witnessCycles sub.sizes.witness⟩
  | _ => pure { success := false, costs := costs, verificationCycles := 0 }

def tailS (m : Message) (pk : PublicKey) (costs : Phase → Nat)
    (sign : RunResult (Output sub.sizes .sign)) : OracleComp HashSpec HonestResult :=
  let costs := recordCost costs .sign sign.hashCompressions
  match sign.value with
  | some signature => do
    let expand ← sub.run .expand (m, pk, signature)
    tailE sub m pk costs expand
  | _ => pure { success := false, costs := costs, verificationCycles := 0 }

def tailK (sk : SecretKey) (m : Message) (keygen : RunResult (Output sub.sizes .keygen)) :
    OracleComp HashSpec HonestResult :=
  let costs := recordCost (fun _ => 0) .keygen keygen.hashCompressions
  match keygen.value with
  | some (pk, cache) => do
    let sign ← sub.run .sign (sk, cache, m)
    tailS sub m pk costs sign
  | _ => pure { success := false, costs := costs, verificationCycles := 0 }

theorem honest_eq (sk : SecretKey) (m : Message) :
    sub.honest sk m = sub.run .keygen sk >>= tailK sub sk m := rfl

theorem tailE_costs (m : Message) (pk : PublicKey) (costs : Phase → Nat)
    (e : RunResult (Output sub.sizes .expand)) :
    ∀ r ∈ support (tailE sub m pk costs e), ∀ ph, ph ≠ .verify →
      r.costs ph = recordCost costs .expand e.hashCompressions ph := by
  intro r hr ph hph
  unfold tailE at hr
  split at hr
  · rw [mem_support_bind_iff] at hr
    obtain ⟨v, -, hr⟩ := hr
    rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr
    simp [recordCost, hph]
  · rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl

theorem tailS_costs (m : Message) (pk : PublicKey) (costs : Phase → Nat)
    (s : RunResult (Output sub.sizes .sign)) :
    ∀ r ∈ support (tailS sub m pk costs s), ∀ ph, ph ≠ .verify → ph ≠ .expand →
      r.costs ph = recordCost costs .sign s.hashCompressions ph := by
  intro r hr ph hph hph'
  unfold tailS at hr
  split at hr
  · rw [mem_support_bind_iff] at hr
    obtain ⟨e, -, hr⟩ := hr
    rw [tailE_costs sub m pk _ e r hr ph hph]
    simp [recordCost, hph']
  · rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr; rfl

theorem tailK_costs (sk : SecretKey) (m : Message) (k : RunResult (Output sub.sizes .keygen)) :
    ∀ r ∈ support (tailK sub sk m k), r.costs .keygen = k.hashCompressions := by
  intro r hr
  unfold tailK at hr
  split at hr
  · rw [mem_support_bind_iff] at hr
    obtain ⟨s, -, hr⟩ := hr
    rw [tailS_costs sub m _ _ s r hr .keygen (by decide) (by decide)]
    simp [recordCost]
  · rw [support_pure, Set.mem_singleton_iff] at hr
    subst hr; simp [recordCost]

end Tails

/-! ## Expectations over the random oracle -/

theorem ev_withRandomOracle {α : Type} (oa : OracleComp HashSpec α) (f : α → ℝ≥0∞) :
    expectedValue (withRandomOracle oa) f = expectedValue (roRun oa ∅) (fun x => f x.1) := by
  unfold withRandomOracle roRun
  rw [StateT.run'_eq, expectedValue_map]

theorem ev_roRun_le_of_support {α : Type} (oa : OracleComp HashSpec α) (c : RCache)
    (g : α → ℝ≥0∞) (v : ℝ≥0∞) (h : ∀ r ∈ support oa, g r ≤ v) :
    expectedValue (roRun oa c) (fun x => g x.1) ≤ v := by
  refine expectedValue_le_of_support fun x hx => h _ ?_
  apply support_simulateQ_run'_subset randomOracle oa c
  rw [StateT.run'_eq, support_map]
  exact ⟨x, hx, rfl⟩

/-- The expectation of `z ^ n` over a count computation is `V`. -/
theorem ev_count_eq_V {α : Type} (z : ℝ≥0∞) (oa : OracleComp HashSpec α) (c : RCache) :
    expectedValue (roRun (Prod.snd <$> countBlocks oa) c) (fun x => z ^ x.1) = V z oa c := by
  rw [roRun_map, expectedValue_map]; rfl

/-- The organizer's cost functional is `zOf budget ^ cost`. -/
theorem costFun_eq (n B : Nat) :
    ENNReal.ofReal (Real.rpow 2 ((n : ℝ) / (B : ℝ))) = zOf B ^ n := by
  rw [zOf_pow, Real.rpow_eq_pow]

theorem ofReal_rpow_zero (B : Nat) : ENNReal.ofReal (Real.rpow 2 ((0 : Nat) / (B : ℝ))) = 1 := by
  simp [Real.rpow_eq_pow]

/-! ## The three phases -/

section Phases
variable (sub : Submission)

/-- The keygen refinement hypothesis (compressions and value). -/
def KeygenRefines : Prop :=
  ∀ sk, ∃ G : Bytes 16 → Option (Output sub.sizes .keygen),
    (fun r => (r.value, r.hashCompressions)) <$> sub.run .keygen sk =
      (fun p => (G p.1, p.2)) <$> countBlocks (keygenRef sk)

/-- The sign refinement hypothesis (compressions), for every cache input. -/
def SignRefines : Prop :=
  ∀ sk cache m, (fun r => r.hashCompressions) <$> sub.run .sign (sk, cache, m) =
    Prod.snd <$> countBlocks (signRef sk m)

/-- Expand makes no hash calls. -/
def ExpandNoHash : Prop :=
  ∀ input, (fun r => r.hashCompressions) <$> sub.run .expand input = pure 0

theorem keygen_count (hK : KeygenRefines sub) (sk : SecretKey) :
    (fun r => r.hashCompressions) <$> sub.run .keygen sk = Prod.snd <$> countBlocks (keygenRef sk) := by
  obtain ⟨G, hG⟩ := hK sk
  have h := congrArg (fun oa => Prod.snd <$> oa) hG
  simp only [Functor.map_map] at h
  exact h

/-- States after keygen satisfy sign's cache invariant. -/
theorem keygen_cacheInv (hK : KeygenRefines sub) (sk : SecretKey)
    (x : RunResult (Output sub.sizes .keygen) × RCache)
    (hx : x ∈ support (roRun (sub.run .keygen sk) ∅)) : CacheInv Inv0 x.2 := by
  obtain ⟨G, hG⟩ := hK sk
  have h1 : ((x.1.value, x.1.hashCompressions), x.2) ∈
      support (roRun ((fun r => (r.value, r.hashCompressions)) <$> sub.run .keygen sk) ∅) := by
    rw [roRun_map, support_map]; exact ⟨x, hx, rfl⟩
  rw [hG, roRun_map, support_map] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  have hy' := mem_support_roRun_of_count _ _ _ y hy
  have := (spec_keygenRef sk).support (I := Inv0)
    (fun q hq => by unfold PT at hq; unfold Inv0; omega) ∅ (fun q u h => by simp at h) _ hy'
  have h2 : x.2 = y.2 := (congrArg Prod.snd hyx).symm
  rw [h2]; exact this.2

theorem keygen_bound (hK : KeygenRefines sub) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ)))) ≤ 2 := by
  rw [ev_withRandomOracle, honest_eq, roRun_bind, expectedValue_bind]
  calc expectedValue (roRun (sub.run .keygen sk) ∅) (fun x =>
        expectedValue (roRun (tailK sub sk m x.1) x.2) (fun y => ENNReal.ofReal
          (Real.rpow 2 ((y.1.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ)))))
      ≤ expectedValue (roRun (sub.run .keygen sk) ∅)
          (fun x => zOf (2 ^ 20) ^ x.1.hashCompressions) := by
        refine expectedValue_mono _ fun x => ?_
        apply ev_roRun_le_of_support (tailK sub sk m x.1) x.2 (fun r => ENNReal.ofReal
          (Real.rpow 2 ((r.costs .keygen : ℝ) / (Phase.keygen.budget : ℝ))))
        intro r hr
        rw [tailK_costs sub sk m x.1 r hr, show Phase.keygen.budget = 2 ^ 20 from rfl, costFun_eq]
    _ = V (zOf (2 ^ 20)) (keygenRef sk) ∅ := by
        rw [← ev_count_eq_V, ← keygen_count sub hK sk, roRun_map, expectedValue_map]
    _ ≤ 2 := V_keygenRef_le_two sk ∅

theorem sign_bound (hK : KeygenRefines sub) (hS : SignRefines sub) (sk : SecretKey)
    (m : Message) :
    expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .sign : ℝ) / (Phase.sign.budget : ℝ)))) ≤ 2 := by
  rw [ev_withRandomOracle, honest_eq, roRun_bind, expectedValue_bind]
  refine expectedValue_le_of_support fun x hx => ?_
  have hinv := keygen_cacheInv sub hK sk x hx
  obtain ⟨k, c⟩ := x
  dsimp only at hinv ⊢
  unfold tailK
  split
  · next pk cache _ =>
    rw [roRun_bind, expectedValue_bind]
    calc expectedValue (roRun (sub.run .sign (sk, cache, m)) c) (fun y =>
          expectedValue (roRun (tailS sub m pk _ y.1) y.2) (fun w => ENNReal.ofReal
            (Real.rpow 2 ((w.1.costs .sign : ℝ) / (Phase.sign.budget : ℝ)))))
        ≤ expectedValue (roRun (sub.run .sign (sk, cache, m)) c)
            (fun y => zOf (2 ^ 17) ^ y.1.hashCompressions) := by
          refine expectedValue_mono _ fun y => ?_
          apply ev_roRun_le_of_support (tailS sub m pk _ y.1) y.2 (fun r => ENNReal.ofReal
            (Real.rpow 2 ((r.costs .sign : ℝ) / (Phase.sign.budget : ℝ))))
          intro r hr
          rw [tailS_costs sub m pk _ y.1 r hr .sign (by decide) (by decide),
            show Phase.sign.budget = 2 ^ 17 from rfl]
          simp only [recordCost, if_true]
          rw [costFun_eq]
      _ = V (zOf (2 ^ 17)) (signRef sk m) c := by
          rw [← ev_count_eq_V, ← hS sk cache m, roRun_map, expectedValue_map]
      _ ≤ 2 := V_signRef_le_two sk m c hinv
  · simp only [roRun_pure, expectedValue_pure]
    simp only [recordCost, show Phase.sign ≠ Phase.keygen by decide, if_false]
    rw [ofReal_rpow_zero]; norm_num

theorem expand_bound (hE : ExpandNoHash sub) (sk : SecretKey) (m : Message) :
    expectedValue (withRandomOracle (sub.honest sk m)) (fun result => ENNReal.ofReal
      (Real.rpow 2 ((result.costs .expand : ℝ) / (Phase.expand.budget : ℝ)))) ≤ 2 := by
  refine le_trans ?_ (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
  rw [ev_withRandomOracle, honest_eq, roRun_bind, expectedValue_bind]
  refine expectedValue_le_of_support fun x _ => ?_
  obtain ⟨k, c⟩ := x
  dsimp only
  unfold tailK
  split
  · next pk cache _ =>
    rw [roRun_bind, expectedValue_bind]
    refine expectedValue_le_of_support fun y _ => ?_
    obtain ⟨s, c'⟩ := y
    dsimp only
    unfold tailS
    split
    · next sig _ =>
      rw [roRun_bind, expectedValue_bind]
      calc expectedValue (roRun (sub.run .expand (m, pk, sig)) c') (fun y =>
            expectedValue (roRun (tailE sub m pk _ y.1) y.2) (fun w => ENNReal.ofReal
              (Real.rpow 2 ((w.1.costs .expand : ℝ) / (Phase.expand.budget : ℝ)))))
          ≤ expectedValue (roRun (sub.run .expand (m, pk, sig)) c')
              (fun y => zOf (2 ^ 20) ^ y.1.hashCompressions) := by
            refine expectedValue_mono _ fun y => ?_
            apply ev_roRun_le_of_support (tailE sub m pk _ y.1) y.2 (fun r => ENNReal.ofReal
              (Real.rpow 2 ((r.costs .expand : ℝ) / (Phase.expand.budget : ℝ))))
            intro r hr
            rw [tailE_costs sub m pk _ y.1 r hr .expand (by decide),
              show Phase.expand.budget = 2 ^ 20 from rfl]
            simp only [recordCost, if_true]
            rw [costFun_eq]
        _ = expectedValue (roRun ((fun r => r.hashCompressions) <$> sub.run .expand (m, pk, sig)) c')
              (fun y => zOf (2 ^ 20) ^ y.1) := by
            rw [roRun_map, expectedValue_map]
        _ ≤ 1 := by
            have h := hE (m, pk, sig)
            erw [h]
            rw [roRun_pure, expectedValue_pure]; simp
    · simp only [roRun_pure, expectedValue_pure]
      simp only [recordCost, show Phase.expand ≠ Phase.sign by decide,
        show Phase.expand ≠ Phase.keygen by decide, if_false]
      rw [ofReal_rpow_zero]
  · simp only [roRun_pure, expectedValue_pure]
    simp only [recordCost, show Phase.expand ≠ Phase.keygen by decide, if_false]
    rw [ofReal_rpow_zero]

/-- **Compression bounds** for any submission refining the reference spec. -/
theorem compressionBounds_of_refinement (hK : KeygenRefines sub) (hS : SignRefines sub)
    (hE : ExpandNoHash sub) : sub.CompressionBounds := by
  intro sk phase hphase
  unfold Submission.honestWorkload
  refine expectedValue_bind_le_of_le fun m => ?_
  simp only [Phase.budgeted, List.mem_cons, List.not_mem_nil, or_false] at hphase
  rcases hphase with rfl | rfl | rfl
  · exact keygen_bound sub hK sk m
  · exact sign_bound sub hK hS sk m
  · exact expand_bound sub hE sk m

end Phases

/-- The competition statement for `SigGolfCandidate.submission`, modulo the refinement facts. -/
theorem submission_compressionBounds (hK : KeygenRefines submission)
    (hS : SignRefines submission) (hE : ExpandNoHash submission) :
    submission.CompressionBounds :=
  compressionBounds_of_refinement submission hK hS hE

end SigGolfCandidate.Budget
