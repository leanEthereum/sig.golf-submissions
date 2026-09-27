import SigGolfCandidate.SphincsSecurity.Proof.Deterministic.GameExpansion
import SigGolfCandidate.SphincsSecurity.Proof.Reference.QueryBound

/-!
# Eliminating the cache MAC and the node masks

After the seed is erased, the experiment (`cachedTableGameAfterSecrets`) publishes the cache
`⟨macs region, region⟩` with `region = tableRegion top masks`, and answers a request `(m, cache)` by the
checked signer when `macs cache.region = cache.tag`. This file compares it with the ideal table game of
`simAdversary`, a message-only adversary that samples a mask table and a tag, publishes
`⟨tag, simRegion masks⟩`, forwards the requests carrying that cache as their message and fails every
other request (`simImpl`).

* Masks: `maskShift top` (XOR the zero-extended node table into the mask table) is an involution, so the
  mask table keeps its law, and it turns the published region into `simRegion masks`, independent of
  the tree (`tableRegion_maskShift`). The honest cache then unmasks to the node table on every node the
  top layer reads (`cachedTableSignChecked_eq_tableSign`).
* MAC: the uniform MAC table is `Function.update table region tag` for an independent uniform tag and
  table (`evalSPMF_uniformSample_bind_update`). The two signers agree on every request that is not
  `MacBad` (a cache off the published region whose tag matches the table there;
  `cachedTableSign_eq_modSign`), identical until bad (`countedRun_identical_until_bad`) for runs of at
  most `q_s = 2^32` requests, which are the only ones that can win; each of those requests is bad with
  probability `2^-256` (`probEvent_macBad_le`).
* Logs: the ideal log is the experiment's log restricted to the published cache (`simulated_run_eq`),
  so a winning experiment run wins the ideal game with the same hash count (`verdict_mono`).
-/

open OracleComp OracleSpec ENNReal

namespace SphincsSecurity.Seeded

set_option backward.isDefEq.respectTransparency false

open Concrete

/-- Run an experiment adversary against a logged request signer. -/
noncomputable def requestLoggedRun {α : Type} (impl : SigningRequest → OracleComp OracleWorld (Option Signature))
    (computation : OracleComp (OracleWorld + RequestSpec) α) : OracleComp OracleWorld (α × QueryLog RequestSpec) :=
  (simulateQ (QueryImpl.ofLift OracleWorld (WriterT (QueryLog RequestSpec) (OracleComp OracleWorld)) +
    QueryImpl.withLogging (fun request : SigningRequest => impl request)) computation).run

theorem loggedRun_pure {α : Type} (impl : SigningRequest → OracleComp OracleWorld (Option Signature)) (a : α) :
    requestLoggedRun impl (pure a) = pure (a, []) := rfl

theorem loggedRun_query_inl {α : Type} (impl : SigningRequest → OracleComp OracleWorld (Option Signature))
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp (OracleWorld + RequestSpec) α) :
    requestLoggedRun impl (liftM ((OracleWorld + RequestSpec).query (.inl input)) >>= next) =
      liftM (OracleWorld.query input) >>= fun answer => requestLoggedRun impl (next answer) := by
  unfold requestLoggedRun
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inl]
  simp only [QueryImpl.ofLift, WriterT.run_bind']
  change ((fun a => (a, ([] : QueryLog RequestSpec))) <$> (liftM (OracleWorld.query input) : OracleComp OracleWorld _)) >>= _ = _
  simp
  exact bind_congr fun _ => id_map _

theorem loggedRun_query_inr {α : Type} (impl : SigningRequest → OracleComp OracleWorld (Option Signature))
    (request : SigningRequest) (next : Option Signature → OracleComp (OracleWorld + RequestSpec) α) :
    requestLoggedRun impl (liftM ((OracleWorld + RequestSpec).query (.inr request)) >>= next) =
      impl request >>= fun answer =>
        (fun result => (result.1, ⟨request, answer⟩ :: result.2)) <$> requestLoggedRun impl (next answer) := by
  unfold requestLoggedRun
  rw [simulateQ_bind, simulateQ_spec_query, QueryImpl.add_apply_inr]
  simp

theorem cachedGameRest_eq (signer : TopCache → Message → OracleComp HashSpec (Option Signature))
    (adversary : Security.Adversary) (pk : PublicKey) (cache : TopCache) :
    cachedGameRest signer adversary pk cache =
      requestLoggedRun (fun request => liftM (signer request.cache request.message)) (adversary.main pk cache) >>= fun result =>
        (fun verified => decide (RequestTranscript.Valid result.2 ∧ ¬RequestTranscript.Contains result.2 result.1) && verified) <$>
          (liftM (Concrete.verify pk result.1.message result.1.signature : OracleComp HashSpec Bool) : OracleComp OracleWorld Bool) := by
  unfold cachedGameRest requestLoggedRun
  simp only [map_eq_bind_pure_comp]
  rfl


namespace MacElim

/-- The counted random-oracle run of a logged experiment adversary, with its final cache. -/
noncomputable def countedRun {α : Type} (impl : SigningRequest → OracleComp OracleWorld (Option Signature))
    (computation : OracleComp (OracleWorld + RequestSpec) α) (cache : QueryCache HashSpec) :
    ProbComp (((α × QueryLog RequestSpec) × Nat) × QueryCache HashSpec) :=
  (simulateQ romImpl (countHashQueries (requestLoggedRun impl computation))).run cache

theorem countedRun_pure {α : Type} (impl : SigningRequest → OracleComp OracleWorld (Option Signature)) (a : α)
    (cache : QueryCache HashSpec) : countedRun impl (pure a) cache = pure (((a, []), 0), cache) := by
  simp [countedRun, loggedRun_pure, countHashQueries_pure]

theorem countedRun_inl {α : Type} (impl : SigningRequest → OracleComp OracleWorld (Option Signature))
    (input : OracleWorld.Domain) (next : OracleWorld.Range input → OracleComp (OracleWorld + RequestSpec) α)
    (cache : QueryCache HashSpec) :
    countedRun impl (liftM ((OracleWorld + RequestSpec).query (.inl input)) >>= next) cache =
      (romImpl input).run cache >>= fun head =>
        (fun result => ((result.1.1, (if (fun input : OracleWorld.Domain => input matches .inr _) input then 1 else 0) +
          result.1.2), result.2)) <$> countedRun impl (next head.1) head.2 := by
  rw [countedRun, loggedRun_query_inl, countHashQueries_query_bind, simulateQ_bind, simulateQ_spec_query,
    StateT.run_bind]
  refine bind_congr fun head => ?_
  simp [countedRun]
  rfl

theorem countedRun_inr {α : Type} (impl : SigningRequest → OracleComp OracleWorld (Option Signature))
    (request : SigningRequest) (next : Option Signature → OracleComp (OracleWorld + RequestSpec) α)
    (cache : QueryCache HashSpec) :
    countedRun impl (liftM ((OracleWorld + RequestSpec).query (.inr request)) >>= next) cache =
      (simulateQ romImpl (countHashQueries (impl request))).run cache >>= fun head =>
        (fun result => (((result.1.1.1, ⟨request, head.1.1⟩ :: result.1.1.2), head.1.2 + result.1.2), result.2)) <$>
          countedRun impl (next head.1.1) head.2 := by
  rw [countedRun, loggedRun_query_inr, countHashQueries_bind, simulateQ_bind, StateT.run_bind]
  refine bind_congr fun head => ?_
  simp [countedRun, countHashQueries_map]


theorem probEvent_bind_le_add_bind {α β γ : Type} (mx : ProbComp α) (f g : α → ProbComp β) (h : α → ProbComp γ)
    (p : β → Prop) (q : γ → Prop) (hle : ∀ a ∈ support mx, Pr[p | f a] ≤ Pr[p | g a] + Pr[q | h a]) :
    Pr[p | mx >>= f] ≤ Pr[p | mx >>= g] + Pr[q | mx >>= h] := by
  simp only [probEvent_bind_eq_tsum]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases ha : a ∈ support mx
  · rw [← mul_add]
    exact mul_le_mul' le_rfl (hle a ha)
  · simp [probOutput_eq_zero_of_not_mem_support ha]

/-- Some request among the first `n` of a log is bad. -/
def BadIn (bad : SigningRequest → Prop) (n : Nat) (log : QueryLog RequestSpec) : Prop :=
  ∃ entry ∈ log.take n, bad entry.1

/-- Identical until bad: two request signers that agree on every request that is not bad give
the same law to every continuation that only scores runs with at most `n` requests, up to the
probability that one of the first `n` requests of the second run is bad. -/
theorem countedRun_identical_until_bad {α β : Type} (bad : SigningRequest → Prop)
    (impl₁ impl₂ : SigningRequest → OracleComp OracleWorld (Option Signature))
    (hagree : ∀ request, ¬bad request → impl₁ request = impl₂ request)
    (computation : OracleComp (OracleWorld + RequestSpec) α) :
    ∀ (n : Nat) (cache : QueryCache HashSpec)
      (cont : ((α × QueryLog RequestSpec) × Nat) × QueryCache HashSpec → ProbComp β) (event : β → Prop),
      (∀ x, n < x.1.1.2.length → Pr[event | cont x] = 0) →
      Pr[event | countedRun impl₁ computation cache >>= cont] ≤
        Pr[event | countedRun impl₂ computation cache >>= cont] +
          Pr[fun x => BadIn bad n x.1.1.2 | countedRun impl₂ computation cache] := by
  induction computation using OracleComp.inductionOn with
  | pure a =>
      intro n cache cont event _
      exact le_self_add
  | query_bind input next ih =>
      intro n cache cont event hlong
      cases input with
      | inl input =>
          rw [countedRun_inl, countedRun_inl, bind_assoc, bind_assoc]
          apply probEvent_bind_le_add_bind
          intro head _
          rw [bind_map_left, bind_map_left, probEvent_map]
          exact ih head.1 n head.2 _ event (fun x hx => hlong _ hx)
      | inr request =>
          by_cases hbad : bad request
          · cases n with
            | zero =>
                refine le_trans (le_of_eq ?_) (zero_le)
                rw [probEvent_eq_zero_iff]
                intro z hz
                rw [countedRun_inr, bind_assoc, mem_support_bind_iff] at hz
                obtain ⟨head, _, hz⟩ := hz
                rw [bind_map_left, mem_support_bind_iff] at hz
                obtain ⟨x, _, hz⟩ := hz
                have hzero := hlong (((x.1.1.1, ⟨request, head.1.1⟩ :: x.1.1.2), head.1.2 + x.1.2), x.2) (by simp)
                rw [probEvent_eq_zero_iff] at hzero
                exact hzero z hz
            | succ n =>
                have hone : Pr[fun x => BadIn bad (n + 1) x.1.1.2 |
                    countedRun impl₂ (liftM ((OracleWorld + RequestSpec).query (.inr request)) >>= next) cache] = 1 := by
                  rw [probEvent_eq_one_iff]
                  refine ⟨by simp, fun x hx => ?_⟩
                  rw [countedRun_inr, mem_support_bind_iff] at hx
                  obtain ⟨head, _, hx⟩ := hx
                  rw [support_map] at hx
                  obtain ⟨y, _, rfl⟩ := hx
                  exact ⟨⟨request, head.1.1⟩, by simp, hbad⟩
                exact probEvent_le_one.trans (hone.symm.le.trans le_add_self)
          · rw [countedRun_inr, countedRun_inr, hagree _ hbad, bind_assoc, bind_assoc]
            apply probEvent_bind_le_add_bind
            intro head _
            rw [bind_map_left, bind_map_left, probEvent_map]
            refine (ih head.1.1 (n - 1) head.2 _ event (fun x hx => hlong _ (by simp; omega))).trans
              (add_le_add le_rfl (probEvent_mono fun x _ hx => ?_))
            obtain ⟨entry, hentry, hbadEntry⟩ := hx
            cases n with
            | zero => simp at hentry
            | succ n =>
                simp only [Nat.add_sub_cancel] at hentry
                exact ⟨entry, by simp [hentry], hbadEntry⟩


/-! ## The top layer only reads the region -/

section Congruence

variable {m : Type → Type} [Monad m] [HasQuery HashSpec m]

/-- Two top-node getters that agree on every node of the cached region. -/
def TopAgree (top₁ top₂ : Nat → Nat → m Digest) : Prop :=
  ∀ level nodeIdx, level < maxLayerHeight → nodeIdx < 2 ^ (maxLayerHeight - level) →
    top₁ level nodeIdx = top₂ level nodeIdx

theorem pathNode_lt (leaf : LeafIndex) (level : Fin maxLayerHeight) :
    Nat.xor (leaf.val / 2 ^ level.val) 1 < 2 ^ (maxLayerHeight - level.val) := by
  have hlevel := level.isLt
  have hleaf := leaf.isLt
  apply Nat.xor_lt_two_pow
  · rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, Nat.sub_add_cancel hlevel.le]
    exact hleaf
  · exact Nat.one_lt_two_pow (by omega)

theorem signTopLayer_congr (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainIndex → m Digest) {top₁ top₂ : Nat → Nat → m Digest} (h : TopAgree top₁ top₂)
    (message : Digest) :
    signTopLayer parameter index secret top₁ message = signTopLayer parameter index secret top₂ message := by
  have hpath : ∀ level : Fin maxLayerHeight,
      top₁ level.val (Nat.xor ((leafIndexAt index topLayer).val / 2 ^ level.val) 1) =
        top₂ level.val (Nat.xor ((leafIndexAt index topLayer).val / 2 ^ level.val) 1) :=
    fun level => h _ _ level.isLt (pathNode_lt _ level)
  unfold signTopLayer
  simp only [hpath]

theorem signLayers_congr (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest) {top₁ top₂ : Nat → Nat → m Digest}
    (h : TopAgree top₁ top₂) (remaining : Nat) (message : Digest) :
    signLayers parameter index secret top₁ remaining message = signLayers parameter index secret top₂ remaining message := by
  induction remaining generalizing message with
  | zero => rfl
  | succ remaining ih =>
      unfold signLayers
      simp only [signTopLayer_congr parameter index _ h, ih]

theorem signFrom_congr (parameter : PublicParameter) (index : Index) (ftsSecret : FtsTree → FtsLeaf → m Digest)
    (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → m Digest) {top₁ top₂ : Nat → Nat → m Digest}
    (h : TopAgree top₁ top₂) (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    signFrom parameter index ftsSecret otsSecret top₁ randomness leaves =
      signFrom parameter index ftsSecret otsSecret top₂ randomness leaves := by
  unfold signFrom
  simp only [signLayers_congr parameter index otsSecret h]

end Congruence

/-- The checked cached signer is the node-table signer when the cache unmasks to the key's table on
the region. -/
theorem cachedTableSignChecked_eq_tableSign (randomizers : RandomizerOutputs) (masks : MaskOutputs)
    (secretKey : SphincsSecurity.SecretKey) (cache : TopCache)
    (h : ∀ level nodeIdx, level < maxLayerHeight → nodeIdx < 2 ^ (maxLayerHeight - level) →
      cache.node level nodeIdx ^^^ maskValue masks level nodeIdx = secretKey.top level nodeIdx)
    (message : Message) :
    cachedTableSignChecked randomizers masks secretKey cache message = tableSign randomizers secretKey message := by
  unfold cachedTableSignChecked tableSign
  refine bind_congr fun attempt => ?_
  rcases attempt with _ | ⟨randomness, index, leaves⟩
  · rfl
  · dsimp only
    rw [Concrete.signAfterDigest]
    exact signFrom_congr _ _ _ _ (fun level nodeIdx hl hn => by simp only [h level nodeIdx hl hn]) _ _

/-! ## Moving the masks -/

/-- XOR the zero-extended node table into the mask table. An involution, so it keeps the uniform
law of the masks. -/
def maskShift (top : Nat → Nat → Digest) (masks : MaskOutputs) : MaskOutputs :=
  fun position => masks position ^^^ (top position.1.val position.2.val).setWidth hashOutputBits

theorem maskShift_maskShift (top : Nat → Nat → Digest) (masks : MaskOutputs) :
    maskShift top (maskShift top masks) = masks := by
  funext position
  simp [maskShift, BitVec.xor_assoc]

theorem maskShift_bijective (top : Nat → Nat → Digest) : Function.Bijective (maskShift top) :=
  Function.Involutive.bijective (maskShift_maskShift top)

theorem truncateHash_xor_setWidth (output : HashOutput) (value : Digest) :
    truncateHash (output ^^^ value.setWidth hashOutputBits) = truncateHash output ^^^ value := by
  unfold truncateHash
  rw [BitVec.extractLsb'_xor]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hi' : i < hashOutputBits := by simp only [digestBits, hashOutputBits] at *; omega
  simp [hi, hi']

theorem maskPosition_of_lt {level nodeIdx : Nat} (hlevel : level < maxLayerHeight)
    (hnode : nodeIdx < 2 ^ (maxLayerHeight - level)) :
    (maskPosition level nodeIdx).1.val = level ∧ (maskPosition level nodeIdx).2.val = nodeIdx := by
  have : 2 ^ (maxLayerHeight - level) ≤ 2 ^ maxLayerHeight := Nat.pow_le_pow_right (by omega) (by omega)
  simp only [maskPosition]
  exact ⟨Nat.mod_eq_of_lt hlevel, Nat.mod_eq_of_lt (by omega)⟩

theorem maskValue_maskShift (top : Nat → Nat → Digest) (masks : MaskOutputs) {level nodeIdx : Nat}
    (hlevel : level < maxLayerHeight) (hnode : nodeIdx < 2 ^ (maxLayerHeight - level)) :
    maskValue (maskShift top masks) level nodeIdx = maskValue masks level nodeIdx ^^^ top level nodeIdx := by
  obtain ⟨h1, h2⟩ := maskPosition_of_lt hlevel hnode
  simp only [maskValue, maskShift, truncateHash_xor_setWidth, h1, h2]

/-- The simulator's region: the masks themselves. -/
def simRegion (masks : MaskOutputs) : TopRegion := fun level nodeIdx => maskValue masks level.val nodeIdx.val

theorem tableRegion_maskShift (top : Nat → Nat → Digest) (masks : MaskOutputs) :
    tableRegion top (maskShift top masks) = simRegion masks := by
  funext level nodeIdx
  simp only [tableRegion, simRegion, maskValue_maskShift top masks level.isLt nodeIdx.isLt]
  rw [BitVec.xor_comm, BitVec.xor_assoc]
  simp

theorem simRegion_node_unmask (top : Nat → Nat → Digest) (masks : MaskOutputs) (tag : HashOutput)
    {level nodeIdx : Nat} (hlevel : level < maxLayerHeight) (hnode : nodeIdx < 2 ^ (maxLayerHeight - level)) :
    (⟨tag, simRegion masks⟩ : TopCache).node level nodeIdx ^^^ maskValue (maskShift top masks) level nodeIdx =
      top level nodeIdx := by
  rw [maskValue_maskShift top masks hlevel hnode]
  simp [TopCache.node, hlevel, hnode, simRegion]


/-! ## The MAC check, up to bad requests -/

/-- The signer once the MAC is gone: the published cache gets the node-table signer, any other cache
fails. -/
def modSign (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey) (published : TopCache)
    (cache : TopCache) (message : Message) : OracleComp HashSpec (Option Signature) :=
  if cache = published then tableSign randomizers secretKey message else pure none

/-- A bad request: a cache off the published region whose tag matches the MAC table there. -/
def MacBad (region : TopRegion) (table : MacOutputs) (request : SigningRequest) : Prop :=
  request.cache.region ≠ region ∧ table request.cache.region = request.cache.tag

theorem cachedTableSign_eq_modSign (randomizers : RandomizerOutputs) (outputs : SecretOutputs)
    (top : Nat → Nat → Digest) (masks : MaskOutputs) (tag : HashOutput) (table : MacOutputs)
    (request : SigningRequest) (hgood : ¬MacBad (simRegion masks) table request) :
    cachedTableSign randomizers (maskShift top masks) (Function.update table (simRegion masks) tag)
        (tableKey 0 top outputs) request.cache request.message =
      modSign randomizers (tableKey 0 top outputs) ⟨tag, simRegion masks⟩ request.cache request.message := by
  unfold cachedTableSign modSign
  by_cases hcache : request.cache = ⟨tag, simRegion masks⟩
  · rw [hcache, if_pos rfl]
    simp only [Function.update_self, if_true]
    exact cachedTableSignChecked_eq_tableSign _ _ _ _
      (fun level nodeIdx hl hn => simRegion_node_unmask top masks tag hl hn) _
  · rw [if_neg hcache, if_neg]
    intro htag
    by_cases hregion : request.cache.region = simRegion masks
    · rw [hregion, Function.update_self] at htag
      apply hcache
      cases hc : request.cache
      rw [hc] at htag hregion
      simp_all
    · rw [Function.update_of_ne hregion] at htag
      exact hgood ⟨hregion, htag⟩

/-! ## The bad requests are unlikely -/

theorem probEvent_exists_list_le {X Y : Type} (mx : ProbComp X) (entries : List Y) (event : Y → X → Prop)
    (c : ℝ≥0∞) (hc : ∀ y ∈ entries, Pr[event y | mx] ≤ c) :
    Pr[fun x => ∃ y ∈ entries, event y x | mx] ≤ entries.length * c := by
  induction entries with
  | nil => simp
  | cons head tail ih =>
      calc Pr[fun x => ∃ y ∈ head :: tail, event y x | mx]
          = Pr[fun x => event head x ∨ ∃ y ∈ tail, event y x | mx] := by
            apply probEvent_ext
            intro x _
            simp
        _ ≤ Pr[event head | mx] + Pr[fun x => ∃ y ∈ tail, event y x | mx] := probEvent_or_le _ _ _
        _ ≤ c + tail.length * c := add_le_add (hc head (by simp)) (ih fun y hy => hc y (by simp [hy]))
        _ = (head :: tail).length * c := by
            simp only [List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
            rw [add_comm]

theorem probOutput_uniform_hashOutput (value : HashOutput) :
    Pr[= value | ($ᵗ HashOutput : ProbComp HashOutput)] = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  rw [probOutput_uniformSample]
  congr 1
  simp [hashOutputBits]
  norm_num

theorem probEvent_macTable_eq (region : TopRegion) (tag : HashOutput) :
    Pr[fun table : MacOutputs => table region = tag | sampleMacOutputs] = (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hlaw := @evalSPMF_uniformSample_bind_update TopRegion HashOutput _ _ _ _ _ macOutputsSampleableType region
  rw [sampleMacOutputs, ← probEvent_congr' (fun _ _ => Iff.rfl) hlaw, probEvent_bind_eq_tsum]
  simp only [bind_pure_comp, probEvent_map, Function.comp_def, Function.update_self]
  simp
  rfl


theorem probEvent_macBad_le {X : Type} (region : TopRegion) (mx : ProbComp X) (logOf : X → QueryLog RequestSpec)
    (n : Nat) :
    Pr[fun p : MacOutputs × X => BadIn (MacBad region p.1) n (logOf p.2) |
      sampleMacOutputs >>= fun table => (fun x => (table, x)) <$> mx] ≤ n * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  simp only [map_eq_bind_pure_comp, Function.comp_def]
  rw [probEvent_bind_bind_swap, probEvent_bind_eq_tsum]
  calc ∑' x, Pr[= x | mx] * Pr[fun p : MacOutputs × X => BadIn (MacBad region p.1) n (logOf p.2) |
          sampleMacOutputs >>= fun table => pure (table, x)]
      ≤ ∑' x, Pr[= x | mx] * (n * (2 ^ 256 : ℝ≥0∞)⁻¹) := by
        refine ENNReal.tsum_le_tsum fun x => mul_le_mul' le_rfl ?_
        rw [show (sampleMacOutputs >>= fun table => pure (table, x)) =
          (fun table => (table, x)) <$> sampleMacOutputs from bind_pure_comp _ _, probEvent_map]
        refine (probEvent_mono fun table _ hbad => ?_).trans
          ((probEvent_exists_list_le sampleMacOutputs ((logOf x).take n)
            (fun entry table => table entry.1.cache.region = entry.1.cache.tag) _
            fun entry _ => (probEvent_macTable_eq _ _).le).trans ?_)
        · obtain ⟨entry, hentry, hbadEntry⟩ := hbad
          exact ⟨entry, hentry, hbadEntry.2⟩
        · exact mul_le_mul' (by exact_mod_cast List.length_take_le _ _) le_rfl
    _ = (∑' x, Pr[= x | mx]) * (n * (2 ^ 256 : ℝ≥0∞)⁻¹) := ENNReal.tsum_mul_right
    _ ≤ n * (2 ^ 256 : ℝ≥0∞)⁻¹ := mul_le_of_le_one_left zero_le tsum_probOutput_le_one

end MacElim

/-! ## The simulating adversary -/

/-- Answer the experiment adversary's queries for a message-only adversary: hash and sampling queries
are forwarded, requests carrying the published cache are forwarded as their message, and any other
cache fails, as its MAC check would. -/
def simImpl (published : TopCache) :
    QueryImpl (OracleWorld + RequestSpec) (OracleComp (OracleWorld + SigningSpec))
  | .inl input => liftM ((OracleWorld + SigningSpec).query (.inl input))
  | .inr request =>
      if request.cache = published then liftM ((OracleWorld + SigningSpec).query (.inr request.message))
      else pure none

/-- Private sampling of a message-only adversary: each uniform query goes to the world's sampling
oracle. -/
def liftSample {X : Type} (p : ProbComp X) : OracleComp (OracleWorld + SigningSpec) X :=
  simulateQ (fun t => (liftM ((OracleWorld + SigningSpec).query (.inl (.inl t))) :
    OracleComp (OracleWorld + SigningSpec) (unifSpec.Range t))) p

/-- The message-only adversary: sample a mask table and a tag, publish the cache made of the masks
(the masked region's law) and the tag, and run the experiment adversary against `simImpl`. Its hash
queries are exactly the experiment adversary's. -/
noncomputable def simAdversary (adversary : Security.Adversary) : Adversary where
  main pk := do
    let masks ← liftSample sampleMaskOutputs
    let tag ← liftSample ($ᵗ HashOutput)
    simulateQ (simImpl ⟨tag, MacElim.simRegion masks⟩) (adversary.main pk ⟨tag, MacElim.simRegion masks⟩)

namespace MacElim

/-- The message-only log of a run against `simImpl`: the requests carrying the published cache. -/
def projectLog (published : TopCache) : QueryLog RequestSpec → QueryLog SigningSpec
  | [] => []
  | entry :: rest =>
      if entry.1.cache = published then ⟨entry.1.message, entry.2⟩ :: projectLog published rest
      else projectLog published rest

theorem simulated_run_eq {α : Type} (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (published : TopCache) (computation : OracleComp (OracleWorld + RequestSpec) α) :
    (simulateQ (forwardOracles + signingOracle (tableScheme randomizers) secretKey)
        (simulateQ (simImpl published) computation)).run =
      (fun result => (result.1, projectLog published result.2)) <$>
        requestLoggedRun (fun request => liftM (modSign randomizers secretKey published request.cache request.message))
          computation := by
  induction computation using OracleComp.inductionOn with
  | pure a => simp [loggedRun_pure, projectLog]
  | query_bind input next ih =>
      cases input with
      | inl input =>
          rw [loggedRun_query_inl]
          simp only [simulateQ_bind, simImpl, simulateQ_spec_query, QueryImpl.add_apply_inl, forwardOracles,
            WriterT.run_bind', ih]
          change ((fun a => (a, ([] : QueryLog SigningSpec))) <$>
            (liftM (OracleWorld.query input) : OracleComp OracleWorld _)) >>= _ = _
          simp [map_bind]
      | inr request =>
          rw [loggedRun_query_inr]
          by_cases hcache : request.cache = published
          · have hsign : modSign randomizers secretKey published request.cache request.message =
                tableSign randomizers secretKey request.message := if_pos hcache
            have hsim : simImpl published (.inr request) =
                liftM ((OracleWorld + SigningSpec).query (.inr request.message)) := if_pos hcache
            have horacle : (signingOracle (tableScheme randomizers) secretKey request.message).run =
                (liftM (tableSign randomizers secretKey request.message) : OracleComp OracleWorld _) >>= fun u =>
                  pure (u, [⟨request.message, u⟩]) := by
              simp [signingOracle, tableScheme]
            simp only [simulateQ_bind, simulateQ_spec_query]
            rw [hsim, hsign]
            simp only [simulateQ_spec_query, QueryImpl.add_apply_inr, WriterT.run_bind', horacle, ih]
            simp [projectLog, hcache, map_bind]
          · have hsign : modSign randomizers secretKey published request.cache request.message = pure none :=
              if_neg hcache
            have hsim : simImpl published (.inr request) = pure none := if_neg hcache
            simp only [simulateQ_bind, simulateQ_spec_query]
            rw [hsim, hsign]
            simp only [simulateQ_pure, pure_bind, ih]
            simp [projectLog, hcache]

/-! ## Sampling inside the games -/

theorem run_simulateQ_liftSample {X : Type}
    (signer : QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld))) (p : ProbComp X) :
    (simulateQ (forwardOracles + signer) (liftSample p)).run =
      (fun x => (x, ([] : QueryLog SigningSpec))) <$> (liftM p : OracleComp OracleWorld X) := by
  induction p using OracleComp.inductionOn with
  | pure x => simp [liftSample]
  | query_bind t k ih =>
      unfold liftSample at ih ⊢
      rw [simulateQ_bind, simulateQ_bind, simulateQ_spec_query, simulateQ_spec_query, liftM_bind,
        WriterT.run_bind']
      change (forwardOracles (.inl t)).run >>= _ = (liftM (OracleWorld.query (.inl t)) >>= _ : OracleComp OracleWorld _) <&> _
      simp only [forwardOracles, ih]
      change ((fun a => (a, ([] : QueryLog SigningSpec))) <$>
        (liftM (OracleWorld.query (.inl t)) : OracleComp OracleWorld _)) >>= _ = _
      simp [map_bind]

theorem run_simulateQ_liftSample_bind {X Y : Type}
    (signer : QueryImpl SigningSpec (WriterT (QueryLog SigningSpec) (OracleComp OracleWorld)))
    (p : ProbComp X) (f : X → OracleComp (OracleWorld + SigningSpec) Y) :
    (simulateQ (forwardOracles + signer) (liftSample p >>= f)).run =
      (liftM p : OracleComp OracleWorld X) >>= fun x => (simulateQ (forwardOracles + signer) (f x)).run := by
  rw [simulateQ_bind, WriterT.run_bind', run_simulateQ_liftSample]
  simp
  exact bind_congr fun _ => id_map _

theorem romRun_count_liftM_bind {X Y : Type} (p : ProbComp X) (f : X → OracleComp OracleWorld Y)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (countHashQueries ((liftM p : OracleComp OracleWorld X) >>= f))).run' cache =
      p >>= fun x => (simulateQ romImpl (countHashQueries (f x))).run' cache := by
  rw [countHashQueries_bind, countHashQueries_lift_prob, bind_map_left]
  simp only [zero_add, Prod.mk.eta, bind_pure]
  exact run'_lift_sample_bind p _ cache

/-- The ideal game once the simulator has sampled its cache, written on the experiment's log. -/
noncomputable def idealGame (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (adversary : Security.Adversary) (pk : PublicKey) (published : TopCache) : OracleComp OracleWorld Bool :=
  requestLoggedRun (fun request => liftM (modSign randomizers secretKey published request.cache request.message))
      (adversary.main pk published) >>= fun result =>
    (fun verified => decide (SigningTranscript.Valid (projectLog published result.2) ∧
        ¬SigningTranscript.Contains (projectLog published result.2) result.1) && verified) <$>
      (liftM (Concrete.verify pk result.1.message result.1.signature : OracleComp HashSpec Bool) :
        OracleComp OracleWorld Bool)

theorem gameRest_simAdversary (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (adversary : Security.Adversary) (pk : PublicKey) :
    gameRest (tableScheme randomizers) (simAdversary adversary) pk secretKey =
      (liftM sampleMaskOutputs : OracleComp OracleWorld MaskOutputs) >>= fun masks =>
        (liftM ($ᵗ HashOutput) : OracleComp OracleWorld HashOutput) >>= fun tag =>
          idealGame randomizers secretKey adversary pk ⟨tag, simRegion masks⟩ := by
  unfold gameRest
  simp only [simAdversary, run_simulateQ_liftSample_bind, bind_assoc, simulated_run_eq, idealGame,
    map_eq_bind_pure_comp]
  rfl

theorem romRun_gameRest_simAdversary (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (adversary : Security.Adversary) (pk : PublicKey) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (countHashQueries (gameRest (tableScheme randomizers) (simAdversary adversary) pk secretKey))).run'
        cache =
      sampleMaskOutputs >>= fun masks => ($ᵗ HashOutput) >>= fun tag =>
        (simulateQ romImpl (countHashQueries (idealGame randomizers secretKey adversary pk ⟨tag, simRegion masks⟩))).run'
          cache := by
  rw [gameRest_simAdversary, romRun_count_liftM_bind]
  refine bind_congr fun masks => ?_
  rw [romRun_count_liftM_bind]

/-! ## The comparison once the tree is built -/

theorem romRun_count_bind {α β : Type} (first : OracleComp OracleWorld α) (next : α → OracleComp OracleWorld β)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (countHashQueries (first >>= next))).run' cache =
      (simulateQ romImpl (countHashQueries first)).run cache >>= fun head =>
        (fun result => (result.1, head.1.2 + result.2)) <$>
          (simulateQ romImpl (countHashQueries (next head.1.1))).run' head.2 := by
  rw [countHashQueries_bind, simulateQ_bind, StateT.run'_eq, StateT.run_bind, map_bind]
  apply bind_congr
  intro head
  simp only [bind_pure_comp, simulateQ_map, StateT.run'_eq, StateT.run_map, Functor.map_map]

theorem romRun_count_map {α β : Type} (computation : OracleComp OracleWorld α) (f : α → β)
    (cache : QueryCache HashSpec) :
    (simulateQ romImpl (countHashQueries (f <$> computation))).run' cache =
      (fun result => (f result.1, result.2)) <$> (simulateQ romImpl (countHashQueries computation)).run' cache := by
  rw [countHashQueries_map, simulateQ_map, StateT.run'_eq, StateT.run'_eq, StateT.run_map, Functor.map_map,
    Functor.map_map]

/-- The verdict after a logged run: the final verification, scored by `verdict`, with the run's count. -/
noncomputable def verdictRun (verdict : Bool → Bool) (pk : PublicKey) (forgery : Forgery) (count : Nat)
    (cache : QueryCache HashSpec) : ProbComp (Bool × Nat) :=
  (fun result => (verdict result.1, count + result.2)) <$>
    (simulateQ romImpl (countHashQueries (liftM (Concrete.verify pk forgery.message forgery.signature :
      OracleComp HashSpec Bool) : OracleComp OracleWorld Bool))).run' cache

theorem romRun_logged_verdict (impl : SigningRequest → OracleComp OracleWorld (Option Signature))
    (computation : OracleComp (OracleWorld + RequestSpec) Forgery) (pk : PublicKey)
    (verdict : Forgery × QueryLog RequestSpec → Bool → Bool) (cache : QueryCache HashSpec) :
    (simulateQ romImpl (countHashQueries (requestLoggedRun impl computation >>= fun result =>
        (verdict result) <$> (liftM (Concrete.verify pk result.1.message result.1.signature :
          OracleComp HashSpec Bool) : OracleComp OracleWorld Bool)))).run' cache =
      countedRun impl computation cache >>= fun head =>
        verdictRun (verdict head.1.1) pk head.1.1.1 head.1.2 head.2 := by
  rw [romRun_count_bind]
  refine bind_congr fun head => ?_
  rw [romRun_count_map, Functor.map_map]
  rfl

theorem validLog_of_verdict {E : Bool × Nat → Prop} (hE : ∀ result, E result → result.1 = true)
    (pk : PublicKey) (forgery : Forgery) (log : QueryLog RequestSpec) (count : Nat) (cache : QueryCache HashSpec)
    (hlong : signatureLimit < log.length) :
    Pr[E | verdictRun (fun verified => decide (RequestTranscript.Valid log ∧ ¬RequestTranscript.Contains log forgery) &&
      verified) pk forgery count cache] = 0 := by
  rw [probEvent_eq_zero_iff]
  intro result hresult hevent
  have := hE result hevent
  rw [verdictRun, support_map] at hresult
  obtain ⟨_, _, rfl⟩ := hresult
  simp [RequestTranscript.Valid, Nat.not_le.mpr hlong] at this

theorem length_projectLog_le (published : TopCache) (log : QueryLog RequestSpec) :
    (projectLog published log).length ≤ log.length := by
  induction log with
  | nil => simp [projectLog]
  | cons entry rest ih =>
      unfold projectLog
      split <;> simp <;> omega

theorem contains_of_projectLog (published : TopCache) (log : QueryLog RequestSpec) (forgery : Forgery)
    (h : SigningTranscript.Contains (projectLog published log) forgery) : RequestTranscript.Contains log forgery := by
  induction log with
  | nil => simp [projectLog, SigningTranscript.Contains] at h
  | cons entry rest ih =>
      unfold projectLog at h
      split at h
      · obtain ⟨e, he, hmsg, hsig⟩ := h
        simp only [List.mem_cons] at he
        rcases he with rfl | he
        · exact ⟨entry, by simp, hmsg, hsig⟩
        · obtain ⟨e', he', h1, h2⟩ := ih ⟨e, he, hmsg, hsig⟩
          exact ⟨e', by simp [he'], h1, h2⟩
      · obtain ⟨e', he', h1, h2⟩ := ih h
        exact ⟨e', by simp [he'], h1, h2⟩

theorem verdict_mono (published : TopCache) (log : QueryLog RequestSpec) (forgery : Forgery) (verified : Bool)
    (h : (decide (RequestTranscript.Valid log ∧ ¬RequestTranscript.Contains log forgery) && verified) = true) :
    (decide (SigningTranscript.Valid (projectLog published log) ∧
      ¬SigningTranscript.Contains (projectLog published log) forgery) && verified) = true := by
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨⟨hvalid, hcontains⟩, hverified⟩ := h
  exact ⟨⟨(length_projectLog_le published log).trans hvalid, fun hc => hcontains (contains_of_projectLog _ _ _ hc)⟩,
    hverified⟩

/-- The experiment's verdict after a logged run. -/
noncomputable def requestVerdict (pk : PublicKey) (head : ((Forgery × QueryLog RequestSpec) × Nat) × QueryCache HashSpec) :
    ProbComp (Bool × Nat) :=
  verdictRun (fun verified => decide (RequestTranscript.Valid head.1.1.2 ∧
    ¬RequestTranscript.Contains head.1.1.2 head.1.1.1) && verified) pk head.1.1.1 head.1.2 head.2

/-- The ideal game's verdict after a logged run, on the projected log. -/
noncomputable def signingVerdict (published : TopCache) (pk : PublicKey)
    (head : ((Forgery × QueryLog RequestSpec) × Nat) × QueryCache HashSpec) : ProbComp (Bool × Nat) :=
  verdictRun (fun verified => decide (SigningTranscript.Valid (projectLog published head.1.1.2) ∧
    ¬SigningTranscript.Contains (projectLog published head.1.1.2) head.1.1.1) && verified) pk head.1.1.1 head.1.2
      head.2

/-- The request signer of the experiment once the masks are shifted and the MAC table is split at the
published region. -/
noncomputable def realImpl (randomizers : RandomizerOutputs) (outputs : SecretOutputs) (top : Nat → Nat → Digest)
    (masks : MaskOutputs) (tag : HashOutput) (table : MacOutputs) (request : SigningRequest) :
    OracleComp OracleWorld (Option Signature) :=
  liftM (cachedTableSign randomizers (maskShift top masks) (Function.update table (simRegion masks) tag)
    (tableKey 0 top outputs) request.cache request.message)

/-- The request signer without the MAC. -/
noncomputable def modImpl (randomizers : RandomizerOutputs) (secretKey : SphincsSecurity.SecretKey)
    (published : TopCache) (request : SigningRequest) : OracleComp OracleWorld (Option Signature) :=
  liftM (modSign randomizers secretKey published request.cache request.message)

/-- Once the masks and the tag are fixed, the MAC table off the published region only matters through
bad requests. -/
theorem probEvent_macTable_le_ideal (randomizers : RandomizerOutputs) (outputs : SecretOutputs)
    (adversary : Security.Adversary) (top : Nat → Nat → Digest) (masks : MaskOutputs) (tag : HashOutput)
    (cache : QueryCache HashSpec) (P : Nat → Prop) :
    Pr[fun result => result.1 = true ∧ P result.2 | sampleMacOutputs >>= fun table =>
        (simulateQ romImpl (countHashQueries (cachedGameRest
          (cachedTableSign randomizers (maskShift top masks) (Function.update table (simRegion masks) tag)
            (tableKey 0 top outputs)) adversary ⟨top (layerHeight topLayer) 0, 0⟩ ⟨tag, simRegion masks⟩))).run' cache] ≤
      Pr[fun result => result.1 = true ∧ P result.2 |
        (simulateQ romImpl (countHashQueries (idealGame randomizers (tableKey 0 top outputs) adversary
          ⟨top (layerHeight topLayer) 0, 0⟩ ⟨tag, simRegion masks⟩))).run' cache] +
        (signatureLimit : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  have hreal : ∀ table, (simulateQ romImpl (countHashQueries (cachedGameRest
      (cachedTableSign randomizers (maskShift top masks) (Function.update table (simRegion masks) tag)
        (tableKey 0 top outputs)) adversary ⟨top (layerHeight topLayer) 0, 0⟩ ⟨tag, simRegion masks⟩))).run' cache =
      countedRun (realImpl randomizers outputs top masks tag table)
        (adversary.main ⟨top (layerHeight topLayer) 0, 0⟩ ⟨tag, simRegion masks⟩) cache >>=
          requestVerdict ⟨top (layerHeight topLayer) 0, 0⟩ := by
    intro table
    rw [cachedGameRest_eq]
    exact romRun_logged_verdict _ _ _ _ cache
  have hideal : (simulateQ romImpl (countHashQueries (idealGame randomizers (tableKey 0 top outputs) adversary
      ⟨top (layerHeight topLayer) 0, 0⟩ ⟨tag, simRegion masks⟩))).run' cache =
      countedRun (modImpl randomizers (tableKey 0 top outputs) ⟨tag, simRegion masks⟩)
        (adversary.main ⟨top (layerHeight topLayer) 0, 0⟩ ⟨tag, simRegion masks⟩) cache >>=
          signingVerdict ⟨tag, simRegion masks⟩ ⟨top (layerHeight topLayer) 0, 0⟩ := by
    unfold idealGame
    exact romRun_logged_verdict _ _ _ _ cache
  simp only [hreal, hideal]
  calc _ ≤ Pr[fun result => result.1 = true ∧ P result.2 | sampleMacOutputs >>= fun _ =>
          countedRun (modImpl randomizers (tableKey 0 top outputs) ⟨tag, simRegion masks⟩)
            (adversary.main ⟨top (layerHeight topLayer) 0, 0⟩ ⟨tag, simRegion masks⟩) cache >>=
              requestVerdict ⟨top (layerHeight topLayer) 0, 0⟩] +
        Pr[fun x : MacOutputs × (((Forgery × QueryLog RequestSpec) × Nat) × QueryCache HashSpec) =>
            BadIn (MacBad (simRegion masks) x.1) signatureLimit x.2.1.1.2 |
          sampleMacOutputs >>= fun table => (fun x => (table, x)) <$>
            countedRun (modImpl randomizers (tableKey 0 top outputs) ⟨tag, simRegion masks⟩)
              (adversary.main ⟨top (layerHeight topLayer) 0, 0⟩ ⟨tag, simRegion masks⟩) cache] := by
        apply probEvent_bind_le_add_bind
        intro table _
        rw [probEvent_map]
        refine countedRun_identical_until_bad (MacBad (simRegion masks) table) _ _
          (fun request hgood => congrArg liftM (cachedTableSign_eq_modSign randomizers outputs top masks tag table
            request hgood)) _ signatureLimit cache _ _ ?_
        intro x hx
        exact validLog_of_verdict (fun _ h => h.1) _ _ _ _ _ hx
    _ ≤ _ := by
        refine add_le_add ?_ (probEvent_macBad_le _ _
          (fun x : ((Forgery × QueryLog RequestSpec) × Nat) × QueryCache HashSpec => x.1.1.2) _)
        rw [probEvent_bind_const]
        simp only [probFailure_eq_zero, tsub_zero, one_mul]
        refine probEvent_bind_mono fun head _ => ?_
        simp only [requestVerdict, signingVerdict, verdictRun, probEvent_map]
        exact probEvent_mono fun result _ h => ⟨verdict_mono _ _ _ _ h.1, h.2⟩

/-- Once the top tree is built: the experiment with uniform masks and MAC table against the ideal game
of the simulating adversary. -/
theorem probEvent_cachedGameRest_le (randomizers : RandomizerOutputs) (outputs : SecretOutputs)
    (adversary : Security.Adversary) (top : Nat → Nat → Digest) (cache : QueryCache HashSpec) (P : Nat → Prop) :
    Pr[fun result => result.1 = true ∧ P result.2 | do
        let masks ← sampleMaskOutputs
        let macs ← sampleMacOutputs
        (simulateQ romImpl (countHashQueries (cachedGameRest
          (cachedTableSign randomizers masks macs (tableKey 0 top outputs)) adversary
            ⟨top (layerHeight topLayer) 0, 0⟩ ⟨macs (tableRegion top masks), tableRegion top masks⟩))).run' cache] ≤
      Pr[fun result => result.1 = true ∧ P result.2 |
        (simulateQ romImpl (countHashQueries (gameRest (tableScheme randomizers) (simAdversary adversary)
          ⟨top (layerHeight topLayer) 0, 0⟩ (tableKey 0 top outputs)))).run' cache] +
        (signatureLimit : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
  rw [romRun_gameRest_simAdversary]
  -- Shift the masks by the tree: the published region becomes the simulator's.
  have hshift := evalSPMF_map_bijective_uniform_cross (α := MaskOutputs) (β := MaskOutputs) (maskShift top)
    (maskShift_bijective top)
  have hmove : ∀ G : MaskOutputs → ProbComp (Bool × Nat),
      𝒮[sampleMaskOutputs >>= G] = 𝒮[sampleMaskOutputs >>= fun masks => G (maskShift top masks)] := by
    intro G
    rw [← bind_map_left (maskShift top), evalSPMF_bind, evalSPMF_bind, sampleMaskOutputs, hshift]
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (show 𝒮[sampleMaskOutputs >>= fun masks => sampleMacOutputs >>= fun macs =>
      (simulateQ romImpl (countHashQueries (cachedGameRest
          (cachedTableSign randomizers masks macs (tableKey 0 top outputs)) adversary
            ⟨top (layerHeight topLayer) 0, 0⟩ ⟨macs (tableRegion top masks), tableRegion top masks⟩))).run' cache] =
      𝒮[sampleMaskOutputs >>= fun masks => sampleMacOutputs >>= fun macs =>
      (simulateQ romImpl (countHashQueries (cachedGameRest
          (cachedTableSign randomizers (maskShift top masks) macs (tableKey 0 top outputs)) adversary
            ⟨top (layerHeight topLayer) 0, 0⟩ ⟨macs (simRegion masks), simRegion masks⟩))).run' cache] by
    simp only [← tableRegion_maskShift top]
    exact hmove (fun masks => sampleMacOutputs >>= fun macs =>
      (simulateQ romImpl (countHashQueries (cachedGameRest
          (cachedTableSign randomizers masks macs (tableKey 0 top outputs)) adversary
            ⟨top (layerHeight topLayer) 0, 0⟩ ⟨macs (tableRegion top masks), tableRegion top masks⟩))).run' cache))]
  apply probEvent_bind_congr_le_add
  intro masks _
  -- Split the MAC table at the published region.
  have hlaw := @evalSPMF_uniformSample_bind_update TopRegion HashOutput _ _ _ _ _ macOutputsSampleableType
    (simRegion masks)
  rw [probEvent_congr' (fun _ _ => Iff.rfl) (show 𝒮[sampleMacOutputs >>= fun macs =>
      (simulateQ romImpl (countHashQueries (cachedGameRest
          (cachedTableSign randomizers (maskShift top masks) macs (tableKey 0 top outputs)) adversary
            ⟨top (layerHeight topLayer) 0, 0⟩ ⟨macs (simRegion masks), simRegion masks⟩))).run' cache] =
      𝒮[($ᵗ HashOutput) >>= fun tag => sampleMacOutputs >>= fun table =>
      (simulateQ romImpl (countHashQueries (cachedGameRest
          (cachedTableSign randomizers (maskShift top masks) (Function.update table (simRegion masks) tag)
            (tableKey 0 top outputs)) adversary
            ⟨top (layerHeight topLayer) 0, 0⟩ ⟨tag, simRegion masks⟩))).run' cache] by
    rw [evalSPMF_bind, sampleMacOutputs, ← hlaw, ← evalSPMF_bind]
    simp only [bind_assoc, pure_bind, Function.update_self])]
  apply probEvent_bind_congr_le_add
  intro tag _
  exact probEvent_macTable_le_ideal randomizers outputs adversary top masks tag cache P

theorem probEvent_bind_congr_eq {A B : Type} (ma : ProbComp A) (f g : A → ProbComp B) (event : B → Prop)
    (h : ∀ a, Pr[event | f a] = Pr[event | g a]) : Pr[event | ma >>= f] = Pr[event | ma >>= g] := by
  simp only [probEvent_bind_eq_tsum, h]

theorem probEvent_bind_swap_three {A B C D : Type} (ma : ProbComp A) (mb : ProbComp B) (mc : ProbComp C)
    (f : A → B → C → ProbComp D) (event : D → Prop) :
    Pr[event | ma >>= fun a => mb >>= fun b => mc >>= fun c => f a b c] =
      Pr[event | mc >>= fun c => ma >>= fun a => mb >>= fun b => f a b c] := by
  rw [probEvent_bind_congr_eq ma _ (fun a => mc >>= fun c => mb >>= fun b => f a b c) event
    (fun a => probEvent_bind_bind_swap mb mc (f a) event)]
  exact probEvent_bind_bind_swap ma mc (fun a c => mb >>= fun b => f a b c) event

end MacElim

open MacElim in
/-- **Eliminating the cache MAC and the node masks.** The experiment from derivation tables, with
uniform mask and MAC tables, wins with at most `b` hash calls no more often than the ideal table game
of the simulating message-only adversary, up to `2^32 / 2^256`: one chance in `2^256` per signing
request of a winning run to forge a MAC tag off the published region. -/
theorem cachedTable_le_simulated (adversary : Security.Adversary) (outputs : SecretOutputs)
    (randomizers : RandomizerOutputs) (b : Nat) :
    Pr[fun result => result.1 = true ∧ result.2 ≤ b | do
        let masks ← sampleMaskOutputs
        let macs ← sampleMacOutputs
        (simulateQ romImpl (countHashQueries
          (cachedTableGameAfterSecrets adversary outputs randomizers masks macs))).run' ∅] ≤
      Pr[fun result => result.1 = true ∧ result.2 ≤ b |
        (simulateQ romImpl (countHashQueries
          (tableGameAfterSecrets (simAdversary adversary) outputs randomizers))).run' ∅] +
      (2 ^ 32 : ℝ≥0∞) / 2 ^ 256 := by
  have hreal : ∀ masks macs, cachedTableGameAfterSecrets adversary outputs randomizers masks macs =
      (liftM (Concrete.keygenTable 0 (tableOts outputs topLayer Concrete.rootTree) :
        OracleComp HashSpec (Nat → Nat → Digest)) : OracleComp OracleWorld _) >>= fun top =>
          cachedGameRest (cachedTableSign randomizers masks macs (tableKey 0 top outputs)) adversary
            ⟨top (layerHeight topLayer) 0, 0⟩ ⟨macs (tableRegion top masks), tableRegion top masks⟩ := by
    intro masks macs
    unfold cachedTableGameAfterSecrets
    rw [keygenCachedWith_pure, liftM_map, bind_map_left]
  have hideal : tableGameAfterSecrets (simAdversary adversary) outputs randomizers =
      (liftM (Concrete.keygenTable 0 (tableOts outputs topLayer Concrete.rootTree) :
        OracleComp HashSpec (Nat → Nat → Digest)) : OracleComp OracleWorld _) >>= fun top =>
          gameRest (tableScheme randomizers) (simAdversary adversary) ⟨top (layerHeight topLayer) 0, 0⟩
            (tableKey 0 top outputs) := rfl
  have hbound : (signatureLimit : ℝ≥0∞) * (2 ^ 256 : ℝ≥0∞)⁻¹ = (2 ^ 32 : ℝ≥0∞) / 2 ^ 256 := by
    rw [div_eq_mul_inv]
    simp [signatureLimit]
    norm_num
  rw [← hbound]
  simp only [hreal, hideal, romRun_count_bind]
  refine (le_of_eq (probEvent_bind_swap_three _ _ _ _ _)).trans ?_
  apply probEvent_bind_congr_le_add
  intro head _
  simp only [← map_bind, probEvent_map]
  exact probEvent_cachedGameRest_le randomizers outputs adversary head.1.1 head.2 (fun count => head.1.2 + count ≤ b)

end SphincsSecurity.Seeded
