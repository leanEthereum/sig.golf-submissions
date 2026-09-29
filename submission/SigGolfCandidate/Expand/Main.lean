import SigGolfCandidate.Expand.Init
import SigGolfCandidate.Expand.RefExpand
import SigGolfCandidate.Sign.Sim

/-!
# `expand` refines `expandRef`

The program makes exactly one oracle query (the digest block at `DG = 0x20`, instructions
0 .. 13), then runs deterministically (`post_hash`: key extraction, sort, pass test, schedule,
pad check, copies) to HALT(1) or HALT(0) with the witness `witnessList …`.

Main results (namespace `SigGolfCandidate.Expand`):

* `expand_refines_counts` : value, calls, compressions of `submission.run .expand` =
  `countBoth (expandRef m pk σ)` (the `Budget.RefinesCounts` form, with `F = id`);
* `expand_refines` : value and calls = `countCalls (expandRef m pk σ)`;
* `expand_blocks` : value and compressions = `(r, 1)` for the value `r` of `expandRef m pk σ`
  (exactly one compression on every path);
* `expand_terminates` : every run under every oracle finishes in fewer than `2^32` cycles.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem
  OracleComp


theorem start_mem (s : MachineState) (a : Nat) (ha : a < 2 ^ 64) (h : 0x40 ≤ a) :
    (blk0.res.toState s).getMem (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a) := by
  have e : ∀ c : Nat, c < 64 → BitVec.ofNat 64 a ≠ BitVec.ofNat 64 c := by
    intro c hc; rw [Ne, ofNat_eq_iff]; omega
  simp only [blk0.res, rv_simp]
  simp [e 56 (by omega), e 48 (by omega), e 40 (by omega), e 32 (by omega)]

theorem start_hash (s : MachineState) (rho msg : List Byte) (hr : rho.length = 16) (hm : msg.length = 32)
    (hsig : s.readWords (BitVec.ofNat 64 0x3300) 2 = wordsOf rho)
    (hmsg : s.readWords (BitVec.ofNat 64 0x40) 4 = wordsOf msg) :
    hashInput (blk0.res.toState s) = fmt (digestInput rho msg) := by
  have h10 : (blk0.res.toState s).getReg .x10 = BitVec.ofNat 64 32 := by simp only [blk0.res, rv_simp]
  refine hashInput_eq_digest _ _ _ hr hm (by simp only [blk0.res, rv_simp]) (by rw [h10]; decide) ?_
  rw [h10, show 8 = 1 + 1 + 1 + 1 + 4 from rfl, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add,
    readWords_ofNat_add]
  simp only [Nat.reduceMul, Nat.reduceAdd, readWords_ofNat_one]
  have e : ∀ c : Nat, c < 64 → ∀ d : Nat, d < 64 → c ≠ d → BitVec.ofNat 64 c ≠ BitVec.ofNat 64 d := by
    intro c hc d hd hcd; rw [Ne, ofNat_eq_iff]; omega
  have g32 : (blk0.res.toState s).getMem (BitVec.ofNat 64 32) = BitVec.ofNat 64 3073 := by
    simp only [blk0.res, rv_simp]; simp [e 32 (by omega) 56 (by omega) (by omega),
      e 32 (by omega) 48 (by omega) (by omega), e 32 (by omega) 40 (by omega) (by omega)]
  have g40 : (blk0.res.toState s).getMem (BitVec.ofNat 64 40) = 0 := by
    simp only [blk0.res, rv_simp]; simp [e 40 (by omega) 56 (by omega) (by omega),
      e 40 (by omega) 48 (by omega) (by omega)]
  have g48 : (blk0.res.toState s).getMem (BitVec.ofNat 64 48) = s.getMem (BitVec.ofNat 64 0x3300) := by
    simp only [blk0.res, rv_simp]; simp [e 48 (by omega) 56 (by omega) (by omega)]
  have g56 : (blk0.res.toState s).getMem (BitVec.ofNat 64 56) = s.getMem (BitVec.ofNat 64 0x3308) := by
    simp only [blk0.res, rv_simp]; simp
  have w64 : (blk0.res.toState s).readWords (BitVec.ofNat 64 64) 4 = wordsOf msg := by
    rw [← hmsg]
    exact readWords_congr _ _ _ _ (fun i hi => (start_mem s _ (by omega) (by omega)))
  rw [readWords_ofNat_two] at hsig
  rw [g32, g40, g48, g56, w64, ← hsig]
  simp only [twWords_eq, List.cons_append, List.nil_append, List.cons.injEq, and_true]
  exact ⟨by unfold twWord0; rfl, rfl⟩



/-- The outcome of `expand` in the form `Sim.run_eq` needs. -/
def Qexp (r : Option (Bytes 6348)) (t : MachineState) : Prop :=
  fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
    r = if t.getReg .x10 = 0 then some (readBuffer t 0x800 6348) else none

theorem qexp_none (t : MachineState) (h : Final none t) : Qexp none t := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by rw [if_neg h3]⟩

/-- Everything after the digest query, from the state right after it. -/
theorem post_hash (ans : BitVec 256) (sig : List Byte) (hsig : sig.length = 6100) (s2 : MachineState)
    (hpc : s2.pc = pcOf 14) (hdo : DOk ans s2) (hsok : SigOK s2 sig)
    (hz : ∀ a, 0x800 ≤ a → a < 0x2190 → s2.getByte (BitVec.ofNat 64 a) = 0) :
    Run s2 15000 (Qexp ((expandOf sig ans.toNat).map (ofList 6348))) := by
  set N := ans.toNat with hN
  refine Run.seq (B₂ := 14666) (ext_run ans s2 hdo s2 hpc (Frame.refl _ _)) (fun t1 h1 => ?_) (by norm_num)
  refine Run.seq (B₂ := 13139) (sort_run ans s2 t1 h1) (fun t2 h2 => ?_) (by norm_num)
  obtain ⟨t2pc, ⟨A, hA, hF, hs⟩, hsent, hfr2⟩ := h2
  have hSK : SortedKeys N A := by
    refine ⟨?_, hF.lt, hs⟩
    refine List.Perm.trans (List.Perm.of_eq ?_) hF.perm
    apply List.map_congr_left; intro p hp; rw [List.mem_range] at hp; simp [show p ≠ 15 by omega]
  -- bytes of t2 outside KEYS are those of s2
  have hb2 : ∀ a, a < 2 ^ 64 → ¬ (0x6E0 ≤ a ∧ a < 0x760) → t2.getByte (BitVec.ofNat 64 a) = s2.getByte (BitVec.ofNat 64 a) := by
    intro a ha hk
    rw [getByte_ofNat _ _ ha, getByte_ofNat _ _ ha, hfr2 _ (by omega) (by unfold KW; omega)]
  refine Run.seq (B₂ := 12405) (pass_run A hSK.lt t2 t2pc hA) (fun t3 h3 => ?_) (by norm_num)
  by_cases hp : PassOK A
  · rw [if_pos hp] at h3
    obtain ⟨t3pc, t3m⟩ := h3
    have hpo := (passOK_iff hSK).mp hp
    have hv := vsOf_eq hSK
    have hleaves := leaves_vsOf hSK.sorted hSK.lt hp.1
    obtain ⟨hcr, hcs⟩ := schedule_counts hleaves (by simp [vsOf])
    have hoct : octopusSize (vsOf A) ≤ 120 := by rw [hv]; exact hpo.2
    have hb3 : ∀ a, a < 2 ^ 64 → ¬ (0x6E0 ≤ a ∧ a < 0x760) → t3.getByte (BitVec.ofNat 64 a) = s2.getByte (BitVec.ofNat 64 a) := by
      intro a ha hk; rw [getByte_ofNat _ _ ha, t3m, ← getByte_ofNat _ _ ha]; exact hb2 a ha hk
    have hc : SchCtx A sig t3 := ⟨hA.frame t3m, hSK.lt, by rw [t3m]; exact hsent,
      fun j hj => by rw [hb3 _ (by omega) (by omega)]; exact hsok j hj, hsig⟩
    have hz3 : ∀ i < 2152, t3.getByte (BitVec.ofNat 64 (0x910 + i)) = 0 := by
      intro i hi; rw [hb3 _ (by omega) (by omega)]; exact hz _ (by omega) (by omega)
    have hsched := sch_run A sig t3 hc hp.1 t3pc hz3 (by rw [hcr]; exact hoct) (by rw [hcs]; simp [vsOf])
    refine Run.seq (B₂ := 7643) hsched (fun t4 h4 => ?_) (by norm_num)
    set F := (List.range 15).foldl (schedLeaf (vsOf A)) ⟨[], [], []⟩ with hFdef
    have hsch : schedule (vsOf A) = (F.segs, F.reads) := by
      unfold schedule; rw [show (vsOf A).length = 15 by simp [vsOf]]
    rw [hsch] at hcr hcs
    simp only at hcr hcs
    have hn : F.reads.length ≤ 120 := by rw [hcr]; exact hoct
    obtain ⟨t4pc, _, _, _, t4x29, _, _, _, _, _, t4str, _, _, t4fr⟩ := h4
    rw [if_neg (by omega)] at t4pc
    refine Run.seq (B₂ := 6440) (pad_run sig t3 t4 hc.sigok t4fr t4pc F.reads.length hn t4x29)
      (fun t5 h5 => ?_) (by omega)
    have hall := all_iff_padOK sig hsig F.reads.length hn
    have hexp := expandOf_eq (sig := sig) hpo.1 hpo.2
    rw [← hv, hsch] at hexp
    simp only at hexp
    by_cases hpad : PadOK sig F.reads.length
    · obtain ⟨t5pc, t5m⟩ := h5.1 hpad
      rw [hexp, if_pos (hall.mpr hpad)]
      have hA5 : ArrOk t5 A := by
        intro p hp'
        rw [t5m, t4fr _ (by omega) (by unfold SW; omega)]; exact hc.arr p hp'
      refine (copy_run A t5 t5pc hA5).mono (le_refl _) (fun t6 ⟨h61, h62, h63, h64⟩ => ⟨h61, h62, ?_⟩)
      rw [if_pos h63, Option.map_some]
      apply congrArg some
      rw [readBuffer_eq]
      unfold ofList
      apply congrArg (BitVec.ofNat (8 * 6348))
      have hlen := length_witnessList sig hsig (leavesOf N) (vsOf A) F.segs (by simp [vsOf, porsK])
      rw [witBytes] at hlen
      have := witness_bytes sig hsig N A hSK hpo.1 F.segs (fun a => t5.getByte (BitVec.ofNat 64 a))
        (fun j hj => by
          show t5.getByte _ = _
          rw [getByte_ofNat _ _ (by omega), t5m, ← getByte_ofNat _ _ (by omega)]
          rw [getByte_ofNat _ _ (by omega), t4fr _ (by omega) (by unfold SW; omega), ← getByte_ofNat _ _ (by omega)]
          exact hc.sigok j hj)
        (fun i hi => by
          show t5.getByte _ = _
          rw [getByte_ofNat _ _ (by omega), t5m, ← getByte_ofNat _ _ (by omega)]
          exact t4str i hi)
        (by
          show t5.getByte _ = _
          rw [getByte_ofNat _ _ (by omega), t5m, t4fr _ (by omega) (by unfold SW; omega),
            ← getByte_ofNat _ _ (by omega), hb3 _ (by omega) (by omega)]
          exact hz _ (by omega) (by omega))
      apply congrArg
      apply List.ext_getElem (by simp [hlen])
      intro i h1 h2
      have hi : i < 6348 := by rw [hlen] at h1; exact h1
      rw [List.getElem_map, List.getElem_range, h64 _ (by omega), this i hi, List.getD_eq_getElem _ _ h1]
    · have h5' := h5.2 hpad
      rw [hexp, if_neg (fun h => hpad (hall.mp h))]
      exact (Run.done' (qexp_none t5 h5'))
  · rw [if_neg hp] at h3
    rw [expandOf_none (sig := sig) (fun h => hp ((passOK_iff hSK).mpr h))]
    exact (Run.done' (qexp_none t3 h3))



theorem Sim.of_run {s : MachineState} {B : Nat} {α : Type} {v : α} {Q : α → MachineState → Prop}
    (h : Run s B (Q v)) : Sign.Sim image s B (pure v) Q := by
  obtain ⟨t, k, c, hst, hc, hQ⟩ := h
  exact (Sign.Sim.pure_steps hst hQ).mono hc (fun _ _ h => h)

/-- `expand` from a state that looks like its initial state. -/
theorem expand_sim (sig msg : List Byte) (hsig : sig.length = 6100) (hmsg : msg.length = 32)
    (s : MachineState) (hpc : s.pc = pcOf 0) (h5 : s.getReg .x5 = 0)
    (hrho : s.readWords (BitVec.ofNat 64 0x3300) 2 = wordsOf (sigRho sig))
    (hm : s.readWords (BitVec.ofNat 64 0x40) 4 = wordsOf msg) (hsok : SigOK s sig)
    (hz : ∀ a, 0x800 ≤ a → a < 0x2190 → s.getByte (BitVec.ofNat 64 a) = 0) :
    Sign.Sim image s (13 + (8 + 15000))
      ((liftM (HashSpec.query (fmt (digestInput (sigRho sig) msg))) : OracleComp HashSpec _) >>= fun a =>
        pure ((expandOf sig a.toNat).map (ofList 6348))) Qexp := by
  have hr : (sigRho sig).length = 16 := by simp [sigRho, slice, hsig]
  have hst := symRun_sound blk0 codeAt_0 s hpc (by simp only [blk0.res, rv_simp])
  rw [show blk0.res.cycles = 13 by kernel_rfl] at hst
  refine Sign.Sim.steps hst ?_
  set s1 := blk0.res.toState s with hs1
  have e1 : fetch image s1 = some (.base .ECALL) :=
    symRun_ecall blk0 codeAt_0 s (by simp only [blk0.res, rv_simp]) rfl
  have x5 : s1.getReg .x5 = 0 := by simp only [hs1, blk0.res, rv_simp, h5]
  have x10 : s1.getReg .x10 = BitVec.ofNat 64 32 := by simp only [hs1, blk0.res, rv_simp]
  have x11 : s1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [hs1, blk0.res, rv_simp]
  have x12 : s1.getReg .x12 = BitVec.ofNat 64 352 := by simp only [hs1, blk0.res, rv_simp]
  have hv : hashArgumentsValid s1 = true :=
    hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hq := start_hash s (sigRho sig) msg hr hmsg hrho hm
  have hb : (fmt (digestInput (sigRho sig) msg)).blocks = 1 :=
    blocks_fmt_digest _ ⟨by simp [digestInput, thInput, hr, hmsg, length_tweak, P, zeros], rfl⟩
  have := Sign.Sim.query_bind (W := 15000) (f := fun a => (pure ((expandOf sig a.toNat).map (ofList 6348)) :
      OracleComp HashSpec _)) (Q := Qexp) e1 x5 hv hq (fun a => ?_)
  · rw [hb] at this; exact this
  set s2 := writeHash s1 a with hs2
  -- memory of `s2` above `0x40` outside `DO`
  have hmem : ∀ x : Nat, x < 2 ^ 64 → 0x40 ≤ x → (x < 0x160 ∨ 0x180 ≤ x) →
      s2.getMem (BitVec.ofNat 64 x) = s.getMem (BitVec.ofNat 64 x) := by
    intro x hx h1 h2
    rw [hs2, writeHash_getMem_frame s1 a 352 x x12 (by norm_num) hx (by omega), hs1, start_mem s x hx h1]
  have hbyte : ∀ x : Nat, x < 2 ^ 64 → 0x40 ≤ x → (x < 0x160 ∨ 0x180 ≤ x) →
      s2.getByte (BitVec.ofNat 64 x) = s.getByte (BitVec.ofNat 64 x) := by
    intro x hx h1 h2
    rw [getByte_ofNat _ _ hx, getByte_ofNat _ _ hx, hmem _ (by omega) (by omega) (by omega)]
  refine Sim.of_run (post_hash a sig hsig s2 ?_ ?_ ?_ ?_)
  · rw [hs2, writeHash_pc, hs1]; simp only [blk0.res, rv_simp]; rfl
  · intro i hi
    rw [hs2, writeHash_getMem_ofNat s1 a 352 _ x12 (by norm_num) (by omega)]
    interval_cases i <;> simp
  · intro j hj; rw [hbyte _ (by omega) (by omega) (by omega)]; exact hsok j hj
  · intro x h1 h2; rw [hbyte _ (by omega) (by omega) (by omega)]; exact hz x h1 h2



theorem expandRef_eq (m : Message) (pk : PublicKey) (σ : Bytes 6100) :
    expandRef m pk σ = (liftM (HashSpec.query (fmt (digestInput (sigRho (toList σ)) (toList m)))) :
      OracleComp HashSpec _) >>= fun a => pure ((expandOf (toList σ) a.toNat).map (ofList 6348)) := by
  simp only [expandRef, expandList, digest, H, bind_assoc, pure_bind]

theorem sI_words_sig (m : Message) (pk : PublicKey) (σ : Bytes 6100) :
    (sI m pk σ).readWords (BitVec.ofNat 64 0x3300) 2 = wordsOf (sigRho (toList σ)) := by
  have hl : (toList σ).length = 6100 := by simp [toList, length_bytes]
  apply readWords_of_bytes _ _ _ _ (by simp [sigRho, slice, hl]) (by norm_num) (by norm_num)
  intro j hj
  rw [sI_getByte _ _ _ _ (by omega), if_pos (by omega), sigRho, getD_slice' _ _ _ _ (by omega)]
  simp [toList]

theorem sI_words_msg (m : Message) (pk : PublicKey) (σ : Bytes 6100) :
    (sI m pk σ).readWords (BitVec.ofNat 64 0x40) 4 = wordsOf (toList m) := by
  apply readWords_of_bytes _ _ _ _ (by simp [toList, length_bytes]) (by norm_num) (by norm_num)
  intro j hj
  rw [sI_getByte _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_pos (by omega)]
  simp [toList]

theorem sim_sI (m : Message) (pk : PublicKey) (σ : Bytes 6100) :
    Sign.Sim image (sI m pk σ) (13 + (8 + 15000)) (expandRef m pk σ) Qexp := by
  rw [expandRef_eq]
  have hl : (toList σ).length = 6100 := by simp [toList, length_bytes]
  refine expand_sim (toList σ) (toList m) hl (by simp [toList, length_bytes]) (sI m pk σ) (sI_pc m pk σ)
    (sI_getReg m pk σ .x5 (by decide)) (sI_words_sig m pk σ) (sI_words_msg m pk σ) ?_ ?_
  · intro j hj; rw [sI_getByte _ _ _ _ (by omega), if_pos (by omega)]; simp [toList]
  · intro a h1 h2; rw [sI_getByte _ _ _ _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem qexp_halt (r : Option (Bytes 6348)) (t : MachineState) (h : Qexp r t) :
    fetch (submission.image .expand) t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
      id r = if t.getReg .x10 = 0 then some (readOutput submission.sizes submission.layout .expand t) else none :=
  ⟨h.1, h.2.1, h.2.2⟩

/-- **expand refines `expandRef`** (value, oracle calls, compressions; the `Budget.RefinesCounts`
form with `F = id`). -/
theorem expand_refines_counts (m : Message) (pk : PublicKey) (σ : Bytes 6100) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .expand (m, pk, σ) =
      (fun p => (p.1, p.2.1, p.2.2)) <$> Sign.countBoth (expandRef m pk σ) :=
  Sign.Sim.run_eq submission .expand (m, pk, σ) (initialState_eq m pk σ) (sim_sI m pk σ)
    (by norm_num [CYCLE_LIMIT]) id (fun a t h => qexp_halt a t h)

/-- **expand refines `expandRef`**: value and number of oracle calls. -/
theorem expand_refines (m : Message) (pk : PublicKey) (σ : Bytes 6100) :
    (fun r => (r.value, r.hashCalls)) <$> submission.run .expand (m, pk, σ) =
      (fun p => (p.1, p.2)) <$> countCalls (expandRef m pk σ) := by
  have h := congrArg (fun x => (fun t => (t.1, t.2.1)) <$> x) (expand_refines_counts m pk σ)
  simp only [Functor.map_map] at h
  rw [h, ← Sign.countBoth_calls, Functor.map_map]; rfl

/-- The compression count of every run is `1`. -/
theorem countBlocks_expandRef (m : Message) (pk : PublicKey) (σ : Bytes 6100) :
    countBlocks (expandRef m pk σ) = (fun r => (r, 1)) <$> expandRef m pk σ := by
  have hr : (sigRho (toList σ)).length = 16 := by simp [sigRho, slice, toList, length_bytes]
  have hml : (toList m).length = 32 := by simp [toList, length_bytes]
  have hb : (fmt (digestInput (sigRho (toList σ)) (toList m))).blocks = 1 :=
    blocks_fmt_digest _ ⟨by simp only [digestInput, thInput, List.length_append, length_tweak, P, zeros,
      List.length_replicate, hr, hml], rfl⟩
  rw [expandRef_eq]
  unfold countBlocks
  rw [countWith_bind, countWith_query]
  simp only [map_bind, bind_map_left, countWith_pure, map_pure, Nat.add_zero, hb]

/-- **expand compressions**: value and compressions (one compression on every path). -/
theorem expand_blocks (m : Message) (pk : PublicKey) (σ : Bytes 6100) :
    (fun r => (r.value, r.hashCompressions)) <$> submission.run .expand (m, pk, σ) =
      (fun r => (r, 1)) <$> expandRef m pk σ := by
  have h := congrArg (fun x => (fun t => (t.1, t.2.2)) <$> x) (expand_refines_counts m pk σ)
  simp only [Functor.map_map] at h
  rw [h, ← countBlocks_expandRef, ← Sign.countBoth_blocks]
  exact Functor.map_map (fun p : Option (Bytes 6348) × Nat × Nat => (p.1, p.2.1, p.2.2))
    (fun t : Option (Bytes 6348) × Nat × Nat => (t.1, t.2.2)) _

/-- **expand terminates**: under every oracle, every run finishes in fewer than `2^32` cycles. -/
theorem expand_terminates (hash : Hash) (m : Message) (pk : PublicKey)
    (σ : Bytes 6100) :
    (submission.runWith hash .expand (m, pk, σ)).finished = true ∧
      (submission.runWith hash .expand (m, pk, σ)).cycles < CYCLE_LIMIT := by
  have := Sign.Sim.runWith submission .expand (m, pk, σ) (initialState_eq m pk σ) (sim_sI m pk σ)
    (by norm_num [CYCLE_LIMIT]) (fun a t h => ⟨h.1, h.2.1⟩) hash
  exact ⟨this.1, lt_of_le_of_lt this.2 (by norm_num [CYCLE_LIMIT])⟩

/-- Every run (every oracle) takes at most 15022 cycles (honest runs: about 10.2k .. 10.5k). -/
theorem expand_cycles_le (hash : Hash) (m : Message) (pk : PublicKey) (σ : Bytes 6100) :
    (submission.runWith hash .expand (m, pk, σ)).cycles ≤ 15022 :=
  (Sign.Sim.runWith submission .expand (m, pk, σ) (initialState_eq m pk σ) (sim_sI m pk σ)
    (by norm_num [CYCLE_LIMIT]) (fun a t h => ⟨h.1, h.2.1⟩) hash).2


end SigGolfCandidate.Expand
