import SigGolfCandidate.Expand.Sort
import SigGolfCandidate.Expand.Sched

/-!
# `expand`: admissibility pass (`da_pass`, instructions 55 .. 71)

On the sorted keys `A` (leaf values `A s / 256`): for `s = 0 .. 13` fail on equal neighbours,
else add `bitLen (v_s xor v_{s+1})` (the `bitlen_1` do-while loop) to `SUM`; fail if
`SUM > 134` (octopus `SUM - 14 > 120`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem nat_xor_eq_zero (a b : Nat) : a ^^^ b = 0 ↔ a = b := by
  constructor
  · intro h0
    exact Nat.eq_of_testBit_eq (fun i => by
      have := congrArg (fun x => Nat.testBit x i) h0
      simp only [Nat.testBit_xor, Nat.zero_testBit] at this
      revert this; cases Nat.testBit a i <;> cases Nat.testBit b i <;> simp)
  · rintro rfl; exact Nat.xor_self a

theorem bitLen_half (y : Nat) (hy : 0 < y) : bitLen y = bitLen (y / 2) + 1 := by
  unfold bitLen
  rw [if_neg (by omega), Nat.log2_def y]
  by_cases h : 2 ≤ y
  · rw [if_pos h, if_neg (by omega)]
  · rw [if_neg h, if_pos (by omega)]

theorem bitLen_lt (y : Nat) : y < 2 ^ bitLen y := by
  unfold bitLen; split
  · simp_all
  · exact Nat.lt_log2_self

/-- The leaf value of key `A s`. -/
def lv (A : Nat → Nat) (s : Nat) : Nat := A s / 256

/-- The contribution of the pair `(s, s+1)`. -/
def pairBits (A : Nat → Nat) (s : Nat) : Nat := bitLen (lv A s ^^^ lv A (s + 1))

def pairSum (A : Nat → Nat) (n : Nat) : Nat := ((List.range n).map (pairBits A)).sum

/-- The program's admissibility test on the sorted keys. -/
def PassOK (A : Nat → Nat) : Prop := (∀ s < 14, lv A s ≠ lv A (s + 1)) ∧ pairSum A 14 ≤ 134

instance (A : Nat → Nat) : Decidable (PassOK A) := by unfold PassOK; infer_instance

/-- The `bitlen_1` loop (instructions 64 .. 66). -/
theorem bitlen1_loop : ∀ y, 0 < y → y < 2 ^ 64 → ∀ (u : MachineState) (c : Nat), u.pc = pcOf 64 →
    u.getReg .x9 = BitVec.ofNat 64 y → u.getReg .x15 = BitVec.ofNat 64 c → c + bitLen y < 2 ^ 64 →
    Run u (3 * bitLen y) (fun v => v.pc = pcOf 67 ∧ v.getReg .x15 = BitVec.ofNat 64 (c + bitLen y) ∧
      v.getReg .x8 = u.getReg .x8 ∧ ∀ a, v.getMem a = u.getMem a) := by
  intro y
  induction y using Nat.strong_induction_on with
  | _ y ih =>
    intro hy hy64 u c upc u9 u15 hc
    have hb := bitLen_half y hy
    refine (Run.blk blk64 codeAt_64 upc (by simp only [blk64.res, rv_simp]) (B := 3 * bitLen (y / 2)) ?_).mono
      (by rw [show blk64.res.cycles = 3 from rfl]; omega) (fun _ h => h)
    set v := blk64.res.toState u with hv
    have v9 : v.getReg .x9 = BitVec.ofNat 64 (y / 2) := by
      simp only [hv, blk64.res, rv_simp, u9]; ex_bvsimp []
    have v15 : v.getReg .x15 = BitVec.ofNat 64 (c + 1) := by
      simp only [hv, blk64.res, rv_simp, u15]; ex_bvsimp []
    have v8 : v.getReg .x8 = u.getReg .x8 := by simp only [hv, blk64.res, rv_simp]
    have vm : ∀ a, v.getMem a = u.getMem a := toState_getMem_nil rfl u
    have vpc : v.pc = if y / 2 = 0 then pcOf 67 else pcOf 64 := by
      simp only [hv, blk64.res, rv_simp, u9]; ex_bvsimp [ofNat_bne_ofNat]
      by_cases h : y / 2 = 0 <;> simp [h]
    by_cases h0 : y / 2 = 0
    · rw [if_pos h0] at vpc
      refine Run.done' ⟨vpc, ?_, v8, vm⟩
      rw [v15, hb, h0]; rfl
    · rw [if_neg h0] at vpc
      have := ih (y / 2) (by omega) (by omega) (by omega) v (c + 1) vpc v9 v15 (by omega)
      refine this.mono (le_refl _) (fun w ⟨h1, h2, h3, h4⟩ => ⟨h1, ?_, by rw [h3, v8], fun a => by rw [h4, vm]⟩)
      rw [h2, hb]; congr 1; omega

theorem lv_lt {A : Nat → Nat} (hlt : ∀ p < 15, A p < 2 ^ 22) {s : Nat} (hs : s < 15) : lv A s < 2 ^ 14 := by
  unfold lv; have := hlt s hs; omega

theorem pairBits_le {A : Nat → Nat} (hlt : ∀ p < 15, A p < 2 ^ 22) {s : Nat} (hs : s < 14) :
    pairBits A s ≤ 14 :=
  bitLen_le (Nat.xor_lt_two_pow (lv_lt hlt (by omega)) (lv_lt hlt (by omega)))

theorem pairSum_succ (A : Nat → Nat) (n : Nat) : pairSum A (n + 1) = pairSum A n + pairBits A n := by
  simp [pairSum, List.range_succ]

theorem pairSum_le {A : Nat → Nat} (hlt : ∀ p < 15, A p < 2 ^ 22) : ∀ n ≤ 14, pairSum A n ≤ 14 * n := by
  intro n
  induction n with
  | zero => intro _; simp [pairSum]
  | succ n ih => intro hn; rw [pairSum_succ]; have := pairBits_le hlt (s := n) (by omega); have := ih (by omega); omega

/-- Pass loop invariant (`k` pairs left). -/
def PassInv (A : Nat → Nat) (t0 : MachineState) (k : Nat) (u : MachineState) : Prop :=
  k ≤ 14 ∧ ((Final none u ∧ ¬ PassOK A) ∨
    ((∀ s < 14 - k, lv A s ≠ lv A (s + 1)) ∧ u.getReg .x15 = BitVec.ofNat 64 (pairSum A (14 - k)) ∧
      (∀ a, u.getMem a = t0.getMem a) ∧
      if k = 0 then u.pc = pcOf 70 else u.pc = pcOf 57 ∧ u.getReg .x8 = BitVec.ofNat 64 (14 - k)))

theorem pass_body (A : Nat → Nat) (hlt : ∀ p < 15, A p < 2 ^ 22) (t0 : MachineState) (hA : ArrOk t0 A)
    (k : Nat) (u : MachineState) (h : PassInv A t0 (k + 1) u) : Run u 52 (PassInv A t0 k) := by
  obtain ⟨hk, hfail | ⟨hd, u15, um, hpc⟩⟩ := h
  · exact Run.done' ⟨by omega, Or.inl hfail⟩
  rw [if_neg (Nat.succ_ne_zero k)] at hpc
  obtain ⟨upc, u8⟩ := hpc
  set s := 14 - (k + 1) with hsdef
  have hs : s < 14 := by omega
  have hobl : blk57.res.obligs u := by
    simp only [blk57.res, rv_simp, u8]; ex_bvsimp [accessValid_ofNat]; omega
  refine (Run.blk blk57 codeAt_57 upc hobl (B := 45) ?_).mono
    (by rw [show blk57.res.cycles = 7 from rfl]) (fun _ h => h)
  set v := blk57.res.toState u with hv
  have a0 : u.getMem (BitVec.ofNat 64 (s * 8 + 1760)) = BitVec.ofNat 64 (A s) := by
    rw [um, show s * 8 + 1760 = 0x6E0 + 8 * s by ring]; exact hA s (by omega)
  have a1 : u.getMem (BitVec.ofNat 64 (s * 8 + 1768)) = BitVec.ofNat 64 (A (s + 1)) := by
    rw [um, show s * 8 + 1768 = 0x6E0 + 8 * (s + 1) by ring]; exact hA (s + 1) (by omega)
  have hA0 := hlt s (by omega)
  have hA1 := hlt (s + 1) (by omega)
  have hl0 := lv_lt hlt (s := s) (by omega)
  have hl1 := lv_lt hlt (s := s + 1) (by omega)
  have hxl : lv A s ^^^ lv A (s + 1) < 2 ^ 14 := Nat.xor_lt_two_pow hl0 hl1
  have v9 : v.getReg .x9 = BitVec.ofNat 64 (lv A s ^^^ lv A (s + 1)) := by
    simp only [hv, blk57.res, rv_simp, u8]; ex_bvsimp []; rw [a0, a1]; ex_bvsimp [lv]
  have vpc : v.pc = if lv A s = lv A (s + 1) then pcOf 284 else pcOf 64 := by
    simp only [hv, blk57.res, rv_simp, u8]; ex_bvsimp []; rw [a0, a1]; ex_bvsimp [ofNat_beq_ofNat]
    rw [Nat.mod_eq_of_lt (a := A s / 256 ^^^ A (s + 1) / 256) (by have := hxl; unfold lv at this; omega)]
    change (if decide (lv A s ^^^ lv A (s + 1) = 0) = true then _ else _) = _
    by_cases h : lv A s = lv A (s + 1) <;> simp [h, nat_xor_eq_zero]
  have v15 : v.getReg .x15 = BitVec.ofNat 64 (pairSum A s) := by simp only [hv, blk57.res, rv_simp, u15]
  have v8 : v.getReg .x8 = BitVec.ofNat 64 s := by simp only [hv, blk57.res, rv_simp, u8]
  have vm : ∀ a, v.getMem a = t0.getMem a := fun a => by rw [toState_getMem_nil rfl, um]
  by_cases heq : lv A s = lv A (s + 1)
  · rw [if_pos heq] at vpc
    exact (run_fail v vpc).mono (by omega) (fun w hw => ⟨by omega, Or.inl ⟨hw, fun hp => hp.1 s hs heq⟩⟩)
  · rw [if_neg heq] at vpc
    have hy : 0 < lv A s ^^^ lv A (s + 1) := by
      rcases Nat.eq_zero_or_pos (lv A s ^^^ lv A (s + 1)) with h0 | h0
      · exact absurd ((nat_xor_eq_zero _ _).mp h0) heq
      · exact h0
    have hps := pairSum_le hlt s (by omega)
    have hpb : pairBits A s ≤ 14 := pairBits_le hlt hs
    have hbl := bitlen1_loop _ hy (by omega) v (pairSum A s) vpc v9 v15 (by unfold pairBits at hpb; omega)
    refine (Run.bind (B₂ := 3) hbl (fun w ⟨wpc, w15, w8, wm⟩ => ?_)).mono
      (by unfold pairBits at hpb; omega) (fun _ h => h)
    refine Run.of (symRun_sound blk67 codeAt_67 w wpc (by simp only [blk67.res, rv_simp])) (le_refl _) ?_
    set x := blk67.res.toState w with hx
    have x15 : x.getReg .x15 = BitVec.ofNat 64 (pairSum A (14 - k)) := by
      simp only [hx, blk67.res, rv_simp, w15]
      rw [show 14 - k = s + 1 by omega, pairSum_succ]; rfl
    have xm : ∀ a, x.getMem a = t0.getMem a := fun a => by rw [toState_getMem_nil rfl, wm, vm]
    have hd' : ∀ s' < 14 - k, lv A s' ≠ lv A (s' + 1) := by
      intro s' hs'
      by_cases h' : s' = s
      · subst h'; exact heq
      · exact hd s' (by omega)
    refine ⟨by omega, Or.inr ⟨hd', x15, xm, ?_⟩⟩
    have x8 : x.getReg .x8 = BitVec.ofNat 64 (s + 1) := by
      simp only [hx, blk67.res, rv_simp, w8, v8]; ex_bvsimp []
    have xpc : x.pc = if s + 1 = 14 then pcOf 70 else pcOf 57 := by
      simp only [hx, blk67.res, rv_simp, w8, v8]; ex_bvsimp [ofNat_bne_ofNat]
      by_cases h : s + 1 = 14 <;> simp [h] <;> omega
    by_cases hk0 : k = 0
    · rw [if_pos hk0, xpc, if_pos (by omega)]
    · rw [if_neg hk0, xpc, if_neg (by omega), x8, show 14 - k = s + 1 by omega]; exact ⟨rfl, rfl⟩

/-- The pass phase: from instruction 55 (sorted keys `A` in memory). -/
theorem pass_run (A : Nat → Nat) (hlt : ∀ p < 15, A p < 2 ^ 22) (t : MachineState) (tpc : t.pc = pcOf 55)
    (hA : ArrOk t A) :
    Run t (2 + 14 * 52 + 4) (fun u => if PassOK A then u.pc = pcOf 72 ∧ ∀ a, u.getMem a = t.getMem a
      else Final none u) := by
  refine (Run.blk blk55 codeAt_55 tpc (by simp only [blk55.res, rv_simp]) (B := 14 * 52 + 4) ?_).mono
    (by rw [show blk55.res.cycles = 2 from rfl]; try omega) (fun _ h => h)
  set t1 := blk55.res.toState t with ht1
  have h0 : PassInv A t 14 t1 := by
    refine ⟨le_refl _, Or.inr ⟨fun s hs => by omega, ?_, toState_getMem_nil rfl t, ?_⟩⟩
    · simp only [ht1, blk55.res, rv_simp]; rfl
    · rw [if_neg (by decide)]; exact ⟨by simp only [ht1, blk55.res, rv_simp], by simp only [ht1, blk55.res, rv_simp]⟩
  have hl := Run.loop (PassInv A t) 52 (pass_body A hlt t hA) 14 t1 h0
  refine Run.bind hl (fun u ⟨_, hu⟩ => ?_)
  rcases hu with ⟨hf, hnp⟩ | ⟨hd, u15, um, upc⟩
  · exact Run.done' (by beta_reduce; rw [if_neg hnp]; exact hf)
  · rw [if_pos rfl] at upc
    have hps := pairSum_le hlt 14 le_rfl
    refine (Run.blk blk70 codeAt_70 upc (by simp only [blk70.res, rv_simp]) (B := 2) ?_).mono
      (by rw [show blk70.res.cycles = 2 from rfl]) (fun _ h => h)
    set v := blk70.res.toState u with hv
    have vpc : v.pc = if pairSum A 14 ≤ 134 then pcOf 72 else pcOf 284 := by
      simp only [hv, blk70.res, rv_simp, u15]; ex_bvsimp []
      rw [ofNat_slt_ofNat _ _ (by norm_num) (by omega)]
      by_cases h : pairSum A 14 ≤ 134 <;> simp [h] <;> omega
    by_cases hp : pairSum A 14 ≤ 134
    · rw [if_pos hp] at vpc
      refine Run.done' ?_
      beta_reduce; rw [if_pos ⟨fun s hs => hd s (by omega), hp⟩]
      exact ⟨vpc, fun a => by rw [toState_getMem_nil rfl, um]⟩
    · rw [if_neg hp] at vpc
      exact (run_fail v vpc).mono (by norm_num) (fun _ h => by beta_reduce; rw [if_neg (fun h => hp h.2)]; exact h)

end SigGolfCandidate.Expand
