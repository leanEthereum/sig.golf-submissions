import SigGolfCandidate.Verify.Layers

/-! # The final comparison with the public key -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

def cmpAcc : PRes :=
  ⟨⟨((((RegFile.withKnown globK).set .x1 (ldE 392)).set .x2 (ldE 168)).set .x5 (cw 1)).set .x10 (cw 0),
    [], []⟩, pcOf 20042, true, 8, 8, [⟨.ne, ldE 392, ldE 168, false⟩, ⟨.ne, ldE 384, ldE 160, false⟩]⟩
def cmpRej1 : PRes :=
  ⟨⟨((((RegFile.withKnown globK).set .x1 (ldE 384)).set .x2 (ldE 160)).set .x5 (cw 1)).set .x10 (cw 1),
    [], []⟩, pcOf 20045, true, 5, 5, [⟨.ne, ldE 384, ldE 160, true⟩]⟩
def cmpRej2 : PRes :=
  ⟨⟨((((RegFile.withKnown globK).set .x1 (ldE 392)).set .x2 (ldE 168)).set .x5 (cw 1)).set .x10 (cw 1),
    [], []⟩, pcOf 20045, true, 8, 8, [⟨.ne, ldE 392, ldE 168, true⟩, ⟨.ne, ldE 384, ldE 160, false⟩]⟩

theorem cmp_runs :
    runAt globK [] 20034 [false, false] = some cmpAcc ∧ runAt globK [] 20034 [true] = some cmpRej1 ∧
    runAt globK [] 20034 [false, true] = some cmpRej2 := by
  refine ⟨optBeq_eq ?_, optBeq_eq ?_, optBeq_eq ?_⟩ <;> decide +kernel

theorem leNat_inj : ∀ (l1 l2 : List Byte), l1.length = l2.length → leNat l1 = leNat l2 → l1 = l2
  | [], [], _, _ => rfl
  | a :: l1, b :: l2, hl, h => by
    simp only [leNat] at h
    have ha := a.isLt; have hb := b.isLt
    have h1 : a.toNat = b.toNat := by omega
    have h2 : leNat l1 = leNat l2 := by omega
    rw [BitVec.eq_of_toNat_eq h1, leNat_inj l1 l2 (by simpa using hl) h2]
  | [], _ :: _, hl, _ => by simp at hl
  | _ :: _, [], hl, _ => by simp at hl

theorem w64_inj (l1 l2 : List Byte) (h1 : l1.length = 8) (h2 : l2.length = 8) :
    w64 l1 = w64 l2 ↔ l1 = l2 := by
  constructor
  · intro h
    have := congrArg BitVec.toNat h
    rw [w64_toNat _ (by omega), w64_toNat _ (by omega)] at this
    exact leNat_inj _ _ (by omega) this
  · intro h; rw [h]

theorem val_eq_iff (M P : Val) (hM : M.length = 16) (hP : P.length = 16) :
    M = P ↔ vw0 M = w64 (P.take 8) ∧ vw1 M = w64 (P.drop 8) := by
  unfold vw0 vw1
  rw [w64_inj _ _ (by simp; omega) (by simp; omega), w64_inj _ _ (by simp; omega) (by simp; omega)]
  constructor
  · intro h; rw [h]; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← List.take_append_drop 8 M, ← List.take_append_drop 8 P, h1, h2]

def FinalIn (wl pk : List Byte) (idx : Nat) (M : Val) (s : MachineState) : Prop :=
  ∃ u a, FoldEndL ⟨wl, pk, 0, idx⟩ u ∧ s = writeHash u a ∧ M = answerBytes 16 a

theorem compare_good (wl pk : List Byte) (hpk : pk.length = 16) (idx : Nat) (M : Val)
    (s : MachineState) (hs : FinalIn wl pk idx M s) : Good s 9 9 (pure (M == pk, 0)) := by
  obtain ⟨u, a, ⟨s0, ⟨hG, hK, hF, hpc, -, -⟩, -, -, -⟩, rfl, rfl⟩ := hs
  have hdst : (layFC ⟨wl, pk, 0, idx⟩).dst = 0x180 := by simp [layFC]
  have h12 : u.getReg .x12 = BitVec.ofNat 64 0x180 := by
    rw [← hdst]
    exact hK (.x12, _) (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (List.mem_singleton_self _))))
  have hG' := Glob_writeHash hG a _ h12 (by decide)
  have hK' : KnownOK globK (writeHash u a) := fun p hp => by
    rw [writeHash_getReg]; exact hK p (List.mem_append_left _ hp)
  have hpc' : (writeHash u a).pc = pcOf 20034 := by
    rw [writeHash_pc, hpc, pcOf_add4]; simp [layFC]; decide
  have m0 : (writeHash u a).getMem (BitVec.ofNat 64 384) = vw0 (answerBytes 16 a) :=
    (writeHash_at0 _ a _ h12 (by omega)).trans (vw0_answer a).symm
  have m1 : (writeHash u a).getMem (BitVec.ofNat 64 392) = vw1 (answerBytes 16 a) :=
    (writeHash_at8 _ a 0x180 h12 (by omega)).trans (vw1_answer a).symm
  have p0 : (writeHash u a).getMem (BitVec.ofNat 64 160) = w64 (pk.take 8) := hG'.2.2.1.1
  have p1 : (writeHash u a).getMem (BitVec.ofNat 64 168) = w64 (pk.drop 8) := hG'.2.2.1.2
  have heq := val_eq_iff (answerBytes 16 a) pk (by simp) hpk
  obtain ⟨r1, r2, r3⟩ := cmp_runs
  by_cases e0 : vw0 (answerBytes 16 a) = w64 (pk.take 8)
  · by_cases e1 : vw1 (answerBytes 16 a) = w64 (pk.drop 8)
    · obtain ⟨hst, hec⟩ := run_post' r1 rfl _ hpc' hK' (by
        intro b hb
        simp only [cmpAcc, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl <;>
          simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, m0, m1, p0, p1, e0, e1, bne_self_eq_false])
      have hb : (answerBytes 16 a == pk) = true := beq_iff_eq.mpr (heq.mpr ⟨e0, e1⟩)
      have := Good.steps hst (Good.halt (hec rfl) rfl)
      rw [show (cmpAcc.toState (writeHash u a)).getReg .x10 = 0 from rfl] at this
      rw [hb]; exact this.mono (by simp [cmpAcc]) (by simp [cmpAcc])
    · obtain ⟨hst, hec⟩ := run_post' r3 rfl _ hpc' hK' (by
        intro b hb
        simp only [cmpRej2, List.mem_cons, List.not_mem_nil, or_false] at hb
        rcases hb with rfl | rfl
        · simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, m1, p1]; simpa using e1
        · simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, m0, p0, e0, bne_self_eq_false])
      have hb : (answerBytes 16 a == pk) = false := by
        rw [beq_eq_false_iff_ne]; intro h; exact e1 (heq.mp h).2
      have := Good.steps hst (Good.reject (hec rfl) rfl rfl)
      rw [hb]; exact this.mono (by simp [cmpRej2]) (by simp [cmpRej2])
  · obtain ⟨hst, hec⟩ := run_post' r2 rfl _ hpc' hK' (by
      intro b hb
      simp only [cmpRej1, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, m0, p0]; simpa using e0)
    have hb : (answerBytes 16 a == pk) = false := by
      rw [beq_eq_false_iff_ne]; intro h; exact e0 (heq.mp h).1
    have := Good.steps hst (Good.reject (hec rfl) rfl rfl)
    rw [hb]; exact this.mono (by simp [cmpRej1]) (by simp [cmpRej1])

/-! ## All layers -/

def Kfin (pk : List Byte) : Option Val → OracleComp HashSpec Obs
  | none => pure (false, 0)
  | some root => pure (root == pk, 0)

def InLayer (wl pk : List Byte) (idx : Nat) : Nat → Val → MachineState → Prop
  | 0 => FinalIn wl pk idx
  | n + 1 => LayerIn ⟨wl, pk, n, idx⟩

def layersCost : Nat → Nat
  | 0 => 9
  | n + 1 => layersCost n + layerCost n

theorem layers_good (wl pk : List Byte) (hpk : pk.length = 16) (idx : Nat) (hidx : idx < 2 ^ 34)
    (hwl : wl.length = 7756) :
    ∀ n, n ≤ 7 → ∀ M s, InLayer wl pk idx n M s →
      Good s (5000 * n + 9) (layersCost n) (cc (verifyLayers wl idx n M) (Kfin pk)) := by
  intro n
  induction n with
  | zero =>
    intro _ M s hs
    simp only [verifyLayers, cc_pure, Kfin, layersCost]
    exact compare_good wl pk hpk idx M s hs
  | succ n ih =>
    intro hn M s hs
    rw [verifyLayers_succ, cc_bind]
    have hL : (⟨wl, pk, n, idx⟩ : LCtx).ok := ⟨show n < 7 by omega, hidx, hwl⟩
    have := layer_good ⟨wl, pk, n, idx⟩ hL M
      (fun o => cc (match o with
        | none => pure none
        | some r => verifyLayers wl idx n r) (Kfin pk)) (by simp [Kfin])
      (5000 * n + 9) (layersCost n) (by
        intro a u hu
        simp only []
        apply ih (by omega)
        cases n with
        | zero => exact ⟨u, a, hu, rfl, rfl⟩
        | succ m => exact foldEnd_layerIn wl pk (m + 1) idx (by omega) (by omega) u hu a) s hs
    exact this.mono (by omega) (by dsimp only; simp only [layersCost]; omega)

end SigGolfCandidate.Verify
