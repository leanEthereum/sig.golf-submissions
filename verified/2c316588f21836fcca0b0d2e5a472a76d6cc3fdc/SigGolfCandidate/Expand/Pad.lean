import SigGolfCandidate.Expand.SchedRun

/-!
# `expand`: the zero check of the unused auth slots (`pad_loop`, instructions 132 .. 138)

From the first unread auth slot (`t4 = SIG + 256 + 16 n`, `n` = number of reads) to the first layer
(`SIG + 2176`), every dword must be zero (`PadOK sig n`), else HALT(1).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref


theorem word_zero_of_bytes (w : Word) (h : ∀ k < 8, extractByte w k = 0) : w = 0 := by
  apply BitVec.eq_of_getLsbD_eq; intro i hi
  have := congrArg (fun b => b.getLsbD (i % 8)) (h (i / 8) (by omega))
  simp only [extractByte, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_zero] at this
  rw [show i / 8 * 8 + i % 8 = i by omega] at this
  simp at this
  simpa using this (by omega)



/-- The unused auth slots `n .. 119` of the signature are zero. -/
def PadOK (sig : List Byte) (n : Nat) : Prop := ∀ j < 2176, 256 + 16 * n ≤ j → sig.getD j 0 = 0


/-- Pad loop invariant (`m` dwords left). -/
def PadInv (sig : List Byte) (n : Nat) (u0 : MachineState) (m : Nat) (v : MachineState) : Prop :=
  m ≤ 240 - 2 * n ∧ ((Final none v ∧ ¬ PadOK sig n) ∨
    (v.pc = pcOf 134 ∧ v.getReg .x29 = BitVec.ofNat 64 (0x3B80 - 8 * m) ∧
      v.getReg .x25 = BitVec.ofNat 64 0x3B80 ∧ (∀ a, v.getMem a = u0.getMem a) ∧
      ∀ j, 256 + 16 * n ≤ j → j < 2176 - 8 * m → sig.getD j 0 = 0))

theorem pad_body (sig : List Byte) (t0 u0 : MachineState) (hsig : SigOK t0 sig) (hfr : Frame t0 u0 SW)
    (n : Nat) (hn : n ≤ 120) (m : Nat) (v : MachineState) (h : PadInv sig n u0 (m + 1) v) :
    Run v 5 (PadInv sig n u0 m) := by
  obtain ⟨hm, hf | ⟨vpc, v29, v25, vm, hz⟩⟩ := h
  · exact Run.done' ⟨by omega, Or.inl hf⟩
  refine (Run.blk blk134 codeAt_134 vpc (by simp only [blk134.res, rv_simp]) (B := 4) ?_).mono
    (by rw [show blk134.res.cycles = 1 from rfl]) (fun _ h => h)
  set v1 := blk134.res.toState v with hv1
  have p1 : v1.pc = pcOf 135 := by
    simp only [hv1, blk134.res, rv_simp, v29, v25]; ex_bvsimp [ofNat_beq_ofNat]; simp <;> omega
  have r1 : RegsEq v v1 [] := by regs_eq
  have hobl : blk135.res.obligs v1 := by
    simp only [blk135.res, rv_simp, r1.get .x29 List.not_mem_nil, v29]; ex_bvsimp [accessValid_ofNat]; omega
  refine (Run.blk blk135 codeAt_135 p1 hobl (B := 2) ?_).mono
    (by rw [show blk135.res.cycles = 2 from rfl]) (fun _ h => h)
  set v2 := blk135.res.toState v1 with hv2
  set d := 2176 - 8 * (m + 1) with hd
  have hw : v1.getMem (BitVec.ofNat 64 (0x3B80 - 8 * (m + 1))) = t0.getMem (BitVec.ofNat 64 (0x3300 + d)) := by
    rw [toState_getMem_nil rfl, vm, hfr _ (by omega) (by unfold SW; omega)]; congr 2; omega
  have hbytes : ∀ k < 8, extractByte (t0.getMem (BitVec.ofNat 64 (0x3300 + d))) k = sig.getD (d + k) 0 :=
    fun k hk => sig_dword_byte hsig d k (by omega) hk (by omega)
  by_cases hzero : ∀ k < 8, sig.getD (d + k) 0 = 0
  · have hw0 : t0.getMem (BitVec.ofNat 64 (0x3300 + d)) = 0 :=
      word_zero_of_bytes _ (fun k hk => by rw [hbytes k hk, hzero k hk])
    have p2 : v2.pc = pcOf 137 := by
      simp only [hv2, blk135.res, rv_simp, r1.get .x29 List.not_mem_nil, v29]; (try ex_bvsimp [])
      rw [hw, hw0]; rfl
    refine Run.of (symRun_sound blk137 codeAt_137 v2 p2 (by simp only [blk137.res, rv_simp])) (le_refl _) ?_
    refine ⟨by omega, Or.inr ⟨by simp only [blk137.res, rv_simp], ?_, ?_, ?_, ?_⟩⟩
    · simp only [blk137.res, rv_simp, hv2, blk135.res, r1.get .x29 List.not_mem_nil, v29]; ex_bvsimp []
      exact ofNat_congr (by omega)
    · simp only [blk137.res, rv_simp, hv2, blk135.res, r1.get .x25 List.not_mem_nil, v25]
    · intro a; rw [toState_getMem_nil rfl, hv2, toState_getMem_nil rfl, toState_getMem_nil rfl, vm]
    · intro j h1 h2
      by_cases hj : j < 2176 - 8 * (m + 1)
      · exact hz j h1 hj
      · have := hzero (j - d) (by omega); rwa [show d + (j - d) = j by omega] at this
  · have hnz : t0.getMem (BitVec.ofNat 64 (0x3300 + d)) ≠ 0 := by
      intro h0; apply hzero; intro k hk; rw [← hbytes k hk, h0]; simp [extractByte]
    have p2 : v2.pc = pcOf 284 := by
      simp only [hv2, blk135.res, rv_simp, r1.get .x29 List.not_mem_nil, v29]; (try ex_bvsimp [])
      rw [hw]; simp only [ofNat_bne_ofNat, bne_iff_ne, ne_eq]; simp; exact hnz
    refine (run_fail v2 p2).mono (le_refl _) (fun w hw => ⟨by omega, Or.inl ⟨hw, fun hp => hzero fun k hk => ?_⟩⟩)
    exact hp (d + k) (by omega) (by omega)

theorem pad_run (sig : List Byte) (t0 u : MachineState) (hsig : SigOK t0 sig) (hfr : Frame t0 u SW)
    (hpc : u.pc = pcOf 132) (n : Nat) (hn : n ≤ 120) (h29 : u.getReg .x29 = BitVec.ofNat 64 (0x3400 + 16 * n)) :
    Run u (2 + (240 - 2 * n) * 5 + 1) (fun v => (PadOK sig n → v.pc = pcOf 139 ∧ ∀ a, v.getMem a = u.getMem a) ∧
      (¬ PadOK sig n → Final none v)) := by
  have hst := symRun_sound blk132 codeAt_132 u hpc (by simp only [blk132.res, rv_simp])
  rw [show blk132.res.cycles = 2 by kernel_rfl] at hst
  refine (Run.steps hst (B := (240 - 2 * n) * 5 + 1) ?_).mono (by omega) (fun _ h => h)
  set u1 := blk132.res.toState u with hu1
  have h0 : PadInv sig n u (240 - 2 * n) u1 := by
    refine ⟨le_refl _, Or.inr ⟨by simp only [hu1, blk132.res, rv_simp], ?_, by simp only [hu1, blk132.res, rv_simp],
      toState_getMem_nil rfl u, fun j h1 h2 => by omega⟩⟩
    simp only [hu1, blk132.res, rv_simp, h29]; exact ofNat_congr (by omega)
  have hl := Run.loop (PadInv sig n u) 5 (pad_body sig t0 u hsig hfr n hn) (240 - 2 * n) u1 h0
  refine Run.bind (B₂ := 1) hl (fun v ⟨_, hv⟩ => ?_)
  rcases hv with ⟨hf, hnp⟩ | ⟨vpc, v29, v25, vm, hz⟩
  · exact Run.done' ⟨fun hp => absurd hp hnp, fun _ => hf⟩
  · refine Run.of (symRun_sound blk134 codeAt_134 v vpc (by simp only [blk134.res, rv_simp])) (le_refl _) ?_
    have hp : PadOK sig n := fun j h2 h1 => hz j h1 (by omega)
    refine ⟨fun _ => ⟨?_, fun a => by rw [toState_getMem_nil rfl, vm]⟩, fun h => absurd hp h⟩
    simp only [blk134.res, rv_simp, v29, v25]; simp


end SigGolfCandidate.Expand
