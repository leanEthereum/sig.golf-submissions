import SigGolfCandidate.Verify.FoldRuns

/-! # Partial specifications of path runs (only the registers of interest are pinned down) -/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

structure Spec where
  regs : List (Reg × E)
  mem : List (Addr × E)
  pc : Nat
  ecall : Bool
  steps : Nat
  brs : List Br
  spc : Option E := none

def regsB (r : PRes) (l : List (Reg × E)) : Bool := l.all fun p => E.beq (r.st.regs.get p.1) p.2

def specB (gk : List (Reg × Word)) (o : Option PRes) (sp : Spec) (post : List (Reg × Word))
    (keep : List Reg) : Bool :=
  match o with
  | none => false
  | some r =>
    regsB r sp.regs && listBeq pairBeq r.st.mem sp.mem && (sp.spc.isSome || r.pc.toNat == (pcOf sp.pc).toNat) &&
      r.ecall == sp.ecall && r.steps == sp.steps && r.cycles == sp.steps &&
      listBeq Br.beq r.brs sp.brs && optEBeq r.spc sp.spc && resOK gk r && knownB post r &&
      keepB keep r

theorem Glob_toState' {gk0 gk : List (Reg × Word)} {wl pk : List Byte} {s : MachineState}
    (hG : Glob gk0 wl pk s) (σ : SymState)
    (pc : Word) (hm : memOK σ.mem = true) (hr : regsOK gk σ.regs = true) :
    Glob gk wl pk (σ.toState s pc) := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  have fr : ∀ A, A < 2 ^ 64 → (0x800 ≤ A ∨ A ∈ pSlots ∨ A = 0xA0 ∨ A = 0xA8) →
      (σ.toState s pc).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hp
    rw [SymState.toState_getMem]
    exact memEval_frame s _ _ (memOK_ne hm s A hA hp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro p hp
    have := List.all_eq_true.mp hr p hp
    rw [SymState.toState_getReg, E.beq_eq this]; rfl
  · intro j hj
    rw [fr _ (by omega) (Or.inl (by omega))]; exact h2 j hj
  · exact ⟨(fr 0xA0 (by omega) (by simp)).trans h3.1, (fr 0xA8 (by omega) (by simp)).trans h3.2⟩
  · intro a ha
    have : a < 2 ^ 64 := by simp [pSlots] at ha; omega
    rw [fr a this (Or.inr (Or.inl ha))]; exact h4 a ha

/-- What a checked run gives on a concrete state. -/
structure SpecRes (gk : List (Reg × Word)) (sp : Spec) (post : List (Reg × Word)) (keep : List Reg)
    (s t : MachineState) : Prop where
  steps : Steps image s sp.steps sp.steps t
  ecall : sp.ecall = true → fetch image t = some (.base .ECALL)
  glob : ∀ gk0 wl pk, Glob gk0 wl pk s → Glob gk wl pk t
  known : KnownOK post t
  keep : ∀ x ∈ keep, t.getReg x = s.getReg x
  regs : ∀ p ∈ sp.regs, t.getReg p.1 = p.2.eval s
  mem : ∀ A, t.getMem A = memEval s sp.mem A
  pc : sp.spc = none → t.pc = pcOf sp.pc
  spc : ∀ e, sp.spc = some e → t.pc = e.eval s

theorem spec_run {gk known post : List (Reg × Word)} {stops : List Nat} {n : Nat} {dirs : List Dir}
    {sp : Spec} {keep : List Reg} (h : specB gk (runAt known stops n dirs) sp post keep = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s) (hbr : ∀ b ∈ sp.brs, b.holds s) :
    ∃ t, SpecRes gk sp post keep s t := by
  unfold specB at h
  split at h
  · cases h
  rename_i r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hregs, hmem⟩, hpc'⟩, hec⟩, hst⟩, hcy⟩, hbrs⟩, hspc⟩, hok⟩, hkn⟩, hkeep⟩ := h
  have hbrs' := listBeq_eq (fun _ _ => Br.beq_eq) hbrs
  have hmem' := listBeq_eq (fun _ _ => pairBeq_eq) hmem
  have hspc' := optEBeq_eq hspc
  obtain ⟨hst', hec', -⟩ := run_post hr hok s hpc hk (by rw [hbrs']; exact hbr)
  simp only [resOK, Bool.and_eq_true, List.isEmpty_iff] at hok
  refine ⟨r.toState s, ⟨?_, ?_, ?_, knownB_ok hkn s, keepB_ok hkeep s, ?_, ?_, ?_, ?_⟩⟩
  · rw [hcy, hst] at hst'; exact hst'
  · intro he; exact hec' (hec.trans he)
  · intro gk0 wl pk hG; exact Glob_toState' hG r.st _ hok.1.1 hok.1.2
  · intro p hp
    rw [PRes.toState_getReg, E.beq_eq (List.all_eq_true.mp hregs p hp)]
  · intro A; rw [PRes.toState_getMem, hmem']
  · intro hn
    rw [hn] at hpc'
    simp only [Option.isSome_none, Bool.false_or, beq_iff_eq] at hpc'
    rw [PRes.toState_pc _ _ (hspc'.trans hn), BitVec.eq_of_toNat_eq hpc']
  · intro e he; simp [PRes.toState, PRes.finalPc, hspc'.trans he]

end SigGolfCandidate.Verify
