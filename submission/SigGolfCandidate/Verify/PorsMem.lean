import SigGolfCandidate.Verify.Spec
import SigGolfCandidate.Verify.Common
import SigGolfCandidate.Verify.PorsTab

/-!
# The PORS phase: memory frame and checked runs with side conditions

During the PORS stack machine the constant data (public key, the leaf indices `PIND`, the tweak
words of the hash buffers CB, NB and of the 14 stack blocks, their zero `P` slots, the stack
guard) sits in memory written once by the setup. `GlobP gk s0 s` says that the constant registers
`gk` hold and that these words, the low halves of the tweak words `+8` (whose high halves are the
per-hash `j` fields) and the witness region are as in the reference state `s0` (the state after
the setup). Every PORS run is checked (`pspecB`) to write only below the witness, never to a
protected word, and to a half-protected word only by a `sw` into its high half (`memOKP`).

Unlike `specB`, `pspecB` allows the side conditions of accesses at symbolic addresses (the
stream pointer `FR`, the leaf index table): they are listed and must be proved by the caller.
-/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## Layout of the PORS phase -/

def aCB : Nat := 0xC0
def aNB : Nat := 0x1C0
def aEB : Nat := 0x100
/-- Stack block `i` (tweak address; its `Q` word at `-16`, `L` at `+32`, `R` at `+48`). -/
def PSB : Nat := 0x2A0
/-- `STK` of the empty stack; its `Q` word is the guard at `EMPTY - 16 = 0x240`. -/
def EMPTY : Nat := 0x250
def PIND : Nat := 0x780
/-- The number of witness doublewords the verifier may read (the stream reads up to 7000 bytes). -/
def NW : Nat := 880

def tbN : Nat := 0x1000 + 4 * ptabN
def tbL : Nat := 0x1000 + 4 * ptabL

/-- Constant registers of the PORS phase: `x5 = 0`, witness bases, `P1..P5`, `K14 = 2^14`,
`MASK = 2^14 - 1`, `a1 = 64`. -/
def gkP : List (Reg × Word) := baseK ++ [(.x25, 0x4000), (.x26, 0x3FFF), (.x11, 64)]

/-- Words never written in the PORS phase. -/
def protP : List Nat :=
  [0x10, 0x18, 0xA0, 0xA8, 0xC0, 0xD0, 0xD8, 0xF0, 0xF8, 0x110, 0x118, 0x1C0, 0x1D0, 0x1D8, 0x230,
    0x238, 0x240] ++
  (List.range 14).flatMap (fun i => [PSB + 80 * i, PSB + 80 * i + 16, PSB + 80 * i + 24]) ++
  (List.range 16).map (fun r => PIND + 8 * r)

/-- Tweak words `+8` whose low half (`tau mod 2^32 = idx mod 2^32`) is constant. -/
def halfP : List Nat := [0xC8, 0x1C8] ++ (List.range 14).map (fun i => PSB + 80 * i + 8)

def PFrame (s0 s : MachineState) : Prop :=
  (∀ a ∈ protP, s.getMem (BitVec.ofNat 64 a) = s0.getMem (BitVec.ofNat 64 a)) ∧
  (∀ a ∈ halfP, (s.getMem (BitVec.ofNat 64 a)).toNat % 2 ^ 32 = (s0.getMem (BitVec.ofNat 64 a)).toNat % 2 ^ 32) ∧
  (∀ j, j < NW → s.getMem (BitVec.ofNat 64 (0x800 + 8 * j)) = s0.getMem (BitVec.ofNat 64 (0x800 + 8 * j)))

def GlobP (gk : List (Reg × Word)) (s0 s : MachineState) : Prop :=
  (∀ p ∈ gk, s.getReg p.1 = p.2) ∧ PFrame s0 s

theorem PFrame.refl (s : MachineState) : PFrame s s := ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- A write of the high half of the word at `a` (`sw v, a + 4`). -/
def isHalfW (a : Nat) : E → Bool
  | .bin (.st .w 4) (.ld (.c k)) _ => k.toNat == a
  | _ => false

def memOKP (ws : SymMem) : Bool :=
  ws.all fun p => p.1.base.isNone && decide (p.1.off.toNat + 8 ≤ 0x800) &&
    !(protP.contains p.1.off.toNat) && (!(halfP.contains p.1.off.toNat) || isHalfW p.1.off.toNat p.2)

def safeDestP (d : Nat) : Bool :=
  decide (d % 8 = 0) && decide (d + 32 ≤ 0x800) &&
    (protP ++ halfP).all (fun q => decide (q + 8 ≤ d ∨ d + 32 ≤ q))

/-! ## Constant-address write lists -/

def memLook : SymMem → Nat → Option E
  | [], _ => none
  | (k, v) :: ws, A => if k.base.isNone && k.off.toNat == A then some v else memLook ws A

theorem memEval_look (s : MachineState) : ∀ (ws : SymMem) (A : Nat), A < 2 ^ 64 →
    (ws.all fun p => p.1.base.isNone) = true →
    memEval s ws (BitVec.ofNat 64 A) =
      match memLook ws A with
      | some v => v.eval s
      | none => s.getMem (BitVec.ofNat 64 A)
  | [], A, _, _ => rfl
  | (⟨b, off⟩, v) :: ws, A, hA, hc => by
    simp only [List.all_cons, Bool.and_eq_true] at hc
    obtain ⟨hb, hc⟩ := hc
    cases b with
    | some _ => simp at hb
    | none =>
      rw [memEval_cons]
      by_cases h : off.toNat = A
      · have : BitVec.ofNat 64 A = Addr.eval s ⟨none, off⟩ := by
          apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]; exact h.symm
        rw [if_pos this]
        simp [memLook, h]
      · have : BitVec.ofNat 64 A ≠ Addr.eval s ⟨none, off⟩ := by
          intro e; apply h; rw [show Addr.eval s ⟨none, off⟩ = off from rfl] at e
          rw [← e, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]
        rw [if_neg this]
        simp only [memLook, Option.isNone_none, Bool.true_and, beq_iff_eq, h, if_false]
        exact memEval_look s ws A hA hc

theorem memOKP_const {ws : SymMem} (h : memOKP ws = true) : (ws.all fun p => p.1.base.isNone) = true := by
  simp only [memOKP, List.all_eq_true, Bool.and_eq_true] at h ⊢
  intro p hp; exact (h p hp).1.1.1

theorem memLook_mem : ∀ {ws : SymMem} {A : Nat} {v : E}, memLook ws A = some v →
    ∃ p ∈ ws, p.1.base.isNone = true ∧ p.1.off.toNat = A ∧ p.2 = v
  | [], _, _, h => by simp [memLook] at h
  | (k, w) :: ws, A, v, h => by
    simp only [memLook] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact ⟨(k, w), List.mem_cons_self .., hc.1, hc.2, h⟩
    · obtain ⟨p, hp, h1⟩ := memLook_mem h
      exact ⟨p, List.mem_cons_of_mem _ hp, h1⟩

theorem merge_w4_low (w v : Word) : (StoreKind.merge .w w 4 v).toNat % 2 ^ 32 = w.toNat % 2 ^ 32 := by
  have := merge_w4_toNat w v
  rw [this]; omega

theorem memOKP_frame {ws : SymMem} (h : memOKP ws = true) (s : MachineState) :
    (∀ a ∈ protP, memEval s ws (BitVec.ofNat 64 a) = s.getMem (BitVec.ofNat 64 a)) ∧
    (∀ a ∈ halfP, (memEval s ws (BitVec.ofNat 64 a)).toNat % 2 ^ 32 = (s.getMem (BitVec.ofNat 64 a)).toNat % 2 ^ 32) ∧
    (∀ A, A < 2 ^ 64 → 0x800 ≤ A → memEval s ws (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A)) := by
  have hc := memOKP_const h
  simp only [memOKP, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true',
    Bool.or_eq_true] at h
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun A hA hA' => ?_⟩
  · have ha' : a < 2 ^ 64 := by simp [protP, PSB, PIND] at ha; omega
    rw [memEval_look s ws a ha' hc]
    split
    · rename_i v hv
      obtain ⟨p, hp, -, hoff, -⟩ := memLook_mem hv
      have := (h p hp).1.2
      rw [hoff] at this
      simp [List.contains_iff_mem, ha] at this
    · rfl
  · have ha' : a < 2 ^ 64 := by simp [halfP, PSB] at ha; omega
    rw [memEval_look s ws a ha' hc]
    split
    · rename_i v hv
      obtain ⟨p, hp, -, hoff, hv'⟩ := memLook_mem hv
      have h2 := (h p hp).2
      rw [hoff] at h2
      rcases h2 with h2 | h2
      · simp [List.contains_iff_mem, ha] at h2
      · subst hv'
        obtain ⟨k, w⟩ := p
        simp only at h2 hoff ⊢
        unfold isHalfW at h2
        split at h2
        · rename_i kk x
          simp only [beq_iff_eq] at h2
          have : kk = BitVec.ofNat 64 a := by
            apply BitVec.eq_of_toNat_eq; rw [h2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha']
          subst this
          exact merge_w4_low _ _
        · cases h2
    · rfl
  · rw [memEval_look s ws A hA hc]
    split
    · rename_i v hv
      obtain ⟨p, hp, -, hoff, -⟩ := memLook_mem hv
      have := (h p hp).1.1.2
      omega
    · rfl

theorem GlobP_toState {gk0 gk : List (Reg × Word)} {s0 s : MachineState} (hG : GlobP gk0 s0 s)
    (σ : SymState) (pc : Word) (hm : memOKP σ.mem = true) (hr : regsOK gk σ.regs = true) :
    GlobP gk s0 (σ.toState s pc) := by
  obtain ⟨-, h1, h2, h3⟩ := hG
  obtain ⟨f1, f2, f3⟩ := memOKP_frame hm s
  refine ⟨fun p hp => ?_, fun a ha => ?_, fun a ha => ?_, fun j hj => ?_⟩
  · have := List.all_eq_true.mp hr p hp
    rw [SymState.toState_getReg, E.beq_eq this]; rfl
  · rw [SymState.toState_getMem, f1 a ha]; exact h1 a ha
  · rw [SymState.toState_getMem, f2 a ha]; exact h2 a ha
  · rw [SymState.toState_getMem, f3 _ (by unfold NW at hj; omega) (by omega)]; exact h3 j hj

theorem GlobP_writeHash {gk : List (Reg × Word)} {s0 s : MachineState} (hG : GlobP gk s0 s)
    (ans : BitVec 256) (d : Nat) (hd : s.getReg .x12 = BitVec.ofNat 64 d)
    (hsafe : safeDestP d = true) : GlobP gk s0 (writeHash s ans) := by
  obtain ⟨h0, h1, h2, h3⟩ := hG
  simp only [safeDestP, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hsafe
  obtain ⟨⟨-, hd1⟩, hd2⟩ := hsafe
  have fr : ∀ A, A < 2 ^ 64 → (A + 8 ≤ d ∨ d + 32 ≤ A) →
      (writeHash s ans).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA hp
    rw [writeHash_getMem_ofNat s ans d A hd hA (by omega)]
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  refine ⟨fun p hp => by rw [writeHash_getReg]; exact h0 p hp, fun a ha => ?_, fun a ha => ?_,
    fun j hj => ?_⟩
  · have := hd2 a (List.mem_append_left _ ha)
    have : a < 2 ^ 64 := by simp [protP, PSB, PIND] at ha; omega
    rw [fr a this (by omega)]; exact h1 a ha
  · have := hd2 a (List.mem_append_right _ ha)
    have : a < 2 ^ 64 := by simp [halfP, PSB] at ha; omega
    rw [fr a this (by omega)]; exact h2 a ha
  · rw [fr _ (by unfold NW at hj; omega) (by omega)]; exact h3 j hj

theorem Known_writeHash' {known : List (Reg × Word)} {s : MachineState} (h : KnownOK known s)
    (a : BitVec 256) : KnownOK known (writeHash s a) := by
  intro p hp; rw [writeHash_getReg]; exact h p hp

/-! ## Checked runs with side conditions -/

def pspecB (gk : List (Reg × Word)) (o : Option PRes) (sp : Spec) (obl : List Oblig)
    (post : List (Reg × Word)) (keep : List Reg) : Bool :=
  match o with
  | none => false
  | some r =>
    regsB r sp.regs && listBeq pairBeq r.st.mem sp.mem &&
      (sp.spc.isSome || r.pc.toNat == (pcOf sp.pc).toNat) &&
      r.ecall == sp.ecall && r.steps == sp.steps && r.cycles == sp.steps &&
      listBeq Br.beq r.brs sp.brs && optEBeq r.spc sp.spc && listBeq Oblig.beq r.st.obl obl &&
      memOKP r.st.mem && regsOK gk r.st.regs && knownB post r && keepB keep r

/-- What a checked PORS run gives on a concrete state. -/
structure PSpecRes (gk : List (Reg × Word)) (sp : Spec) (post : List (Reg × Word)) (keep : List Reg)
    (s t : MachineState) : Prop where
  steps : Steps image s sp.steps sp.steps t
  ecall : sp.ecall = true → fetch image t = some (.base .ECALL)
  glob : ∀ gk0 s0, GlobP gk0 s0 s → GlobP gk s0 t
  known : KnownOK post t
  keep : ∀ x ∈ keep, t.getReg x = s.getReg x
  regs : ∀ p ∈ sp.regs, t.getReg p.1 = p.2.eval s
  mem : ∀ A, t.getMem A = memEval s sp.mem A
  memc : memOKP sp.mem = true
  pc : sp.spc = none → t.pc = pcOf sp.pc
  spc : ∀ e, sp.spc = some e → t.pc = e.eval s

theorem pspec_run {gk known post : List (Reg × Word)} {stops : List Nat} {n : Nat} {dirs : List Dir}
    {sp : Spec} {obl : List Oblig} {keep : List Reg}
    (h : pspecB gk (runAt known stops n dirs) sp obl post keep = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ sp.brs, b.holds s) (hob : ∀ o ∈ obl, o.holds s) :
    ∃ t, PSpecRes gk sp post keep s t := by
  unfold pspecB at h
  split at h
  · cases h
  rename_i r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hregs, hmem⟩, hpc'⟩, hec⟩, hst⟩, hcy⟩, hbrs⟩, hspc⟩, hobl⟩, hmok⟩, hrok⟩, hkn⟩,
    hkeep⟩ := h
  have hbrs' := listBeq_eq (fun _ _ => Br.beq_eq) hbrs
  have hmem' := listBeq_eq (fun _ _ => pairBeq_eq) hmem
  have hspc' := optEBeq_eq hspc
  have hobl' := listBeq_eq (fun _ _ => Oblig.beq_eq) hobl
  obtain ⟨hst', hec'⟩ := pathRun_sound hr vlook_ok s hpc hk (by rw [hobl']; exact hob)
    (by rw [hbrs']; exact hbr)
  refine ⟨r.toState s, ⟨?_, ?_, ?_, knownB_ok hkn s, keepB_ok hkeep s, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [hcy, hst] at hst'; exact hst'
  · intro he; exact hec' (hec.trans he)
  · intro gk0 s0 hG; exact GlobP_toState hG r.st _ hmok hrok
  · intro p hp
    rw [PRes.toState_getReg, E.beq_eq (List.all_eq_true.mp hregs p hp)]
  · intro A; rw [PRes.toState_getMem, hmem']
  · rw [← hmem']; exact hmok
  · intro hn
    rw [hn] at hpc'
    simp only [Option.isSome_none, Bool.false_or, beq_iff_eq] at hpc'
    rw [PRes.toState_pc _ _ (hspc'.trans hn), BitVec.eq_of_toNat_eq hpc']
  · intro e he; simp [PRes.toState, PRes.finalPc, hspc'.trans he]

end SigGolfCandidate.Verify
