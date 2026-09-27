import SigGolfCandidate.Verify.Mem

/-! # Generic consequences of a checked path run -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

def pcOf (n : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * n)

def cfg0 : Config := {}

def runAt (known : List (Reg × Word)) (stops : List Nat) (n : Nat) (dirs : List Bool) : Option PRes :=
  pathAux cfg0 vlook (stops.map pcOf) 400 (pcOf n) dirs (σK known) []

def KnownOK (known : List (Reg × Word)) (s : MachineState) : Prop := ∀ p ∈ known, s.getReg p.1 = p.2

/-- Side-condition-free, preserves the global invariant. -/
def resOK (r : PRes) : Bool := memOK r.st.mem && regsOK r.st.regs && r.st.obl.isEmpty

def knownB (known : List (Reg × Word)) (r : PRes) : Bool :=
  known.all fun p => E.beq (r.st.regs.get p.1) (.c p.2)

def keepB (rs : List Reg) (r : PRes) : Bool := rs.all fun x => E.beq (r.st.regs.get x) (.reg x)

theorem PRes.toState_getReg (r : PRes) (s : MachineState) (x : Reg) :
    (r.toState s).getReg x = (r.st.regs.get x).eval s := SymState.toState_getReg _ _ _ _

theorem PRes.toState_getMem (r : PRes) (s : MachineState) (a : Word) :
    (r.toState s).getMem a = memEval s r.st.mem a := rfl

theorem PRes.toState_pc (r : PRes) (s : MachineState) : (r.toState s).pc = r.pc := rfl

theorem knownB_ok {known : List (Reg × Word)} {r : PRes} (h : knownB known r = true)
    (s : MachineState) : KnownOK known (r.toState s) := by
  intro p hp
  have := List.all_eq_true.mp h p hp
  rw [PRes.toState_getReg, E.beq_eq this]; rfl

theorem keepB_ok {rs : List Reg} {r : PRes} (h : keepB rs r = true) (s : MachineState) :
    ∀ x ∈ rs, (r.toState s).getReg x = s.getReg x := by
  intro x hx
  have := List.all_eq_true.mp h x hx
  rw [PRes.toState_getReg, E.beq_eq this]; rfl

theorem run_post {known : List (Reg × Word)} {stops : List Nat} {n : Nat} {dirs : List Bool}
    {r : PRes} (hrun : runAt known stops n dirs = some r) (hok : resOK r = true)
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch image (r.toState s) = some (.base .ECALL)) ∧
      (∀ wl pk, Glob wl pk s → Glob wl pk (r.toState s)) := by
  simp only [resOK, Bool.and_eq_true, List.isEmpty_iff] at hok
  obtain ⟨⟨hm, hr⟩, ho⟩ := hok
  obtain ⟨h1, h2⟩ := pathRun_sound hrun vlook_ok s hpc hk (by rw [ho]; simp) hbr
  exact ⟨h1, h2, fun wl pk hG => Glob_toState hG r.st r.pc hm hr⟩

theorem run_post' {known : List (Reg × Word)} {stops : List Nat} {n : Nat} {dirs : List Bool}
    {r : PRes} (hrun : runAt known stops n dirs = some r) (hobl : r.st.obl = [])
    (s : MachineState) (hpc : s.pc = pcOf n) (hk : KnownOK known s)
    (hbr : ∀ b ∈ r.brs, b.holds s) :
    Steps image s r.steps r.cycles (r.toState s) ∧
      (r.ecall = true → fetch image (r.toState s) = some (.base .ECALL)) :=
  pathRun_sound hrun vlook_ok s hpc hk (by rw [hobl]; simp) hbr

theorem br_ne_zero (x : E) (d : Bool) (s : MachineState) :
    Br.holds s ⟨.ne, x, .c 0, d⟩ ↔ (decide (x.eval s ≠ 0) = d) := by
  simp only [Br.holds, CmpOp.eval, E.eval]
  cases d <;> simp [bne_iff_ne]

theorem br_eq_zero (x : E) (d : Bool) (s : MachineState) :
    Br.holds s ⟨.eq, x, .c 0, d⟩ ↔ (decide (x.eval s = 0) = d) := by
  simp only [Br.holds, CmpOp.eval, E.eval]
  cases d <;> simp

/-! ## HASH arguments at constant registers -/

def hashArgsB (a n d : Nat) : Bool :=
  decide (a % 8 = 0) && decide (0 < n ∧ n % 64 = 0) && decide (a + n ≤ MEMORY_BYTES) &&
    decide (d + 8 ≤ MEMORY_BYTES ∧ d % 8 = 0) && decide (d + 32 ≤ MEMORY_BYTES)

theorem hashArgs_ofNat (t : MachineState) (a n d : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 n) (h12 : t.getReg .x12 = BitVec.ofNat 64 d)
    (ha : a < 2 ^ 64) (hn : n < 2 ^ 64) (hd : d < 2 ^ 64) (h : hashArgsB a n d = true) :
    hashArgumentsValid t = true := by
  simp only [hashArgsB, Bool.and_eq_true, decide_eq_true_eq] at h
  simp only [hashArgumentsValid, h10, h11, h12, rangeValid, accessValid, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hd, Bool.and_eq_true,
    decide_eq_true_eq]
  omega

theorem readWords_ofNat (t : MachineState) (a : Nat) : ∀ m, a + 8 * m < 2 ^ 64 →
    t.readWords (BitVec.ofNat 64 a) m =
      (List.range m).map fun j => t.getMem (BitVec.ofNat 64 (a + 8 * j)) := by
  intro m
  induction m generalizing a with
  | zero => intro _; rfl
  | succ m ih =>
    intro h
    rw [MachineState.readWords_succ, show (8 : Word) = BitVec.ofNat 64 8 from rfl,
      BitVec.ofNat_add_ofNat, ih (a + 8) (by omega), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.mul_zero, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp]
    congr 2; omega

theorem hashInput_ofNat (t : MachineState) (a n : Nat) (h10 : t.getReg .x10 = BitVec.ofNat 64 a)
    (h11 : t.getReg .x11 = BitVec.ofNat 64 (64 * (n + 1))) (ha : a % 8 = 0)
    (hb : a + 64 * (n + 1) < 2 ^ 64) :
    hashInput t = queryOfWords n
      ((List.range (8 * (n + 1))).map fun j => t.getMem (BitVec.ofNat 64 (a + 8 * j))) := by
  rw [hashInput_eq_words t n h11 (by omega) (by rw [h10, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega)]; exact ha),
    h10, readWords_ofNat t a _ (by omega)]

/-! ## Frames at constant addresses -/

theorem memEval_frame_ofNat (s : MachineState) (ws : SymMem) (A : Nat) (hA : A < 2 ^ 64)
    (h : ∀ p ∈ ws, p.1.base = none ∧ p.1.off.toNat ≠ A) :
    memEval s ws (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
  apply memEval_frame
  intro p hp heq
  obtain ⟨h1, h2⟩ := h p hp
  obtain ⟨⟨b, off⟩, v⟩ := p
  simp only at h1; subst h1
  simp only [Addr.eval] at heq
  apply h2; rw [← heq, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hA]

theorem writeHash_frame (t : MachineState) (ans : BitVec 256) (d A : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hA : A < 2 ^ 64) (hd' : d + 24 < 2 ^ 64)
    (h : A + 8 ≤ d ∨ d + 32 ≤ A) :
    (writeHash t ans).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
  rw [writeHash_getMem_ofNat t ans d A hd hA hd', if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_neg (by omega)]

theorem writeHash_at0 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 d) = ans.extractLsb' 0 64 := by
  rw [writeHash_getMem_ofNat t ans d d hd (by omega) hd', if_neg (by omega), if_neg (by omega),
    if_neg (by omega), if_pos rfl]

theorem writeHash_at8 (t : MachineState) (ans : BitVec 256) (d : Nat)
    (hd : t.getReg .x12 = BitVec.ofNat 64 d) (hd' : d + 24 < 2 ^ 64) :
    (writeHash t ans).getMem (BitVec.ofNat 64 (d + 8)) = ans.extractLsb' 64 64 := by
  rw [writeHash_getMem_ofNat t ans d _ hd (by omega) hd', if_neg (by omega), if_neg (by omega),
    if_pos rfl]

end SigGolfCandidate.Verify
