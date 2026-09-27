import SigGolfCandidate.Verify.PorsStart

/-!
# The PORS stack machine: one block at a time

State-level lemmas: from an invariant (`PorsDefs`) through one checked run (and, where the run
ends at a HASH, the answer) to the next invariant, or to a HALT(1).
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## Generic helpers -/

theorem protP_pind : ∀ r, r < 16 → PIND + 8 * r ∈ protP := by decide
theorem protP_blk : ∀ i, i < 14 → PSB + 80 * i ∈ protP ∧ PSB + 80 * i + 16 ∈ protP ∧
    PSB + 80 * i + 24 ∈ protP := by decide
theorem halfP_blk : ∀ i, i < 14 → PSB + 80 * i + 8 ∈ halfP := by decide

theorem PB.prot {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) {a : Nat}
    (ha : a ∈ protP) : m.getMem (BitVec.ofNat 64 a) = s0.getMem (BitVec.ofNat 64 a) :=
  h.glob.2.1 a ha

theorem PB.halfv {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) {a : Nat}
    (ha : a ∈ halfP) : (m.getMem (BitVec.ofNat 64 a)).toNat % 2 ^ 32 = P.idx % 2 ^ 32 :=
  (h.glob.2.2.1 a ha).trans (h.s0ok.half a ha)

theorem PB.wit {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) : WitOK P.wl m :=
  fun j hj => (h.glob.2.2.2 j (by unfold NW; omega)).trans (h.s0ok.wit j hj)

theorem PB.zero {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) {a : Nat}
    (ha : a ∈ zeroP) : m.getMem (BitVec.ofNat 64 a) = 0 :=
  (h.prot (zeroP_sub a ha)).trans (h.s0ok.zero a ha)

theorem PB.reg {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) {r : Reg} {v : Word}
    (hr : (r, v) ∈ gkP) : m.getReg r = v := h.glob.1 _ (List.mem_append_left _ hr)

theorem PB.x20 {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) :
    m.getReg .x20 = BitVec.ofNat 64 tb := h.glob.1 _ (List.mem_append_right _ (List.mem_singleton_self _))

theorem PB.known {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) :
    KnownOK (gkP ++ [(.x20, BitVec.ofNat 64 tb)]) m := h.glob.1

/-- `PB` after a checked run that keeps `x20` (or sets it to `tb'`) and keeps `x22`. -/
theorem PB.run {P : PCtx} {s0 m t : MachineState} {tb tb' : Nat} {sp : Spec} {post : List (Reg × Word)}
    {keep : List Reg} (h : PB P s0 m tb) (hr : PSpecRes gkP sp post keep m t)
    (h20 : t.getReg .x20 = BitVec.ofNat 64 tb') (h22 : .x22 ∈ keep) : PB P s0 t tb' := by
  have hg := hr.glob _ _ h.glob
  refine ⟨⟨?_, hg.2⟩, h.s0ok, ?_⟩
  · intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hg.1 p hp
    · simp only [List.mem_singleton] at hp; subst hp; exact h20
  · rw [hr.keep .x22 h22]; exact h.idx

theorem PB.hash {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) (ans : BitVec 256)
    (d : Nat) (hd : m.getReg .x12 = BitVec.ofNat 64 d) (hsafe : safeDestP d = true) :
    PB P s0 (writeHash m ans) tb :=
  ⟨GlobP_writeHash h.glob ans d hd hsafe, h.s0ok, by rw [writeHash_getReg]; exact h.idx⟩

theorem psr_look {gk : List (Reg × Word)} {sp : Spec} {post : List (Reg × Word)} {keep : List Reg}
    {s t : MachineState} (hr : PSpecRes gk sp post keep s t) (A : Nat) (hA : A < 2 ^ 64) :
    t.getMem (BitVec.ofNat 64 A) = match memLook sp.mem A with
      | some v => v.eval s
      | none => s.getMem (BitVec.ofNat 64 A) := by
  rw [hr.mem]; exact memEval_look s sp.mem A hA (memOKP_const hr.memc)

theorem memLook_cons_ne (k : Addr) (v : E) (ws : SymMem) (A : Nat) (h : k.off.toNat ≠ A) :
    memLook ((k, v) :: ws) A = memLook ws A := by
  simp [memLook, h]

theorem memLook_cons_eq (off : Nat) (v : E) (ws : SymMem) (A : Nat) (h : off = A) (ho : off < 2 ^ 64) :
    memLook ((⟨none, BitVec.ofNat 64 off⟩, v) :: ws) A = some v := by
  subst h
  simp only [memLook, Option.isNone_none, Bool.true_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ho,
    beq_self_eq_true, if_true]

theorem ofNat_toNat_lt (n : Nat) (h : n < 2 ^ 64) : (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

/-- The merged tweak word `+8` (`sw v, +12` into a word whose low half is `lo`). -/
theorem stW_eval' (s : MachineState) (a : Nat) (v : E) (V lo : Nat) (hv : v.eval s = BitVec.ofNat 64 V)
    (hV : V < 2 ^ 32) (hlo : (s.getMem (BitVec.ofNat 64 a)).toNat % 2 ^ 32 = lo) :
    (stW a v).eval s = BitVec.ofNat 64 (lo + 2 ^ 32 * V) := by
  have _ := hV
  apply BitVec.eq_of_toNat_eq
  show (StoreKind.merge .w (s.getMem (BitVec.ofNat 64 a)) 4 (v.eval s)).toNat = _
  rw [merge_w4_toNat, hv, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : lo < 2 ^ 32 := by rw [← hlo]; exact Nat.mod_lt _ (by decide)
  omega

theorem twHi_eq (idx H : Nat) (hH : H < 2 ^ 32) : idx % 2 ^ 32 + 2 ^ 32 * H = twHi idx H := by
  unfold twHi; rw [Nat.mod_eq_of_lt hH]

/-- The byte `bo` of the witness doubleword at `off` (`lbu`). -/
theorem bu_w64 (l : List Byte) (bo : Nat) (hl : l.length ≤ 8) :
    (LoadKind.bu.fromWord (w64 l) bo).toNat = (l.getD bo 0).toNat := by
  simp only [LoadKind.fromWord, extractByte, BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  rw [w64_toNat _ hl, Nat.mod_eq_of_lt (show leNat l / 2 ^ (bo * 8) % 2 ^ 8 < 2 ^ 64 from
    lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by decide)), Nat.mul_comm bo 8, Nat.pow_mul]
  exact leNat_div_mod l bo

theorem getD_slice (l : List Byte) (off bo : Nat) (hbo : bo < 8) :
    (slice l off 8).getD bo 0 = l.getD (off + bo) 0 := by
  simp only [slice, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hbo, List.getElem?_drop]

/-- A witness byte read by `lbu` at `WIT + off` (any `off < 7040`). -/
theorem wit_byte {wl : List Byte} {s : MachineState} (hW : WitOK wl s) (off : Nat) (hoff : off < 7040) :
    (LoadKind.bu.fromWord (s.getMem (BitVec.ofNat 64 (0x800 + off / 8 * 8))) (off % 8)).toNat = wbyte wl off := by
  rw [show 0x800 + off / 8 * 8 = 0x800 + 8 * (off / 8) by omega, hW (off / 8) (by omega),
    bu_w64 _ _ (by simp [slice]), getD_slice _ _ _ (Nat.mod_lt _ (by decide)), wbyte]
  congr 2; omega


/-! ## The stack frame -/

theorem StackOK.frame {stk : List (Val × Nat)} {m u : MachineState} (h : StackOK stk m)
    (hf : ∀ i, i < stk.length → u.getMem (BitVec.ofNat 64 (blkQ i)) = m.getMem (BitVec.ofNat 64 (blkQ i)) ∧
      u.getMem (BitVec.ofNat 64 (blkL i)) = m.getMem (BitVec.ofNat 64 (blkL i)) ∧
      u.getMem (BitVec.ofNat 64 (blkL i + 8)) = m.getMem (BitVec.ofNat 64 (blkL i + 8))) :
    StackOK stk u := by
  intro i hi
  obtain ⟨e1, e2, e3⟩ := hf i hi
  rw [e1, e2, e3]; exact h i hi

/-- A stack inside the stack region is unchanged by writes outside `[0x290, 0x800)`. -/
theorem StackOK.frame_low {stk : List (Val × Nat)} {m u : MachineState} (h : StackOK stk m)
    (hd : stk.length ≤ 14)
    (hf : ∀ A, 0x290 ≤ A → A < 0x800 → u.getMem (BitVec.ofNat 64 A) = m.getMem (BitVec.ofNat 64 A)) :
    StackOK stk u :=
  h.frame fun i hi => ⟨hf _ (by unfold blkQ PSB; omega) (by unfold blkQ PSB; omega),
    hf _ (by unfold blkL PSB; omega) (by unfold blkL PSB; omega),
    hf _ (by unfold blkL PSB; omega) (by unfold blkL PSB; omega)⟩

/-! ## Leaves -/

/-- The leaf index of slot `s` (`ref.pors_root`'s `x`). -/
def leafX (P : PCtx) (s : Nat) : Nat := (P.v ++ [porsT]).getD (witPi P.wl s / 8 % 16) 0

theorem getD_v_le (P : PCtx) (k : Nat) : (P.v ++ [porsT]).getD k 0 ≤ 2 ^ 14 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hk : k < 15
  · rw [List.getElem?_append_left (by simp [PCtx.v, leavesOf, porsK]; omega)]
    simp only [PCtx.v, leavesOf, porsK, List.getElem?_map, List.getElem?_range hk, Option.map_some,
      Option.getD_some, leafOf, porsH]
    have := Nat.mod_lt (P.A / 2 ^ (totalH + 14 * k)) (show 2 ^ 14 > 0 by decide)
    omega
  · by_cases h15 : k = 15
    · subst h15; simp [PCtx.v, leavesOf, porsK, porsT, porsH]
    · rw [List.getElem?_eq_none (by simp [PCtx.v, leavesOf, porsK]; omega)]; simp

theorem leafX_le (P : PCtx) (s : Nat) : leafX P s ≤ 2 ^ 14 := getD_v_le P _

theorem leafCheck_at (s : Nat) (hs : s < 15) : leafCheck s = true :=
  List.all_eq_true.mp leafCheck_all s (List.mem_range.mpr hs)

theorem land0x78 (b : Nat) (_hb : b < 256) : b &&& 0x78 = 8 * (b / 8 % 16) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, show (0x78 : Nat) = 120 from rfl]
  rw [show 8 * (b / 8 % 16) = 2 ^ 3 * (b / 2 ^ 3 % 2 ^ 4) by norm_num]
  rw [Nat.testBit_two_pow_mul, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  have h120 : ∀ j, Nat.testBit 120 j = (decide (3 ≤ j) && decide (j < 7)) := by
    intro j
    by_cases h : j < 8
    · interval_cases j <;> rfl
    · rw [show (120 : Nat) = 120 % 2 ^ 8 from rfl, Nat.testBit_mod_two_pow]; simp [h]; omega
  rw [h120]
  by_cases h1 : 3 ≤ j
  · by_cases h2 : j < 7
    · simp [h1, h2, show j - 3 < 4 by omega, show j - 3 + 3 = j by omega]
    · simp [h1, h2, show ¬ (j - 3 < 4) by omega]
  · simp [h1]

theorem piT_eval {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) (s : Nat) (hs : s < 15) :
    (piT s).eval m = BitVec.ofNat 64 (8 * (witPi P.wl s / 8 % 16)) := by
  have hb := wit_byte h.wit (16 + s) (by omega)
  apply BitVec.eq_of_toNat_eq
  show ((LoadKind.bu.fromWord (m.getMem (BitVec.ofNat 64 (0x800 + 16 + (16 + s) / 8 * 8 - 16))) ((16 + s) % 8)) &&&
    BitVec.ofNat 64 0x78).toNat = _
  rw [show 0x800 + 16 + (16 + s) / 8 * 8 - 16 = 0x800 + (16 + s) / 8 * 8 by omega, BitVec.toNat_and, hb]
  have hw : wbyte P.wl (16 + s) = witPi P.wl s := rfl
  rw [hw, ofNat_toNat_lt _ (by decide), land0x78 _ (by unfold witPi; exact (P.wl.getD _ 0).isLt),
    ofNat_toNat_lt _ (by omega)]

theorem xE_eval {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) (s : Nat) (hs : s < 15) :
    (xE s).eval m = BitVec.ofNat 64 (leafX P s) := by
  show m.getMem ((piT s).eval m + BitVec.ofNat 64 PIND) = _
  rw [piT_eval h s hs, BitVec.ofNat_add_ofNat, show 8 * (witPi P.wl s / 8 % 16) + PIND =
    PIND + 8 * (witPi P.wl s / 8 % 16) by omega, h.prot (protP_pind _ (Nat.mod_lt _ (by decide))),
    h.s0ok.pind _ (Nat.mod_lt _ (by decide))]
  rfl

theorem leafObl_holds {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) (s : Nat)
    (hs : s < 15) : ∀ o ∈ leafObl s, o.holds m := by
  intro o ho
  simp only [leafObl, List.mem_singleton] at ho
  subst ho
  simp only [Oblig.holds, Addr.eval, piT_eval h s hs, accessValid, rangeValid, BitVec.ofNat_add_ofNat,
    Bool.and_eq_true, decide_eq_true_eq, MEMORY_BYTES]
  have := Nat.mod_lt (witPi P.wl s / 8) (show 16 > 0 by decide)
  rw [ofNat_toNat_lt _ (by unfold PIND; omega)]
  unfold PIND; omega

theorem geu_iff (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    CmpOp.geu.eval (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (¬ a < b) := by
  simp only [CmpOp.eval, BitVec.ult, ofNat_toNat_lt _ ha, ofNat_toNat_lt _ hb]
  by_cases h : a < b <;> simp [h]

theorem srl14_ne (x : Nat) (hx : x ≤ 2 ^ 14) :
    CmpOp.ne.eval ((BitVec.ofNat 64 x) >>> ((BitVec.ofNat 64 14).toNat % 64)) 0 = decide (¬ x < porsT) := by
  simp only [CmpOp.eval, bne_iff_ne, ne_eq]
  have e : (BitVec.ofNat 64 x) >>> ((BitVec.ofNat 64 14).toNat % 64) = BitVec.ofNat 64 (x / 2 ^ 14) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt (show x < 2 ^ 64 by omega)]; norm_num
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [e]
  unfold porsT porsH
  by_cases h : x < 2 ^ 14
  · rw [Nat.div_eq_of_lt h]; simp; omega
  · have : x = 2 ^ 14 := by omega
    subst this; decide

theorem leaf_brs_iff {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) (s : Nat) (hs : s < 15)
    (prev : Nat) (hp : 0 < s → m.getReg (xReg (s + 1)) = BitVec.ofNat 64 prev ∧ prev ≤ 2 ^ 14)
    (d1 d2 : Bool) :
    (∀ b ∈ leafBrs s d1 d2, b.holds m) ↔
      ((s ≠ 0 → d1 = decide (¬ prev < leafX P s)) ∧ (s = 14 → d2 = decide (¬ leafX P s < porsT))) := by
  have hx := xE_eval h s hs
  have hxl := leafX_le P s
  unfold leafBrs
  by_cases h0 : s = 0
  · subst h0; simp
  · have hpv := hp (by omega)
    have hg : Br.holds m ⟨.geu, .reg (xReg (s + 1)), xE s, d1⟩ ↔ d1 = decide (¬ prev < leafX P s) := by
      simp only [Br.holds, E.eval, hpv.1, hx, geu_iff prev (leafX P s) (by omega) (by omega)]
      constructor <;> intro e <;> exact e.symm
    by_cases h14 : s = 14
    · subst h14
      have hn : Br.holds m ⟨.ne, .bin .srl (xE 14) (cw 14), .c 0, d2⟩ ↔ d2 = decide (¬ leafX P 14 < porsT) := by
        simp only [Br.holds, E.eval, BinOp.eval, cw, hx]
        rw [srl14_ne _ hxl]
        constructor <;> intro e <;> exact e.symm
      simp only [if_true, if_false, show (14 : Nat) ≠ 0 by decide, List.cons_append, List.nil_append,
        List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq, hn, hg]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, forall_const, and_comm]
    · simp only [h14, h0, if_false, List.nil_append, List.mem_singleton, forall_eq, hg]
      simp [h0, h14]

/-- The leaf code of slot `s`: reject, or the dispatch of its first segment. -/
theorem pleaf_step (P : PCtx) (hP : P.ok) (s0 : MachineState) (s : Nat) (st : PorsState) (m : MachineState)
    (h : LeafIn P s0 s st m) :
    (((s ≠ 0 ∧ ¬ st.prev < leafX P s) ∨ (s = porsK - 1 ∧ ¬ leafX P s < porsT)) →
      ∃ u k, k ≤ 11 ∧ Steps image m k k u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (¬ ((s ≠ 0 ∧ ¬ st.prev < leafX P s) ∨ (s = porsK - 1 ∧ ¬ leafX P s < porsT)) →
      ∃ u, Steps image m (if s = 0 then 10 else if s = 14 then 15 else 11)
        (if s = 0 then 10 else if s = 14 then 15 else 11) u ∧
        DispIn P s0 s (leafX P s) s st.ptr (porsT ||| leafX P s) st.folds
          (.leaf (leafX P s) (witSecret P.wl s)) st.node st.stack u) := by
  have hs : s < 15 := h.bnd.1
  have hc := leafCheck_at s hs
  simp only [leafCheck, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
  obtain ⟨⟨cAcc, cRej1⟩, cRej2⟩ := hc
  have hK : KnownOK leafKnown m := h.pb.known
  have hob := leafObl_holds h.pb s hs
  have hbr := leaf_brs_iff h.pb s hs st.prev h.prev
  have hxl := leafX_le P s
  constructor
  · intro hrej
    by_cases h1 : s ≠ 0 ∧ ¬ st.prev < leafX P s
    · have c1 := cRej1.resolve_left h1.1
      obtain ⟨u, hu⟩ := pspec_run c1 m h.pc hK (by
        intro b hb
        simp only [rejSpec, List.mem_singleton] at hb
        subst hb
        have := (hbr true false).mp
        have hp := h.prev (by omega)
        simp only [Br.holds, E.eval, hp.1, xE_eval h.pb s hs, geu_iff st.prev (leafX P s) (by omega) (by omega)]
        simp [h1.2]) hob
      exact ⟨u, _, by simp only [rejSpec]; split_ifs <;> omega, hu.steps, hu.ecall rfl,
        hu.regs (.x5, cw 1) (by simp [rejSpec]), hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
    · have h2 : s = 14 ∧ ¬ leafX P s < porsT := by
        rcases hrej with h' | h'
        · exact absurd h' h1
        · exact h'
      have c2 := cRej2.resolve_left (by rw [h2.1]; decide)
      have hprev : ¬ (s ≠ 0 ∧ ¬ st.prev < leafX P s) := h1
      obtain ⟨u, hu⟩ := pspec_run c2 m h.pc hK ((hbr false true).mpr ⟨fun hs0 => by
        rw [eq_comm, decide_eq_false_iff_not, not_not]; by_contra hc; exact hprev ⟨hs0, hc⟩,
        fun _ => by simp [h2.2]⟩) hob
      exact ⟨u, _, le_refl _, hu.steps, hu.ecall rfl,
        hu.regs (.x5, cw 1) (by simp [rejSpec]), hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  · intro hacc
    have hbr' : ∀ b ∈ (leafSpec s).brs, b.holds m := by
      show ∀ b ∈ leafBrs s false false, b.holds m
      rw [hbr]
      refine ⟨fun hs0 => ?_, fun h14 => ?_⟩
      · rw [eq_comm, decide_eq_false_iff_not, not_not]; by_contra hc; exact hacc (Or.inl ⟨hs0, hc⟩)
      · rw [eq_comm, decide_eq_false_iff_not, not_not]; by_contra hc
        exact hacc (Or.inr ⟨by rw [h14]; rfl, hc⟩)
    obtain ⟨u, hu⟩ := pspec_run cAcc m h.pc hK hbr' hob
    have hx := xE_eval h.pb s hs
    have hK' := hu.known
    have r20 : u.getReg .x20 = BitVec.ofNat 64 (tbOf s) := hK' (.x20, BitVec.ofNat 64 (tbOf s)) (by simp [pleafPost])
    have pb := h.pb.run hu r20 (by simp [pleafKeep])
    have hlook := psr_look hu
    have hsec : ∀ k, k < 2 → m.getMem (BitVec.ofNat 64 (secA s + 8 * k)) =
        (if k = 0 then vw0 else vw1) (witSecret P.wl s) := by
      intro k hk
      rw [show secA s + 8 * k = 0x800 + (32 + 16 * s + 8 * k) by unfold secA; omega,
        wit_word h.pb.wit _ (by omega) (by omega)]
      interval_cases k
      · simp [witSecret, vw0_slice, wSec]
      · simp [witSecret, vw1_slice, wSec]
    refine ⟨u, ?_, ⟨pb, ?_, Or.inl ⟨rfl, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun h => by omega,
      h.bnd, ?_, hxl⟩⟩
    · have := hu.steps; simp only [leafSpec] at this; exact this
    · rw [hu.pc rfl]; simp [leafSpec, dispPc, hs]
    · rw [hu.keep .x14 (by simp [pleafKeep])]; exact h.fr
    · rw [hu.regs (.x23, .bin .or (xE s) (cw 0x4000)) (by simp [leafSpec])]
      simp only [E.eval, BinOp.eval, hx, cw]
      apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_or, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (show leafX P s < 2 ^ 64 by omega), Nat.or_comm,
        Nat.mod_eq_of_lt (show porsT ||| leafX P s < 2 ^ 64 from
          lt_of_lt_of_le (Nat.or_lt_two_pow (show porsT < 2 ^ 15 by decide) (show leafX P s < 2 ^ 15 by omega)) (by decide))]
      rfl
    · rw [hu.keep .x29 (by simp [pleafKeep])]; exact h.sum
    · rw [hu.keep .x15 (by simp [pleafKeep])]; exact h.rS
    · apply h.stack.frame_low (by have := h.bnd; unfold SegBnd at this; omega)
      intro A h1 h2
      rw [hlook A (by omega)]
      simp only [leafSpec]
      rw [memLook_cons_ne _ _ _ _ (by simp; omega), memLook_cons_ne _ _ _ _ (by simp; omega),
        memLook_cons_ne _ _ _ _ (by simp; omega)]
      rfl
    · rw [hK' (.x10, 0xC0) (by simp [pleafPost])]; rfl
    · refine ⟨?_, ?_, ?_, ?_, hxl⟩
      · rw [hlook 0xC8 (by omega)]
        simp only [leafSpec]
        rw [memLook_cons_ne _ _ _ _ (by simp), memLook_cons_ne _ _ _ _ (by simp),
          memLook_cons_eq _ _ _ _ rfl (by omega)]
        dsimp only
        rw [stW_eval' m 0xC8 (xE s) _ _ hx (by omega) (h.pb.halfv (by decide)), twHi_eq _ _ (by omega)]
      · rw [hlook 0xE0 (by omega)]
        simp only [leafSpec]
        rw [memLook_cons_ne _ _ _ _ (by simp), memLook_cons_eq _ _ _ _ rfl (by omega)]
        dsimp only
        have := hsec 0 (by decide)
        simpa [ldE, cw, E.eval] using this
      · rw [hlook 0xE8 (by omega)]
        simp only [leafSpec]
        rw [memLook_cons_eq _ _ _ _ rfl (by omega)]
        dsimp only
        have := hsec 1 (by decide)
        simpa [ldE, cw, E.eval] using this
      · unfold witSecret; apply length_slice16; rw [hP.1]; unfold wSec; omega
    · rw [hu.regs (xReg s, xE s) (by simp [leafSpec]), hx]
    · exact Nat.or_lt_two_pow (show porsT < 2 ^ 15 by decide) (show leafX P s < 2 ^ 15 by omega)


/-! ## Hash destinations and the pending input -/

theorem safe_nb : ∀ t, t < 2 → safeDestP (0x1E0 + 16 * t) = true := by decide
theorem safe_m : ∀ d, d ≤ 14 → safeDestP (stkOf' d + 48) = true := by decide
theorem safe_p : ∀ d, d ≤ 13 → safeDestP (stkOf' d + 112) = true := by decide
theorem safe_f : safeDestP 0x120 = true := by decide

theorem safe_dest (V d : Nat) (hd : d ≤ 14) (hp : V = 1 → d < 14) : safeDestP (destOf V d) = true := by
  unfold destOf
  split_ifs with h0 h1
  · exact safe_m d hd
  · exact safe_p d (by have := hp h1; omega)
  · exact safe_f

theorem StackOK.hash {stk : List (Val × Nat)} {m : MachineState} (h : StackOK stk m) (ans : BitVec 256)
    (D : Nat) (hd : m.getReg .x12 = BitVec.ofNat 64 D) (hD : D + 32 < 2 ^ 64)
    (hs : ∀ i, i < stk.length → (blkQ i + 8 ≤ D ∨ D + 32 ≤ blkQ i) ∧ (blkL i + 16 ≤ D ∨ D + 32 ≤ blkL i))
    (hlen : stk.length ≤ 14) : StackOK stk (writeHash m ans) := by
  apply h.frame
  intro i hi
  have hq : blkQ i < 2 ^ 64 := by unfold blkQ PSB; omega
  have hl : blkL i + 8 < 2 ^ 64 := by unfold blkL PSB; omega
  obtain ⟨h1, h2⟩ := hs i hi
  exact ⟨writeHash_frame _ _ D _ hd hq (by omega) (by omega),
    writeHash_frame _ _ D _ hd (by omega) (by omega) (by omega),
    writeHash_frame _ _ D _ hd hl (by omega) (by omega)⟩

theorem stack_dest (V d : Nat) (_hd : d ≤ 14) : ∀ i, i < d →
    (blkQ i + 8 ≤ destOf V d ∨ destOf V d + 32 ≤ blkQ i) ∧
    (blkL i + 16 ≤ destOf V d ∨ destOf V d + 32 ≤ blkL i) := by
  intro i hi
  unfold destOf stkOf' blkQ blkL EMPTY PSB
  split_ifs <;> omega

theorem even_andNot1' (n : Nat) (h : n % 2 = 0) :
    BitVec.ofNat 64 n &&& ~~~1#64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_getLsbD_eq; intro j hj
  rw [BitVec.getLsbD_and, BitVec.getLsbD_not, BitVec.getLsbD_one]
  by_cases h0 : j = 0
  · subst h0; simp; rw [← BitVec.getLsbD_eq_getElem, BitVec.getLsbD_ofNat, Nat.testBit_zero]; simp [h]
  · simp [h0, hj]

theorem pend_hashInput {P : PCtx} {s0 u : MachineState} {tb : Nat} (pb : PB P s0 u tb) (pend : Pending)
    (node : Val) (d : Nat) (h10 : u.getReg .x10 = BitVec.ofNat 64 (pendAddr pend d))
    (h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1))) (hpm : PendMem P node d u pend) :
    hashInput u = fmt (pendInput P node pend) ∧ (fmt (pendInput P node pend)).blocks = 1 := by
  cases pend with
  | leaf x sec =>
    obtain ⟨m8, m32, m40, hsl, hx⟩ := hpm
    have hf : fmt (pendInput P node (.leaf x sec)) = queryOfWords 0
        [BitVec.ofNat 64 (twLo 9 0 P.idx 0), BitVec.ofNat 64 (twHi P.idx x), 0, 0, vw0 sec, vw1 sec, 0, 0] := by
      simp only [pendInput]
      rw [show porsLeafInput P.idx x sec = thInput (tweak 9 0 P.idx 0 x) sec from rfl,
        fmt_th _ _ _ _ _ _ (by decide), ← show porsLeafInput P.idx x sec = thInput (tweak 9 0 P.idx 0 x) sec from rfl,
        pad64_porsLeafInput _ _ _ hsl]
    refine ⟨?_, by rw [hf]; rfl⟩
    rw [hf, hashInput_ofNat u 0xC0 0 h10 h11 (by decide) (by decide)]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero, List.cons.injEq]
    refine ⟨?_, m8, pb.zero (by decide), pb.zero (by decide), m32, m40, pb.zero (by decide),
      pb.zero (by decide), trivial⟩
    rw [pb.prot (by decide), pb.s0ok.cb0]
  | merge H l =>
    obtain ⟨m8, m32, m40, m48, m56, hl, hn, hH, hd⟩ := hpm
    have hf : fmt (pendInput P node (.merge H l)) = queryOfWords 0
        [BitVec.ofNat 64 (twLo 10 0 P.idx 0), BitVec.ofNat 64 (twHi P.idx H), 0, 0, vw0 l, vw1 l,
          vw0 node, vw1 node] := by
      simp only [pendInput]
      rw [show porsNodeInput P.idx H l node = thInput (tweak 10 0 P.idx 0 H) (l ++ node) from rfl,
        fmt_th _ _ _ _ _ _ (by decide),
        ← show porsNodeInput P.idx H l node = thInput (tweak 10 0 P.idx 0 H) (l ++ node) from rfl,
        pad64_porsNodeInput _ _ _ _ hl hn]
    refine ⟨?_, by rw [hf]; rfl⟩
    rw [hf, hashInput_ofNat u (PSB + 80 * d) 0 h10 h11 (by unfold PSB; omega) (by unfold PSB; omega)]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero, List.cons.injEq]
    obtain ⟨b0, b16, b24⟩ := protP_blk d hd
    refine ⟨?_, by simpa [Nat.add_assoc] using m8, ?_, ?_, by simpa [Nat.add_assoc] using m32,
      by simpa [Nat.add_assoc] using m40, by simpa [Nat.add_assoc] using m48,
      by simpa [Nat.add_assoc] using m56, trivial⟩
    · rw [pb.prot b0, pb.s0ok.blk0 d hd]
    · rw [show PSB + 80 * d + 8 * 2 = PSB + 80 * d + 16 by omega]
      exact pb.zero (by simp only [zeroP, List.mem_append, List.mem_flatMap, List.mem_range]; right; exact ⟨d, hd, by simp⟩)
    · rw [show PSB + 80 * d + 8 * 3 = PSB + 80 * d + 24 by omega]
      exact pb.zero (by simp only [zeroP, List.mem_append, List.mem_flatMap, List.mem_range]; right; exact ⟨d, hd, by simp⟩)


/-! ## A segment's start: dispatch, table entry, pending hash -/

/-- The table of leaf `s` (`0` = normal, `1` = last leaf). -/
def tsel (s : Nat) : Nat := if s = 14 then 1 else 0

theorem tbOf_tsel (s : Nat) : tbOf s = 0x1000 + 4 * tabBase (tsel s) := by
  by_cases h : s = 14 <;> simp [tbOf, tsel, tabBase, h, tbL, tbN]

theorem dispCheck2_ok (c tb : Nat) (hc : c < 18) (h1 : c < 15 → tb = tbOf c) (h2 : tb = tbN ∨ tb = tbL) :
    dispCheck2 c tb = true := by
  have := List.all_eq_true.mp dispCheck_all c (List.mem_range.mpr hc)
  unfold dispCheck at this
  split_ifs at this with hlt
  · rw [h1 hlt]; exact this
  · simp only [Bool.and_eq_true] at this
    rcases h2 with rfl | rfl
    · exact this.1
    · exact this.2

theorem wbyte_lt (wl : List Byte) (off : Nat) : wbyte wl off < 256 := (wl.getD off 0).isLt

theorem dispT_eval {P : PCtx} {s0 m : MachineState} {tb' : Nat} (pb : PB P s0 m tb') (ptr tb : Nat)
    (hfr : m.getReg .x14 = BitVec.ofNat 64 (0x800 + ptr - 224)) (hp : 272 ≤ ptr) (hp8 : ptr % 8 = 0)
    (hp2 : ptr < 7040) (_htb : tb < 2 ^ 32) :
    (dispT tb).eval m = BitVec.ofNat 64 (tb + 16 * wbyte P.wl ptr) := by
  have hb := wit_byte pb.wit ptr hp2
  rw [show 0x800 + ptr / 8 * 8 = 0x800 + ptr by omega, show ptr % 8 = 0 from hp8] at hb
  have hbl := wbyte_lt P.wl ptr
  apply BitVec.eq_of_toNat_eq
  show ((LoadKind.bu.fromWord (m.getMem (m.getReg .x14 + BitVec.ofNat 64 224)) 0 <<<
    ((BitVec.ofNat 64 4).toNat % 64)) + BitVec.ofNat 64 tb).toNat = _
  rw [hfr, BitVec.ofNat_add_ofNat, show 0x800 + ptr - 224 + 224 = 0x800 + ptr by omega,
    show (BitVec.ofNat 64 4).toNat % 64 = 4 from rfl]
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, hb, Nat.shiftLeft_eq]
  omega

theorem dispObl_holds {m : MachineState} (ptr : Nat) (hfr : m.getReg .x14 = BitVec.ofNat 64 (0x800 + ptr - 224))
    (hp : 272 ≤ ptr) (hp8 : ptr % 8 = 0) (hp2 : ptr < 7040) : ∀ o ∈ dispObl, o.holds m := by
  intro o ho
  simp only [dispObl, List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl
  · simp only [Oblig.holds, E.eval, hfr, ofNat_toNat_lt _ (show 0x800 + ptr - 224 < 2 ^ 64 by omega)]; omega
  · simp only [Oblig.holds, Addr.eval, E.eval, hfr, BitVec.ofNat_add_ofNat, accessValid, rangeValid,
      Bool.and_eq_true, decide_eq_true_eq, MEMORY_BYTES]
    rw [ofNat_toNat_lt _ (by omega)]; omega

theorem tabCheck1_parts (tb b : Nat) (htb : tb < 2) (hb : b < 256) :
    (segA b > 14 → pspecB [] (runAt gkP [] (tabBase tb + 4 * b) []) (tabSpec tb b) [] [] [] = true) ∧
    (segA b ≤ 14 → pspecB gkP (runAt gkP [] (tabBase tb + 4 * b) (if segA b = 0 then [] else [.br false]))
      (tabSpec tb b) [] gkP tabKeep = true) ∧
    (1 ≤ segA b → segA b ≤ 14 →
      pspecB [] (runAt gkP [] (tabBase tb + 4 * b) [.br true]) (tabRej b) [] [] [] = true) := by
  have := tabCheck1_ok tb b htb hb
  unfold tabCheck1 at this
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_⟩
  · rwa [if_pos h] at this
  · rw [if_neg (by omega)] at this
    by_cases h0 : segA b = 0
    · rw [if_pos h0] at this; rw [if_pos h0]; exact this
    · rw [if_neg h0, Bool.and_eq_true] at this; rw [if_neg h0]; exact this.1
  · rw [if_neg (by omega), if_neg (by omega), Bool.and_eq_true] at this; exact this.2

/-- The entry code's parity test: taken iff bit 0 of `E` differs from `t`. -/
theorem parBr_holds {m : MachineState} {E : Nat} (h : m.getReg .x23 = BitVec.ofNat 64 E)
    (t : Nat) (ht : t < 2) (d : Bool) : Br.holds m (parBr t d) ↔ d = decide (E % 2 ≠ t) := by
  have key : parE.eval m = BitVec.ofNat 64 (E % 2) := by
    apply BitVec.eq_of_toNat_eq
    simp only [parE, Rv.E.eval, BinOp.eval, cw, h, BitVec.toNat_and, BitVec.toNat_ofNat]
    rw [Nat.and_one_is_mod]; omega
  simp only [Br.holds, parBr, key]
  rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl <;>
    rcases Nat.mod_two_eq_zero_or_one E with he | he <;>
    simp [he, CmpOp.eval, Rv.E.eval]

theorem segV_lt (tb b : Nat) : segV tb b < 3 := by unfold segV; split_ifs <;> omega

/-- A segment's start: the dispatch jumps to the table entry of the header byte `b`; `a > 14`
rejects; `a ≥ 1` with the parity bit `t ≠ E % 2` rejects (the entry's parity test); otherwise the
entry performs the pending hash, into NB slot `t` (`a ≥ 1`) or straight into the variant's
destination (`a = 0`). -/
theorem seg_step (P : PCtx) (_hP : P.ok) (s0 : MachineState) (s x c ptr E folds : Nat) (pend : Pending)
    (node : Val) (stk : List (Val × Nat)) (m : MachineState) (h : DispIn P s0 s x c ptr E folds pend node stk m) :
    (14 < wbyte P.wl ptr % 16 → ∃ u, Steps image m 8 8 u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (1 ≤ wbyte P.wl ptr % 16 → wbyte P.wl ptr % 16 ≤ 14 → segT (wbyte P.wl ptr) ≠ E % 2 →
        ∃ u, Steps image m 12 12 u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (wbyte P.wl ptr % 16 ≤ 14 → (wbyte P.wl ptr % 16 = 0 ∨ segT (wbyte P.wl ptr) = E % 2) →
        ∃ k u, k ≤ 10 ∧ Steps image m k k u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧ hashInput u = fmt (pendInput P node pend) ∧
        (fmt (pendInput P node pend)).blocks = 1 ∧
        ∀ ans, (wbyte P.wl ptr % 16 = 0 → TailIn P s0 s x (segV (tsel s) (wbyte P.wl ptr)) 2 (ptr + 8) E folds
            (answerBytes 16 ans) stk (writeHash u ans)) ∧
          (1 ≤ wbyte P.wl ptr % 16 → EntIn P s0 s x (segV (tsel s) (wbyte P.wl ptr)) (segT (wbyte P.wl ptr))
            (wbyte P.wl ptr % 16) ptr E folds (answerBytes 16 ans) stk (writeHash u ans))) := by
  obtain ⟨hs, hd, hp, hp8, hpb, hfb⟩ := h.bnd
  have hp2 : ptr < 7040 := by omega
  set b := wbyte P.wl ptr with hbdef
  have hbl : b < 256 := wbyte_lt P.wl ptr
  have htb : tbOf s = tbN ∨ tbOf s = tbL := by unfold tbOf; split_ifs <;> simp
  have hc18 : c < 18 := by rcases h.copy with ⟨h1, -⟩ | ⟨-, h2, -⟩ <;> omega
  have cD := dispCheck2_ok c (tbOf s) hc18 (fun hc => by rcases h.copy with ⟨h1, -⟩ | ⟨h1, -, -⟩ <;> [rw [h1]; omega]) htb
  obtain ⟨u1, hu1⟩ := pspec_run cD m h.pc h.pb.known (by simp [dispSpec])
    (dispObl_holds ptr h.fr hp hp8 hp2)
  have htbl : tbOf s < 2 ^ 32 := by rcases htb with e | e <;> rw [e] <;> decide
  have hpc1 : u1.pc = pcOf (tabBase (tsel s) + 4 * b) := by
    rw [hu1.spc _ rfl]
    show (dispT (tbOf s)).eval m &&& ~~~1#64 = _
    rw [dispT_eval h.pb ptr (tbOf s) h.fr hp hp8 hp2 htbl, even_andNot1' _ (by
      rw [tbOf_tsel]; omega), pcOf, tbOf_tsel]
    congr 1; omega
  have pb1 := h.pb.run hu1 (hu1.known (.x20, BitVec.ofNat 64 (tbOf s)) (by simp [dispKnown])) (by simp [dispKeep])
  have hts : tsel s < 2 := by unfold tsel; split_ifs <;> omega
  obtain ⟨cRej, cOk, cPar⟩ := tabCheck1_parts (tsel s) b hts hbl
  have hE1 : u1.getReg .x23 = BitVec.ofNat 64 E := by rw [hu1.keep .x23 (by simp [dispKeep])]; exact h.rE
  have ht : segT b < 2 := by unfold segT; omega
  refine ⟨?_, ?_, ?_⟩
  · intro ha
    have ha1 : segA b > 14 := ha
    have hsp : tabSpec (tsel s) b = rejSpec 4 [] := by unfold tabSpec; rw [if_pos ha1]
    obtain ⟨u, hu⟩ := pspec_run (cRej ha1) u1 hpc1 (fun p hp => pb1.known p (List.mem_append_left _ hp))
      (by rw [hsp]; simp [rejSpec]) (by simp)
    refine ⟨u, (hu1.steps.trans hu.steps).of_eq (by simp [dispSpec, hsp, rejSpec]) (by simp [dispSpec, hsp, rejSpec]),
      hu.ecall (by simp [hsp, rejSpec]), hu.regs (.x5, cw 1) (by simp [hsp, rejSpec]),
      hu.regs (.x10, cw 1) (by simp [hsp, rejSpec])⟩
  · intro h1 h14 hne
    obtain ⟨u, hu⟩ := pspec_run (cPar h1 h14) u1 hpc1 (fun p hp => pb1.known p (List.mem_append_left _ hp))
      (by
        intro br hbr; simp only [tabRej, rejSpec, List.mem_singleton] at hbr; subst hbr
        exact (parBr_holds hE1 _ ht true).mpr (by simp [Ne.symm hne])) (by simp)
    refine ⟨u, (hu1.steps.trans hu.steps).of_eq (by simp [dispSpec, tabRej, rejSpec])
        (by simp [dispSpec, tabRej, rejSpec]),
      hu.ecall (by simp [tabRej, rejSpec]), hu.regs (.x5, cw 1) (by simp [tabRej, rejSpec]),
      hu.regs (.x10, cw 1) (by simp [tabRej, rejSpec])⟩
  · intro ha hpar
    have ha' : ¬ segA b > 14 := by unfold segA; omega
    have hsp : tabSpec (tsel s) b = ⟨[(.x29, addC (.reg .x29) (BitVec.ofNat 64 (b % 16))),
        (.x14, addC (.reg .x14) (BitVec.ofNat 64 (16 * (b % 16) + 8))),
        (.x12, if b % 16 = 0 then destE (segV (tsel s) b) else cw (0x1E0 + 16 * segT b))], [],
        if b % 16 = 0 then entry0Pc (segV (tsel s) b) + 1 else entryPc (segT b) (segV (tsel s) b) (b % 16) + 3,
        true, if b % 16 = 0 then 4 else 6, if b % 16 = 0 then [] else [parBr (segT b) false], none⟩ := by
      unfold tabSpec; rw [if_neg ha']; rfl
    obtain ⟨u, hu⟩ := pspec_run (cOk (by unfold segA; omega)) u1 hpc1 (fun p hp => pb1.known p (List.mem_append_left _ hp))
      (by
        rw [hsp]; intro br hbr
        by_cases h0 : b % 16 = 0
        · simp [h0] at hbr
        · simp only [if_neg h0, List.mem_singleton] at hbr; subst hbr
          exact (parBr_holds hE1 _ ht false).mpr (by
            rcases hpar with e | e
            · exact absurd e h0
            · simp [e])) (by simp)
    have pb := pb1.run hu (by rw [hu.keep .x20 (by simp [tabKeep])]; exact pb1.x20) (by simp [tabKeep])
    have hK := hu.known
    have hkeep1 := hu1.keep
    have hkeep := hu.keep
    have r10 : u.getReg .x10 = BitVec.ofNat 64 (pendAddr pend stk.length) := by
      rw [hkeep .x10 (by simp [tabKeep]), hkeep1 .x10 (by simp [dispKeep])]; exact h.a0
    have r11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK (.x11, 64) (by simp [gkP])
    have r15 : u.getReg .x15 = BitVec.ofNat 64 (stkOf' stk.length) := by
      rw [hkeep .x15 (by simp [tabKeep]), hkeep1 .x15 (by simp [dispKeep])]; exact h.rS
    have mem : ∀ A, u.getMem A = m.getMem A := by
      intro A; rw [hu.mem, hsp]; show u1.getMem A = _; rw [hu1.mem]; rfl
    have hpm : PendMem P node stk.length u pend := by
      cases pend <;> simpa [PendMem, mem] using h.pmem
    obtain ⟨hin, hbl1⟩ := pend_hashInput pb pend node stk.length r10 r11 hpm
    have r12 : u.getReg .x12 = (if b % 16 = 0 then destE (segV (tsel s) b) else cw (0x1E0 + 16 * segT b)).eval u1 :=
      hu.regs (.x12, if b % 16 = 0 then destE (segV (tsel s) b) else cw (0x1E0 + 16 * segT b)) (by rw [hsp]; simp)
    have hdest : u.getReg .x12 = BitVec.ofNat 64 (if b % 16 = 0 then destOf (segV (tsel s) b) stk.length
        else 0x1E0 + 16 * segT b) := by
      rw [r12]
      split_ifs with h0
      · unfold destE destOf
        have r15' : u1.getReg .x15 = BitVec.ofNat 64 (stkOf' stk.length) := by
          rw [hkeep1 .x15 (by simp [dispKeep])]; exact h.rS
        split_ifs <;> simp [Rv.E.eval, BinOp.eval, cw, r15', BitVec.ofNat_add_ofNat]
      · rfl
    have hdl : stk.length ≤ 14 := by omega
    have hV1 : segV (tsel s) b = 1 → stk.length < 14 := by
      intro hv
      by_cases h14 : s = 14
      · subst h14; unfold segV tsel at hv; split_ifs at hv <;> simp_all
      · omega
    have hpa : pendAddr pend stk.length % 8 = 0 ∧ pendAddr pend stk.length + 64 ≤ 0x800 := by
      cases pend with
      | leaf => simp [pendAddr]
      | merge => simp only [pendAddr, PSB]; omega
    have hda : (if b % 16 = 0 then destOf (segV (tsel s) b) stk.length else 0x1E0 + 16 * segT b) % 8 = 0 ∧
        (if b % 16 = 0 then destOf (segV (tsel s) b) stk.length else 0x1E0 + 16 * segT b) + 32 ≤ 0x800 := by
      have ht : segT b < 2 := by unfold segT; omega
      split_ifs
      · unfold destOf stkOf' EMPTY; split_ifs <;> omega
      · omega
    have hsafe : safeDestP (if b % 16 = 0 then destOf (segV (tsel s) b) stk.length else 0x1E0 + 16 * segT b) = true := by
      split_ifs
      · exact safe_dest _ _ hdl hV1
      · exact safe_nb _ (by unfold segT; omega)
    have hargs : hashArgsB (pendAddr pend stk.length) (64 * (0 + 1))
        (if b % 16 = 0 then destOf (segV (tsel s) b) stk.length else 0x1E0 + 16 * segT b) = true := by
      simp only [hashArgsB, MEMORY_BYTES, Bool.and_eq_true, decide_eq_true_eq, Nat.reducePow,
        Nat.reduceMul, Nat.reduceAdd]
      refine ⟨⟨⟨⟨hpa.1, ?_, trivial⟩, decide_eq_true ?_⟩, decide_eq_true (And.intro ?_ hda.1)⟩, decide_eq_true ?_⟩ <;> omega
    refine ⟨4 + (if b % 16 = 0 then 4 else 6), u, by split_ifs <;> omega,
      (hu1.steps.trans hu.steps).of_eq (by simp [dispSpec, hsp]) (by simp [dispSpec, hsp]),
      hu.ecall (by simp [hsp]), pb.reg (by simp [gkP, baseK]),
      hashArgs_ofNat _ _ _ _ r10 r11 hdest (by omega) (by omega) (by omega) hargs,
      hin, hbl1, fun ans => ⟨fun h0 => ?_, fun h1 => ?_⟩⟩
    · -- a = 0: the pending hash went straight to the destination
      have hd0 : u.getReg .x12 = BitVec.ofNat 64 (destOf (segV (tsel s) b) stk.length) := by
        rw [hdest, if_pos h0]
      have hdl' : destOf (segV (tsel s) b) stk.length + 24 < 2 ^ 64 := by
        unfold destOf stkOf' EMPTY; split_ifs <;> omega
      refine ⟨pb.hash ans _ hd0 (safe_dest _ _ hdl hV1), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        (writeHash_at0 _ ans _ hd0 hdl').trans (vw0_answer ans).symm,
        (writeHash_at8 _ ans _ hd0 hdl').trans (vw1_answer ans).symm, by simp,
        by rw [writeHash_getReg]; exact hd0, ?_, h.hE, h.hx,
        by decide, segV_lt _ _, hV1⟩
      · rw [writeHash_pc, hu.pc (by rw [hsp]), hsp]
        simp only [if_pos h0, pcOf_add4, tailPc, if_true]
      · rw [writeHash_getReg, hu.regs (.x14, addC (.reg .x14) (BitVec.ofNat 64 (16 * (b % 16) + 8))) (by rw [hsp]; simp)]
        simp only [addC_eval, Rv.E.eval, hkeep1 .x14 (by simp [dispKeep]), h.fr, h0]
        rw [BitVec.ofNat_add_ofNat]; congr 1; omega
      · rw [writeHash_getReg, hkeep .x23 (by simp [tabKeep]), hkeep1 .x23 (by simp [dispKeep])]; exact h.rE
      · rw [writeHash_getReg, hu.regs (.x29, addC (.reg .x29) (BitVec.ofNat 64 (b % 16))) (by rw [hsp]; simp)]
        simp only [addC_eval, Rv.E.eval, hkeep1 .x29 (by simp [dispKeep]), h.sum, h0]
        rw [BitVec.ofNat_add_ofNat, Nat.add_zero]
      · rw [writeHash_getReg]; exact r15
      · apply StackOK.hash _ ans _ hd0 (by unfold destOf stkOf' EMPTY; split_ifs <;> omega)
          (stack_dest _ _ hdl) hdl
        apply h.stack.frame; intro i hi; simp [mem]
      · rw [writeHash_getReg, hkeep (xReg s) (by unfold xReg; split_ifs <;> simp [tabKeep]),
          hkeep1 (xReg s) (by unfold xReg; split_ifs <;> simp [dispKeep])]; exact h.cur
      · rw [writeHash_getReg, hkeep .x24 (by simp [tabKeep])]
        rcases h.copy with ⟨hc, -⟩ | ⟨hc, -, -⟩
        · rw [hu1.regs (.x24, cw (0x1000 + 4 * (dispPc c + 4))) (by simp [dispSpec, hc, hs])]
          simp [cw, Rv.E.eval, lnkOf, hc, dispPc, hs]
        · rw [hkeep1 .x24 (by simp [dispKeep, show ¬ c < 15 by omega])]; exact h.lnk hc
      · refine ⟨hs, hd, by omega, by omega, by omega, by omega⟩
    · -- a ≥ 1: the pending hash went into NB slot `t`
      have hdn : u.getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * segT b) := by
        rw [hdest, if_neg (by omega)]
      refine ⟨pb.hash ans _ hdn (safe_nb _ ht), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        (writeHash_at0 _ ans _ hdn (by omega)).trans (vw0_answer ans).symm, ?_, by simp, ⟨hs, hd, hp, hp8, hpb, hfb⟩, h.hE, h.hx,
        ⟨h1, by omega⟩, ht, segV_lt _ _, hV1⟩
      · rw [writeHash_pc, hu.pc (by rw [hsp]), hsp]
        simp only [if_neg (show ¬ b % 16 = 0 by omega), pcOf_add4]
      · rw [writeHash_getReg, hu.regs (.x14, addC (.reg .x14) (BitVec.ofNat 64 (16 * (b % 16) + 8))) (by rw [hsp]; simp)]
        simp only [addC_eval, Rv.E.eval, hkeep1 .x14 (by simp [dispKeep]), h.fr]
        rw [BitVec.ofNat_add_ofNat, Nat.add_assoc]
      · rw [writeHash_getReg, hkeep .x23 (by simp [tabKeep]), hkeep1 .x23 (by simp [dispKeep])]; exact h.rE
      · rw [writeHash_getReg, hu.regs (.x29, addC (.reg .x29) (BitVec.ofNat 64 (b % 16))) (by rw [hsp]; simp)]
        simp only [addC_eval, Rv.E.eval, hkeep1 .x29 (by simp [dispKeep]), h.sum]
        rw [BitVec.ofNat_add_ofNat]
      · rw [writeHash_getReg]; exact r15
      · apply StackOK.hash _ ans _ hdn (by omega) (fun i hi => by unfold blkQ blkL PSB; omega) hdl
        apply h.stack.frame; intro i hi; simp [mem]
      · rw [writeHash_getReg, hkeep (xReg s) (by unfold xReg; split_ifs <;> simp [tabKeep]),
          hkeep1 (xReg s) (by unfold xReg; split_ifs <;> simp [dispKeep])]; exact h.cur
      · rw [writeHash_getReg, hkeep .x24 (by simp [tabKeep])]
        rcases h.copy with ⟨hc, -⟩ | ⟨hc, -, -⟩
        · rw [hu1.regs (.x24, cw (0x1000 + 4 * (dispPc c + 4))) (by simp [dispSpec, hc, hs])]
          simp [cw, Rv.E.eval, lnkOf, hc, dispPc, hs]
        · rw [hkeep1 .x24 (by simp [dispKeep, show ¬ c < 15 by omega])]; exact h.lnk hc
      · rw [show 0x1E8 + 16 * segT b = 0x1E0 + 16 * segT b + 8 by omega]
        exact (writeHash_at8 _ ans _ hdn (by omega)).trans (vw1_answer ans).symm


/-! ## Entry tails and ladder positions -/

theorem entCheck_at (t V k : Nat) (ht : t < 2) (hV : V < 3) (hk1 : 1 ≤ k) (hk : k ≤ 14) :
    pspecB gkP (runAt gkP [ladPc V t (14 - k)] (entryPc t V k + 4) []) (entSpec t V k) []
      (gkP ++ [(.x10, 0x1C0)]) [.x14, .x15, .x16, .x17, .x20, .x22, .x23, .x24, .x29] = true := by
  have := entCheck_ok
  simp only [entCheck, List.all_eq_true, List.mem_range, List.mem_range'] at this
  exact this t ht V hV k ⟨k - 1, by omega, by omega⟩

/-- After the pending hash (`a ≥ 1`): `a0 = NB`, jump to the ladder position `14 - a`. -/
theorem ent_step (P : PCtx) (s0 : MachineState) (s x V t a ptr E folds : Nat) (node : Val)
    (stk : List (Val × Nat)) (m : MachineState) (h : EntIn P s0 s x V t a ptr E folds node stk m) :
    ∃ u, Steps image m 2 2 u ∧ PosIn P s0 s x V t a 0 ptr E folds node stk u := by
  have c := entCheck_at t V a h.ht h.hV h.ha.1 h.ha.2
  obtain ⟨u, hu⟩ := pspec_run c m h.pc (fun p hp => h.pb.known p (List.mem_append_left _ hp)) (by simp [entSpec]) (by simp)
  have kp : ∀ r ∈ ([.x14, .x15, .x16, .x17, .x20, .x22, .x23, .x24, .x29] : List Reg), u.getReg r = m.getReg r := hu.keep
  have pb := h.pb.run hu (by rw [kp .x20 (by simp)]; exact h.pb.x20) (by simp)
  have mem : ∀ A, u.getMem A = m.getMem A := fun A => by rw [hu.mem]; rfl
  refine ⟨u, hu.steps, pb, by rw [hu.pc rfl]; simp [entSpec], hu.known (.x10, 0x1C0) (by simp), ?_, ?_, ?_, ?_,
    h.stack.frame (fun i _ => by simp [mem]), ?_, ?_, by rw [mem]; exact h.node0, by rw [mem]; exact h.node1,
    h.nodeLen, h.bnd, h.hE, h.hx, ⟨h.ha.1, h.ha.2⟩, h.ht, h.hV, h.hd⟩
  · rw [kp .x14 (by simp)]; exact h.fr
  · rw [kp .x23 (by simp)]; exact h.rE
  · rw [kp .x29 (by simp)]; exact h.sum
  · rw [kp .x15 (by simp)]; exact h.rS
  · rw [kp (xReg s) (by unfold xReg; split_ifs <;> simp)]; exact h.cur
  · rw [kp .x24 (by simp)]; exact h.lnk

/-- The 16 bytes read at `off` (zero beyond the witness) as two memory words. -/
theorem range_getD (l : List Byte) (n : Nat) :
    (List.range n).map (fun i => l.getD i 0) = l.take n ++ zeros (n - l.length) := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.length_map, List.length_range] at h1
  simp only [List.getElem_map, List.getElem_range, List.getD_eq_getElem?_getD]
  by_cases hi : i < l.length
  · rw [List.getElem_append_left (by simp; omega), List.getElem_take, List.getElem?_eq_getElem hi]; rfl
  · rw [List.getElem_append_right (by simp; omega), List.getElem?_eq_none (by omega)]
    simp [zeros]

theorem w64_pad (l : List Byte) (k : Nat) : w64 (l ++ zeros k) = w64 l := by
  simp only [w64, leNat_append, leNat_zeros]; simp

theorem wbytes_split (wl : List Byte) (off : Nat) :
    vw0 (wbytes wl off 16) = w64 (slice wl off 8) ∧ vw1 (wbytes wl off 16) = w64 (slice wl (off + 8) 8) := by
  have e : ∀ o n, wbytes wl o n = (List.range n).map (fun i => (wl.drop o).getD i 0) := by
    intro o n; unfold wbytes; apply List.map_congr_left; intro i _
    simp [List.getD_eq_getElem?_getD]
  constructor
  · unfold vw0
    rw [e, ← List.map_take, List.take_range, show min 8 16 = 8 from rfl, range_getD, w64_pad]
    rfl
  · unfold vw1
    rw [e, ← List.map_drop, List.range_eq_range', List.drop_range', List.range'_eq_map_range, List.map_map]
    have : ((fun i => (wl.drop off).getD i 0) ∘ fun i => 0 + 8 + i) = fun i => (wl.drop (off + 8)).getD i 0 := by
      funext i; simp [List.getD_eq_getElem?_getD, Nat.add_comm, Nat.add_left_comm]
    rw [this, show 16 - 8 = 8 from rfl, range_getD, w64_pad]
    rfl

theorem psib_words {P : PCtx} {s0 m : MachineState} {tb : Nat} (h : PB P s0 m tb) (off : Nat)
    (h8 : off % 8 = 0) (hoff : off + 16 ≤ 7040) :
    m.getMem (BitVec.ofNat 64 (0x800 + off)) = vw0 (wbytes P.wl off 16) ∧
    m.getMem (BitVec.ofNat 64 (0x800 + off + 8)) = vw1 (wbytes P.wl off 16) := by
  rw [(wbytes_split P.wl off).1, (wbytes_split P.wl off).2, Nat.add_assoc]
  exact ⟨wit_word h.wit _ h8 (by omega), wit_word h.wit _ (by omega) (by omega)⟩

theorem lbr_lad : ∀ V, V < 3 → ∀ t, t < 2 → ∀ p, p < 13 → lbrPc V t (p + 1) + 2 = ladPc V t (p + 1) := by
  decide

theorem posCheck_at (V t p t' : Nat) (hV : V < 3) (ht : t < 2) (hp : p < 14) (ht' : t' < 2)
    (h13 : ¬ (p = 13 ∧ t' = 1)) : posCheck1 V t p t' = true := by
  have hc : posCheck V = true := by
    rcases (show V = 0 ∨ V = 1 ∨ V = 2 by omega) with rfl | rfl | rfl
    exacts [posCheck_0, posCheck_1, posCheck_2]
  simp only [posCheck, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at hc
  exact (hc t ht p hp t' ht').resolve_left h13

/-- The fold input of a ladder position (current node in slot `t`). -/
def foldInput (P : PCtx) (E t : Nat) (sib node : Val) : List Byte :=
  if t = 1 then porsNodeInput P.idx (E / 2) sib node else porsNodeInput P.idx (E / 2) node sib


theorem nb_hashInput {P : PCtx} {s0 u : MachineState} {tb : Nat} (pb : PB P s0 u tb) (H : Nat) (l r : Val)
    (hl : l.length = 16) (hr : r.length = 16) (_hH : H < 2 ^ 32)
    (h10 : u.getReg .x10 = BitVec.ofNat 64 0x1C0) (h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)))
    (m8 : u.getMem (BitVec.ofNat 64 0x1C8) = BitVec.ofNat 64 (twHi P.idx H))
    (l0 : u.getMem (BitVec.ofNat 64 0x1E0) = vw0 l) (l1 : u.getMem (BitVec.ofNat 64 0x1E8) = vw1 l)
    (r0 : u.getMem (BitVec.ofNat 64 0x1F0) = vw0 r) (r1 : u.getMem (BitVec.ofNat 64 0x1F8) = vw1 r) :
    hashInput u = fmt (porsNodeInput P.idx H l r) ∧ (fmt (porsNodeInput P.idx H l r)).blocks = 1 := by
  have hf : fmt (porsNodeInput P.idx H l r) = queryOfWords 0
      [BitVec.ofNat 64 (twLo 10 0 P.idx 0), BitVec.ofNat 64 (twHi P.idx H), 0, 0, vw0 l, vw1 l, vw0 r, vw1 r] := by
    rw [show porsNodeInput P.idx H l r = thInput (tweak 10 0 P.idx 0 H) (l ++ r) from rfl,
      fmt_th _ _ _ _ _ _ (by decide),
      ← show porsNodeInput P.idx H l r = thInput (tweak 10 0 P.idx 0 H) (l ++ r) from rfl,
      pad64_porsNodeInput _ _ _ _ hl hr]
  refine ⟨?_, by rw [hf]; rfl⟩
  rw [hf, hashInput_ofNat u 0x1C0 0 h10 h11 (by decide) (by decide)]
  congr 1
  simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
    Nat.mul_zero, List.cons.injEq]
  exact ⟨by rw [pb.prot (by decide), pb.s0ok.nb0], m8, pb.zero (by decide), pb.zero (by decide), l0, l1, r0, r1,
    trivial⟩

theorem eS_eval {m : MachineState} {E : Nat} (h : m.getReg .x23 = BitVec.ofNat 64 E) (hE : E < 2 ^ 15) :
    eS.eval m = BitVec.ofNat 64 (E / 2) := by
  apply BitVec.eq_of_toNat_eq
  simp only [eS, Rv.E.eval, BinOp.eval, cw, h, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.mod_eq_of_lt (show E < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show E / 2 < 2 ^ 64 by omega)]

/-- A ladder position: the fold of the current node (slot `t`) with the witness sibling, into
slot `(E / 2) mod 2` of NB (or into the variant's destination at the last position). -/
theorem pos_step (P : PCtx) (s0 : MachineState) (s x V t a i ptr E folds : Nat) (node : Val)
    (stk : List (Val × Nat)) (m : MachineState) (h : PosIn P s0 s x V t a i ptr E folds node stk m) :
    ∃ u, Steps image m (if i + 1 = a then 7 else 9) (if i + 1 = a then 7 else 9) u ∧
      fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧
      hashInput u = fmt (foldInput P E t (wbytes P.wl (ptr + 8 + 16 * i) 16) node) ∧
      (fmt (foldInput P E t (wbytes P.wl (ptr + 8 + 16 * i) 16) node)).blocks = 1 ∧
      ∀ ans, (i + 1 < a → PosIn P s0 s x V (E / 2 % 2) a (i + 1) ptr (E / 2) folds (answerBytes 16 ans) stk
          (writeHash u ans)) ∧
        (i + 1 = a → TailIn P s0 s x V t (ptr + 8 + 16 * a) (E / 2) (folds + a) (answerBytes 16 ans) stk
          (writeHash u ans)) := by
  obtain ⟨hs, hd, hp, hp8, hpb, hfb⟩ := h.bnd
  obtain ⟨hi1, ha14⟩ := h.ha
  have hE := h.hE
  have hp14 : 14 - a + i < 14 := by omega
  obtain ⟨t', ht'⟩ : ∃ t', t' = if i + 1 = a then 0 else E / 2 % 2 := ⟨_, rfl⟩
  have ht'2 : t' < 2 := by rw [ht']; split_ifs <;> omega
  have ht'13 : ¬ (14 - a + i = 13 ∧ t' = 1) := by
    rw [ht']; by_cases hl : i + 1 = a
    · rw [if_pos hl]; omega
    · rw [if_neg hl]; omega
  have c := posCheck_at V t (14 - a + i) t' h.hV h.ht hp14 ht'2 ht'13
  have hfr' : m.getReg .x14 = BitVec.ofNat 64 (0x800 + ptr + 8 + 16 * i - 16 * (14 - a + i)) := by
    rw [h.fr]; congr 1; omega
  have hsa : ∀ q, q = 0 ∨ q = 8 → (addC (.reg .x14) (BitVec.ofNat 64 (16 * (14 - a + i) + q))).eval m =
      BitVec.ofNat 64 (0x800 + (ptr + 8 + 16 * i) + q) := by
    intro q hq
    rw [addC_eval]; simp only [Rv.E.eval, hfr', BitVec.ofNat_add_ofNat]
    congr 1; omega
  have hK : KnownOK posKnown m := by
    intro q hq
    simp only [posKnown, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | hq
    · exact h.pb.reg hq
    · subst hq; exact h.a0
  have hEs := eS_eval h.rE h.hE
  obtain ⟨u, hu⟩ := pspec_run c m h.pc hK (by
      intro br hbr
      by_cases h13 : 14 - a + i = 13
      · simp [posSpec, h13] at hbr
      · simp only [posSpec, if_neg h13, List.mem_singleton] at hbr
        subst hbr
        have := sll63_cmp eS (E / 2) (by omega) m hEs
        simp only [Br.holds]
        rw [ht', if_neg (show ¬ i + 1 = a by omega)]
        unfold crossDir
        by_cases ht0 : t = 0
        · rw [if_pos ht0, if_pos ht0, this.1]
        · rw [if_neg ht0, if_neg ht0, this.2])
    (by
      intro o ho
      simp only [posObl, List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl
      · simp only [Oblig.holds, Addr.eval, Rv.E.eval, hfr', BitVec.ofNat_add_ofNat, accessValid, rangeValid,
          Bool.and_eq_true, decide_eq_true_eq, MEMORY_BYTES]
        rw [ofNat_toNat_lt _ (by omega)]; omega
      · simp only [Oblig.holds, Addr.eval, Rv.E.eval, hfr', BitVec.ofNat_add_ofNat, accessValid, rangeValid,
          Bool.and_eq_true, decide_eq_true_eq, MEMORY_BYTES]
        rw [ofNat_toNat_lt _ (by omega)]; omega)
  have hK' := hu.known
  have kp := hu.keep
  have pb := h.pb.run hu (by rw [kp .x20 (by simp [posKeep])]; exact h.pb.x20) (by simp [posKeep])
  have hlook := psr_look hu
  obtain ⟨sb0, sb1⟩ := psib_words h.pb (ptr + 8 + 16 * i) (by omega) (by omega)
  set sib := wbytes P.wl (ptr + 8 + 16 * i) 16 with hsib
  have hsl : sib.length = 16 := by simp [hsib, wbytes]
  have e1 : (ldR .x14 (16 * (14 - a + i))).eval m = vw0 sib := by
    show m.getMem ((addC (.reg .x14) (BitVec.ofNat 64 (16 * (14 - a + i)))).eval m) = _
    rw [show 16 * (14 - a + i) = 16 * (14 - a + i) + 0 from rfl, hsa 0 (Or.inl rfl), Nat.add_zero]; exact sb0
  have e2 : (ldR .x14 (16 * (14 - a + i) + 8)).eval m = vw1 sib := by
    show m.getMem ((addC (.reg .x14) (BitVec.ofNat 64 (16 * (14 - a + i) + 8))).eval m) = _
    rw [hsa 8 (Or.inr rfl)]; exact sb1
  have ht := h.ht
  have hpm : (posSpec V t (14 - a + i) t').mem = posMem t (14 - a + i) := by
    unfold posSpec; split_ifs <;> rfl
  have mem8 : u.getMem (BitVec.ofNat 64 0x1C8) = BitVec.ofNat 64 (twHi P.idx (E / 2)) := by
    rw [hlook 0x1C8 (by omega), hpm]
    simp only [posMem]
    rw [memLook_cons_eq _ _ _ _ rfl (by omega)]
    dsimp only
    rw [stW_eval' m 0x1C8 eS _ _ hEs (by omega) (h.pb.halfv (by decide)), twHi_eq _ _ (by omega)]
  have memS : u.getMem (BitVec.ofNat 64 (0x1F0 - 16 * t)) = vw0 sib ∧
      u.getMem (BitVec.ofNat 64 (0x1F8 - 16 * t)) = vw1 sib := by
    constructor
    · rw [hlook _ (by omega), hpm]
      simp only [posMem]
      rw [memLook_cons_ne _ _ _ _ (by simp; omega), memLook_cons_ne _ _ _ _ (by simp; omega),
        memLook_cons_eq _ _ _ _ rfl (by omega)]
      exact e1
    · rw [hlook _ (by omega), hpm]
      simp only [posMem]
      rw [memLook_cons_ne _ _ _ _ (by simp; omega), memLook_cons_eq _ _ _ _ rfl (by omega)]
      exact e2
  have memFr : ∀ A, A < 2 ^ 64 → A ≠ 0x1C8 → A ≠ 0x1F0 - 16 * t → A ≠ 0x1F8 - 16 * t →
      u.getMem (BitVec.ofNat 64 A) = m.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3
    rw [hlook A hA, hpm]
    simp only [posMem]
    rw [memLook_cons_ne _ _ _ _ (by simp; omega), memLook_cons_ne _ _ _ _ (by simp; omega),
      memLook_cons_ne _ _ _ _ (by simp; omega)]
    rfl
  have memN : u.getMem (BitVec.ofNat 64 (0x1E0 + 16 * t)) = vw0 node ∧
      u.getMem (BitVec.ofNat 64 (0x1E8 + 16 * t)) = vw1 node := by
    rw [memFr _ (by omega) (by omega) (by omega) (by omega), memFr _ (by omega) (by omega) (by omega) (by omega)]
    exact ⟨h.node0, h.node1⟩
  have r10 : u.getReg .x10 = BitVec.ofNat 64 0x1C0 := hK' (.x10, 0x1C0) (by simp [posKnown])
  have r11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, 64) (by simp [posKnown, gkP])
  have hH : E / 2 < 2 ^ 32 := by omega
  have hin : hashInput u = fmt (foldInput P E t sib node) ∧ (fmt (foldInput P E t sib node)).blocks = 1 := by
    unfold foldInput
    rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
    · simp only [if_neg (show ¬ (0 : Nat) = 1 by decide)]
      exact nb_hashInput pb _ _ _ h.nodeLen hsl hH r10 r11 mem8 (by simpa using memN.1) (by simpa using memN.2)
        (by simpa using memS.1) (by simpa using memS.2)
    · simp only [if_true]
      exact nb_hashInput pb _ _ _ hsl h.nodeLen hH r10 r11 mem8 (by simpa using memS.1) (by simpa using memS.2)
        (by simpa using memN.1) (by simpa using memN.2)
  have r15 : u.getReg .x15 = BitVec.ofNat 64 (stkOf' stk.length) := by rw [kp .x15 (by simp [posKeep])]; exact h.rS
  have r12 : u.getReg .x12 = BitVec.ofNat 64 (if i + 1 = a then destOf V stk.length else 0x1E0 + 16 * t') := by
    by_cases hl : i + 1 = a
    · rw [hu.regs (.x12, destE V) (by simp [posSpec, show 14 - a + i = 13 by omega]), if_pos hl]
      unfold destE destOf
      split_ifs <;> simp [Rv.E.eval, BinOp.eval, cw, h.rS, BitVec.ofNat_add_ofNat]
    · rw [hu.regs (.x12, cw (0x1E0 + 16 * t')) (by simp [posSpec, show ¬ 14 - a + i = 13 by omega]), if_neg hl]
      rfl
  have hdl : stk.length ≤ 14 := by omega
  have hdst : (if i + 1 = a then destOf V stk.length else 0x1E0 + 16 * t') + 32 ≤ 0x800 ∧
      (if i + 1 = a then destOf V stk.length else 0x1E0 + 16 * t') % 8 = 0 := by
    split_ifs
    · unfold destOf stkOf' EMPTY; split_ifs <;> omega
    · omega
  have hsafe : safeDestP (if i + 1 = a then destOf V stk.length else 0x1E0 + 16 * t') = true := by
    split_ifs
    · exact safe_dest _ _ hdl h.hd
    · exact safe_nb _ ht'2
  have hargs : hashArgsB 0x1C0 (64 * (0 + 1)) (if i + 1 = a then destOf V stk.length else 0x1E0 + 16 * t') = true := by
    simp only [hashArgsB, MEMORY_BYTES, Bool.and_eq_true, decide_eq_true_eq, Nat.reducePow,
      Nat.reduceMul, Nat.reduceAdd]
    refine ⟨⟨⟨⟨by decide, ?_, trivial⟩, decide_eq_true ?_⟩, decide_eq_true (And.intro ?_ hdst.2)⟩,
      decide_eq_true ?_⟩ <;> omega
  have hsteps : (posSpec V t (14 - a + i) t').steps = if i + 1 = a then 7 else 9 := by
    by_cases hl : i + 1 = a
    · simp [posSpec, show 14 - a + i = 13 by omega, hl]
    · simp [posSpec, show ¬ 14 - a + i = 13 by omega, hl]
  refine ⟨u, hsteps ▸ hu.steps, hu.ecall (by by_cases hl : 14 - a + i = 13 <;> simp [posSpec, hl]),
    pb.reg (by simp [gkP, baseK]), hashArgs_ofNat _ _ _ _ r10 r11 r12 (by omega) (by omega) (by omega) hargs,
    hin.1, hin.2, fun ans => ⟨fun hlt => ?_, fun hl => ?_⟩⟩
  · -- the next position
    have r12' : u.getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * t') := by rw [r12, if_neg (by omega)]
    have ht'v : t' = E / 2 % 2 := by rw [ht', if_neg (by omega)]
    rw [← ht'v]
    refine ⟨pb.hash ans _ r12' (safe_nb _ ht'2), ?_, by rw [writeHash_getReg]; exact r10, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, (writeHash_at0 _ ans _ r12' (by omega)).trans (vw0_answer ans).symm, ?_, by simp,
      ⟨hs, hd, hp, hp8, hpb, hfb⟩, by omega, h.hx, ⟨hlt, ha14⟩, ht'2, h.hV, h.hd⟩
    · rw [writeHash_pc, hu.pc (by simp [posSpec, show ¬ 14 - a + i = 13 by omega]), pcOf_add4]
      simp only [posSpec, show ¬ 14 - a + i = 13 by omega, if_false]
      rw [lbr_lad V h.hV t' ht'2 (14 - a + i) (by omega), show 14 - a + i + 1 = 14 - a + (i + 1) by omega]
    · rw [writeHash_getReg, kp .x14 (by simp [posKeep])]; exact h.fr
    · rw [writeHash_getReg, hu.regs (.x23, eS) (by simp [posSpec]; split_ifs <;> simp), hEs]
    · rw [writeHash_getReg, kp .x29 (by simp [posKeep])]; exact h.sum
    · rw [writeHash_getReg]; exact r15
    · apply StackOK.hash _ ans _ r12' (by omega) (fun i hi => by unfold blkQ blkL PSB; omega) hdl
      apply h.stack.frame_low hdl
      intro A h1 h2
      exact memFr A (by omega) (by omega) (by omega) (by omega)
    · rw [writeHash_getReg, kp (xReg s) (by unfold xReg; split_ifs <;> simp [posKeep])]; exact h.cur
    · rw [writeHash_getReg, kp .x24 (by simp [posKeep])]; exact h.lnk
    · rw [show 0x1E8 + 16 * t' = 0x1E0 + 16 * t' + 8 by omega]
      exact (writeHash_at8 _ ans _ r12' (by omega)).trans (vw1_answer ans).symm
  · -- the last position: the variant's destination
    have r12' : u.getReg .x12 = BitVec.ofNat 64 (destOf V stk.length) := by rw [r12, if_pos hl]
    have hdl' : destOf V stk.length + 24 < 2 ^ 64 := by unfold destOf stkOf' EMPTY; split_ifs <;> omega
    refine ⟨pb.hash ans _ r12' (safe_dest _ _ hdl h.hd), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (writeHash_at0 _ ans _ r12' hdl').trans (vw0_answer ans).symm,
      (writeHash_at8 _ ans _ r12' hdl').trans (vw1_answer ans).symm, by simp,
      by rw [writeHash_getReg]; exact r12', ?_, by omega, h.hx,
      by omega, h.hV, h.hd⟩
    · rw [writeHash_pc, hu.pc (by simp [posSpec, show 14 - a + i = 13 by omega]), pcOf_add4]
      simp only [posSpec, show 14 - a + i = 13 by omega, if_true, tailPc, show ¬ t = 2 by omega, if_false]
    · rw [writeHash_getReg, kp .x14 (by simp [posKeep]), h.fr]; congr 1; omega
    · rw [writeHash_getReg, hu.regs (.x23, eS) (by simp [posSpec]; split_ifs <;> simp), hEs]
    · rw [writeHash_getReg, kp .x29 (by simp [posKeep])]; exact h.sum
    · rw [writeHash_getReg]; exact r15
    · apply StackOK.hash _ ans _ r12' (by unfold destOf stkOf' EMPTY; split_ifs <;> omega)
        (stack_dest _ _ hdl) hdl
      apply h.stack.frame_low hdl
      intro A h1 h2
      exact memFr A (by omega) (by omega) (by omega) (by omega)
    · rw [writeHash_getReg, kp (xReg s) (by unfold xReg; split_ifs <;> simp [posKeep])]; exact h.cur
    · rw [writeHash_getReg, kp .x24 (by simp [posKeep])]; exact h.lnk
    · refine ⟨hs, hd, by omega, by omega, by omega, by omega⟩


/-! ## Tails -/

theorem tailCheck_parts (c : Nat) (hc : c < 3) :
    (∀ d, d < 15 →
      pspecB gkP (runAt (tailKnown d) [dispTailPc c] (tailPc 0 c) [.br false]) (tailMSpec c d) []
        (tailKnown d |>.map fun p => if p.1 = .x15 then (.x15, BitVec.ofNat 64 (stkOf d - 80)) else p)
        tailKeep = true ∧
      pspecB [] (runAt (tailKnown d) [] (tailPc 0 c) [.br true]) (tailMRej d) [] [] [] = true) ∧
    (∀ d, d < 14 →
      pspecB gkP (runAt (tailKnown d) [] (tailPc 1 c) [.jmp]) (tailPSpec d) []
        (tailKnown d |>.map fun p => if p.1 = .x15 then (.x15, BitVec.ofNat 64 (stkOf d + 80)) else p)
        [.x14, .x16, .x17, .x20, .x22, .x23, .x24, .x29] = true) := by
  have := List.all_eq_true.mp tailCheck_all c (List.mem_range.mpr hc)
  simp only [tailCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at this
  exact ⟨fun d hd => this.1 d hd, fun d hd => this.2 d hd⟩

theorem stkOf_eq (d : Nat) : stkOf d = stkOf' d := rfl

theorem stkE_cons' (stk : List (Val × Nat)) (e : Val × Nat) (i : Nat) (hi : i < stk.length) :
    stkE (e :: stk) i = stkE stk i := by
  unfold stkE
  rw [List.reverse_cons, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; omega)]

theorem StackOK.pop {e : Val × Nat} {rest : List (Val × Nat)} {m : MachineState}
    (h : StackOK (e :: rest) m) : StackOK rest m := by
  intro i hi
  have := h i (by simp; omega)
  rw [stkE_cons' rest e i hi] at this
  exact this

theorem tailKnown_ok {P : PCtx} {s0 m : MachineState} {tb d : Nat} (pb : PB P s0 m tb)
    (h15 : m.getReg .x15 = BitVec.ofNat 64 (stkOf' d)) : KnownOK (tailKnown d) m := by
  intro q hq
  simp only [tailKnown, List.mem_append, List.mem_singleton] at hq
  rcases hq with hq | hq
  · exact pb.reg hq
  · subst hq; exact h15

theorem stkE_cons (stk : List (Val × Nat)) (e : Val × Nat) (i : Nat) (hi : i < stk.length) :
    stkE (e :: stk) i = stkE stk i := by
  unfold stkE
  rw [List.reverse_cons, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp; omega)]

theorem stkE_top (stk : List (Val × Nat)) (e : Val × Nat) : stkE (e :: stk) stk.length = e := by
  unfold stkE
  rw [List.reverse_cons, List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

/-- The merge tail: pop (compare the popped `Q` with `E`), the merge block becomes the pending
input, `E := E / 2`; up to the dispatch of the next segment. -/
theorem tailM_step (P : PCtx) (s0 : MachineState) (s x c ptr E folds : Nat) (node : Val)
    (stk : List (Val × Nat)) (m : MachineState) (h : TailIn P s0 s x 0 c ptr E folds node stk m) :
    (∀ (pnode : Val) (Q : Nat) (rest : List (Val × Nat)), stk = (pnode, Q) :: rest → Q ≠ E →
      ∃ u, Steps image m 5 5 u ∧ fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (stk = [] → ∃ u, Steps image m 5 5 u ∧ fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧
      u.getReg .x10 = 1) ∧
    (∀ (pnode : Val) (rest : List (Val × Nat)), stk = (pnode, E) :: rest →
      ∃ u, Steps image m 6 6 u ∧ DispIn P s0 s x (15 + c) ptr (E / 2) folds (.merge (E / 2) pnode) node rest u) := by
  obtain ⟨hs, hd, hp, hp8, hpb, hfb⟩ := h.bnd
  have hE := h.hE
  have hc := h.hc
  have hd15 : stk.length < 15 := by omega
  obtain ⟨cM, -⟩ := tailCheck_parts c hc
  obtain ⟨cAcc, cRej⟩ := cM stk.length hd15
  have hK := tailKnown_ok h.pb h.rS
  -- the word below STK: the guard (empty stack) or the top's Q
  have hq : ∀ (pnode : Val) (Q : Nat) (rest : List (Val × Nat)), stk = (pnode, Q) :: rest →
      m.getMem (BitVec.ofNat 64 (stkOf stk.length - 16)) = BitVec.ofNat 64 Q ∧ Q < 2 ^ 15 ∧
        m.getMem (BitVec.ofNat 64 (blkL rest.length)) = vw0 pnode ∧
        m.getMem (BitVec.ofNat 64 (blkL rest.length + 8)) = vw1 pnode ∧ pnode.length = 16 := by
    intro pnode Q rest he
    have hi : rest.length < stk.length := by rw [he]; simp
    have := h.stack rest.length hi
    rw [he, stkE_top] at this
    obtain ⟨q1, q2, q3, q4, q5⟩ := this
    refine ⟨?_, q5, q2, q3, q4⟩
    rw [he, show stkOf ((pnode, Q) :: rest).length - 16 = blkQ rest.length by
      simp [stkOf, blkQ, EMPTY, PSB]; omega]
    exact q1
  have hrej : (m.getMem (BitVec.ofNat 64 (stkOf stk.length - 16)) ≠ BitVec.ofNat 64 E) →
      ∃ u, Steps image m 5 5 u ∧ fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1 := by
    intro hne
    obtain ⟨u, hu⟩ := pspec_run cRej m h.pc hK (by
      intro b hb
      simp only [tailMRej, rejSpec, List.mem_singleton] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, h.rE, bne_iff_ne, ne_eq]
      exact hne) (by simp)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [tailMRej, rejSpec]),
      hu.regs (.x10, cw 1) (by simp [tailMRej, rejSpec])⟩
  refine ⟨fun pnode Q rest he hne => hrej ?_, fun he => hrej ?_, fun pnode rest he => ?_⟩
  · obtain ⟨q1, q2, -⟩ := hq pnode Q rest he
    rw [q1]; intro e; exact hne ((ofNat_eq_iff (by omega) (by omega)).mp e)
  · rw [he]
    show m.getMem (BitVec.ofNat 64 (stkOf 0 - 16)) ≠ _
    rw [show stkOf 0 - 16 = 0x240 from rfl, h.pb.prot (by decide), h.pb.s0ok.guard]
    intro e
    have := congrArg BitVec.toNat e
    rw [ofNat_toNat_lt _ (by omega)] at this
    simp at this; omega
  · obtain ⟨q1, q2, l0, l1, hpl⟩ := hq pnode E rest he
    have hdl : stk.length = rest.length + 1 := by rw [he]; simp
    obtain ⟨u, hu⟩ := pspec_run cAcc m h.pc hK (by
      intro b hb
      simp only [tailMSpec, List.mem_singleton] at hb
      subst hb
      simp only [Br.holds, CmpOp.eval, Rv.E.eval, ldE, cw, h.rE, q1, bne_self_eq_false]) (by simp)
    have kp := hu.keep
    have pb := h.pb.run hu (by rw [kp .x20 (by simp [tailKeep])]; exact h.pb.x20) (by simp [tailKeep])
    have hlook := psr_look hu
    have hEs := eS_eval h.rE hE
    have hb8 : u.getMem (BitVec.ofNat 64 (PSB + 80 * rest.length + 8)) = BitVec.ofNat 64 (twHi P.idx (E / 2)) := by
      rw [hlook _ (by unfold PSB; omega)]
      simp only [tailMSpec]
      rw [memLook_cons_eq _ _ _ _ (by simp [stkOf, EMPTY, PSB, hdl]; omega) (by simp [stkOf, EMPTY]; omega)]
      dsimp only
      rw [stW_eval' m _ eS _ _ hEs (by omega), twHi_eq _ _ (by omega)]
      have := h.pb.halfv (halfP_blk rest.length (by omega))
      rw [show stkOf stk.length + 8 = PSB + 80 * rest.length + 8 by simp [stkOf, EMPTY, PSB, hdl]; omega]
      exact this
    have mfr : ∀ A, A < 2 ^ 64 → A ≠ PSB + 80 * rest.length + 8 → u.getMem (BitVec.ofNat 64 A) = m.getMem (BitVec.ofNat 64 A) := by
      intro A hA hne
      rw [hlook A hA]
      simp only [tailMSpec]
      rw [memLook_cons_ne _ _ _ _ (by simp [stkOf, EMPTY, PSB, hdl] at hne ⊢; omega)]
      rfl
    refine ⟨u, hu.steps, ⟨pb, ?_, Or.inr ⟨by omega, by omega, rfl⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, fun _ => ?_,
      ⟨hs, by omega, hp, hp8, by omega, by omega⟩, by omega, h.hx⟩⟩
    · rw [hu.pc rfl]; simp [tailMSpec, dispPc]
    · rw [kp .x14 (by simp [tailKeep])]; exact h.fr
    · rw [hu.regs (.x23, eS) (by simp [tailMSpec]), hEs]
    · rw [kp .x29 (by simp [tailKeep])]; exact h.sum
    · rw [hu.regs (.x15, cw (stkOf stk.length - 80)) (by simp [tailMSpec])]
      show BitVec.ofNat 64 (stkOf stk.length - 80) = BitVec.ofNat 64 (stkOf' rest.length)
      congr 1; simp only [stkOf, stkOf', hdl]; omega
    · rw [he] at h
      apply h.stack.pop.frame
      intro i hi
      refine ⟨mfr _ (by unfold blkQ PSB; omega) (by unfold blkQ PSB; omega),
        mfr _ (by unfold blkL PSB; omega) (by unfold blkL PSB; omega),
        mfr _ (by unfold blkL PSB; omega) (by unfold blkL PSB; omega)⟩
    · rw [hu.regs (.x10, cw (stkOf stk.length)) (by simp [tailMSpec])]
      show BitVec.ofNat 64 (stkOf stk.length) = _
      simp only [pendAddr, stkOf, hdl, EMPTY, PSB]; congr 1; omega
    · have n0 := h.node0; have n1 := h.node1
      simp only [destOf, if_true, stkOf'] at n0 n1
      refine ⟨hb8, ?_, ?_, ?_, ?_, hpl, h.nodeLen, by omega, by omega⟩
      · rw [mfr _ (by unfold PSB; omega) (by omega), show PSB + 80 * rest.length + 32 = blkL rest.length from rfl]
        exact l0
      · rw [mfr _ (by unfold PSB; omega) (by omega), show PSB + 80 * rest.length + 40 = blkL rest.length + 8 from rfl]
        exact l1
      · rw [mfr _ (by unfold PSB; omega) (by omega), show PSB + 80 * rest.length + 48 = EMPTY + 80 * stk.length + 48 by
          simp [PSB, EMPTY, hdl]; omega]
        exact n0
      · rw [mfr _ (by unfold PSB; omega) (by omega), show PSB + 80 * rest.length + 56 = EMPTY + 80 * stk.length + 48 + 8 by
          simp [PSB, EMPTY, hdl]; omega]
        exact n1
    · rw [kp (xReg s) (by unfold xReg; split_ifs <;> simp [tailKeep])]; exact h.cur
    · rw [kp .x24 (by simp [tailKeep])]; exact h.lnk


theorem disp_next : ∀ s, s < 14 → dispLeafPc s + 4 = leafPc (s + 1) := by decide

theorem lnkOf_even (s : Nat) : lnkOf s % 2 = 0 := by unfold lnkOf; omega

theorem xReg_add2 (s : Nat) : xReg (s + 1 + 1) = xReg s := by
  unfold xReg; congr 1; apply propext; omega

theorem tbOf_lt14 (s : Nat) (hs : s < 14) : tbOf s = tbN := by unfold tbOf; rw [if_neg (by omega)]

/-- The push tail: push `(node, E xor 1)` (the node already sits in the new block's `L` slot),
return to the next leaf. -/
theorem tailP_step (P : PCtx) (s0 : MachineState) (s x c ptr E folds : Nat) (node : Val)
    (stk : List (Val × Nat)) (m : MachineState) (hs14 : s < 14)
    (h : TailIn P s0 s x 1 c ptr E folds node stk m) :
    ∃ u, Steps image m 4 4 u ∧ LeafIn P s0 (s + 1) ⟨ptr, x, E, folds, node, (node, E ^^^ 1) :: stk⟩ u := by
  obtain ⟨hs, hd, hp, hp8, hpb, hfb⟩ := h.bnd
  have hE := h.hE
  have hdl : stk.length < 14 := h.hd rfl
  obtain ⟨-, cP⟩ := tailCheck_parts c h.hc
  have hK := tailKnown_ok h.pb h.rS
  obtain ⟨u, hu⟩ := pspec_run (cP stk.length hdl) m h.pc hK (by simp [tailPSpec]) (by simp)
  have kp := hu.keep
  have pb := h.pb.run hu (tb' := tbN) (by rw [kp .x20 (by simp)]; rw [← tbOf_lt14 s hs14]; exact h.pb.x20) (by simp)
  have hlook := psr_look hu
  have hxor : (E ^^^ 1) < 2 ^ 15 := Nat.xor_lt_two_pow hE (by decide)
  have hq : u.getMem (BitVec.ofNat 64 (stkOf stk.length + 64)) = BitVec.ofNat 64 (E ^^^ 1) := by
    rw [hlook _ (by simp [stkOf, EMPTY]; omega)]
    simp only [tailPSpec]
    rw [memLook_cons_eq _ _ _ _ rfl (by simp [stkOf, EMPTY]; omega)]
    simp only [Rv.E.eval, BinOp.eval, cw, h.rE]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_xor, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (show E < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show (1 : Nat) < 2 ^ 64 by decide),
      Nat.mod_eq_of_lt (show E ^^^ 1 < 2 ^ 64 by omega)]
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ stkOf stk.length + 64 → u.getMem (BitVec.ofNat 64 A) = m.getMem (BitVec.ofNat 64 A) := by
    intro A hA hne
    rw [hlook A hA]
    simp only [tailPSpec]
    rw [memLook_cons_ne _ _ _ _ (by simp [stkOf, EMPTY] at hne ⊢; omega)]
    rfl
  refine ⟨u, hu.steps, ⟨pb, ?_, ?_, ?_, ?_, ?_, fun _ => ⟨?_, h.hx⟩, ⟨by omega, by simp; omega, hp, hp8, by simp; omega,
    by simp; omega⟩⟩⟩
  · rw [hu.spc _ rfl]
    show m.getReg .x24 &&& ~~~1#64 = _
    rw [h.lnk, even_andNot1' _ (lnkOf_even s), lnkOf, disp_next s hs14]; rfl
  · rw [kp .x14 (by simp)]; exact h.fr
  · rw [kp .x29 (by simp)]; exact h.sum
  · rw [hu.regs (.x15, cw (stkOf stk.length + 80)) (by simp [tailPSpec])]
    show BitVec.ofNat 64 (stkOf stk.length + 80) = BitVec.ofNat 64 (stkOf' (stk.length + 1))
    congr 1
  · intro i hi
    simp only [List.length_cons] at hi
    by_cases hit : i < stk.length
    · rw [stkE_cons' stk _ i hit]
      obtain ⟨q1, q2, q3, q4, q5⟩ := h.stack i hit
      refine ⟨?_, ?_, ?_, q4, q5⟩
      · rw [mfr _ (by unfold blkQ PSB; omega) (by unfold blkQ stkOf EMPTY PSB; omega)]; exact q1
      · rw [mfr _ (by unfold blkL PSB; omega) (by unfold blkL stkOf EMPTY PSB; omega)]; exact q2
      · rw [mfr _ (by unfold blkL PSB; omega) (by unfold blkL stkOf EMPTY PSB; omega)]; exact q3
    · have hi' : i = stk.length := by omega
      subst hi'
      rw [stkE_top]
      have n0 := h.node0; have n1 := h.node1
      simp only [destOf, show (1 : Nat) ≠ 0 by decide, if_false, if_true, stkOf'] at n0 n1
      refine ⟨?_, ?_, ?_, h.nodeLen, hxor⟩
      · rw [show blkQ stk.length = stkOf stk.length + 64 by unfold blkQ stkOf EMPTY PSB; omega]; exact hq
      · rw [mfr _ (by unfold blkL PSB; omega) (by unfold blkL stkOf EMPTY PSB; omega),
          show blkL stk.length = EMPTY + 80 * stk.length + 112 by unfold blkL EMPTY PSB; omega]
        exact n0
      · rw [mfr _ (by unfold blkL PSB; omega) (by unfold blkL stkOf EMPTY PSB; omega),
          show blkL stk.length + 8 = EMPTY + 80 * stk.length + 112 + 8 by unfold blkL EMPTY PSB; omega]
        exact n1
  · rw [xReg_add2, kp (xReg s) (by unfold xReg; split_ifs <;> simp)]; exact h.cur

end SigGolfCandidate.Verify
