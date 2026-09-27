import SigGolfCandidate.Verify.StartSem
import SigGolfCandidate.Verify.LayerGood

/-! # FORS trees: tree 0 (after the digest), trees 1..13 (prefix + leaf hash), fold ends, roots -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

def DCtx.idx (d : DCtx) : Nat := d.A % 2 ^ 34
def DCtx.u (d : DCtx) (k : Nat) : Nat := d.A / 2 ^ (34 + 10 * k) % 1024
def DCtx.fw (d : DCtx) (k : Nat) : Nat := 2305 + 65536 * k + 2 ^ 24 * (d.idx / 2 ^ 32)

theorem d_u_lt (d : DCtx) (k : Nat) : d.u k < 1024 := Nat.mod_lt _ (by decide)
theorem d_idx_lt (d : DCtx) : d.idx < 2 ^ 34 := Nat.mod_lt _ (by decide)
theorem d_fw_lt (d : DCtx) (k : Nat) (hk : k < 14) : d.fw k < 2 ^ 32 := by
  have := d_idx_lt d
  unfold DCtx.fw
  have : d.idx / 2 ^ 32 < 4 := by omega
  omega

def RBOk (roots : List Val) (s : MachineState) : Prop :=
  ∀ j, j < roots.length → s.getMem (BitVec.ofNat 64 (0x240 + 16 * j)) = vw0 (roots.getD j []) ∧
    s.getMem (BitVec.ofNat 64 (0x248 + 16 * j)) = vw1 (roots.getD j [])

/-- Registers and memory carried through FORS tree `k` (after its prefix). -/
def TreeCarry (d : DCtx) (k : Nat) (roots : List Val) (s : MachineState) : Prop :=
  s.getReg .x16 = d.a.extractLsb' 0 64 ∧ s.getReg .x17 = d.a.extractLsb' 64 64 ∧
  s.getReg .x25 = d.a.extractLsb' 128 64 ∧ s.getReg .x22 = BitVec.ofNat 64 d.idx ∧
  s.getReg .x29 = BitVec.ofNat 64 (d.fw k) ∧ s.getReg .x27 = BitVec.ofNat 64 (d.fw k + 256 + 2 ^ 32) ∧
  (s.getMem (BitVec.ofNat 64 0xC0)).toNat < 2 ^ 32 ∧
  (s.getMem (BitVec.ofNat 64 0xC8)).toNat % 2 ^ 32 = d.idx % 2 ^ 32 ∧
  s.getMem (BitVec.ofNat 64 0xF0) = 0 ∧ s.getMem (BitVec.ofNat 64 0xF8) = 0 ∧
  RBOk roots s ∧ (∀ v ∈ roots, v.length = 16) ∧
  s.getMem (BitVec.ofNat 64 0x220) = BitVec.ofNat 64 (2817 + 2 ^ 24 * (d.idx / 2 ^ 32)) ∧
  s.getMem (BitVec.ofNat 64 0x228) = BitVec.ofNat 64 (d.idx % 2 ^ 32)

/-- After FORS tree `k - 1` (hash into RB2), in either stream. -/
def ForsIn (d : DCtx) (k : Nat) (roots : List Val) (s : MachineState) : Prop :=
  Glob gkF d.wl d.pk s ∧ KnownOK (fK (k - 1)) s ∧ TreeCarry d (k - 1) roots s ∧ roots.length = k ∧
  (s.getMem (BitVec.ofNat 64 0x1C8)).toNat % 2 ^ 32 = d.idx % 2 ^ 32 ∧
  ∃ t, t < 2 ∧ s.pc = pcOf (tEnd (k - 1) t)

def forsFC (d : DCtx) (k : Nat) : FCtx :=
  ⟨d.wl, d.pk, d.u k, 10, true, k / 7, 10 * (k % 7), 64, 10, k, d.idx, 32 + 176 * k, 0x240 + 16 * k⟩

theorem forsFC_ok (d : DCtx) (hwl : d.wl.length = 7756) (k : Nat) (hk : k < 14) : (forsFC d k).ok := by
  refine ⟨by simp [forsFC], by simp [forsFC], ?_, by simp [forsFC], ?_, hwl, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [forsFC]
  · exact d_u_lt d k
  · omega
  · omega
  · omega
  · interval_cases k <;> decide
  · omega
  · omega

theorem forsFC_check (d : DCtx) (k : Nat) (hk : k < 14) :
    foldCheck (forsFC d k).kind (forsFC d k).a1 (forsFC d k).rg (forsFC d k).j0 (forsFC d k).h
      (0x800 + (forsFC d k).sibOff) (forsFC d k).dst = true := by
  have := forsFoldOk_at k hk
  simp only [forsFoldOk] at this
  simp only [forsFC, ← Nat.add_assoc]
  exact this

theorem wRegE_eval (d : DCtx) (s : MachineState) (h16 : s.getReg .x16 = d.a.extractLsb' 0 64)
    (h17 : s.getReg .x17 = d.a.extractLsb' 64 64) (h25 : s.getReg .x25 = d.a.extractLsb' 128 64) :
    ∀ i, i < 3 → (wRegE i).eval s = BitVec.ofNat 64 (d.A / 2 ^ (64 * i) % 2 ^ 64) := by
  intro i hi
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
  interval_cases i <;>
    simp [wRegE, Rv.E.eval, h16, h17, h25, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, DCtx.A]

theorem wLdE_eval (d : DCtx) (s : MachineState) (h0 : s.getMem (BitVec.ofNat 64 0x160) = d.a.extractLsb' 0 64)
    (h1 : s.getMem (BitVec.ofNat 64 0x168) = d.a.extractLsb' 64 64)
    (h2 : s.getMem (BitVec.ofNat 64 0x170) = d.a.extractLsb' 128 64) :
    ∀ i, i < 3 → (wLdE i).eval s = BitVec.ofNat 64 (d.A / 2 ^ (64 * i) % 2 ^ 64) := by
  intro i hi
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))]
  interval_cases i <;>
    simp [wLdE, ldE, cw, Rv.E.eval, h0, h1, h2, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, DCtx.A]

def LeafF (d : DCtx) (k : Nat) (roots : List Val) (v : Val) (s : MachineState) : Prop :=
  FoldInv (forsFC d k) s 0 v s ∧ TreeCarry d k roots s ∧ roots.length = k

theorem merge_low (w v : Word) (hw : w.toNat < 2 ^ 32) (hv : v.toNat < 2 ^ 32) :
    StoreKind.merge .w w 0 v = v := by
  apply BitVec.eq_of_toNat_eq
  rw [merge_w0_toNat]; omega

theorem stW0_eval (s : MachineState) (a : Nat) (v : E) (V : Nat) (hv : v.eval s = BitVec.ofNat 64 V)
    (hV : V < 2 ^ 32) (hw : (s.getMem (BitVec.ofNat 64 a)).toNat < 2 ^ 32) :
    (stW0 a v).eval s = BitVec.ofNat 64 V := by
  show StoreKind.merge .w (s.getMem (BitVec.ofNat 64 a)) 0 (v.eval s) = _
  rw [hv, merge_low _ _ hw (by rw [BitVec.toNat_ofNat]; omega)]

theorem stW_eval' (s : MachineState) (a : Nat) (v : E) (V lo : Nat) (hv : v.eval s = BitVec.ofNat 64 V)
    (hV : V < 2 ^ 32) (hlo : (s.getMem (BitVec.ofNat 64 a)).toNat % 2 ^ 32 = lo) :
    (stW a v).eval s = BitVec.ofNat 64 (lo + 2 ^ 32 * V) := by
  apply BitVec.eq_of_toNat_eq
  show (StoreKind.merge .w (s.getMem (BitVec.ofNat 64 a)) 4 (v.eval s)).toNat = _
  rw [merge_w4_toNat, hv, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have : lo < 2 ^ 32 := by rw [← hlo]; exact Nat.mod_lt _ (by decide)
  omega


theorem treeCheck_spec (k : Nat) (h1 : 1 ≤ k) (hk : k < 14) (t b : Nat) (ht : t < 2) (hb : b < 2) :
    specB gkF (runAt (fK (k - 1)) [] (tEnd (k - 1) t) [.br (dirOf (tsh k t) b)]) (specTree k t b)
      (fk true 0xC0 64) forsKeep = true := by
  have := treeCheck_at k h1 hk
  simp only [treeCheck, List.all_eq_true, List.mem_range] at this
  exact this t ht b hb

theorem tree_branch (d : DCtx) (k t : Nat) (hk : k < 14) (s : MachineState)
    (hu : (uE' k).eval s = BitVec.ofNat 64 (d.u k)) :
    Br.holds s ⟨if tsh k t = 0 then .lt else .ge, .bin .sll (uE' k) (cw 63), .c 0,
      dirOf (tsh k t) (d.u k % 2)⟩ := by
  obtain ⟨hlt, hge⟩ := sll63_cmp (uE' k) (d.u k) (by have := d_u_lt d k; omega) s hu
  simp only [Br.holds]
  by_cases h0 : tsh k t = 0
  · rw [if_pos h0, hlt, dirOf, if_pos h0]
    rcases Nat.mod_two_eq_zero_or_one (d.u k) with h | h <;> simp [h]
  · rw [if_neg h0, hge, dirOf, if_neg h0]
    rcases Nat.mod_two_eq_zero_or_one (d.u k) with h | h <;> simp [h]

theorem tree_leaf (d : DCtx) (hwl : d.wl.length = 7756) (k : Nat) (hk1 : 1 ≤ k) (hk : k < 14)
    (roots : List Val) (s : MachineState) (hs : ForsIn d k roots s) :
    ∃ u, Steps image s (treeSteps k) (treeSteps k) u ∧ fetch image u = some (.base .ECALL) ∧
      u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧
      hashInput u = pad64 (ftsLeafInput k d.idx (d.u k) (witFtsSecret d.wl k)) ∧
      ∀ ans, LeafF d k roots (answerBytes 16 ans) (writeHash u ans) := by
  obtain ⟨hG, hK, ⟨h16, h17, h25, h22, h29, h27, hC0, hC8, hF0, hF8, hRB, hrv, hR0, hR8⟩, hlen, hN8,
    t, ht, hpc⟩ := hs
  have hU := uExprW_eval wRegE d.A s (wRegE_eval d s h16 h17 h25) k hk
  have hul := d_u_lt d k
  have hidx := d_idx_lt d
  have hfwl := d_fw_lt d k hk
  set b := d.u k % 2 with hb
  obtain ⟨u, hu⟩ := spec_run (treeCheck_spec k hk1 hk t b ht (by omega)) s hpc hK (by
    intro br hbr
    simp only [specTree, List.mem_cons, List.not_mem_nil, or_false] at hbr
    subst hbr
    exact tree_branch d k t hk s hU)
  have hK' := hu.known
  have h10 : u.getReg .x10 = BitVec.ofNat 64 0xC0 := hK' (.x10, _) (by simp [fk])
  have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, _) (by simp [fk])
  have h12 : u.getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * (d.u k % 2)) :=
    hu.regs (.x12, cw (480 + 16 * b)) (by simp [specTree])
  have hfw : fwE'.eval s = BitVec.ofNat 64 (d.fw k) := by
    show s.getReg .x29 + 65536#64 = _
    rw [h29, show (65536#64 : Word) = BitVec.ofNat 64 65536 from rfl, BitVec.ofNat_add_ofNat]
    congr 1; unfold DCtx.fw; omega
  have hmem := hu.mem
  have mfr : ∀ A, A < 2 ^ 64 → A ≠ 232 → A ≠ 224 → A ≠ 200 → A ≠ 192 →
      u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2 h3 h4
    rw [hmem, memEval_frame_ofNat _ _ _ hA (by
      simp only [specTree, List.mem_cons, List.not_mem_nil, or_false]
      rintro p (rfl | rfl | rfl | rfl) <;> simp <;> omega)]
  have mC0 : u.getMem (BitVec.ofNat 64 192) = BitVec.ofNat 64 (d.fw k) := by
    rw [hmem]; simp only [specTree]
    rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
      memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]
    exact stW0_eval s 192 _ _ hfw hfwl hC0
  have mC8 : u.getMem (BitVec.ofNat 64 200) = BitVec.ofNat 64 (d.idx % 2 ^ 32 + 2 ^ 32 * d.u k) := by
    rw [hmem]; simp only [specTree]
    rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
      memEval_cons_eq _ _ _ _ _ rfl]
    exact stW_eval' s 200 _ _ _ hU (by omega) hC8
  have sa : secAddr k = 0x800 + (16 + 176 * k) := by unfold secAddr; omega
  have hsl : (witFtsSecret d.wl k).length = 16 := by unfold witFtsSecret; apply length_slice16; omega
  have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
  have gl := hu.glob _ _ _ hG
  refine ⟨u, hu.steps, hu.ecall rfl, hK' (.x5, 0) (by simp [fk, gkOf, gkF, baseK]),
    hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
      (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega), ?_, ?_⟩
  · rw [hashInput_ofNat _ 0xC0 0 h10 h11 (by decide) (by decide), pad64_ftsLeafInput _ _ _ _ hsl]
    congr 1
    simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
      Nat.mul_zero, List.cons.injEq]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
    · rw [mC0]; congr 1; unfold twLo DCtx.fw; omega
    · rw [mC8]; congr 1; unfold twHi; omega
    · rw [mfr 0xD0 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · rw [mfr 0xD8 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hP _ (by decide)
    · rw [hmem]; simp only [specTree]
      rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]
      simp only [ldE, cw, Rv.E.eval]
      rw [sa, wit_word hG.2.1 _ (by omega) (by omega), witFtsSecret, vw0_slice]
    · rw [hmem]; simp only [specTree]
      rw [memEval_cons_eq _ _ _ _ _ rfl]
      simp only [ldE, cw, Rv.E.eval]
      rw [sa, show 0x800 + (16 + 176 * k) + 8 = 0x800 + (16 + 176 * k + 8) by omega,
        wit_word hG.2.1 _ (by omega) (by omega), witFtsSecret, vw1_slice]
    · rw [mfr 0xF0 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF0
    · rw [mfr 0xF8 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF8
  · intro ans
    have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x1E0 + 16 * (d.u k % 2) ∨ 0x1E0 + 16 * (d.u k % 2) + 32 ≤ A) =>
      writeHash_frame _ ans _ A h12 hA (by omega) h
    have fr : ∀ A, A < 2 ^ 64 → A ≠ 232 → A ≠ 224 → A ≠ 200 → A ≠ 192 →
        (A + 8 ≤ 0x1E0 + 16 * (d.u k % 2) ∨ 0x1E0 + 16 * (d.u k % 2) + 32 ≤ A) →
        (writeHash u ans).getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) :=
      fun A hA h1 h2 h3 h4 h5 => (wf A hA h5).trans (mfr A hA h1 h2 h3 h4)
    have rg : ∀ x ∈ forsKeep, (writeHash u ans).getReg x = s.getReg x := fun x hx => by
      rw [writeHash_getReg]; exact hu.keep x hx
    have hbit : bitOf (d.u k) 0 = d.u k % 2 := by simp [bitOf]
    have r29 : (writeHash u ans).getReg .x29 = BitVec.ofNat 64 (d.fw k) := by
      rw [writeHash_getReg, hu.regs (.x29, fwE') (by simp [specTree]), hfw]
    have r27 : (writeHash u ans).getReg .x27 = BitVec.ofNat 64 (d.fw k + 256 + 2 ^ 32) := by
      rw [writeHash_getReg, hu.regs (.x27, .bin .add (.reg .x27) (.c 65536)) (by simp [specTree])]
      show s.getReg .x27 + 65536#64 = _
      rw [h27, show (65536#64 : Word) = BitVec.ofNat 64 65536 from rfl, BitVec.ofNat_add_ofNat]
      congr 1; unfold DCtx.fw; omega
    refine ⟨⟨Glob_writeHash gl ans _ h12 (by
        rcases Nat.mod_two_eq_zero_or_one (d.u k) with h | h <;> rw [h] <;> decide),
      ?_, ?_, ?_, ?_, ?_, ?_, by simp, ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩,
      ⟨?_, ?_, ?_, ?_, r29, r27, ?_, ?_, ?_, ?_, ?_, hrv, ?_, ?_⟩, by omega⟩
    · have := Known_writeHash hK' ans
      simpa [forsFC] using this
    · rw [writeHash_getReg, hu.regs (.x23, uE' k) (by simp [specTree])]; exact hU
    · simp only [NBhdr, forsFC, if_true]
      rw [r27]; congr 1; unfold FCtx.lo0 DCtx.fw; simp only
      have : d.idx / 2 ^ 32 < 4 := by omega
      omega
    · rw [wf 0x1C8 (by omega) (by omega), mfr 0x1C8 (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hN8
    · simp only [forsFC, hbit]
      rw [writeHash_at0 _ ans _ h12 (by omega)]; exact (vw0_answer ans).symm
    · simp only [forsFC, hbit]
      rw [show 0x1E8 + 16 * (d.u k % 2) = 0x1E0 + 16 * (d.u k % 2) + 8 by omega,
        writeHash_at8 _ ans _ h12 (by omega)]; exact (vw1_answer ans).symm
    · rw [writeHash_pc, hu.pc rfl, pcOf_add4]
      simp only [specTree, forsFC, hbit, lvlPc, Nat.add_zero]
      rfl
    · rw [rg .x16 (by simp [forsKeep])]; exact h16
    · rw [rg .x17 (by simp [forsKeep])]; exact h17
    · rw [rg .x25 (by simp [forsKeep])]; exact h25
    · rw [rg .x22 (by simp [forsKeep])]; exact h22
    · rw [wf 0xC0 (by omega) (by omega), mC0, BitVec.toNat_ofNat]; omega
    · rw [wf 0xC8 (by omega) (by omega), mC8, BitVec.toNat_ofNat]; omega
    · rw [fr 0xF0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF0
    · rw [fr 0xF8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hF8
    · intro j hj
      rw [fr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        fr _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact hRB j hj
    · rw [fr 0x220 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hR0
    · rw [fr 0x228 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hR8


theorem stW0_mod (s : MachineState) (a : Nat) (v : E) (V : Nat) (hv : v.eval s = BitVec.ofNat 64 V)
    (hV : V < 2 ^ 64) (hw : (s.getMem (BitVec.ofNat 64 a)).toNat < 2 ^ 32) :
    (stW0 a v).eval s = BitVec.ofNat 64 (V % 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  show (StoreKind.merge .w (s.getMem (BitVec.ofNat 64 a)) 0 (v.eval s)).toNat = _
  rw [merge_w0_toNat, hv, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

theorem topCheck_parts :
    specB gkF (runAt dgK [] 33 [.br true, .br false]) (specDgOk 0) (fk true 0xC0 64) [] = true ∧
    specB gkF (runAt dgK [] 33 [.br true, .br true]) (specDgOk 1) (fk true 0xC0 64) [] = true ∧
    specB [] (runAt dgK [] 33 [.br false]) specDgRej [] [] = true := by
  have := topCheck_ok
  simp only [topCheck, Bool.and_eq_true] at this
  exact ⟨this.1.1.2, this.1.2, this.2⟩

theorem dg_leaf (d : DCtx) (hwl : d.wl.length = 7756) (s : MachineState) (hs : DigestOut d s) :
    (admissible (d.A % 2 ^ 184) = false → ∃ t, Steps image s 6 6 t ∧ fetch image t = some (.base .ECALL) ∧
        t.getReg .x5 = 1 ∧ t.getReg .x10 = 1) ∧
    (admissible (d.A % 2 ^ 184) = true → ∃ u, Steps image s 34 34 u ∧ fetch image u = some (.base .ECALL) ∧
        u.getReg .x5 = 0 ∧ hashArgumentsValid u = true ∧
        hashInput u = pad64 (ftsLeafInput 0 d.idx (d.u 0) (witFtsSecret d.wl 0)) ∧
        ∀ ans, LeafF d 0 [] (answerBytes 16 ans) (writeHash u ans)) := by
  obtain ⟨hG, hK, h0, h1, h2, hC0, hF0, hF8, hR0, hR8, hpc⟩ := hs
  obtain ⟨cOk0, cOk1, cRej⟩ := topCheck_parts
  have hw := wLdE_eval d s h0 h1 h2
  have hadm : admE.eval s = BitVec.ofNat 64 (d.A / 2 ^ 174 % 1024) := admE_eval d.A s (by
    have := hw 2 (by decide); simpa using this)
  have hadm' : admissible (d.A % 2 ^ 184) = decide (d.A / 2 ^ 174 % 1024 = 0) := by
    simp only [admissible, uOf, totalH, ftsA]
    rw [beq_eq_decide]
    congr 1
    apply propext
    constructor <;> intro h <;> omega
  have hbr : ∀ dd, Br.holds s ⟨.eq, admE, .c 0, dd⟩ ↔ decide (d.A / 2 ^ 174 % 1024 = 0) = dd := by
    intro dd
    simp only [Br.holds, CmpOp.eval, E.eval, hadm]
    rw [show (0 : Word) = BitVec.ofNat 64 0 from rfl]
    have : (BitVec.ofNat 64 (d.A / 2 ^ 174 % 1024) == BitVec.ofNat 64 0) =
        decide (d.A / 2 ^ 174 % 1024 = 0) := by
      rw [beq_eq_decide]; congr 1; apply propext
      exact ofNat_eq_iff (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) (by norm_num)) (by norm_num)
    rw [this]
  constructor
  · intro hna
    rw [hadm'] at hna
    obtain ⟨u, hu⟩ := spec_run cRej s hpc hK (by
      intro b hb
      simp only [specDgRej, List.mem_cons, List.not_mem_nil, or_false] at hb
      subst hb; exact (hbr false).mpr hna)
    exact ⟨u, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [specDgRej, rejK]),
      hu.regs (.x10, cw 1) (by simp [specDgRej, rejK])⟩
  · intro ha
    rw [hadm'] at ha
    have hU : u0E.eval s = BitVec.ofNat 64 (d.u 0) := uExprW_eval wLdE d.A s hw 0 (by decide)
    have hul := d_u_lt d 0
    have hidx := d_idx_lt d
    have hfwl := d_fw_lt d 0 (by decide)
    have hie : idxE.eval s = BitVec.ofNat 64 d.idx := idxE_eval d.A s (by simpa using hw 0 (by decide))
    have hhi : hiE.eval s = BitVec.ofNat 64 (2 ^ 24 * (d.idx / 2 ^ 32)) :=
      hiE_eval d.A s (by simpa using hw 0 (by decide))
    have hadd : ∀ c, (E.bin .add hiE (cw c)).eval s = BitVec.ofNat 64 (2 ^ 24 * (d.idx / 2 ^ 32) + c) := by
      intro c
      show hiE.eval s + BitVec.ofNat 64 c = _
      rw [hhi, BitVec.ofNat_add_ofNat]
    have hq : d.idx / 2 ^ 32 < 4 := by omega
    set b := d.u 0 % 2 with hb
    have hsp : specB gkF (runAt dgK [] 33 [.br true, .br (b == 1)]) (specDgOk b) (fk true 0xC0 64) [] = true := by
      rcases Nat.mod_two_eq_zero_or_one (d.u 0) with h | h
      · rw [hb, h]; exact cOk0
      · rw [hb, h]; exact cOk1
    obtain ⟨u, hu⟩ := spec_run hsp s hpc hK (by
      intro br hbr'
      simp only [specDgOk, List.mem_cons, List.not_mem_nil, or_false] at hbr'
      rcases hbr' with rfl | rfl
      · obtain ⟨hlt, -⟩ := sll63_cmp u0E (d.u 0) (by omega) s hU
        simp only [Br.holds]; rw [hlt]
        rcases Nat.mod_two_eq_zero_or_one (d.u 0) with h | h <;> simp [hb, h]
      · exact (hbr true).mpr ha)
    have hK' := hu.known
    have h10 : u.getReg .x10 = BitVec.ofNat 64 0xC0 := hK' (.x10, _) (by simp [fk])
    have h11 : u.getReg .x11 = BitVec.ofNat 64 (64 * (0 + 1)) := hK' (.x11, _) (by simp [fk])
    have h12 : u.getReg .x12 = BitVec.ofNat 64 (0x1E0 + 16 * (d.u 0 % 2)) :=
      hu.regs (.x12, cw (480 + 16 * b)) (by simp [specDgOk])
    have hmem := hu.mem
    have mfr : ∀ A, A < 2 ^ 64 → A ≠ 232 → A ≠ 224 → A ≠ 200 → A ≠ 192 → A ≠ 544 → A ≠ 552 →
        A ≠ 456 → u.getMem (BitVec.ofNat 64 A) = s.getMem (BitVec.ofNat 64 A) := by
      intro A hA h1 h2 h3 h4 h5 h6 h7
      rw [hmem, memEval_frame_ofNat _ _ _ hA (by
        simp only [specDgOk, List.mem_cons, List.not_mem_nil, or_false]
        rintro p (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp <;> omega)]
    have mC0 : u.getMem (BitVec.ofNat 64 192) = BitVec.ofNat 64 (d.fw 0) := by
      rw [hmem]; simp only [specDgOk]
      rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl,
        stW0_eval s 192 _ _ (hadd 2305) (by omega) hC0]
      congr 1; unfold DCtx.fw; omega
    have mC8 : u.getMem (BitVec.ofNat 64 200) = BitVec.ofNat 64 (d.idx % 2 ^ 32 + 2 ^ 32 * d.u 0) := by
      rw [hmem]; simp only [specDgOk]
      rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_eq _ _ _ _ _ rfl]
      apply BitVec.eq_of_toNat_eq
      show (StoreKind.merge .w (StoreKind.merge .w (s.getMem (BitVec.ofNat 64 200)) 0 (idxE.eval s)) 4
        (u0E.eval s)).toNat = _
      rw [merge_w4_toNat, merge_w0_toNat, hie, hU]
      simp only [BitVec.toNat_ofNat]
      omega
    have mR0 : u.getMem (BitVec.ofNat 64 544) = BitVec.ofNat 64 (2817 + 2 ^ 24 * (d.idx / 2 ^ 32)) := by
      rw [hmem]; simp only [specDgOk]
      rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_eq _ _ _ _ _ rfl, stW0_eval s 544 _ _ (hadd 2817) (by omega) hR0]
      congr 1; omega
    have mR8 : u.getMem (BitVec.ofNat 64 552) = BitVec.ofNat 64 (d.idx % 2 ^ 32) := by
      rw [hmem]; simp only [specDgOk]
      rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl,
        stW0_mod s 552 _ _ hie (by omega) hR8]
    have mN8 : (u.getMem (BitVec.ofNat 64 456)).toNat % 2 ^ 32 = d.idx % 2 ^ 32 := by
      rw [hmem]; simp only [specDgOk]
      rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_ne _ _ _ _ _ (by decide),
        memEval_cons_eq _ _ _ _ _ rfl]
      show (StoreKind.merge .w (s.getMem (BitVec.ofNat 64 456)) 0 (idxE.eval s)).toNat % 2 ^ 32 = _
      rw [merge_w0_toNat, hie, BitVec.toNat_ofNat]
      omega
    have hsl : (witFtsSecret d.wl 0).length = 16 := by unfold witFtsSecret; apply length_slice16; omega
    have hP : ∀ a ∈ pSlots, s.getMem (BitVec.ofNat 64 a) = 0 := hG.2.2.2
    have gl := hu.glob _ _ _ hG
    refine ⟨u, hu.steps, hu.ecall rfl, hK' (.x5, 0) (by simp [fk, gkOf, gkF, baseK]),
      hashArgs_ofNat _ _ _ _ h10 h11 h12 (by omega) (by omega) (by omega)
        (by simp only [hashArgsB, MEMORY_BYTES]; simp; omega), ?_, ?_⟩
    · rw [hashInput_ofNat _ 0xC0 0 h10 h11 (by decide) (by decide), pad64_ftsLeafInput _ _ _ _ hsl]
      congr 1
      simp only [List.range, List.range.loop, List.map, Nat.reduceAdd, Nat.reduceMul, Nat.add_zero,
        Nat.mul_zero, List.cons.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, trivial⟩
      · rw [mC0]; congr 1; unfold twLo DCtx.fw; omega
      · rw [mC8]; congr 1; unfold twHi; omega
      · rw [mfr 0xD0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hP _ (by decide)
      · rw [mfr 0xD8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hP _ (by decide)
      · rw [hmem]; simp only [specDgOk]
        rw [memEval_cons_ne _ _ _ _ _ (by decide), memEval_cons_eq _ _ _ _ _ rfl]
        simp only [ldE, cw, Rv.E.eval]
        rw [show (2064 : Nat) = 0x800 + 16 from rfl, wit_word hG.2.1 _ (by omega) (by omega), witFtsSecret,
          show 16 + 176 * 0 = 16 from rfl, vw0_slice]
      · rw [hmem]; simp only [specDgOk]
        rw [memEval_cons_eq _ _ _ _ _ rfl]
        simp only [ldE, cw, Rv.E.eval]
        rw [show (2072 : Nat) = 0x800 + 24 from rfl, wit_word hG.2.1 _ (by omega) (by omega), witFtsSecret,
          show 16 + 176 * 0 = 16 from rfl, vw1_slice]
      · rw [mfr 0xF0 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hF0
      · rw [mfr 0xF8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
        exact hF8
    · intro ans
      have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x1E0 + 16 * (d.u 0 % 2) ∨ 0x1E0 + 16 * (d.u 0 % 2) + 32 ≤ A) =>
        writeHash_frame _ ans _ A h12 hA (by omega) h
      have rg : ∀ (x : Reg) (e : E), (x, e) ∈ (specDgOk b).regs →
          (writeHash u ans).getReg x = e.eval s := fun x e hx => by
        rw [writeHash_getReg]; exact hu.regs (x, e) hx
      have hbit : bitOf (d.u 0) 0 = d.u 0 % 2 := by simp [bitOf]
      have r27 : (writeHash u ans).getReg .x27 = BitVec.ofNat 64 (d.fw 0 + 256 + 2 ^ 32) := by
        rw [rg .x27 (.bin .add hiE (cw 4294969857)) (by simp [specDgOk]), hadd]; congr 1; unfold DCtx.fw; omega
      refine ⟨⟨Glob_writeHash gl ans _ h12 (by
          rcases Nat.mod_two_eq_zero_or_one (d.u 0) with h | h <;> rw [h] <;> decide),
        ?_, ?_, ?_, ?_, ?_, ?_, by simp, ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩, ?_⟩,
        ⟨?_, ?_, ?_, ?_, ?_, r27, ?_, ?_, ?_, ?_, fun j hj => by simp at hj, fun v hv => by simp at hv,
          ?_, ?_⟩, rfl⟩
      · have := Known_writeHash hK' ans
        simpa [forsFC] using this
      · rw [rg .x23 u0E (by simp [specDgOk])]; exact hU
      · simp only [NBhdr, forsFC, if_true]
        rw [r27]; congr 1; unfold FCtx.lo0 DCtx.fw; simp only
        omega
      · rw [wf 0x1C8 (by omega) (by omega)]; exact mN8
      · simp only [forsFC, hbit]
        rw [writeHash_at0 _ ans _ h12 (by omega)]; exact (vw0_answer ans).symm
      · simp only [forsFC, hbit]
        rw [show 0x1E8 + 16 * (d.u 0 % 2) = 0x1E0 + 16 * (d.u 0 % 2) + 8 by omega,
          writeHash_at8 _ ans _ h12 (by omega)]; exact (vw1_answer ans).symm
      · rw [writeHash_pc, hu.pc rfl, pcOf_add4]
        simp only [specDgOk, forsFC, hbit, lvlPc, Nat.add_zero]
        rfl
      · rw [rg .x16 (wLdE 0) (by simp [specDgOk])]; simpa [wLdE, ldE, cw, E.eval] using h0
      · rw [rg .x17 (wLdE 1) (by simp [specDgOk])]; simpa [wLdE, ldE, cw, E.eval] using h1
      · rw [rg .x25 (wLdE 2) (by simp [specDgOk])]; simpa [wLdE, ldE, cw, E.eval] using h2
      · rw [rg .x22 idxE (by simp [specDgOk])]; exact hie
      · rw [rg .x29 (.bin .add hiE (cw 2305)) (by simp [specDgOk]), hadd]; congr 1; unfold DCtx.fw; omega
      · rw [wf 0xC0 (by omega) (by omega), mC0, BitVec.toNat_ofNat]; omega
      · rw [wf 0xC8 (by omega) (by omega), mC8, BitVec.toNat_ofNat]; omega
      · rw [wf 0xF0 (by omega) (by omega), mfr 0xF0 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)]; exact hF0
      · rw [wf 0xF8 (by omega) (by omega), mfr 0xF8 (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega)]; exact hF8
      · rw [wf 0x220 (by omega) (by omega), mR0]
      · rw [wf 0x228 (by omega) (by omega), mR8]


theorem tree_end (d : DCtx) (k : Nat) (hk : k < 14) (roots : List Val) (t u : MachineState)
    (hc : TreeCarry d k roots t) (hlen : roots.length = k) (hu : FoldEnd (forsFC d k) t u)
    (ans : BitVec 256) : ForsIn d (k + 1) (roots ++ [answerBytes 16 ans]) (writeHash u ans) := by
  obtain ⟨hG, hK, hF, hpc, -, hN8⟩ := hu
  obtain ⟨h16, h17, h25, h22, h29, h27, hC0, hC8, hF0, hF8, hRB, hrv, hR0, hR8⟩ := hc
  have h12 : u.getReg .x12 = BitVec.ofNat 64 (0x240 + 16 * k) :=
    hK (.x12, _) (List.mem_append_right _ (List.mem_singleton_self _))
  have wf := fun A (hA : A < 2 ^ 64) (h : A + 8 ≤ 0x240 + 16 * k ∨ 0x240 + 16 * k + 32 ≤ A) =>
    writeHash_frame u ans _ A h12 hA (by omega) h
  have fr : ∀ A, A < 2 ^ 64 → (A < 0x1C0 ∨ 0x210 ≤ A) → (A + 8 ≤ 0x240 + 16 * k ∨ 0x240 + 16 * k + 32 ≤ A) →
      (writeHash u ans).getMem (BitVec.ofNat 64 A) = t.getMem (BitVec.ofNat 64 A) := by
    intro A hA h1 h2; rw [wf A hA h2]; exact hF.2 A hA h1
  have kr : ∀ x ∈ fkeep true, (writeHash u ans).getReg x = t.getReg x := fun x hx => by
    rw [writeHash_getReg]; exact hF.1 x hx
  refine ⟨Glob_writeHash hG ans _ h12 (by interval_cases k <;> decide), ?_,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [hlen], ?_, ?_⟩
  · intro p hp; rw [writeHash_getReg]
    exact hK p (by simpa [fK, forsFC] using hp)
  · rw [kr .x16 (by simp [fkeep])]; exact h16
  · rw [kr .x17 (by simp [fkeep])]; exact h17
  · rw [kr .x25 (by simp [fkeep])]; exact h25
  · rw [kr .x22 (by simp [fkeep])]; exact h22
  · rw [kr .x29 (by simp [fkeep])]; simpa using h29
  · rw [kr .x27 (by simp [fkeep])]; simpa using h27
  · rw [fr 0xC0 (by omega) (by omega) (by omega)]; exact hC0
  · rw [fr 0xC8 (by omega) (by omega) (by omega)]; exact hC8
  · rw [fr 0xF0 (by omega) (by omega) (by omega)]; exact hF0
  · rw [fr 0xF8 (by omega) (by omega) (by omega)]; exact hF8
  · intro j hj
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hjk : j < k
    · rw [fr _ (by omega) (by omega) (by omega), fr _ (by omega) (by omega) (by omega),
        List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
      exact hRB j (by omega)
    · have : j = k := by omega
      subst this
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen, Nat.sub_self]
      simp only [List.getElem?_cons_zero, Option.getD_some]
      refine ⟨(writeHash_at0 _ ans _ h12 (by omega)).trans (vw0_answer ans).symm, ?_⟩
      rw [show 0x248 + 16 * j = 0x240 + 16 * j + 8 by omega, writeHash_at8 _ ans _ h12 (by omega)]
      exact (vw1_answer ans).symm
  · intro v hv
    rcases List.mem_append.mp hv with h | h
    · exact hrv v h
    · rw [List.mem_singleton.mp h]; simp
  · rw [fr 0x220 (by omega) (by omega) (by omega)]; exact hR0
  · rw [fr 0x228 (by omega) (by omega) (by omega)]; exact hR8
  · rw [wf 0x1C8 (by omega) (by omega)]; exact hN8
  · refine ⟨bitOf (forsFC d k).E ((forsFC d k).h - 1), by simp [bitOf]; omega, ?_⟩
    rw [writeHash_pc, hpc, pcOf_add4]
    simp only [forsFC, tEnd, Nat.add_sub_cancel]

end SigGolfCandidate.Verify
