import SigGolfCandidate.Sign.TreeChain
import SigGolfCandidate.Sign.DigAn

/-!
# `sign`, the PORS leaves (`por_leaf_loop`, instructions 179 .. 209)

`porsLeaves_sim` : from `por_leaf_loop` with `J = 0`, the machine refines
`buildPorsLeaves S idx`: leaf `j` is stored at `FA + 16 j` (`FA = 0x30000`); the secret of the
`c`-th smallest opened leaf `vs[c]` is captured at `SIG + 16 + 16 c` (`SIGL`, `x18`), where the
machine walks the sorted keys (`EP`, `x20`; `U = KEYS[EP] >> 8`, `x13`; `U = 2^14` after the last,
from the sentinel `KEYS[15] = 2^22`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- The key index `c`'s leaf, `2^14` past the last one. -/
def vsAt (vs : List Nat) (c : Nat) : Nat := if c < 15 then vs.getD c 0 else 2 ^ 14

/-- The (fixed) facts at the start of the PORS leaf loop. -/
structure PLeafCtx (S : List Byte) (idx : Nat) (L : List Nat) (t0 : MachineState) : Prop where
  hidx : idx < 2 ^ 34
  hlen : L.length = 15
  hsort : (L.map keyV).Pairwise (· < ·)
  hlt : ∀ v ∈ L.map keyV, v < 2 ^ 14
  hbound : KeysBound L
  keys : KeysAt t0 L
  sent : t0.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22)
  pb0 : t0.getMem (BitVec.ofNat 64 0x6A0) = twWord0 8 0 idx 0
  pb8 : lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) = BitVec.ofNat 32 idx
  pbP : t0.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t0.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cb0 : t0.getMem (BitVec.ofNat 64 0xC0) = twWord0 9 0 idx 0
  cb8 : lo32 (t0.getMem (BitVec.ofNat 64 0xC8)) = BitVec.ofNat 32 idx
  cbP : t0.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]
  cbZ : t0.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]
  x5 : t0.getReg .x5 = 0
  x17 : t0.getReg .x17 = BitVec.ofNat 64 (2 ^ 14)
  x19 : t0.getReg .x19 = BitVec.ofNat 64 0x30000

/-- Addresses written by the leaf loop. -/
def pleafW (a : Nat) : Prop :=
  a = 0x6A8 ∨ a = 0xC8 ∨ (0xE0 ≤ a ∧ a < 0xF0) ∨ (0x140 ≤ a ∧ a < 0x160) ∨
    (0x30000 ≤ a ∧ a < 0x30000 + 16 * (2 ^ 14 + 1)) ∨ (0x3310 ≤ a ∧ a < 0x3310 + 16 * 15)

def pleafRegs : List Reg := [.x1, .x2, .x3, .x9, .x10, .x11, .x12, .x13, .x18, .x20]

/-- The capture state after `j` leaves: `c` keys captured. -/
def CapInv (vs : List Nat) (j : Nat) (secs : List Val) (t : MachineState) (c : Nat) : Prop :=
  c ≤ 15 ∧ (∀ s < c, vs.getD s 0 < j) ∧ (c < 15 → j ≤ vs.getD c 0) ∧
  (∀ s < c, t.readWords (BitVec.ofNat 64 (0x3310 + 16 * s)) 2 = wordsOf (secs.getD (vs.getD s 0) [])) ∧
  t.getReg .x18 = BitVec.ofNat 64 (0x3310 + 16 * c) ∧ t.getReg .x20 = BitVec.ofNat 64 (0x6E0 + 8 * c) ∧
  t.getReg .x13 = BitVec.ofNat 64 (vsAt vs c)

/-- Invariant after `j` leaves. -/
def PLeafInv (L : List Nat) (t0 : MachineState) (j : Nat) (st : List Val × List Val) (t : MachineState) :
    Prop :=
  j ≤ 2 ^ 14 ∧ st.1.length = j ∧ st.2.length = j ∧ (∀ v ∈ st.1, v.length = 16) ∧
  (∀ v ∈ st.2, v.length = 16) ∧ Slots t 0x30000 st.1 ∧ (∃ c, CapInv (L.map keyV) j st.2 t c) ∧
  t.pc = (if j < 2 ^ 14 then pcOf 179 else pcOf 210) ∧ t.getReg .x9 = BitVec.ofNat 64 j ∧
  RegsEq t0 t pleafRegs ∧ Frame t0 t pleafW ∧
  lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8))

theorem getD_append_lt {α : Type} (l : List α) (x d : α) (i : Nat) (hi : i < l.length) :
    (l ++ [x]).getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hi, ← List.getD_eq_getElem?_getD]

theorem getD_append_eq {α : Type} (l : List α) (x d : α) : (l ++ [x]).getD l.length d = x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]; simp

/-- From `por_nocap` (202): the leaf hash and the loop step. -/
theorem pleaf_tail (S : List Byte) (idx : Nat) (L : List Nat) (t0 : MachineState)
    (ctx : PLeafCtx S idx L t0) (j : Nat) (hj : j < 2 ^ 14)
    (acc secs : List Val) (hlen : acc.length = j) (hlen2 : secs.length = j + 1)
    (hvals : ∀ v ∈ acc, v.length = 16) (hsecs : ∀ v ∈ secs, v.length = 16) (s : Val)
    (hs : s.length = 16) (t : MachineState) (tpc : t.pc = pcOf 202)
    (t9 : t.getReg .x9 = BitVec.ofNat 64 j)
    (tregs : RegsEq t0 t pleafRegs) (tframe : Frame t0 t pleafW)
    (tlo1 : lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)))
    (tlo2 : lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8)))
    (tsv : t.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf s)
    (tz : t.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0]) (hslots : Slots t 0x30000 acc)
    (hcap : ∃ c, CapInv (L.map keyV) (j + 1) secs t c) :
    Sim image t 15 (hash16 (porsLeafInput idx j s) >>= fun leaf => pure (acc ++ [leaf], secs))
      (fun r t' => PLeafInv L t0 (j + 1) r t' ∧ SecPres t t') := by
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by simp [pleafRegs]), ctx.x5]
  have tx19 : t.getReg .x19 = BitVec.ofNat 64 0x30000 := by
    rw [tregs.get .x19 (by simp [pleafRegs]), ctx.x19]
  have tx17 : t.getReg .x17 = BitVec.ofNat 64 (2 ^ 14) := by
    rw [tregs.get .x17 (by simp [pleafRegs]), ctx.x17]
  have hs1 := symRun_sound blk202 codeAt_202 t tpc (by simp only [blk202.res, rv_simp])
  have hc1 : blk202.res.cycles = 5 := rfl
  rw [hc1] at hs1
  set t1 := blk202.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0xC8) := by
    apply frame_toState; intro x hx hW
    simp only [blk202.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x3, .x10, .x11, .x12] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk202 codeAt_202 t (by simp only [blk202.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0xC0 := by simp only [ht1, blk202.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht1, blk202.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 (0x30000 + 16 * j) := by
    rvs [ht1, blk202.res, t9, tx19]; congr 1; ring
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tx5]
  have pc1 : t1.pc = pcOf 207 := by simp only [ht1, blk202.res, rv_simp]
  have mC8 : t1.getMem (BitVec.ofNat 64 0xC8) =
      BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32)) := by
    rvs [ht1, blk202.res, t9]
    exact word_of_halves _ idx j (by rw [lo32_replace1, tlo2, ctx.cb8]) (by rw [hi32_replace1])
  have hq : hashInput t1 = pad64 (porsLeafInput idx j s) := by
    obtain ⟨hn, hw⟩ := words_th16 9 0 idx 0 j s hs
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [porsLeafInput, hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 2 + 2 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, mC8, f1.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [pleafW]; omega), ctx.cb0,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [pleafW]; omega), ctx.cbP, tsv, tz]
    simp [twWords_eq]
  have hb : (pad64 (porsLeafInput idx j s)).blocks = 1 :=
    congrArg (· + 1) (words_th16 9 0 idx 0 j s hs).1
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 2) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by omega) (by omega)
      (by norm_num)) hq (fmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x30000 + 16 * j ≤ x ∧ x < 0x30000 + 16 * j + 32) :=
    frame_writeHash t1 a _ x12 (by omega)
  have v2 : t2.readWords (BitVec.ofNat 64 (0x30000 + 16 * j)) 2 = wordsOf (answerBytes 16 a) :=
    writeHash_readWords_val t1 a _ x12 (by omega)
  have pc2 : t2.pc = pcOf 208 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have hs2 := symRun_sound blk208 codeAt_208 t2 pc2 (by simp only [blk208.res, rv_simp])
  have hc2 : blk208.res.cycles = 2 := rfl
  rw [hc2] at hs2
  set t3 := blk208.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun _ => False) := by
    apply frame_toState; intro x hx hW; simp [blk208.res]
  have r3 : RegsEq t2 t3 [.x9] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have t29 : t2.getReg .x9 = BitVec.ofNat 64 j := by rw [ht2, writeHash_getReg, r1.get .x9, t9]
  have ftot : Frame t t3 (fun x => x = 0xC8 ∨ (0x30000 + 16 * j ≤ x ∧ x < 0x30000 + 16 * j + 32)) :=
    ((f1.trans f2).trans f3).mono (by intro x hx; (try simp only [or_false] at hx ⊢); omega)
  have rtot : RegsEq t t3 [.x3, .x9, .x10, .x11, .x12] :=
    ((r1.trans (regsEq_writeHash _ _ [])).trans r3).mono (by decide)
  refine Sim.pure_steps hs2 ⟨⟨by omega, by simp [hlen], hlen2, ?_, hsecs, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    fun x hx h1 h2 => ftot.getMem hx (by omega)⟩
  · intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hvals v hv
    · simp at hv; subst hv; simp
  · apply Slots.snoc
    · exact hslots.frame ftot (by omega) (by intro i hi; constructor <;> ((try simp only); omega))
    · rw [hlen, f3.readWords _ _ (by omega) (by simp), v2]
  · obtain ⟨c, hc, hlt, hge, hsl, h18, h20, h13⟩ := hcap
    refine ⟨c, hc, hlt, hge, fun s hs => ?_, by rw [rtot.get .x18, h18], by rw [rtot.get .x20, h20],
      by rw [rtot.get .x13, h13]⟩
    rw [ftot.readWords _ _ (by omega) (by intro i hi; omega), hsl s hs]
  · simp only [ht3, blk208.res, rv_simp, t29, ofNat_add_ofNat, ofNat_bne_ofNat,
      show t2.getReg .x17 = BitVec.ofNat 64 (2 ^ 14) by rw [ht2, writeHash_getReg, r1.get .x17, tx17]]
    by_cases h : j + 1 < 2 ^ 14
    · rw [if_pos (by simp; omega), if_pos h]
    · rw [if_neg (by simp; omega), if_neg h]
  · simp only [ht3, blk208.res, rv_simp, t29, ofNat_add_ofNat]
  · exact (tregs.trans rtot).mono (by decide)
  · exact (tframe.trans ftot).mono (by intro x hx; simp only [pleafW] at hx ⊢; omega)
  · rw [ftot.getMem (by norm_num) (by omega), tlo1]
  · rw [f3.getMem (by norm_num) (by simp), f2.getMem (by norm_num) (by omega)]
    rvs [ht1, blk202.res, t9]
    rw [lo32_replace1, tlo2]

theorem vs_getD (L : List Nat) (c : Nat) : (L.map keyV).getD c 0 = keyV (L.getD c 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases L[c]? <;> rfl

theorem vs_lt_succ (L : List Nat) (hlen : L.length = 15) (hs : (L.map keyV).Pairwise (· < ·)) (c : Nat)
    (hc : c + 1 < 15) : (L.map keyV).getD c 0 < (L.map keyV).getD (c + 1) 0 := by
  rw [List.pairwise_iff_getElem] at hs
  have := hs c (c + 1) (by simp [hlen]; omega) (by simp [hlen]; omega) (by omega)
  rw [List.getD_eq_getElem _ _ (by simp [hlen]; omega), List.getD_eq_getElem _ _ (by simp [hlen]; omega)]
  exact this

theorem vs_lt_T (L : List Nat) (hlen : L.length = 15) (hlt : ∀ v ∈ L.map keyV, v < 2 ^ 14) (c : Nat)
    (hc : c < 15) : (L.map keyV).getD c 0 < 2 ^ 14 := by
  rw [List.getD_eq_getElem _ _ (by simp [hlen]; omega)]
  exact hlt _ (List.getElem_mem _)

/-- From `prf_have` (187) for leaf `j` whose secret `s` sits at `SEC + 16 (j & 1)`: the copy to
`CB+32`, the capture, the leaf hash, the loop step. -/
theorem pleaf_B (S : List Byte) (idx : Nat) (L : List Nat) (t0 : MachineState)
    (ctx : PLeafCtx S idx L t0) (j : Nat) (hj : j < 2 ^ 14)
    (acc secs : List Val) (hlen : acc.length = j) (hlen2 : secs.length = j)
    (hvals : ∀ v ∈ acc, v.length = 16) (hsecs : ∀ v ∈ secs, v.length = 16) (s : Val)
    (hs : s.length = 16) (t : MachineState) (tpc : t.pc = pcOf 187)
    (t9 : t.getReg .x9 = BitVec.ofNat 64 j)
    (hsec : t.readWords (BitVec.ofNat 64 (0x140 + 16 * (j % 2))) 2 = wordsOf s)
    (hslots : Slots t 0x30000 acc) (hcap : ∃ c, CapInv (L.map keyV) j secs t c)
    (tregs : RegsEq t0 t pleafRegs) (tframe : Frame t0 t pleafW)
    (tlo1 : lo32 (t.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)))
    (tlo2 : lo32 (t.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8))) :
    Sim image t 30 (hash16 (porsLeafInput idx j s) >>= fun leaf => pure (acc ++ [leaf], secs ++ [s]))
      (fun r t' => PLeafInv L t0 (j + 1) r t' ∧ SecPres t t') := by
  have hj2 : j % 2 < 2 := Nat.mod_lt _ (by norm_num)
  obtain ⟨c, hc, hclt, hcge, hcsl, h18, h20, h13⟩ := hcap
  -- block 187: copy the secret to CB+32, test J = U
  have hs3 := symRun_sound blk187 codeAt_187 t tpc (by
    simp only [blk187.res, rv_simp, t9]; rw [secAddr j (by omega) 328 (by norm_num), secAddr j (by omega) 320 (by norm_num)]
    simp only [accessValid_ofNat]; omega)
  have hc3 : blk187.res.cycles = 7 := rfl
  rw [hc3] at hs3
  set t3 := blk187.res.toState t with ht3
  have f3 : Frame t t3 (fun x => x = 0xE0 ∨ x = 0xE8) := by
    apply frame_toState; intro x hx hW
    simp only [blk187.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t t3 [.x1, .x2, .x3] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have x39 : t3.getReg .x9 = BitVec.ofNat 64 j := by rw [r3.get .x9, t9]
  have v3 : t3.readWords (BitVec.ofNat 64 0xE0) 2 = wordsOf s := by
    rw [← hsec, readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht3, blk187.res, rv_simp, t9]
    rw [secAddr j (by omega) 328 (by norm_num), secAddr j (by omega) 320 (by norm_num)]
    simp (config := { decide := true }) only [↓reduceIte]
    rw [show 328 + 16 * (j % 2) = 0x140 + 16 * (j % 2) + 8 by omega]
  have hU : vsAt (L.map keyV) c < 2 ^ 64 := by
    unfold vsAt; split
    · have := vs_lt_T L ctx.hlen ctx.hlt c (by assumption); omega
    · norm_num
  have pc3 : t3.pc = if j = vsAt (L.map keyV) c then pcOf 194 else pcOf 202 := by
    simp only [ht3, blk187.res, rv_simp, t9, h13, ofNat_bne_ofNat]
    by_cases h : j = vsAt (L.map keyV) c
    · rw [if_pos h, if_neg (by simp; omega)]
    · rw [if_neg h, if_pos (by simp; omega)]
  have ft3 : Frame t0 t3 pleafW := (tframe.trans f3).mono (by
    intro x hx; simp only [pleafW] at hx ⊢; omega)
  have rt3 : RegsEq t0 t3 pleafRegs := (tregs.trans r3).mono (by decide)
  have z3 : t3.readWords (BitVec.ofNat 64 0xF0) 2 = [0, 0] := by
    rw [ft3.readWords _ _ (by norm_num) (by intro i hi; simp only [pleafW]; omega), ctx.cbZ]
  have lo3a : lo32 (t3.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) := by
    rw [f3.getMem (by norm_num) (by omega), tlo1]
  have lo3b : lo32 (t3.getMem (BitVec.ofNat 64 0xC8)) = lo32 (t0.getMem (BitVec.ofNat 64 0xC8)) := by
    rw [f3.getMem (by norm_num) (by omega), tlo2]
  have hslots3 : Slots t3 0x30000 acc := hslots.frame f3 (by omega)
    (by intro i hi; constructor <;> omega)
  have sec3 : ∀ x, x < 2 ^ 64 → 0x140 ≤ x → x < 0x160 →
      t3.getMem (BitVec.ofNat 64 x) = t.getMem (BitVec.ofNat 64 x) := fun x hx h1 h2 =>
    f3.getMem hx (by omega)
  have hsecs' : ∀ v ∈ secs ++ [s], v.length = 16 := by
    intro v hv; rcases List.mem_append.mp hv with hv | hv
    · exact hsecs v hv
    · simp at hv; subst hv; exact hs
  have getOld : ∀ q < c, (secs ++ [s]).getD ((L.map keyV).getD q 0) [] = secs.getD ((L.map keyV).getD q 0) [] :=
    fun q hq => getD_append_lt _ _ _ _ (by rw [hlen2]; exact hclt q hq)
  by_cases hju : j = vsAt (L.map keyV) c
  · -- capture
    have hc15 : c < 15 := by
      by_contra h; unfold vsAt at hju; rw [if_neg h] at hju; omega
    have hjc : (L.map keyV).getD c 0 = j := by unfold vsAt at hju; rw [if_pos hc15] at hju; omega
    have t318 : t3.getReg .x18 = BitVec.ofNat 64 (0x3310 + 16 * c) := by rw [r3.get .x18, h18]
    have t320 : t3.getReg .x20 = BitVec.ofNat 64 (0x6E0 + 8 * c) := by rw [r3.get .x20, h20]
    have hs4 := symRun_sound blk194 codeAt_194 t3 (by rw [pc3, if_pos hju]) (by
      simp only [blk194.res, rv_simp, t318, t320, ofNat_add_ofNat, accessValid_ofNat, ne_eq, ofNat_eq_iff,
        Nat.reducePow]
      omega)
    have hc4 : blk194.res.cycles = 8 := rfl
    rw [hc4] at hs4
    set t4 := blk194.res.toState t3 with ht4
    have f4 : Frame t3 t4 (fun x => x = 0x3310 + 16 * c ∨ x = 0x3310 + 16 * c + 8) := by
      apply frame_toState; intro x hx hW
      simp only [blk194.res, rv_simp, t318, ofNat_add_ofNat, List.forall_mem_cons, List.not_mem_nil,
        IsEmpty.forall_iff, implies_true, and_true, ne_eq, ofNat_eq_iff]
      omega
    have r4 : RegsEq t3 t4 [.x1, .x2, .x13, .x18, .x20] := by
      intro r hr; rw [ht4, Result.toState_getReg]
      cases r <;> first | exact absurd (by decide) hr | rfl
    have sig4 : t4.readWords (BitVec.ofNat 64 (0x3310 + 16 * c)) 2 = wordsOf s := by
      rw [← v3, readWords_ofNat_two, readWords_ofNat_two]
      simp only [ht4, blk194.res, rv_simp, t318, ofNat_add_ofNat, ofNat_eq_iff]
      simp (disch := bvomega) only [if_pos, if_neg, if_true, Nat.reduceAdd]
    have x413 : t4.getReg .x13 = BitVec.ofNat 64 (vsAt (L.map keyV) (c + 1)) := by
      simp only [ht4, blk194.res, rv_simp, t320, ofNat_add_ofNat]
      rw [show 0x6E0 + 8 * c + 8 = 0x6E0 + 8 * (c + 1) by ring]
      have hk : t3.getMem (BitVec.ofNat 64 (0x6E0 + 8 * (c + 1))) = t0.getMem (BitVec.ofNat 64 (0x6E0 + 8 * (c + 1))) :=
        ft3.getMem (by omega) (by simp only [pleafW]; omega)
      rw [hk]
      by_cases hc1 : c + 1 < 15
      · rw [ctx.keys (c + 1) hc1, show (8#64 : Word).toNat % 64 = 8 from rfl, ushr8 _ (by have := keysBound_getD ctx.hbound (c + 1); omega)]
        unfold vsAt; rw [if_pos hc1, vs_getD]
      · rw [show c + 1 = 15 by omega, show 0x6E0 + 8 * 15 = 0x758 from rfl, ctx.sent,
          show (8#64 : Word).toNat % 64 = 8 from rfl, ushr8 _ (by norm_num)]
        unfold vsAt; rw [if_neg (by omega)]; rfl
    have := pleaf_tail S idx L t0 ctx j hj acc (secs ++ [s]) hlen (by simp [hlen2]) hvals hsecs' s hs t4
      (by simp only [ht4, blk194.res, rv_simp])
      (by rw [r4.get .x9, x39])
      (rt3.trans r4 |>.mono (by decide))
      ((ft3.trans f4).mono (by
        intro x hx; (try simp only [or_false] at hx ⊢); simp only [pleafW] at hx ⊢; omega))
      (by rw [f4.getMem (by norm_num) (by omega), lo3a])
      (by rw [f4.getMem (by norm_num) (by omega), lo3b])
      (by rw [f4.readWords _ _ (by norm_num) (by intro i hi; omega), v3])
      (by rw [f4.readWords _ _ (by norm_num) (by intro i hi; omega), z3])
      (hslots3.frame f4 (by omega) (by intro i hi; constructor <;> ((try simp only); omega)))
      ⟨c + 1, by omega, fun q hq => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | hq
        · have := hclt q hq; omega
        · rw [hq, hjc]; omega,
       fun h => by have := vs_lt_succ L ctx.hlen ctx.hsort c h; omega,
       fun q hq => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hq with hq | hq
        · rw [f4.readWords _ _ (by omega) (by intro i hi; omega), f3.readWords _ _ (by omega) (by intro i hi; omega),
            hcsl q hq, getOld q hq]
        · rw [hq, sig4, hjc, ← hlen2, getD_append_eq],
       by simp only [ht4, blk194.res, rv_simp, t318, ofNat_add_ofNat]; exact ofNat_congr (by ring),
       by simp only [ht4, blk194.res, rv_simp, t320, ofNat_add_ofNat]; exact ofNat_congr (by ring),
       x413⟩
    exact (Sim.steps hs3 (Sim.steps hs4 this)).mono (by norm_num) (fun _ _ h => ⟨h.1, fun x hx h1 h2 => by
      rw [h.2 x hx h1 h2, f4.getMem hx (by omega), sec3 x hx h1 h2]⟩)
  · have := pleaf_tail S idx L t0 ctx j hj acc (secs ++ [s]) hlen (by simp [hlen2]) hvals hsecs' s hs t3
      (by rw [pc3, if_neg hju]) x39 rt3 ft3 lo3a lo3b v3 z3 hslots3
      ⟨c, hc, fun q hq => by have := hclt q hq; omega,
       fun h => by
        have h1 := hcge h
        have : j ≠ (L.map keyV).getD c 0 := by unfold vsAt at hju; rw [if_pos h] at hju; exact hju
        omega,
       fun q hq => by rw [f3.readWords _ _ (by omega) (by intro i hi; omega), hcsl q hq, getOld q hq],
       by rw [r3.get .x18, h18], by rw [r3.get .x20, h20], by rw [r3.get .x13, h13]⟩
    exact (Sim.steps hs3 this).mono (by norm_num) (fun _ _ h => ⟨h.1, fun x hx h1 h2 => by
      rw [h.2 x hx h1 h2, sec3 x hx h1 h2]⟩)

theorem pors_pair_spec (S : List Byte) (idx q : Nat) (st : List Val × List Val) :
    (do
      let (s0, s1) ← prf2 (porsPrfInput S idx q)
      let l0 ← hash16 (porsLeafInput idx (2 * q) s0)
      let l1 ← hash16 (porsLeafInput idx (2 * q + 1) s1)
      pure (st.1 ++ [l0, l1], st.2 ++ [s0, s1]) : OracleComp HashSpec (List Val × List Val)) =
    H (porsPrfInput S idx q) >>= fun a =>
      (hash16 (porsLeafInput idx (2 * q) (answerBytes 16 a)) >>= fun l0 =>
        pure (st.1 ++ [l0], st.2 ++ [answerBytes 16 a])) >>= fun r =>
      hash16 (porsLeafInput idx (2 * q + 1) (hiVal a)) >>= fun l1 =>
        pure (r.1 ++ [l1], r.2 ++ [hiVal a]) := by
  simp only [prf2_eq, bind_assoc, pure_bind, List.append_assoc, List.cons_append, List.nil_append]

theorem pleaf_pair (S : List Byte) (hS : S.length = 32) (idx : Nat) (L : List Nat) (t0 : MachineState)
    (ctx : PLeafCtx S idx L t0) (q : Nat) (hq : q < 2 ^ 13) (st : List Val × List Val) (t : MachineState)
    (hinv : PLeafInv L t0 (2 * q) st t) :
    Sim image t 79 (do
        let (s0, s1) ← prf2 (porsPrfInput S idx q)
        let l0 ← hash16 (porsLeafInput idx (2 * q) s0)
        let l1 ← hash16 (porsLeafInput idx (2 * q + 1) s1)
        pure (st.1 ++ [l0, l1], st.2 ++ [s0, s1]))
      (PLeafInv L t0 (2 * q + 2)) := by
  rw [pors_pair_spec]
  have hidx := ctx.hidx
  obtain ⟨-, hlen, hlen2, hvals, hsecs, hslots, hcap, tpc, t9, tregs, tframe, tlo1, tlo2⟩ := hinv
  have tpc' : t.pc = pcOf 179 := by rw [tpc, if_pos (by omega)]
  have tx5 : t.getReg .x5 = 0 := by rw [tregs.get .x5 (by simp [pleafRegs]), ctx.x5]
  -- block 179: even
  have hs0 := symRun_sound blk179 codeAt_179 t tpc' (by simp only [blk179.res, rv_simp])
  have hc0 : blk179.res.cycles = 2 := rfl
  rw [hc0] at hs0
  set t1 := blk179.res.toState t with ht1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk179.res.st.mem = [] from rfl, memEval_nil]
  have r1 : RegsEq t t1 [.x3] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc1 : t1.pc = pcOf 181 := by
    simp only [ht1, blk179.res, rv_simp, t9]
    rw [and_one_ofNat _ (by omega), if_neg (by rw [ofNat_bne_ofNat]; simp)]
  -- block 181: the paired prf query
  have hs2 := symRun_sound blk181 codeAt_181 t1 pc1 (by simp only [blk181.res, rv_simp])
  have hc2 : blk181.res.cycles = 5 := rfl
  rw [hc2] at hs2
  set t2 := blk181.res.toState t1 with ht2
  have f2 : Frame t1 t2 (fun x => x = 0x6A8) := by
    apply frame_toState; intro x hx hW
    simp only [blk181.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r2 : RegsEq t1 t2 [.x3, .x10, .x11, .x12] := by
    intro r hr; rw [ht2, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e2 := symRun_ecall blk181 codeAt_181 t1 (by simp only [blk181.res, rv_simp]) rfl
  have x10 : t2.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht2, blk181.res, rv_simp]
  have x11 : t2.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht2, blk181.res, rv_simp]
  have x12 : t2.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht2, blk181.res, rv_simp]
  have x5 : t2.getReg .x5 = 0 := by rw [r2.get .x5, r1.get .x5, tx5]
  have pc2 : t2.pc = pcOf 186 := by simp only [ht2, blk181.res, rv_simp]
  have t19 : t1.getReg .x9 = BitVec.ofNat 64 (2 * q) := by rw [r1.get .x9, t9]
  have m6A8 : t2.getMem (BitVec.ofNat 64 0x6A8) =
      BitVec.ofNat 64 (idx % 2 ^ 32 + 2 ^ 32 * (q % 2 ^ 32)) := by
    simp only [ht2, blk181.res, rv_simp, t19]
    bvsimp []
    rw [show 2 * q / 2 = q by omega]
    refine (word_of_halves _ idx q ?_ ?_).trans (ofNat_congr (by omega))
    · rw [lo32_replace1, m1, tlo1, ctx.pb8]
    · rw [hi32_replace1]
  have ft2 : Frame t t2 (fun x => x = 0x6A8) := fun z hz hW => by rw [f2.getMem hz hW, m1]
  have hq' : hashInput t2 = pad64 (porsPrfInput S idx q) := by
    obtain ⟨hn, hw⟩ := words_porsPrfInput S hS idx q
    refine hashInput_eq_pad64 t2 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m6A8, ft2.getMem (by norm_num) (by norm_num),
      tframe.getMem (by norm_num) (by simp only [pleafW]; omega), ctx.pb0,
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [pleafW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [pleafW]; omega), ctx.pbP, ctx.pbS]
    simp [twWords_eq]
  have hb : (pad64 (porsPrfInput S idx q)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_porsPrfInput S hS idx q).1]
  refine (Sim.steps hs0 (Sim.steps hs2 (Sim.query_bind (W := 30 + (2 + 30)) e2 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (hq'.trans (fmt_thInput _ _ _ _ _ _ (by decide)).symm) (fun a => ?_)))).mono
    (by rw [show porsPrfInput S idx q = thInput (tweak 8 0 idx 0 q) S from rfl] at *
        rw [blocks_fmt_th _ _ _ _ _ _ (by decide)]; rw [hb]; norm_num)
    (fun _ _ h => h)
  set t3 := writeHash t2 a with ht3
  have f3 : Frame t2 t3 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t2 a _ x12 (by norm_num)
  have pc3 : t3.pc = pcOf 187 := by rw [ht3, writeHash_pc, pc2]; apply BitVec.eq_of_toNat_eq; simp
  have g3 : ∀ q, t3.getReg q = t2.getReg q := fun q => by rw [ht3, writeHash_getReg]
  have ft3 : Frame t t3 (fun x => x = 0x6A8 ∨ (0x140 ≤ x ∧ x < 0x140 + 32)) := ft2.trans f3
  have rt23 : RegsEq t t3 [.x3, .x10, .x11, .x12] :=
    ((r1.trans r2).trans (show RegsEq t2 t3 [] from fun q _ => g3 q)).mono (by decide)
  have rt3 : RegsEq t0 t3 pleafRegs := (tregs.trans rt23).mono (by decide)
  have lo3 : lo32 (t3.getMem (BitVec.ofNat 64 0x6A8)) = lo32 (t0.getMem (BitVec.ofNat 64 0x6A8)) := by
    rw [f3.getMem (by norm_num) (by omega), m6A8, ctx.pb8, lo32_ofNat]
    apply BitVec.eq_of_toNat_eq; simp
  obtain ⟨c, hc, hclt, hcge, hcsl, h18, h20, h13⟩ := hcap
  have hA := pleaf_B S idx L t0 ctx (2 * q) (by omega) st.1 st.2 hlen hlen2 hvals hsecs (answerBytes 16 a)
    (by simp) t3 pc3 (by rw [g3, r2.get .x9, t19])
    (by rw [show 0x140 + 16 * (2 * q % 2) = 0x140 by omega]; exact sec_lo t2 a x12)
    (hslots.frame ft3 (by omega) (by intro i hi; constructor <;> omega))
    ⟨c, hc, hclt, hcge, fun s hs => by rw [ft3.readWords _ _ (by omega) (by intro i hi; omega), hcsl s hs],
      by rw [rt23.get .x18, h18], by rw [rt23.get .x20, h20], by rw [rt23.get .x13, h13]⟩
    rt3 ((tframe.trans ft3).mono (by intro x hx; simp only [pleafW] at hx ⊢; omega)) lo3
    (by rw [ft3.getMem (by norm_num) (by omega), tlo2])
  refine Sim.bind hA (fun r t4 h4 => ?_)
  obtain ⟨⟨-, hlen4, hlen42, hvals4, hsecs4, hslots4, hcap4, tpc4, t49, tregs4, tframe4, tlo14, tlo24⟩, sec4⟩ := h4
  -- block 179: odd
  have hs5 := symRun_sound blk179 codeAt_179 t4 (by rw [tpc4, if_pos (by omega)])
    (by simp only [blk179.res, rv_simp])
  have hc5 : blk179.res.cycles = 2 := rfl
  rw [hc5] at hs5
  set t5 := blk179.res.toState t4 with ht5
  have m5 : ∀ z, t5.getMem z = t4.getMem z := fun z => by
    rw [ht5, Result.toState_getMem, show blk179.res.st.mem = [] from rfl, memEval_nil]
  have r5 : RegsEq t4 t5 [.x3] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc5 : t5.pc = pcOf 187 := by
    simp only [ht5, blk179.res, rv_simp, t49]
    rw [and_one_ofNat _ (by omega), if_pos (by rw [ofNat_bne_ofNat]; simp)]
  have fr5 : Frame t4 t5 (fun _ => False) := fun z _ _ => m5 _
  obtain ⟨c4, hc4, hclt4, hcge4, hcsl4, h184, h204, h134⟩ := hcap4
  have hB := pleaf_B S idx L t0 ctx (2 * q + 1) (by omega) r.1 r.2 hlen4 hlen42 hvals4 hsecs4 (hiVal a)
    (by simp) t5 pc5 (by rw [r5.get .x9, t49])
    (by
      rw [show 0x140 + 16 * ((2 * q + 1) % 2) = 0x150 by omega, readWords_ofNat_two, m5, m5,
        sec4 _ (by norm_num) (by norm_num) (by norm_num), sec4 _ (by norm_num) (by norm_num) (by norm_num),
        ← readWords_ofNat_two]
      exact sec_hi t2 a x12)
    (hslots4.frame fr5 (by omega) (by simp))
    ⟨c4, hc4, hclt4, hcge4, fun s hs => by rw [fr5.readWords _ _ (by omega) (by simp), hcsl4 s hs],
      by rw [r5.get .x18, h184], by rw [r5.get .x20, h204], by rw [r5.get .x13, h134]⟩
    ((tregs4.trans r5).mono (by decide)) ((tframe4.trans fr5).mono (by intro x hx; rcases hx with h | h; exact h; exact h.elim))
    (by rw [m5, tlo14]) (by rw [m5, tlo24])
  exact (Sim.steps hs5 hB).mono (by norm_num) (fun _ _ h => h.1)

theorem PLeafInv.init (L : List Nat) (t0 : MachineState) (hpc : t0.pc = pcOf 179)
    (h9 : t0.getReg .x9 = BitVec.ofNat 64 0) (hcap : CapInv (L.map keyV) 0 [] t0 0) :
    PLeafInv L t0 0 ([], []) t0 :=
  ⟨by norm_num, rfl, rfl, by simp, by simp, Slots.nil _ _, ⟨0, hcap⟩, by simpa using hpc, h9,
    RegsEq.refl _ _, Frame.refl _ _, rfl, rfl⟩

/-- **PORS leaves** (pairs `q = 0 .. 2^13 - 1`). -/
theorem porsLeaves_sim (S : List Byte) (hS : S.length = 32) (idx : Nat) (L : List Nat) (t0 : MachineState)
    (ctx : PLeafCtx S idx L t0) (hpc : t0.pc = pcOf 179) (h9 : t0.getReg .x9 = BitVec.ofNat 64 0)
    (hcap : CapInv (L.map keyV) 0 [] t0 0) :
    Sim image t0 (2 ^ 13 * 79) (buildPorsLeaves S idx) (PLeafInv L t0 (2 ^ 14)) := by
  unfold buildPorsLeaves porsT porsH
  exact Sim.foldlM_range (2 ^ 14 / 2) _ ([], []) (fun q => PLeafInv L t0 (2 * q)) 79
    (fun q hq st t h => pleaf_pair S hS idx L t0 ctx q (by omega) st t h)
    (PLeafInv.init L t0 hpc h9 hcap)

end SigGolfCandidate.Sign
