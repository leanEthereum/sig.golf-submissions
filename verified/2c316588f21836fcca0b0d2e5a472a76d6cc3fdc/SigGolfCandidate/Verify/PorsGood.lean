import SigGolfCandidate.Verify.PorsSem
import SigGolfCandidate.Verify.LayerGood

/-!
# The PORS stack machine: the simulation judgment

The root tail (into the layers), then `GoodQ` for the ladder (`segFolds`), one segment
(`segment`), the segments of a leaf (`segLoop`, by induction on the stack), the leaves
(`porsLeaves`) and `porsRoot`.

Cycle bounds: a segment with `a` folds costs `16` if `a = 0` (dispatch 4, table entry 4, pending
hash 8) and `18 + 17 a` if `a ≥ 1` (the entry's parity test adds 2; `17 a` for the folds incl. the
entry tail), at most `18 + 17 a` in both cases; tails: merge 6, push 4, root 22.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 20000

namespace SigGolfCandidate.Verify
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref OracleComp

/-! ## The root tail -/

theorem tailFCheck_at (c : Nat) (hc : c < 3) : tailFCheck c = true :=
  List.all_eq_true.mp tailFCheck_all c (List.mem_range.mpr hc)

theorem f4Pc_pre (c : Nat) (hc : c < 3) : ∃ t, t < nCopy 4 ∧ f4Pc c = preStart 4 t := by
  rcases (show c = 0 ∨ c = 1 ∨ c = 2 by omega) with rfl | rfl | rfl
  · exact ⟨2, by decide, rfl⟩
  · exact ⟨1, by decide, rfl⟩
  · exact ⟨0, by decide, rfl⟩

theorem PB.glob_layers {P : PCtx} {s0 u : MachineState} {gk : List (Reg × Word)}
    (hg : GlobP gk s0 u) (hs0 : S0 P s0) : Glob gk P.wl P.pk u := by
  refine ⟨hg.1, fun j hj => (hg.2.2.2 j (by unfold NW; omega)).trans (hs0.wit j hj), ?_, ?_⟩
  · exact ⟨(hg.2.1 0xA0 (by decide)).trans hs0.pk.1, (hg.2.1 0xA8 (by decide)).trans hs0.pk.2⟩
  · intro a ha
    exact (hg.2.1 a (zeroP_sub a (pSlots_sub a ha))).trans (hs0.zero a (pSlots_sub a ha))

/-- The root tail: `folds ≤ 120`, `E = 1`, empty stack (else HALT(1)); the layer constants; the
precode of layer 4 with the PORS root as its message. -/
theorem tailF_step (P : PCtx) (_hP : P.ok) (s0 : MachineState) (x c ptr E folds : Nat) (node : Val)
    (stk : List (Val × Nat)) (m : MachineState) (h : TailIn P s0 14 x 2 c ptr E folds node stk m) :
    ((folds > porsM ∨ E ≠ 1 ∨ stk ≠ []) → ∃ u k, k ≤ 9 ∧ Steps image m k k u ∧
        fetch image u = some (.base .ECALL) ∧ u.getReg .x5 = 1 ∧ u.getReg .x10 = 1) ∧
    (¬ (folds > porsM ∨ E ≠ 1 ∨ stk ≠ []) → ∃ u, Steps image m 22 22 u ∧
        LayerIn ⟨P.wl, P.pk, 4, P.idx⟩ node u) := by
  obtain ⟨hs, hd, hp, hp8, hpb, hfb⟩ := h.bnd
  have hE := h.hE
  have hc := h.hc
  have cF := tailFCheck_at c hc
  simp only [tailFCheck, Bool.and_eq_true] at cF
  obtain ⟨⟨⟨cAcc, cR1⟩, cR2⟩, cR3⟩ := cF
  have hK : KnownOK tailFKnown m := by
    intro q hq
    simp only [tailFKnown, List.mem_append, List.mem_singleton] at hq
    rcases hq with hq | hq
    · exact h.pb.reg hq
    · subst hq
      have := h.a2; simp only [destOf, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide,
        if_false] at this
      exact this
  have b1 : ∀ d, Br.holds m (fBr1 d) ↔ d = decide (120 < folds) := by
    intro d
    simp only [fBr1, Br.holds, CmpOp.eval, Rv.E.eval, cw, h.sum, BitVec.ult,
      ofNat_toNat_lt _ (show 120 < 2 ^ 64 by decide), ofNat_toNat_lt _ (show folds < 2 ^ 64 by omega)]
    exact eq_comm
  have b2 : ∀ d, Br.holds m (fBr2 d) ↔ d = decide (E ≠ 1) := by
    intro d
    simp only [fBr2, Br.holds, CmpOp.eval, addC_eval, Rv.E.eval, h.rE]
    have e1 : BitVec.ofNat 64 E + -1#64 = BitVec.ofNat 64 (E + (2 ^ 64 - 1)) := by
      rw [show (-1#64 : Word) = BitVec.ofNat 64 (2 ^ 64 - 1) from rfl, BitVec.ofNat_add_ofNat]
    have : (BitVec.ofNat 64 E + -1#64 != 0) = decide (E ≠ 1) := by
      rw [e1]
      by_cases hE1 : E = 1
      · subst hE1; decide
      · have hne : BitVec.ofNat 64 (E + (2 ^ 64 - 1)) ≠ 0 := by
          intro e; have := congrArg BitVec.toNat e
          simp only [BitVec.toNat_ofNat] at this; simp at this; omega
        rw [show (BitVec.ofNat 64 (E + (2 ^ 64 - 1)) != 0) = true from bne_iff_ne.mpr hne]
        simp [hE1]
    rw [this]; exact eq_comm
  have b3 : ∀ d, Br.holds m (fBr3 d) ↔ d = decide (stk ≠ []) := by
    intro d
    simp only [fBr3, Br.holds, CmpOp.eval, Rv.E.eval, cw, h.rS]
    have : (BitVec.ofNat 64 (stkOf' stk.length) != BitVec.ofNat 64 EMPTY) = decide (stk ≠ []) := by
      cases stk with
      | nil => simp [stkOf']
      | cons e r =>
        have hne : BitVec.ofNat 64 (stkOf' (e :: r).length) ≠ BitVec.ofNat 64 EMPTY :=
          ofNat_ne (by simp only [stkOf', EMPTY, List.length_cons] at hd ⊢; omega) (by decide) (by simp [stkOf', EMPTY])
        rw [show (BitVec.ofNat 64 (stkOf' (e :: r).length) != BitVec.ofNat 64 EMPTY) = true from bne_iff_ne.mpr hne]
        simp
    rw [this]; exact eq_comm
  have hpM : porsM = 120 := rfl
  constructor
  · intro hrej
    by_cases h1 : 120 < folds
    · obtain ⟨u, hu⟩ := pspec_run cR1 m h.pc hK (by
        intro b hb; simp only [rejSpec, List.mem_singleton] at hb; subst hb
        exact (b1 true).mpr (by simp [h1])) (by simp)
      exact ⟨u, 5, by omega, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
        hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
    · by_cases h2 : E ≠ 1
      · obtain ⟨u, hu⟩ := pspec_run cR2 m h.pc hK (by
          intro b hb; simp only [rejSpec, List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl
          · exact (b2 true).mpr (by simp [h2])
          · exact (b1 false).mpr (by simp [h1])) (by simp)
        exact ⟨u, 7, by omega, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
          hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
      · have h3 : stk ≠ [] := by
          rcases hrej with h' | h' | h'
          · exact absurd (by rw [hpM] at h'; exact h') h1
          · exact absurd h' h2
          · exact h'
        obtain ⟨u, hu⟩ := pspec_run cR3 m h.pc hK (by
          intro b hb; simp only [rejSpec, List.mem_cons, List.not_mem_nil, or_false] at hb
          rcases hb with rfl | rfl | rfl
          · exact (b3 true).mpr (by simp [h3])
          · exact (b2 false).mpr (by simp [h2])
          · exact (b1 false).mpr (by simp [h1])) (by simp)
        exact ⟨u, 9, le_refl _, hu.steps, hu.ecall rfl, hu.regs (.x5, cw 1) (by simp [rejSpec]),
          hu.regs (.x10, cw 1) (by simp [rejSpec])⟩
  · intro hacc
    have h1 : ¬ 120 < folds := fun e => hacc (Or.inl (by rw [hpM]; exact e))
    have h2 : ¬ E ≠ 1 := fun e => hacc (Or.inr (Or.inl e))
    have h3 : ¬ stk ≠ [] := fun e => hacc (Or.inr (Or.inr e))
    obtain ⟨u, hu⟩ := pspec_run cAcc m h.pc hK (by
      intro b hb; simp only [tailFSpec, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      · exact (b3 false).mpr (by simp [h3])
      · exact (b2 false).mpr (by simp [h2])
      · exact (b1 false).mpr (by simp [h1])) (by simp)
    have hg := hu.glob _ _ h.pb.glob
    have hmem : ∀ A, u.getMem A = m.getMem A := fun A => by rw [hu.mem]; rfl
    have n0 := h.node0; have n1 := h.node1
    simp only [destOf, show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, if_false] at n0 n1
    obtain ⟨t, ht, hpt⟩ := f4Pc_pre c hc
    refine ⟨u, hu.steps, PB.glob_layers hg h.pb.s0ok, hu.known, ?_, by rw [hmem]; exact n0,
      by rw [hmem]; exact n1, h.nodeLen, fun h => absurd h (lt_irrefl 4), ?_, t, ht, by rw [hu.pc rfl, ← hpt]; rfl⟩
    · show u.getReg .x22 = BitVec.ofNat 64 (routeIn P.idx 4)
      rw [hu.keep .x22 (by simp), h.pb.idx]; rfl
    · rw [hmem, h.pb.prot (by decide), h.pb.s0ok.cb0, ofNat_toNat_lt _ (by unfold twLo; omega)]
      have := P.idx_lt
      unfold twLo; omega


/-! ## The ladder: `segFolds` -/

/-- The body of `segFolds` (fold `i`). -/
def foldBody (idx : Nat) (w : List Byte) (ptr : Nat) : Val × Nat → Nat → OracleComp HashSpec (Val × Nat) :=
  fun st i =>
    let sib := wbytes w (ptr + 8 + 16 * i) 16
    if st.2 % 2 = 1 then do
      let v ← hash16 (porsNodeInput idx (st.2 / 2) sib st.1)
      pure (v, st.2 / 2)
    else do
      let v ← hash16 (porsNodeInput idx (st.2 / 2) st.1 sib)
      pure (v, st.2 / 2)

theorem segFolds_eq (idx : Nat) (w : List Byte) (ptr a : Nat) (node : Val) (E : Nat) :
    segFolds idx w ptr a node E = (List.range a).foldlM (foldBody idx w ptr) (node, E) := rfl

theorem foldBody_eq (P : PCtx) (ptr : Nat) (node : Val) (E i t : Nat) (ht : t = E % 2) :
    foldBody P.idx P.wl ptr (node, E) i =
      hash16 (foldInput P E t (wbytes P.wl (ptr + 8 + 16 * i) 16) node) >>= fun v => pure (v, E / 2) := by
  unfold foldBody foldInput
  simp only []
  rw [← ht]
  split_ifs <;> rfl

theorem folds_good (P : PCtx) (s0 : MachineState) (s x V a ptr folds : Nat)
    (stk : List (Val × Nat)) (K : Val × Nat → OracleComp HashSpec Obs) (NT CT AT : Nat) (QT : Prop)
    (hK : ∀ (t : Nat) (node : Val) (E : Nat) (u : MachineState),
      TailIn P s0 s x V t (ptr + 8 + 16 * a) E (folds + a) node stk u → GoodQ u NT CT QT AT (K (node, E))) :
    ∀ r i t E node m, i + r = a → PosIn P s0 s x V t a i ptr E folds node stk m →
      t = E % 2 →
      GoodQ m (NT + 17 * r) (CT + 17 * r - 2) QT (AT + 17 * r - 2)
        (cc ((List.range' i r).foldlM (foldBody P.idx P.wl ptr) (node, E)) K) := by
  intro r
  induction r with
  | zero => intro i t E node m hir h; have := h.ha; omega
  | succ k ih =>
    intro i t E node m hir h ht
    obtain ⟨u, hst, hf, h5, hv, hin, hbl, hpost⟩ := pos_step P s0 s x V t a i ptr E folds node stk m h
    rw [List.range'_succ, List.foldlM_cons, cc_bind, foldBody_eq P ptr node E i t ht, cc_bind]
    have H : ∀ ans, GoodQ (writeHash u ans) (if i + 1 = a then NT else NT + 17 * k)
        (if i + 1 = a then CT else CT + 17 * k - 2) QT (if i + 1 = a then AT else AT + 17 * k - 2)
        ((fun v => cc (pure (v, E / 2)) fun st =>
          cc ((List.range' (i + 1) k).foldlM (foldBody P.idx P.wl ptr) st) K) (answerBytes 16 ans)) := by
      intro ans
      simp only [cc_pure]
      by_cases hl : i + 1 = a
      · have hk : k = 0 := by omega
        subst hk
        simp only [List.range'_zero, List.foldlM_nil, cc_pure, if_pos hl]
        exact hK t _ _ _ ((hpost ans).2 hl)
      · simp only [if_neg hl]
        exact ih (i + 1) (E / 2 % 2) (E / 2) (answerBytes 16 ans) (writeHash u ans) (by omega)
          ((hpost ans).1 (by have := h.ha; omega)) rfl
    have h3 := GoodQ.hash (x := foldInput P E t (wbytes P.wl (ptr + 8 + 16 * i) 16) node)
      (K := fun v => cc (pure (v, E / 2)) fun st =>
          cc ((List.range' (i + 1) k).foldlM (foldBody P.idx P.wl ptr) st) K) hf h5 hv hin H
    rw [hbl] at h3
    have ha := h.ha
    refine GoodQ.steps' hst h3 ?_ ?_ ?_
    · split_ifs <;> omega
    · split_ifs with hl
      · have hk : k = 0 := by omega
        subst hk; omega
      · omega
    · intro q
      refine ⟨q, ?_⟩
      split_ifs with hl
      · have hk : k = 0 := by omega
        subst hk; omega
      · omega


/-! ## One segment -/

theorem pendingHash_eq (P : PCtx) (node : Val) (pend : Pending) :
    pendingHash P.idx node pend = hash16 (pendInput P node pend) := by
  cases pend <;> rfl

/-- One segment: `segment` from a dispatch; the continuation receives the Ref's result at the
tail of variant `V` (merge ↔ `V = 0`). Budgets: a segment with `a` folds costs at most `18 + 17 a`
(the parity reject: 12 steps and the halt). -/
theorem segment_good (P : PCtx) (hP : P.ok) (s0 : MachineState) (s x c ptr E folds : Nat) (pend : Pending)
    (node : Val) (stk : List (Val × Nat)) (m : MachineState) (h : DispIn P s0 s x c ptr E folds pend node stk m)
    (K : Option (Nat × Nat × Nat × Val × Bool) → OracleComp HashSpec Obs) (hnone : K none = pure (false, 0))
    (N C A : Nat) (NT CT : Nat → Nat) (AT : Nat → Nat → Nat)
    (hK : ∀ (a V c' E' : Nat) (node' : Val) (u : MachineState), a ≤ 14 →
      V = segV (tsel s) (wbyte P.wl ptr) → a = wbyte P.wl ptr % 16 →
      TailIn P s0 s x V c' (ptr + 8 + 16 * a) E' (folds + a) node' stk u →
      GoodQ u (NT V) (CT V) (folds + a ≤ 120) (AT V (folds + a))
        (K (some (ptr + 8 + 16 * a, E', folds + a, node', decide (wbyte P.wl ptr / 16 % 2 = 1)))))
    (hN : ∀ V, V < 3 → 18 + 17 * 14 + NT V ≤ N) (hC : ∀ V a, V < 3 → a ≤ 14 → 18 + 17 * a + CT V ≤ C)
    (hA : ∀ V a, V < 3 → a ≤ 14 → folds + a ≤ 120 → 18 + 17 * a + AT V (folds + a) ≤ A)
    (h9 : 13 ≤ N ∧ 13 ≤ C ∧ 13 ≤ A) :
    GoodQ m N C (folds ≤ 120) A (cc (Ref.segment P.idx P.wl ptr E folds pend node) K) := by
  obtain ⟨hrej, hpar, hacc⟩ := seg_step P hP s0 s x c ptr E folds pend node stk m h
  unfold Ref.segment
  simp only []
  set b := wbyte P.wl ptr with hb
  by_cases ha : b % 16 > porsH
  · rw [if_pos ha, cc_pure, hnone]
    obtain ⟨u, hst, hf, h5, h10⟩ := hrej (by unfold porsH at ha; omega)
    exact GoodQ.steps' hst (GoodQ.reject (Q := folds ≤ 120) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  rw [if_neg ha]
  have ha14 : b % 16 ≤ 14 := by unfold porsH at ha; omega
  by_cases hp : 0 < b % 16 ∧ b / 32 % 2 ≠ E % 2
  · rw [if_pos hp, cc_pure, hnone]
    obtain ⟨u, hst, hf, h5, h10⟩ := hpar (by omega) ha14 hp.2
    exact GoodQ.steps' hst (GoodQ.reject (Q := folds ≤ 120) (A := 0) hf h5 h10) (by omega) (by omega)
      (fun q => ⟨q, by omega⟩)
  · rw [if_neg hp, cc_bind, pendingHash_eq]
    have hpar' : b % 16 = 0 ∨ segT b = E % 2 := by unfold segT; omega
    obtain ⟨k, u, hk, hst, hf, h5, hv, hin, hbl, hpost⟩ := hacc ha14 hpar'
    have hVl := segV_lt (tsel s) b
    set a := b % 16 with hadef
    set V := segV (tsel s) b with hV
    -- after the pending hash
    have H : ∀ ans, GoodQ (writeHash u ans) (NT V + 17 * 14 + 2) (CT V + 17 * a) (folds + a ≤ 120) (AT V (folds + a) + 17 * a)
        ((fun v => cc (segFolds P.idx P.wl ptr a v E) fun p =>
          match p with
          | (node, E) => K (some (ptr + 8 + 16 * a, E, folds + a, node, decide (b / 16 % 2 = 1))))
          (answerBytes 16 ans)) := by
      intro ans
      simp only []
      by_cases ha0 : a = 0
      · rw [ha0, segFolds_eq]
        simp only [List.range_zero, List.foldlM_nil, cc_pure]
        have hT := (hpost ans).1 ha0
        have := hK 0 V 2 E (answerBytes 16 ans) (writeHash u ans) (by omega) rfl (by omega) (by simpa using hT)
        simp only [Nat.mul_zero, Nat.add_zero] at this
        simp only [ha0, Nat.mul_zero, Nat.add_zero]
        exact this.mono (by omega) (by omega) (fun q => ⟨by omega, by omega⟩)
      · have hE := (hpost ans).2 (by omega)
        obtain ⟨u2, hst2, hP2⟩ := ent_step P s0 s x V (segT b) a ptr E folds (answerBytes 16 ans) stk _ hE
        rw [segFolds_eq, List.range_eq_range']
        have := folds_good P s0 s x V a ptr folds stk
          (fun p => match p with
            | (node, E) => K (some (ptr + 8 + 16 * a, E, folds + a, node, decide (b / 16 % 2 = 1))))
          (NT V) (CT V) (AT V (folds + a)) (folds + a ≤ 120)
          (fun t node' E' u' hT => hK a V t E' node' u' ha14 rfl rfl hT) a 0 (segT b) E (answerBytes 16 ans)
          u2 (by omega) hP2 (by rcases hpar' with e | e <;> [omega; exact e])
        refine GoodQ.steps' hst2 this (by omega) (by omega) (fun q => ⟨by omega, by omega⟩)
    have h3 := GoodQ.hash (x := pendInput P node pend)
      (K := fun v => cc (segFolds P.idx P.wl ptr a v E) fun p =>
          match p with
          | (node, E) => K (some (ptr + 8 + 16 * a, E, folds + a, node, decide (b / 16 % 2 = 1)))) hf h5 hv hin H
    rw [hbl] at h3
    have e2 : (fun node' => cc (segFolds P.idx P.wl ptr a node' E >>= fun x =>
          match x with
          | (node, E) => pure (some (ptr + 8 + 16 * a, E, folds + a, node, decide (b / 16 % 2 = 1)))) K) =
        (fun v => cc (segFolds P.idx P.wl ptr a v E) fun p =>
          match p with
          | (node, E) => K (some (ptr + 8 + 16 * a, E, folds + a, node, decide (b / 16 % 2 = 1)))) := by
      funext v; rw [cc_bind]; congr 1; funext p; obtain ⟨n1, e1⟩ := p; simp only [cc_pure]
    rw [e2]
    exact GoodQ.steps' hst h3 (by have := hN V hVl; omega) (by have := hC V a hVl ha14; omega)
      (fun q => ⟨by omega, by have := hA V a hVl ha14 q; omega⟩)


/-! ## Budgets

At a segment start of leaf `s` with depth `d` and `F` folds so far, at most `segR s d = 29 - 2 s + d`
segments remain (every merge pops, every push ends a leaf), at most `d + 14 - s` merge tails and
`14 - s` push tails. Every run: `256 = 18 + 17 · 14` per segment (`Cseg`); accepting runs:
`18` per segment (`16` without folds, `18` with) plus `17` per fold, and the folds total at most
`120` (`Aseg`). -/

def layN : Nat := 5000 * 5 + 9
/-- The layers' cost (irreducible here, so that unification never evaluates it). -/
@[irreducible] def layC : Nat := layersCost 5
def leafCost (s : Nat) : Nat := if s = 0 then 10 else if s = 14 then 15 else 11
def lrest (s : Nat) : Nat := ((List.range' (s + 1) (14 - s)).map leafCost).sum
def segR (s d : Nat) : Nat := 29 - 2 * s + d

def Cseg (s d : Nat) : Nat :=
  256 * segR s d + 6 * (d + 14 - s) + 4 * (14 - s) + lrest s + 22 + layC
def Aseg (s d F : Nat) : Nat :=
  18 * segR s d + 17 * (120 - F) + 6 * (d + 14 - s) + 4 * (14 - s) + lrest s + 22 + layC
def Nseg (s d : Nat) : Nat := Cseg s d + layN

/-- After the leaf's last segment (before the push / root tail). -/
def CtailPF (s d : Nat) : Nat := if s = 14 then 22 + layC else 4 + leafCost (s + 1) + Cseg (s + 1) (d + 1)
def AtailPF (s d F : Nat) : Nat :=
  if s = 14 then 22 + layC else 4 + leafCost (s + 1) + Aseg (s + 1) (d + 1) F
def NtailPF (s d : Nat) : Nat := CtailPF s d + layN

/-- Before a merge tail. -/
def CtailM (s d : Nat) : Nat := if d = 0 then 6 else 6 + Cseg s (d - 1)
def AtailM (s d F : Nat) : Nat := if d = 0 then 6 else 6 + Aseg s (d - 1) F
def NtailM (s d : Nat) : Nat := CtailM s d + layN

theorem lrest_succ : ∀ s, s < 14 → lrest s = leafCost (s + 1) + lrest (s + 1) := by decide
theorem lrest_14 : lrest 14 = 0 := rfl
theorem leafCost_le (s : Nat) : 10 ≤ leafCost s ∧ leafCost s ≤ 15 := by unfold leafCost; split_ifs <;> omega

/-! ## The segments of a leaf -/

theorem segV_M (tb b : Nat) (h : segV tb b = 0) : b / 16 % 2 = 1 := by
  unfold segV segM at h; split_ifs at h with h1 h2 <;> omega

theorem segV_PF (s b : Nat) (h : segV (tsel s) b ≠ 0) : segV (tsel s) b = (if s = 14 then 2 else 1) ∧
    ¬ b / 16 % 2 = 1 := by
  unfold segV segM tsel at *; split_ifs at * <;> simp_all

theorem seg_budget (s d : Nat) (hs : s < 15) (hd : d ≤ s) :
    (∀ a, a ≤ 14 → 18 + 17 * a + CtailM s d ≤ Cseg s d) ∧
    (∀ a, a ≤ 14 → 18 + 17 * a + CtailPF s d ≤ Cseg s d) ∧
    (18 + 17 * 14 + NtailM s d ≤ Nseg s d) ∧ (18 + 17 * 14 + NtailPF s d ≤ Nseg s d) ∧
    (∀ F a, a ≤ 14 → F + a ≤ 120 → 18 + 17 * a + AtailM s d (F + a) ≤ Aseg s d F) ∧
    (∀ F a, a ≤ 14 → F + a ≤ 120 → 18 + 17 * a + AtailPF s d (F + a) ≤ Aseg s d F) ∧
    (∀ F, 13 ≤ Nseg s d ∧ 13 ≤ Cseg s d ∧ 13 ≤ Aseg s d F) := by
  have hl := leafCost_le (s + 1)
  have hls : s < 14 → lrest s = leafCost (s + 1) + lrest (s + 1) := lrest_succ s
  unfold NtailM NtailPF Nseg CtailM CtailPF AtailM AtailPF Cseg Aseg segR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; split_ifs <;> omega
  · intro a ha
    split_ifs with h14
    · subst h14; rw [lrest_14]; omega
    · have := hls (by omega); omega
  · split_ifs <;> omega
  · split_ifs with h14
    · subst h14; rw [lrest_14]; omega
    · have := hls (by omega); omega
  · intro F a ha hF; split_ifs <;> omega
  · intro F a ha hF
    split_ifs with h14
    · subst h14; rw [lrest_14]; omega
    · have := hls (by omega); omega
  · intro F; omega

theorem segLoop_good (P : PCtx) (hP : P.ok) (s0 : MachineState) (s x : Nat)
    (K : Option (Nat × Nat × Nat × Val × List (Val × Nat)) → OracleComp HashSpec Obs)
    (hnone : K none = pure (false, 0))
    (hK : ∀ ptr E folds node stk c u, TailIn P s0 s x (if s = 14 then 2 else 1) c ptr E folds node stk u →
      GoodQ u (NtailPF s stk.length) (CtailPF s stk.length) (folds ≤ 120) (AtailPF s stk.length folds)
        (K (some (ptr, E, folds, node, stk)))) :
    ∀ stk ptr E folds pend node c m, DispIn P s0 s x c ptr E folds pend node stk m →
      GoodQ m (Nseg s stk.length) (Cseg s stk.length) (folds ≤ 120) (Aseg s stk.length folds)
        (cc (segLoop P.idx P.wl ptr E folds pend node stk) K) := by
  intro stk
  induction stk with
  | nil =>
    intro ptr E folds pend node c m h
    obtain ⟨hs, hd, -⟩ := h.bnd
    obtain ⟨bM, bPF, bNM, bNPF, bAM, bAPF, b9⟩ := seg_budget s 0 hs (by omega)
    simp only [segLoop, cc_bind]
    refine segment_good P hP s0 s x c ptr E folds pend node [] m h _ (by simp [hnone])
      (Nseg s 0) (Cseg s 0) (Aseg s 0 folds)
      (fun V => if V = 0 then NtailM s 0 else NtailPF s 0) (fun V => if V = 0 then CtailM s 0 else CtailPF s 0)
      (fun V F => if V = 0 then AtailM s 0 F else AtailPF s 0 F) ?_
      (fun V _ => by split_ifs <;> omega) (fun V a _ ha => by split_ifs <;> [exact bM a ha; exact bPF a ha])
      (fun V a _ ha hF => by split_ifs <;> [exact bAM folds a ha hF; exact bAPF folds a ha hF])
      (b9 folds)
    intro a V c' E' node' u ha hV haw hT
    by_cases hV0 : V = 0
    · -- merge on an empty stack: reject
      have hm := segV_M _ _ (hV ▸ hV0)
      simp only [hV0, if_true, hm, decide_true, if_true, cc_pure, hnone]
      rw [hV0] at hT
      obtain ⟨u2, hst2, hf2, h52, h102⟩ := (tailM_step P s0 s x c' _ E' _ node' [] u hT).2.1 rfl
      exact GoodQ.steps' hst2 (GoodQ.reject (Q := folds + a ≤ 120) (A := 0) hf2 h52 h102)
        (by unfold NtailM CtailM; simp) (by unfold CtailM; simp) (fun q => ⟨q, by unfold AtailM; simp⟩)
    · obtain ⟨hVe, hm⟩ := segV_PF s _ (hV ▸ hV0)
      simp only [hV0, if_false, hm, decide_false, Bool.false_eq_true, cc_pure]
      rw [hV, hVe] at hT
      have hh := hK (ptr + 8 + 16 * a) E' (folds + a) node' [] c' u hT
      exact hh
  | cons e rest ih =>
    intro ptr E folds pend node c m h
    obtain ⟨pnode, Q⟩ := e
    obtain ⟨hs, hd, -⟩ := h.bnd
    obtain ⟨bM, bPF, bNM, bNPF, bAM, bAPF, b9⟩ := seg_budget s (rest.length + 1) hs (by simpa using hd)
    simp only [segLoop, cc_bind]
    refine segment_good P hP s0 s x c ptr E folds pend node _ m h _ (by simp [hnone])
      (Nseg s (rest.length + 1)) (Cseg s (rest.length + 1)) (Aseg s (rest.length + 1) folds)
      (fun V => if V = 0 then NtailM s (rest.length + 1) else NtailPF s (rest.length + 1))
      (fun V => if V = 0 then CtailM s (rest.length + 1) else CtailPF s (rest.length + 1))
      (fun V F => if V = 0 then AtailM s (rest.length + 1) F else AtailPF s (rest.length + 1) F) ?_
      (fun V _ => by split_ifs <;> omega) (fun V a _ ha => by split_ifs <;> [exact bM a ha; exact bPF a ha])
      (fun V a _ ha hF => by split_ifs <;> [exact bAM folds a ha hF; exact bAPF folds a ha hF])
      (b9 folds)
    intro a V c' E' node' u ha hV haw hT
    by_cases hV0 : V = 0
    · have hm := segV_M _ _ (hV ▸ hV0)
      simp only [hV0, if_true, hm, decide_true, Bool.not_true, Bool.false_eq_true, if_false]
      rw [hV0] at hT
      have tM := tailM_step P s0 s x c' _ E' _ node' ((pnode, Q) :: rest) u hT
      by_cases hQ : Q = E'
      · subst hQ
        simp only [ne_eq, not_true_eq_false, if_false]
        obtain ⟨u2, hst2, hD⟩ := tM.2.2 pnode rest rfl
        have := ih _ _ _ _ _ _ u2 hD
        simp only [NtailM, CtailM, AtailM, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
        exact GoodQ.steps' hst2 this (by simp only [Nseg]; omega) (by omega) (fun q => ⟨q, by omega⟩)
      · simp only [ne_eq, hQ, not_false_eq_true, if_true, cc_pure, hnone]
        obtain ⟨u2, hst2, hf2, h52, h102⟩ := tM.1 pnode Q rest rfl hQ
        exact GoodQ.steps' hst2 (GoodQ.reject (Q := folds + a ≤ 120) (A := 0) hf2 h52 h102)
          (by unfold NtailM CtailM; split_ifs <;> omega) (by unfold CtailM; split_ifs <;> omega)
          (fun q => ⟨q, by unfold AtailM; split_ifs <;> omega⟩)
    · obtain ⟨hVe, hm⟩ := segV_PF s _ (hV ▸ hV0)
      simp only [hV0, if_false, hm, decide_false, Bool.not_false, if_true, cc_pure]
      rw [hV, hVe] at hT
      have hh := hK (ptr + 8 + 16 * a) E' (folds + a) node' ((pnode, Q) :: rest) c' u hT
      exact hh


/-! ## The leaves -/

theorem leafCost_eq (s : Nat) : (if s = 0 then 10 else if s = 14 then 15 else 11) = leafCost s := rfl

theorem leaves_good (P : PCtx) (hP : P.ok) (s0 : MachineState)
    (Kr : Option PorsState → OracleComp HashSpec Obs) (hnone : Kr none = pure (false, 0))
    (hKr : ∀ (x c : Nat) (st : PorsState) (u : MachineState),
      TailIn P s0 14 x 2 c st.ptr st.E st.folds st.node st.stack u →
      GoodQ u (22 + layC + layN) (22 + layC) (st.folds ≤ 120) (22 + layC) (Kr (some st))) :
    ∀ n s (st : PorsState) m, s + n = 15 → LeafIn P s0 s st m →
      GoodQ m (leafCost s + Nseg s st.stack.length) (leafCost s + Cseg s st.stack.length) (st.folds ≤ 120)
        (leafCost s + Aseg s st.stack.length st.folds)
        (cc (porsLeaves P.idx P.v P.wl (List.range' s n) st) Kr) := by
  intro n
  induction n with
  | zero => intro s st m hsn h; have := h.bnd.1; omega
  | succ k ih =>
    intro s st m hsn h
    obtain ⟨hs, hd, -⟩ := h.bnd
    obtain ⟨bM, bPF, bNM, bNPF, bAM, bAPF, b9⟩ := seg_budget s st.stack.length hs hd
    obtain ⟨hrej, hacc⟩ := pleaf_step P hP s0 s st m h
    rw [List.range'_succ]
    simp only [porsLeaves]
    have hx : (P.v ++ [porsT]).getD (witPi P.wl s / 8 % 16) 0 = leafX P s := rfl
    rw [hx]
    have hl := leafCost_le s
    have h9 := b9 st.folds
    by_cases h1 : s ≠ 0 ∧ ¬ st.prev < leafX P s
    · rw [if_pos h1, cc_pure, hnone]
      obtain ⟨u, k', hk', hst, hf, h5, h10⟩ := hrej (Or.inl h1)
      exact GoodQ.steps' hst (GoodQ.reject (Q := st.folds ≤ 120) (A := 0) hf h5 h10)
        (by omega) (by omega) (fun q => ⟨q, by omega⟩)
    · rw [if_neg h1]
      by_cases h2 : s = porsK - 1 ∧ ¬ leafX P s < porsT
      · rw [if_pos h2, cc_pure, hnone]
        obtain ⟨u, k', hk', hst, hf, h5, h10⟩ := hrej (Or.inr h2)
        exact GoodQ.steps' hst (GoodQ.reject (Q := st.folds ≤ 120) (A := 0) hf h5 h10)
          (by omega) (by omega) (fun q => ⟨q, by omega⟩)
      · rw [if_neg h2, cc_bind]
        obtain ⟨u, hst, hD⟩ := hacc (fun hc => hc.elim h1 h2)
        rw [leafCost_eq] at hst
        refine GoodQ.steps' hst (segLoop_good P hP s0 s (leafX P s) _ (by simp [hnone]) ?_ st.stack st.ptr
          (porsT ||| leafX P s) st.folds _ st.node s u hD) (by omega) (by omega) (fun q => ⟨q, by omega⟩)
        intro ptr E folds node stk c u' hT
        simp only []
        by_cases h14 : s = 14
        · subst h14
          have hk0 : k = 0 := by omega
          subst hk0
          simp only [if_true] at hT
          simp only [List.range'_zero, porsK, show ¬ (14 < 15 - 1) by decide, if_false]
          rw [show (porsLeaves P.idx P.v P.wl [] ⟨ptr, leafX P 14, E, folds, node, stk⟩ :
              OracleComp HashSpec (Option PorsState)) = pure (some ⟨ptr, leafX P 14, E, folds, node, stk⟩) from rfl,
            cc_pure]
          have := hKr (leafX P 14) c ⟨ptr, leafX P 14, E, folds, node, stk⟩ u' hT
          simp only [NtailPF, CtailPF, AtailPF, if_true]
          exact this
        · simp only [h14, if_false] at hT
          have hs14 : s < 14 := by omega
          obtain ⟨u2, hst2, hL⟩ := tailP_step P s0 s (leafX P s) c ptr E folds node stk u' hs14 hT
          simp only [porsK, show s < 15 - 1 by omega, if_true]
          have := ih (s + 1) ⟨ptr, leafX P s, E, folds, node, (node, E ^^^ 1) :: stk⟩ u2 (by omega) hL
          simp only [List.length_cons] at this
          simp only [NtailPF, CtailPF, AtailPF, h14, if_false]
          refine GoodQ.steps' hst2 this (by unfold Nseg; omega) (by omega) (fun q => ⟨q, by omega⟩)

end SigGolfCandidate.Verify
