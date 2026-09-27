import SigGolfCandidate.Expand.Ext

/-!
# `expand`: insertion sort of the keys (`da_sort`, instructions 40 .. 54)

The array `KEYS[0 .. 15)` is described by a function `A` (dword `p` holds `A p`). The outer loop
(`da_sort`, `s0 = i`) keeps `A` a permutation of the keys with `A[0 .. i)` strictly increasing;
the inner loop (`da_shift`, hole `j`, key `x` in `s1`) keeps the *logical* array
`update A j x` a permutation of the keys, `A` strictly increasing on `[0, i] \ {j}` and every
element right of the hole above `x`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- The 15 keys in digest-slot order. -/
def keysOf (N : Nat) : List Nat := (List.range 15).map (keyOf N)

theorem keyOf_lt (N r : Nat) (hr : r < 15) : keyOf N r < 2 ^ 22 := by
  unfold keyOf leafOf porsH
  have := Nat.mod_lt (N / 2 ^ (totalH + 14 * r)) (show 0 < 2 ^ 14 by decide)
  omega

theorem keyOf_mod (N r : Nat) (hr : r < 15) : keyOf N r % 256 = 8 * r := by
  unfold keyOf; omega

theorem keysOf_nodup (N : Nat) : (keysOf N).Nodup := by
  unfold keysOf
  refine List.Nodup.map_on (fun a ha b hb h => ?_) List.nodup_range
  have := keyOf_mod N a (List.mem_range.mp ha); have := keyOf_mod N b (List.mem_range.mp hb)
  omega

/-- Swapping two adjacent entries of an array is a permutation of its list. -/
theorem perm_swap_adj (f : Nat → Nat) (n j : Nat) (hj : j + 1 < n) :
    List.Perm ((List.range n).map (fun p => if p = j then f (j + 1) else if p = j + 1 then f j else f p))
      ((List.range n).map f) := by
  have hr : List.range n = List.range j ++ [j, j + 1] ++ (List.range (n - (j + 2))).map (j + 2 + ·) := by
    conv_lhs => rw [show n = (j + 2) + (n - (j + 2)) by omega]
    rw [List.range_add, List.range_succ, List.range_succ]; simp
  rw [hr]
  simp only [List.map_append, List.map_cons, List.map_nil, if_pos, if_true,
    show j + 1 ≠ j by omega, if_false, List.map_map]
  have h1 : (List.range j).map (fun p => if p = j then f (j + 1) else if p = j + 1 then f j else f p) =
      (List.range j).map f := by
    apply List.map_congr_left; intro p hp; rw [List.mem_range] at hp
    rw [if_neg (by omega), if_neg (by omega)]
  have h2 : (List.range (n - (j + 2))).map
      ((fun p => if p = j then f (j + 1) else if p = j + 1 then f j else f p) ∘ (j + 2 + ·)) =
      (List.range (n - (j + 2))).map (f ∘ (j + 2 + ·)) := by
    apply List.map_congr_left; intro p hp
    simp only [Function.comp]; rw [if_neg (by omega), if_neg (by omega)]
  rw [h1, h2]
  exact List.Perm.append_right _ (List.Perm.append_left _ (List.Perm.swap _ _ _))

/-- Nodup lists of array values: distinct positions hold distinct values. -/
theorem inj_of_perm {f : Nat → Nat} {n : Nat} {l : List Nat} (hp : List.Perm ((List.range n).map f) l)
    (hl : l.Nodup) {p q : Nat} (hpn : p < n) (hqn : q < n) (hpq : p ≠ q) : f p ≠ f q := by
  have hnd : ((List.range n).map f).Nodup := hp.nodup_iff.mpr hl
  intro h
  exact hpq ((List.inj_on_of_nodup_map hnd) (List.mem_range.mpr hpn) (List.mem_range.mpr hqn) h)

/-- `KEYS[p] = A p` for `p < 15`. -/
def ArrOk (t : MachineState) (A : Nat → Nat) : Prop :=
  ∀ p < 15, t.getMem (BitVec.ofNat 64 (0x6E0 + 8 * p)) = BitVec.ofNat 64 (A p)

/-- Array facts shared by the sort invariants. -/
structure ArrFacts (N : Nat) (A : Nat → Nat) (j x : Nat) : Prop where
  perm : List.Perm ((List.range 15).map (fun p => if p = j then x else A p)) (keysOf N)
  lt : ∀ p < 15, A p < 2 ^ 22
  xlt : x < 2 ^ 22

/-- Outer loop invariant at `da_sort` (instruction 41): `A[0 .. i)` sorted. -/
structure SortInv (ans : BitVec 256) (s0 : MachineState) (i : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf 41
  x8 : t.getReg .x8 = BitVec.ofNat 64 i
  hi : 1 ≤ i ∧ i < 15
  arr : ∃ A, ArrOk t A ∧ ArrFacts ans.toNat A i (A i) ∧ ∀ p q, p < q → q < i → A p < A q
  sent : t.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22)
  frame : Frame s0 t KW

/-- Inner loop invariant at `da_shift` (44, `pc0 = 44`) or at `da_place` (51, `pc0 = 51`, then
`j = 0 ∨ A (j - 1) < x`): hole `j`, key `x`. -/
structure ShiftInv (ans : BitVec 256) (s0 : MachineState) (pc0 i j x : Nat) (t : MachineState) : Prop where
  pc : t.pc = pcOf pc0
  x8 : t.getReg .x8 = BitVec.ofNat 64 i
  x9 : t.getReg .x9 = BitVec.ofNat 64 x
  x14 : t.getReg .x14 = BitVec.ofNat 64 (0x6E0 + 8 * j)
  hij : j ≤ i
  hi : 1 ≤ i ∧ i < 15
  arr : ∃ A, ArrOk t A ∧ ArrFacts ans.toNat A j x ∧
    (∀ p q, p < q → q ≤ i → p ≠ j → q ≠ j → A p < A q) ∧ (∀ q, j < q → q ≤ i → x < A q) ∧
    (pc0 = 51 → j = 0 ∨ A (j - 1) < x)
  sent : t.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22)
  frame : Frame s0 t KW

/-- After the sort (instruction 55). -/
structure SortDone (ans : BitVec 256) (s0 : MachineState) (t : MachineState) : Prop where
  pc : t.pc = pcOf 55
  arr : ∃ A, ArrOk t A ∧ ArrFacts ans.toNat A 15 0 ∧ ∀ p q, p < q → q < 15 → A p < A q
  sent : t.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22)
  frame : Frame s0 t KW

theorem ArrOk.frame {t u : MachineState} {A : Nat → Nat} (h : ArrOk t A)
    (hm : ∀ a, u.getMem a = t.getMem a) : ArrOk u A := fun p hp => by rw [hm]; exact h p hp

/-- Memory after one `sd` at `KEYS + 8 j`. -/
theorem arr_store {t u : MachineState} {A : Nat → Nat} {j v : Nat} (hA : ArrOk t A) (hj : j < 15)
    (hm : ∀ a : Nat, a < 2 ^ 64 → u.getMem (BitVec.ofNat 64 a) =
      if a = 0x6E0 + 8 * j then BitVec.ofNat 64 v else t.getMem (BitVec.ofNat 64 a)) :
    ArrOk u (fun p => if p = j then v else A p) := by
  intro p hp
  rw [hm _ (by omega)]
  by_cases h : p = j
  · subst h; simp
  · rw [if_neg (by omega)]; simp only [h, if_false]; exact hA p hp

theorem frame_store {s0 t u : MachineState} {j v : Nat} (hf : Frame s0 t KW) (hj : j < 15)
    (hm : ∀ a : Nat, a < 2 ^ 64 → u.getMem (BitVec.ofNat 64 a) =
      if a = 0x6E0 + 8 * j then BitVec.ofNat 64 v else t.getMem (BitVec.ofNat 64 a)) :
    Frame s0 u KW := fun a ha hW => by
  rw [hm a ha, if_neg (by unfold KW at hW; omega), hf a ha hW]

theorem sent_store {t u : MachineState} {j v : Nat} (hs : t.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22))
    (hj : j < 15)
    (hm : ∀ a : Nat, a < 2 ^ 64 → u.getMem (BitVec.ofNat 64 a) =
      if a = 0x6E0 + 8 * j then BitVec.ofNat 64 v else t.getMem (BitVec.ofNat 64 a)) :
    u.getMem (BitVec.ofNat 64 0x758) = BitVec.ofNat 64 (2 ^ 22) := by
  rw [hm _ (by omega), if_neg (by omega), hs]

/-- Memory after a block whose only write is `sd src, 0(a4)` with `a4 = KEYS + 8 j`. -/
theorem mem_sd_a4 {r : Result} {t : MachineState} {j v : Nat} {src : Reg}
    (hmem : r.st.mem = [({ base := some (E.reg .x14), off := 0#64 }, E.reg src)])
    (h14 : t.getReg .x14 = BitVec.ofNat 64 (0x6E0 + 8 * j)) (hv : t.getReg src = BitVec.ofNat 64 v)
    (hj : j < 15) :
    ∀ a : Nat, a < 2 ^ 64 → (r.toState t).getMem (BitVec.ofNat 64 a) =
      if a = 0x6E0 + 8 * j then BitVec.ofNat 64 v else t.getMem (BitVec.ofNat 64 a) := by
  intro a ha
  rw [Result.toState_getMem, hmem]
  simp only [memEval, Addr.eval, E.eval, h14, hv, Option.map, BitVec.add_zero]
  by_cases h : a = 0x6E0 + 8 * j
  · subst h; simp
  · rw [if_neg h, if_neg]; rw [ofNat_eq_iff]; omega


theorem sort_start (ans : BitVec 256) (s0 t : MachineState) (h : ExtDone ans s0 t) :
    Run t 1 (SortInv ans s0 1) := by
  obtain ⟨tpc, tkeys, tsent, tframe⟩ := h
  refine Run.of (symRun_sound blk40 codeAt_40 t tpc (by simp only [blk40.res, rv_simp])) (le_refl _) ?_
  have hm : ∀ a, (blk40.res.toState t).getMem a = t.getMem a := by intro a; simp only [blk40.res, rv_simp]
  refine ⟨by simp only [blk40.res, rv_simp], by simp only [blk40.res, rv_simp], by omega,
    ⟨keyOf ans.toNat, fun p hp => by rw [hm]; exact tkeys p hp, ⟨?_, fun p hp => keyOf_lt _ _ hp,
      keyOf_lt _ _ (by omega)⟩, fun p q hpq hq => by omega⟩, by rw [hm]; exact tsent,
    fun a ha hW => by rw [hm]; exact tframe a ha hW⟩
  have : (List.range 15).map (fun p => if p = 1 then keyOf ans.toNat 1 else keyOf ans.toNat p) =
      keysOf ans.toNat := by
    unfold keysOf; apply List.map_congr_left; intro p _; split <;> simp_all
  rw [this]

theorem sort_head (ans : BitVec 256) (s0 : MachineState) (i : Nat) (t : MachineState) (h : SortInv ans s0 i t) :
    Run t 3 (fun u => ∃ x, ShiftInv ans s0 44 i i x u) := by
  obtain ⟨tpc, t8, hi, ⟨A, hA, hF, hs⟩, tsent, tframe⟩ := h
  have hobl : blk41.res.obligs t := by
    simp only [blk41.res, rv_simp, t8]; ex_bvsimp [accessValid_ofNat]; omega
  refine Run.of (symRun_sound blk41 codeAt_41 t tpc hobl) (le_refl _) ⟨A i, ?_⟩
  have hm : ∀ a, (blk41.res.toState t).getMem a = t.getMem a := by intro a; simp only [blk41.res, rv_simp]
  refine ⟨by simp only [blk41.res, rv_simp] <;> rfl, by simp only [blk41.res, rv_simp, t8],
    ?_, ?_, le_refl _, hi, ⟨A, hA.frame hm, hF, fun p q hpq hq hp hqi => hs p q hpq (by omega),
      fun q hq hq' => by omega, fun h => by omega⟩, by rw [hm]; exact tsent,
      fun a ha hW => by rw [hm]; exact tframe a ha hW⟩
  · simp only [blk41.res, rv_simp, t8]; ex_bvsimp []
    rw [show i * 8 + 1760 = 1760 + 8 * i by ring]; exact hA i hi.2
  · simp only [blk41.res, rv_simp, t8]; ex_bvsimp []; exact ofNat_congr (by ring)



theorem ult_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ult (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [BitVec.ult, BitVec.toNat_ofNat, decide_eq_decide]; omega

theorem shift_loop (ans : BitVec 256) (s0 : MachineState) (i x : Nat) :
    ∀ j t, ShiftInv ans s0 44 i j x t → Run t (7 * j + 4) (fun u => ∃ j', ShiftInv ans s0 51 i j' x u) := by
  intro j
  induction j with
  | zero =>
    intro t h
    obtain ⟨tpc, t8, t9, t14, hij, hi, ⟨A, hA, hF, hs, hx, _⟩, tsent, tframe⟩ := h
    refine Run.of (symRun_sound blk44 codeAt_44 t tpc (by simp only [blk44.res, rv_simp])) (by decide) ⟨0, ?_⟩
    have hm : ∀ a, (blk44.res.toState t).getMem a = t.getMem a := by intro a; simp only [blk44.res, rv_simp]
    refine ⟨?_, by simp only [blk44.res, rv_simp, t8], by simp only [blk44.res, rv_simp, t9],
      by simp only [blk44.res, rv_simp, t14], hij, hi, ⟨A, hA.frame hm, hF, hs, hx, fun _ => Or.inl rfl⟩,
      by rw [hm]; exact tsent, fun a ha hW => by rw [hm]; exact tframe a ha hW⟩
    simp only [blk44.res, rv_simp, t14]; rfl
  | succ j ih =>
    intro t h
    obtain ⟨tpc, t8, t9, t14, hij, hi, ⟨A, hA, hF, hs, hx, _⟩, tsent, tframe⟩ := h
    refine (Run.blk blk44 codeAt_44 tpc (by simp only [blk44.res, rv_simp]) (B := 7 * j + 9) ?_).mono
      (by rw [show blk44.res.cycles = 2 from rfl]; omega) (fun _ h => h)
    set t1 := blk44.res.toState t with ht1
    have p1 : t1.pc = pcOf 46 := by
      have hne : ¬ (1760 + 8 * (j + 1) = 1760) := by omega
      simp only [ht1, blk44.res, rv_simp, t14]; ex_bvsimp [ofNat_beq_ofNat]; simp
    have m1 : ∀ a, t1.getMem a = t.getMem a := by intro a; simp only [ht1, blk44.res, rv_simp]
    have r1 : ∀ r, r = .x8 ∨ r = .x9 ∨ r = .x14 → t1.getReg r = t.getReg r := by
      rintro r (rfl | rfl | rfl) <;> simp only [ht1, blk44.res, rv_simp]
    have hobl2 : blk46.res.obligs t1 := by
      simp only [blk46.res, rv_simp, r1 .x14 (by simp), t14]; ex_bvsimp [accessValid_ofNat]; omega
    have hAj : t1.getMem (BitVec.ofNat 64 (1760 + 8 * (j + 1) - 8)) = BitVec.ofNat 64 (A j) := by
      rw [m1, show 1760 + 8 * (j + 1) - 8 = 1760 + 8 * j by omega]; exact hA j (by omega)
    have hne : A j ≠ x := by
      have := inj_of_perm hF.perm (keysOf_nodup _) (p := j) (q := j + 1) (by omega) (by omega) (by omega)
      simpa using this
    have hxlt : x < 2 ^ 22 := hF.xlt
    have hAlt : A j < 2 ^ 22 := hF.lt j (by omega)
    refine (Run.blk blk46 codeAt_46 p1 hobl2 (B := 7 * j + 7) ?_).mono
      (by rw [show blk46.res.cycles = 2 from rfl]; try omega) (fun _ h => h)
    set t2 := blk46.res.toState t1 with ht2
    have m2 : ∀ a, t2.getMem a = t.getMem a := by intro a; simp only [ht2, blk46.res, rv_simp, m1]
    have p2 : t2.pc = if A j < x then pcOf 51 else pcOf 48 := by
      simp only [ht2, blk46.res, rv_simp, r1 .x14 (by simp), r1 .x9 (by simp), t14, t9]
      ex_bvsimp []; rw [hAj, ult_ofNat _ _ (by omega) (by omega)]
      by_cases hc : A j < x
      · simp [hc, show ¬ x < A j by omega]
      · simp [hc, show x < A j by omega]
    have y8 : t2.getReg .x8 = BitVec.ofNat 64 i := by
      simp only [ht2, blk46.res, rv_simp, r1 .x8 (by simp), t8]
    have y9 : t2.getReg .x9 = BitVec.ofNat 64 x := by
      simp only [ht2, blk46.res, rv_simp, r1 .x9 (by simp), t9]
    have y14 : t2.getReg .x14 = BitVec.ofNat 64 (0x6E0 + 8 * (j + 1)) := by
      simp only [ht2, blk46.res, rv_simp, r1 .x14 (by simp), t14]
    have y13 : t2.getReg .x13 = BitVec.ofNat 64 (A j) := by
      simp only [ht2, blk46.res, rv_simp, r1 .x14 (by simp), t14]; ex_bvsimp []; rw [hAj]
    by_cases hc : A j < x
    · rw [if_pos hc] at p2
      exact (Run.done ⟨j + 1, p2, y8, y9, y14, hij, hi,
        ⟨A, hA.frame m2, hF, hs, hx, fun _ => Or.inr (by simpa using hc)⟩, by rw [m2]; exact tsent,
          fun a ha hW => by rw [m2]; exact tframe a ha hW⟩).mono (by omega) (fun _ h => h)
    · rw [if_neg hc] at p2
      have hobl3 : blk48.res.obligs t2 := by
        simp only [blk48.res, rv_simp, y14]; ex_bvsimp [accessValid_ofNat]; omega
      refine (Run.blk blk48 codeAt_48 p2 hobl3 (B := 7 * j + 4) ?_).mono
        (by rw [show blk48.res.cycles = 3 from rfl]; try omega) (fun _ h => h)
      set t3 := blk48.res.toState t2 with ht3
      have hm3 := mem_sd_a4 (r := blk48.res) (t := t2) (src := .x13) rfl y14 y13 (by omega)
      rw [← ht3] at hm3
      have hmt : ∀ a : Nat, a < 2 ^ 64 → t3.getMem (BitVec.ofNat 64 a) =
          if a = 0x6E0 + 8 * (j + 1) then BitVec.ofNat 64 (A j) else t.getMem (BitVec.ofNat 64 a) := by
        intro a ha; rw [hm3 a ha, m2]
      have hA' := arr_store hA (by omega) hmt
      refine ih t3 ⟨by simp only [ht3, blk48.res, rv_simp],
        by simp only [ht3, blk48.res, rv_simp, y8], by simp only [ht3, blk48.res, rv_simp, y9],
        by simp only [ht3, blk48.res, rv_simp, y14]; ex_bvsimp []; exact ofNat_congr (by omega), by omega, hi,
        ⟨_, hA', ⟨?_, fun p hp => by split <;> [exact hAlt; exact hF.lt p hp], hxlt⟩, ?_, ?_,
          fun h => by omega⟩, sent_store tsent (by omega) hmt, frame_store tframe (by omega) hmt⟩
      · -- the logical array after the shift is a swap of the old one
        have hsw := perm_swap_adj (fun p => if p = j + 1 then x else A p) 15 j (by omega)
        refine List.Perm.trans (List.Perm.of_eq ?_) (hsw.trans hF.perm)
        apply List.map_congr_left; intro p hp
        by_cases h1 : p = j
        · simp [h1]
        · by_cases h2 : p = j + 1
          · simp [h2]
          · simp [h1, h2]
      · intro p q hpq hq hp hq'
        by_cases h1 : q = j + 1
        · rw [if_neg (by omega), if_pos h1]
          exact hs p j (by omega) (by omega) (by omega) (by omega)
        · by_cases h2 : p = j + 1
          · rw [if_pos h2, if_neg h1]
            exact hs j q (by omega) hq (by omega) h1
          · rw [if_neg h2, if_neg h1]; exact hs p q hpq hq h2 h1
      · intro q hq hq'
        by_cases h1 : q = j + 1
        · rw [if_pos h1]; omega
        · rw [if_neg h1]; exact hx q (by omega) hq'



theorem sort_place (ans : BitVec 256) (s0 : MachineState) (i j x : Nat) (t : MachineState)
    (h : ShiftInv ans s0 51 i j x t) :
    Run t 4 (fun u => if i + 1 < 15 then SortInv ans s0 (i + 1) u else SortDone ans s0 u) := by
  obtain ⟨tpc, t8, t9, t14, hij, hi, ⟨A, hA, hF, hs, hx, hpl⟩, tsent, tframe⟩ := h
  have hobl : blk51.res.obligs t := by
    simp only [blk51.res, rv_simp, t14]; ex_bvsimp [accessValid_ofNat]; omega
  refine Run.of (symRun_sound blk51 codeAt_51 t tpc hobl) (le_refl _) ?_
  set u := blk51.res.toState t with hu
  have hm := mem_sd_a4 (r := blk51.res) (t := t) (src := .x9) rfl t14 t9 (by omega)
  rw [← hu] at hm
  have hA' := arr_store hA (by omega) hm
  have hpl' := hpl rfl
  -- the new array is sorted on [0, i]
  have hsort : ∀ p q, p < q → q ≤ i → (fun p => if p = j then x else A p) p < (fun p => if p = j then x else A p) q := by
    intro p q hpq hq
    simp only
    by_cases h1 : q = j
    · subst h1; rw [if_neg (by omega), if_pos rfl]
      rcases hpl' with h0 | h0
      · omega
      · by_cases h2 : p = q - 1
        · subst h2; exact h0
        · exact lt_trans (hs p (q - 1) (by omega) (by omega) (by omega) (by omega)) h0
    · by_cases h2 : p = j
      · subst h2; rw [if_pos rfl, if_neg h1]; exact hx q (by omega) hq
      · rw [if_neg h2, if_neg h1]; exact hs p q hpq hq h2 h1
  have hlt' : ∀ p < 15, (fun p => if p = j then x else A p) p < 2 ^ 22 := by
    intro p hp; simp only; split; exact hF.xlt; exact hF.lt p hp
  have upc : u.pc = if i + 1 < 15 then pcOf 41 else pcOf 55 := by
    simp only [hu, blk51.res, rv_simp, t8]; ex_bvsimp [ofNat_bne_ofNat]
    by_cases h : i + 1 < 15
    · simp [h]; omega
    · simp [h]; omega
  have hm' : ∀ a, u.getMem (BitVec.ofNat 64 a) = u.getMem (BitVec.ofNat 64 a) := fun _ => rfl
  by_cases hc : i + 1 < 15
  · rw [if_pos hc]; rw [if_pos hc] at upc
    refine ⟨upc, by simp only [hu, blk51.res, rv_simp, t8]; ex_bvsimp [], ⟨by omega, hc⟩,
      ⟨_, hA', ⟨?_, hlt', hlt' (i + 1) hc⟩, fun p q hpq hq => hsort p q hpq (by omega)⟩,
      sent_store tsent (by omega) hm, frame_store tframe (by omega) hm⟩
    refine List.Perm.trans (List.Perm.of_eq ?_) hF.perm
    apply List.map_congr_left; intro p hp; split <;> simp_all
  · rw [if_neg hc]; rw [if_neg hc] at upc
    refine ⟨upc, ⟨_, hA', ⟨?_, hlt', by norm_num⟩, fun p q hpq hq => hsort p q hpq (by omega)⟩,
      sent_store tsent (by omega) hm, frame_store tframe (by omega) hm⟩
    refine List.Perm.trans (List.Perm.of_eq ?_) hF.perm
    apply List.map_congr_left; intro p hp; rw [List.mem_range] at hp; simp [show p ≠ 15 by omega]

theorem sort_run (ans : BitVec 256) (s0 t : MachineState) (h : ExtDone ans s0 t) :
    Run t (1 + 14 * 109) (SortDone ans s0) := by
  refine Run.bind (sort_start ans s0 t h) (fun u hu => ?_)
  let Inv : Nat → MachineState → Prop := fun k u =>
    k ≤ 14 ∧ if k = 0 then SortDone ans s0 u else SortInv ans s0 (15 - k) u
  have body : ∀ k u, Inv (k + 1) u → Run u 109 (Inv k) := by
    intro k u ⟨hk, hu⟩
    simp only [if_neg (Nat.succ_ne_zero k)] at hu
    have hi := hu.hi
    refine (Run.bind (sort_head ans s0 _ u hu) (fun v ⟨x, hv⟩ =>
      Run.bind (shift_loop ans s0 _ x _ v hv) (fun w ⟨j', hw⟩ => sort_place ans s0 _ j' x w hw))).mono
      (by omega) (fun w hw => ⟨by omega, ?_⟩)
    by_cases hk0 : k = 0
    · subst hk0; simpa using hw
    · rw [if_neg hk0]; rw [if_pos (by omega)] at hw
      rwa [show 15 - (k + 1) + 1 = 15 - k by omega] at hw
  have := Run.loop Inv 109 body 14 u ⟨le_refl _, by simpa using hu⟩
  exact this.mono (le_refl _) (fun w hw => by simpa [Inv] using hw.2)


end SigGolfCandidate.Expand
