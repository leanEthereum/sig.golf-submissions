import SigGolfCandidate.SphincsSecurity.Proof.Fts.PorsMachine
import SigGolfCandidate.SphincsSecurity.Proof.Scheme.Schedule
/-!
# The structure of an accepted stack-machine run (E2)

Nothing here depends on a hash value: the control flow of the stack machine reads only heap indices, the
stack's sibling heap indices, the segments' fold counts and merge flags, and the leaf values.

* The leaf values of an accepted run increase strictly and stay below `2^14` (`recoverRun_order`), so the
  permutation never names the sentinel slot and the digest's leaves are pairwise distinct.
* **The stack is a chain.** At the start of every leaf of an accepted run, the stack's sibling heap
  indices are ancestors of the leaf's heap index, strictly higher from the top of the stack down
  (`Chain`). This propagates backwards from the end (empty stack), through folds, merges and pushes.
* Hence every leaf climbs exactly as high as the honest schedule's (`bitLength (v ^^^ v') - 1` heights,
  `14` for the last one), and counting heights, merges and segments gives `folds = octopusSize`
  (`recoverRun_folds`). With the fold bound this is admissibility (`ftsRecover_admissible`).
-/

namespace SphincsSecurity.Concrete

open OracleComp

namespace PorsMachine

/-! ### Heap arithmetic -/

theorem start_div_bounds (v x : Nat) (hv : v < 2 ^ ftsTreeHeight) (hx : x ≤ ftsTreeHeight) :
    2 ^ (ftsTreeHeight - x) ≤ (2 ^ ftsTreeHeight + v) / 2 ^ x
      ∧ (2 ^ ftsTreeHeight + v) / 2 ^ x < 2 ^ (ftsTreeHeight - x + 1) := by
  obtain ⟨hclimb, hlow⟩ := heap_climb v x hv hx
  rw [hclimb, pow_succ]
  generalize v / 2 ^ x = q at *
  omega

theorem start_div_large (v x : Nat) (hv : v < 2 ^ ftsTreeHeight) (hx : ftsTreeHeight < x) :
    (2 ^ ftsTreeHeight + v) / 2 ^ x = 0 := by
  apply Nat.div_eq_of_lt
  have hle : 2 ^ (ftsTreeHeight + 1) ≤ 2 ^ x := Nat.pow_le_pow_right (by omega) hx
  rw [pow_succ] at hle
  omega

theorem start_div_pos (v x : Nat) (hv : v < 2 ^ ftsTreeHeight) (hx : x ≤ ftsTreeHeight) :
    1 ≤ (2 ^ ftsTreeHeight + v) / 2 ^ x :=
  le_trans Nat.one_le_two_pow (start_div_bounds v x hv hx).1

/-- A leaf's heap index determines how many heights it climbed. -/
theorem start_div_inj (v x y : Nat) (hv : v < 2 ^ ftsTreeHeight) (hx : x ≤ ftsTreeHeight)
    (h : (2 ^ ftsTreeHeight + v) / 2 ^ x = (2 ^ ftsTreeHeight + v) / 2 ^ y) : x = y := by
  have hbx := start_div_bounds v x hv hx
  by_cases hy : y ≤ ftsTreeHeight
  · have hby := start_div_bounds v y hv hy
    rcases Nat.lt_trichotomy x y with hlt | heq | hgt
    · have : 2 ^ (ftsTreeHeight - y + 1) ≤ 2 ^ (ftsTreeHeight - x) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · exact heq
    · have : 2 ^ (ftsTreeHeight - x + 1) ≤ 2 ^ (ftsTreeHeight - y) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
  · have := start_div_large v y hv (by omega)
    have := Nat.one_le_two_pow (n := ftsTreeHeight - x)
    omega

theorem xor_one_div_two' (e : Nat) : (e ^^^ 1) / 2 = e / 2 := by
  rw [show (2 : Nat) = 2 ^ 1 from rfl, Nat.xor_div_two_pow]
  simp

theorem xor_one_ne (e : Nat) : e ^^^ 1 ≠ e := by
  rcases xor_one_cases e with ⟨_, h⟩ | ⟨_, h⟩ <;> omega

theorem eq_of_xor_eq_zero {a b : Nat} (h : a ^^^ b = 0) : a = b := by
  have : a ^^^ b ^^^ b = b := by rw [h, Nat.zero_xor]
  rwa [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this

theorem bitLength_eq_of (x k : Nat) (hlow : 2 ^ k ≤ x) (hhigh : x < 2 ^ (k + 1)) : bitLength x = k + 1 := by
  have hx : x ≠ 0 := by have := Nat.one_le_two_pow (n := k); omega
  unfold bitLength
  rw [if_neg hx, (Nat.log2_eq_iff hx).mpr ⟨hlow, hhigh⟩]

theorem bitLength_pos_of_ne (x : Nat) (hx : x ≠ 0) : 1 ≤ bitLength x := by
  unfold bitLength
  rw [if_neg hx]
  omega

/-- **The climb of a leaf that is not the last one.** If the node the leaf `v` reached after `k` heights is the
sibling of an ancestor of the next leaf `v'` (and not the root), then `k` is the height below the two leaves'
lowest common ancestor. -/
theorem climb_eq_of_sibling (v v' k b : Nat) (hv : v < 2 ^ ftsTreeHeight) (hv' : v' < 2 ^ ftsTreeHeight)
    (hsib : ((2 ^ ftsTreeHeight + v) / 2 ^ k) ^^^ 1 = (2 ^ ftsTreeHeight + v') / 2 ^ b)
    (htwo : 2 ≤ ((2 ^ ftsTreeHeight + v) / 2 ^ k) ^^^ 1) :
    k = bitLength (v ^^^ v') - 1 ∧ k < ftsTreeHeight := by
  -- the node and the next leaf's ancestor are siblings: same parent, different nodes
  have hk : k < ftsTreeHeight := by
    by_contra hk
    rcases Nat.eq_or_lt_of_le (not_lt.mp hk) with heq | hgt
    · subst heq
      have := start_div_bounds v ftsTreeHeight hv le_rfl
      simp only [Nat.sub_self, pow_zero, zero_add] at this
      have h1 : (2 ^ ftsTreeHeight + v) / 2 ^ ftsTreeHeight = 1 := by omega
      rw [h1] at htwo
      simp at htwo
    · rw [start_div_large v k hv hgt] at htwo
      simp at htwo
  have hparent : (2 ^ ftsTreeHeight + v) / 2 ^ (k + 1) = (2 ^ ftsTreeHeight + v') / 2 ^ b / 2 := by
    rw [← hsib, xor_one_div_two', div_pow_succ]
  have hne : (2 ^ ftsTreeHeight + v) / 2 ^ k ≠ (2 ^ ftsTreeHeight + v') / 2 ^ b := by
    rw [← hsib]
    exact (xor_one_ne _).symm
  -- the heights agree: the sibling lies on the same level
  have hbk : b = k := by
    have hbx := start_div_bounds v k hv hk.le
    have hlevel : 2 ^ (ftsTreeHeight - k) ≤ (2 ^ ftsTreeHeight + v') / 2 ^ b
        ∧ (2 ^ ftsTreeHeight + v') / 2 ^ b < 2 ^ (ftsTreeHeight - k + 1) := by
      rw [← hsib]
      rcases xor_one_cases ((2 ^ ftsTreeHeight + v) / 2 ^ k) with ⟨hmod, hxor⟩ | ⟨hmod, hxor⟩
      · rw [hxor]
        have heven : 2 ^ (ftsTreeHeight - k + 1) % 2 = 0 := by
          rw [pow_succ]; simp
        omega
      · rw [hxor]
        have heven : 2 ^ (ftsTreeHeight - k) % 2 = 0 := by
          rw [show ftsTreeHeight - k = (ftsTreeHeight - k - 1) + 1 by omega, pow_succ]; simp
        omega
    by_cases hb : b ≤ ftsTreeHeight
    · have hby := start_div_bounds v' b hv' hb
      rcases Nat.lt_trichotomy b k with hlt | heq | hgt
      · have : 2 ^ (ftsTreeHeight - k + 1) ≤ 2 ^ (ftsTreeHeight - b) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega
      · exact heq
      · have : 2 ^ (ftsTreeHeight - b + 1) ≤ 2 ^ (ftsTreeHeight - k) :=
          Nat.pow_le_pow_right (by omega) (by omega)
        omega
    · have := start_div_large v' b hv' (by omega)
      have := Nat.one_le_two_pow (n := ftsTreeHeight - k)
      omega
  subst hbk
  -- strip the level offset: `v / 2^(k+1) = v' / 2^(k+1)` and `v / 2^k ≠ v' / 2^k`
  obtain ⟨hc1, _⟩ := heap_climb v (b + 1) hv (by omega)
  obtain ⟨hc2, _⟩ := heap_climb v' (b + 1) hv' (by omega)
  obtain ⟨hc3, _⟩ := heap_climb v b hv (by omega)
  obtain ⟨hc4, _⟩ := heap_climb v' b hv' (by omega)
  rw [← div_pow_succ, hc1, hc2] at hparent
  rw [hc3, hc4] at hne
  have hsame : v / 2 ^ (b + 1) = v' / 2 ^ (b + 1) := by omega
  have hdiff : v / 2 ^ b ≠ v' / 2 ^ b := by omega
  refine ⟨?_, hk⟩
  have hhigh : (v ^^^ v') / 2 ^ (b + 1) = 0 := by
    rw [Nat.xor_div_two_pow, hsame, Nat.xor_self]
  have hlow : (v ^^^ v') / 2 ^ b ≠ 0 := by
    rw [Nat.xor_div_two_pow]
    intro h
    exact hdiff (eq_of_xor_eq_zero h)
  have hlt : v ^^^ v' < 2 ^ (b + 1) := by
    by_contra hge
    have := Nat.div_pos (not_lt.mp hge) (Nat.two_pow_pos (b + 1))
    omega
  have hge : 2 ^ b ≤ v ^^^ v' := by
    by_contra hlt'
    exact hlow (Nat.div_eq_of_lt (not_le.mp hlt'))
  rw [bitLength_eq_of _ b hge hlt]
  omega

/-- Two heap indices on the climbs of leaves `v` and `w` that are siblings (and not the root's children's
parent): they lie on the same level. -/
theorem sibling_level_eq (v w k b : Nat) (hv : v < 2 ^ ftsTreeHeight) (hw : w < 2 ^ ftsTreeHeight)
    (hsib : ((2 ^ ftsTreeHeight + v) / 2 ^ k) ^^^ 1 = (2 ^ ftsTreeHeight + w) / 2 ^ b)
    (htwo : 2 ≤ ((2 ^ ftsTreeHeight + v) / 2 ^ k) ^^^ 1) : b = k ∧ k < ftsTreeHeight := by
  have hk : k < ftsTreeHeight := by
    by_contra hk
    rcases Nat.eq_or_lt_of_le (not_lt.mp hk) with heq | hgt
    · subst heq
      have := start_div_bounds v ftsTreeHeight hv le_rfl
      simp only [Nat.sub_self, pow_zero, zero_add] at this
      have h1 : (2 ^ ftsTreeHeight + v) / 2 ^ ftsTreeHeight = 1 := by omega
      rw [h1] at htwo
      simp at htwo
    · rw [start_div_large v k hv hgt] at htwo
      simp at htwo
  refine ⟨?_, hk⟩
  have hbx := start_div_bounds v k hv hk.le
  have hlevel : 2 ^ (ftsTreeHeight - k) ≤ (2 ^ ftsTreeHeight + w) / 2 ^ b
      ∧ (2 ^ ftsTreeHeight + w) / 2 ^ b < 2 ^ (ftsTreeHeight - k + 1) := by
    rw [← hsib]
    rcases xor_one_cases ((2 ^ ftsTreeHeight + v) / 2 ^ k) with ⟨hmod, hxor⟩ | ⟨hmod, hxor⟩
    · rw [hxor]
      have heven : 2 ^ (ftsTreeHeight - k + 1) % 2 = 0 := by
        rw [pow_succ]; simp
      omega
    · rw [hxor]
      have heven : 2 ^ (ftsTreeHeight - k) % 2 = 0 := by
        rw [show ftsTreeHeight - k = (ftsTreeHeight - k - 1) + 1 by omega, pow_succ]; simp
      omega
  by_cases hb : b ≤ ftsTreeHeight
  · have hby := start_div_bounds w b hw hb
    rcases Nat.lt_trichotomy b k with hlt | heq | hgt
    · have : 2 ^ (ftsTreeHeight - k + 1) ≤ 2 ^ (ftsTreeHeight - b) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
    · exact heq
    · have : 2 ^ (ftsTreeHeight - b + 1) ≤ 2 ^ (ftsTreeHeight - k) :=
        Nat.pow_le_pow_right (by omega) (by omega)
      omega
  · have := start_div_large w b hw (by omega)
    have := Nat.one_le_two_pow (n := ftsTreeHeight - k)
    omega

/-- The stack's nodes lie on the climbs of leaves smaller than `v`. -/
def StackOrigins (stack : List (Digest × Nat)) (v : Nat) : Prop :=
  ∀ entry ∈ stack, ∃ w b, w < v ∧ w < 2 ^ ftsTreeHeight ∧ entry.2 ^^^ 1 = (2 ^ ftsTreeHeight + w) / 2 ^ b

/-- **A merge's current node is a right child.** The node on the stack waits for the current heap index `E`
and lies on the climb of a smaller leaf, so it is `E`'s left sibling. -/
theorem merge_heap_odd (v w k b : Nat) (hv : v < 2 ^ ftsTreeHeight) (hw : w < 2 ^ ftsTreeHeight) (hwv : w < v)
    (hentry : ((2 ^ ftsTreeHeight + v) / 2 ^ k) ^^^ 1 = (2 ^ ftsTreeHeight + w) / 2 ^ b)
    (htwo : 2 ≤ (2 ^ ftsTreeHeight + v) / 2 ^ k) : (2 ^ ftsTreeHeight + v) / 2 ^ k % 2 = 1 := by
  have htwo' : 2 ≤ ((2 ^ ftsTreeHeight + v) / 2 ^ k) ^^^ 1 := by
    rcases xor_one_cases ((2 ^ ftsTreeHeight + v) / 2 ^ k) with ⟨hmod, hxor⟩ | ⟨hmod, hxor⟩ <;> omega
  obtain ⟨hbk, _⟩ := sibling_level_eq v w k b hv hw hentry htwo'
  subst hbk
  have hle : (2 ^ ftsTreeHeight + w) / 2 ^ b ≤ (2 ^ ftsTreeHeight + v) / 2 ^ b :=
    Nat.div_le_div_right (by omega)
  rw [← hentry] at hle
  rcases xor_one_cases ((2 ^ ftsTreeHeight + v) / 2 ^ b) with ⟨hmod, hxor⟩ | ⟨hmod, hxor⟩ <;> omega

/-! ### Chains of waiting siblings -/

/-- The stack's sibling heap indices (top first) wait for ancestors of `heap`, strictly higher going down, and
none of them is the root or above. -/
def Chain : List Nat → Nat → Prop
  | [], _ => True
  | q :: rest, heap => (∃ a, q = heap / 2 ^ a) ∧ 2 ≤ q ∧ Chain rest (q / 2)

theorem chain_div_pow {stack : List Nat} {heap : Nat} (k : Nat) (h : Chain stack (heap / 2 ^ k)) :
    Chain stack heap := by
  cases stack with
  | nil => trivial
  | cons q rest =>
      obtain ⟨⟨a, hq⟩, htwo, hrest⟩ := h
      refine ⟨⟨k + a, ?_⟩, htwo, hrest⟩
      rw [hq, Nat.div_div_eq_div_mul, ← pow_add]

theorem chain_half {stack : List Nat} {heap : Nat} (h : Chain stack (heap / 2)) : Chain stack heap :=
  chain_div_pow 1 (by simpa using h)

theorem chain_merge {rest : List Nat} {heap : Nat} (htwo : 2 ≤ heap) (h : Chain rest (heap / 2)) :
    Chain (heap :: rest) heap :=
  ⟨⟨0, by simp⟩, htwo, h⟩

/-- A chain at `heap / 2^k` (`k > 0`) does not wait for `heap` itself. -/
theorem chain_top_ne {q : Nat} {rest : List Nat} {heap : Nat} (k : Nat) (hk : 0 < k) (hheap : 1 ≤ heap)
    (h : Chain (q :: rest) (heap / 2 ^ k)) : q ≠ heap := by
  obtain ⟨⟨a, hq⟩, _, _⟩ := h
  rw [hq, Nat.div_div_eq_div_mul, ← pow_add]
  apply Nat.ne_of_lt
  apply Nat.div_lt_self (by omega)
  exact Nat.one_lt_two_pow (by omega)

/-! ### What one leaf's segments do to the machine's shape -/

variable (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)

@[simp] theorem foldRun_heap (segment : Segment) (remaining position : Nat) (r : Run) :
    (foldRun f parameter index segment remaining position r).heap = r.heap / 2 ^ remaining := by
  induction remaining generalizing position r with
  | zero => simp [foldRun]
  | succ remaining ih =>
      rw [foldRun, ih]
      show r.heap / 2 / 2 ^ remaining = _
      rw [Nat.div_div_eq_div_mul, ← pow_succ']

/-- One leaf's segments: the entries it popped, one segment per pop plus the last, and the heights it
climbed (a fold or a merge each). -/
theorem segmentsRun_shape (segments : Fin ftsSegments → Segment) (fuel : Nat) (pending : PendingHash)
    (r r' : Run) (hrun : segmentsRun f parameter index segments fuel pending r = some r') :
    ∃ popped : List (Digest × Nat), r.stack = popped ++ r'.stack ∧
      r'.segment = r.segment + popped.length + 1 ∧ r.folds ≤ r'.folds ∧
      r'.heap = r.heap / 2 ^ (r'.folds - r.folds + popped.length) ∧ r'.segment ≤ ftsSegments := by
  induction fuel generalizing pending r with
  | zero => simp [segmentsRun] at hrun
  | succ fuel ih =>
      rw [segmentsRun] at hrun
      by_cases hsegment : r.segment < ftsSegments
      · rw [dif_pos hsegment] at hrun
        dsimp only at hrun
        by_cases hfolds : SegmentRejects (segments ⟨r.segment, hsegment⟩) r.heap
        · rw [if_pos hfolds] at hrun
          simp at hrun
        · rw [if_neg hfolds] at hrun
          set a := (segments ⟨r.segment, hsegment⟩).folds.val with ha
          set folded := foldRun f parameter index (segments ⟨r.segment, hsegment⟩) a 0
            { r.hash f (pendingInput parameter index pending r.node) with
              openings := r.openings ++ pendingOpenings pending } with hfoldedDef
          have hfheap : folded.heap = r.heap / 2 ^ a := foldRun_heap f parameter index _ _ _ _
          have hfstack : folded.stack = r.stack := foldRun_stack f parameter index _ _ _ _
          by_cases hmerge : (segments ⟨r.segment, hsegment⟩).merge = true
          · rw [if_pos hmerge] at hrun
            rcases hstack : folded.stack with _ | ⟨⟨left, sibling⟩, rest⟩
            · rw [hstack] at hrun
              simp at hrun
            · rw [hstack] at hrun
              dsimp only at hrun
              by_cases hsibling : sibling = folded.heap
              · rw [if_pos hsibling] at hrun
                obtain ⟨popped, hpop, hseg, hfolds', hheap', hlimit⟩ := ih _ _ hrun
                refine ⟨(left, sibling) :: popped, ?_, ?_, ?_, ?_, hlimit⟩
                · rw [← hfstack, hstack]
                  simp only at hpop
                  rw [hpop]
                  rfl
                · rw [hseg]
                  simp only [List.length_cons]
                  omega
                · simp only at hfolds'
                  omega
                · rw [hheap']
                  simp only [List.length_cons]
                  show folded.heap / 2 / 2 ^ (r'.folds - (r.folds + a) + popped.length) = _
                  rw [hfheap, Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, ← pow_succ', ← pow_add]
                  congr 2
                  simp only at hfolds'
                  omega
              · rw [if_neg hsibling] at hrun
                simp at hrun
          · rw [if_neg hmerge] at hrun
            cases hrun
            refine ⟨[], by simpa using hfstack.symm, rfl, by simp, ?_, by simp only; omega⟩
            simp only [List.length_nil, Nat.add_zero]
            rw [hfheap]
            congr 2
            omega
      · rw [dif_neg hsegment] at hrun
        simp at hrun

/-- Backwards through one leaf: if the stack is a chain at the leaf's last node's parent, it was a chain at
the leaf's start. -/
theorem segmentsRun_chain (segments : Fin ftsSegments → Segment) (fuel : Nat) (pending : PendingHash)
    (r r' : Run) (hrun : segmentsRun f parameter index segments fuel pending r = some r')
    (hend : Chain (r'.stack.map Prod.snd) (r'.heap / 2)) (hpos : 1 ≤ r'.heap) :
    Chain (r.stack.map Prod.snd) r.heap := by
  induction fuel generalizing pending r with
  | zero => simp [segmentsRun] at hrun
  | succ fuel ih =>
      rw [segmentsRun] at hrun
      by_cases hsegment : r.segment < ftsSegments
      · rw [dif_pos hsegment] at hrun
        dsimp only at hrun
        by_cases hfolds : SegmentRejects (segments ⟨r.segment, hsegment⟩) r.heap
        · rw [if_pos hfolds] at hrun
          simp at hrun
        · rw [if_neg hfolds] at hrun
          set a := (segments ⟨r.segment, hsegment⟩).folds.val with ha
          set folded := foldRun f parameter index (segments ⟨r.segment, hsegment⟩) a 0
            { r.hash f (pendingInput parameter index pending r.node) with
              openings := r.openings ++ pendingOpenings pending } with hfoldedDef
          have hfheap : folded.heap = r.heap / 2 ^ a := foldRun_heap f parameter index _ _ _ _
          have hfstack : folded.stack = r.stack := foldRun_stack f parameter index _ _ _ _
          by_cases hmerge : (segments ⟨r.segment, hsegment⟩).merge = true
          · rw [if_pos hmerge] at hrun
            rcases hstack : folded.stack with _ | ⟨⟨left, sibling⟩, rest⟩
            · rw [hstack] at hrun
              simp at hrun
            · rw [hstack] at hrun
              dsimp only at hrun
              by_cases hsibling : sibling = folded.heap
              · rw [if_pos hsibling] at hrun
                have hrest := ih _ _ hrun
                obtain ⟨popped, _, _, _, hheap', _⟩ := segmentsRun_shape f parameter index segments fuel _ _ _ hrun
                simp only at hrest hheap'
                have hhalf : 1 ≤ folded.heap / 2 := by
                  have := Nat.div_le_self (folded.heap / 2) (2 ^ (r'.folds - (r.folds + a) + popped.length))
                  omega
                rw [← hfstack, hstack]
                apply chain_div_pow a
                rw [← hfheap]
                simp only [List.map_cons]
                rw [hsibling]
                exact chain_merge (by omega) hrest
              · rw [if_neg hsibling] at hrun
                simp at hrun
          · rw [if_neg hmerge] at hrun
            cases hrun
            simp only at hend
            rw [← hfstack]
            apply chain_div_pow (a + 1)
            rw [pow_succ, ← Nat.div_div_eq_div_mul, ← hfheap]
            exact hend
      · rw [dif_neg hsegment] at hrun
        simp at hrun

/-! ### Leaf values -/

/-- The value of the `s`-th leaf, and `0` past the last. -/
def leafValue (values : SlotCode → Nat) (fts : FtsSignature) (s : Nat) : Nat :=
  if hs : s < ftsOpenings then values (fts.perm ⟨s, hs⟩) else 0

theorem leafValue_of_lt (values : SlotCode → Nat) (fts : FtsSignature) (s : Nat) (hs : s < ftsOpenings) :
    leafValue values fts s = values (fts.perm ⟨s, hs⟩) := by
  rw [leafValue, dif_pos hs]

theorem leavesRun_order (values : SlotCode → Nat) (fts : FtsSignature) :
    ∀ (remaining position previous : Nat) (r r' : Run),
      leavesRun f parameter index values fts remaining position previous r = some r' →
      remaining + position = ftsOpenings →
      (position < ftsOpenings → 0 < position → previous < leafValue values fts position) ∧
      (∀ s, position ≤ s → s + 1 < ftsOpenings → leafValue values fts s < leafValue values fts (s + 1)) ∧
      (position < ftsOpenings → leafValue values fts (ftsOpenings - 1) < 2 ^ ftsTreeHeight) := by
  intro remaining
  induction remaining with
  | zero =>
      intro position previous r r' _ hsum
      refine ⟨fun h => by omega, fun s hs hs' => by omega, fun h => by omega⟩
  | succ remaining ih =>
      intro position previous r r' hrun hsum
      have hposition : position < ftsOpenings := by omega
      rw [leavesRun, dif_pos hposition] at hrun
      dsimp only at hrun
      by_cases horder : 0 < position ∧ ¬ previous < values (fts.perm ⟨position, hposition⟩)
      · rw [if_pos horder] at hrun
        simp at hrun
      · rw [if_neg horder] at hrun
        by_cases hlast : position + 1 = ftsOpenings ∧
            ¬ values (fts.perm ⟨position, hposition⟩) < 2 ^ ftsTreeHeight
        · rw [if_pos hlast] at hrun
          simp at hrun
        · rw [if_neg hlast] at hrun
          rcases hsegments : segmentsRun f parameter index fts.segments ftsSegments _ _ with _ | r1
          · rw [hsegments] at hrun
            simp at hrun
          · rw [hsegments] at hrun
            dsimp only at hrun
            obtain ⟨ha, hb, hc⟩ := ih _ _ _ _ hrun (by omega)
            refine ⟨fun _ hpos => ?_, fun s hs hs' => ?_, fun _ => ?_⟩
            · rw [leafValue_of_lt _ _ _ hposition]
              exact not_not.mp (fun h => horder ⟨hpos, h⟩)
            · rcases Nat.eq_or_lt_of_le hs with heq | hlt
              · subst heq
                have := ha hs' (by omega)
                rwa [← leafValue_of_lt values fts _ hposition] at this
              · exact hb s hlt hs'
            · by_cases hend : position + 1 = ftsOpenings
              · have hp : position = ftsOpenings - 1 := by omega
                subst hp
                rw [leafValue_of_lt _ _ _ hposition]
                exact not_not.mp (fun h => hlast ⟨hend, h⟩)
              · exact hc (by omega)

/-- **The leaf values of an accepted run** increase strictly and stay below `2^14`. -/
theorem recoverRun_order (values : SlotCode → Nat) (fts : FtsSignature) (r : Run)
    (hrun : recoverRun f parameter index values fts = some r) :
    (∀ s, s + 1 < ftsOpenings → leafValue values fts s < leafValue values fts (s + 1)) ∧
      ∀ s, s < ftsOpenings → leafValue values fts s < 2 ^ ftsTreeHeight := by
  rw [recoverRun] at hrun
  rcases hleaves : leavesRun f parameter index values fts ftsOpenings 0 0 Run.initial with _ | r'
  · rw [hleaves] at hrun
    simp at hrun
  · obtain ⟨_, hb, hc⟩ := leavesRun_order f parameter index values fts _ _ _ _ _ hleaves rfl
    have hmono : ∀ s, s + 1 < ftsOpenings → leafValue values fts s < leafValue values fts (s + 1) :=
      fun s hs => hb s (Nat.zero_le _) hs
    refine ⟨hmono, fun s hs => ?_⟩
    have hlast := hc (by decide)
    have hle : ∀ t, s + t < ftsOpenings → leafValue values fts s ≤ leafValue values fts (s + t) := by
      intro t
      induction t with
      | zero => intro _; exact le_rfl
      | succ t iht =>
          intro ht
          exact (iht (by omega)).trans (hmono (s + t) (by omega)).le
    have := hle (ftsOpenings - 1 - s) (by omega)
    rw [show s + (ftsOpenings - 1 - s) = ftsOpenings - 1 by omega] at this
    omega

/-! ### The stack is a chain at every leaf start -/

theorem two_pow_or_eq (v : Nat) (hv : v < 2 ^ ftsTreeHeight) :
    2 ^ ftsTreeHeight ||| v = 2 ^ ftsTreeHeight + v :=
  two_pow_or_eq_add v hv

/-- The leaf-start state of leaf `position`. -/
abbrev leafStart (values : SlotCode → Nat) (fts : FtsSignature) (position : Nat) (hposition : position < ftsOpenings)
    (r : Run) : Run :=
  { r with heap := 2 ^ ftsTreeHeight ||| values (fts.perm ⟨position, hposition⟩) }

/-- The leaf's segments: the machine's recursion for leaf `position` from the boundary state `r`. -/
abbrev leafRun (values : SlotCode → Nat) (fts : FtsSignature) (position : Nat) (hposition : position < ftsOpenings)
    (r : Run) : Option Run :=
  segmentsRun f parameter index fts.segments ftsSegments
    (.leaf (values (fts.perm ⟨position, hposition⟩)) (fts.secrets ⟨position, hposition⟩))
    (leafStart values fts position hposition r)

/-- The push after a leaf that is not the last one. -/
abbrev pushed (r : Run) : Run := { r with stack := (r.node, r.heap ^^^ 1) :: r.stack }

/-- One step of `leavesRun`, unfolded: the leaf's segments, the push, the rest. -/
theorem leavesRun_succ_eq (values : SlotCode → Nat) (fts : FtsSignature) (remaining position previous : Nat)
    (r r' : Run) (hposition : position < ftsOpenings)
    (hrun : leavesRun f parameter index values fts (remaining + 1) position previous r = some r') :
    ∃ r1, leafRun f parameter index values fts position hposition r = some r1 ∧
      leavesRun f parameter index values fts remaining (position + 1) (values (fts.perm ⟨position, hposition⟩))
        (if position + 1 < ftsOpenings then pushed r1 else r1) = some r' := by
  rw [leavesRun, dif_pos hposition] at hrun
  dsimp only at hrun
  by_cases horder : 0 < position ∧ ¬ previous < values (fts.perm ⟨position, hposition⟩)
  · rw [if_pos horder] at hrun
    simp at hrun
  · rw [if_neg horder] at hrun
    by_cases hlast : position + 1 = ftsOpenings ∧
        ¬ values (fts.perm ⟨position, hposition⟩) < 2 ^ ftsTreeHeight
    · rw [if_pos hlast] at hrun
      simp at hrun
    · rw [if_neg hlast] at hrun
      rcases hsegments : segmentsRun f parameter index fts.segments ftsSegments _ _ with _ | r1
      · rw [hsegments] at hrun
        simp at hrun
      · rw [hsegments] at hrun
        exact ⟨r1, hsegments, hrun⟩

theorem leavesRun_zero_eq (values : SlotCode → Nat) (fts : FtsSignature) (position previous : Nat) (r r' : Run)
    (hrun : leavesRun f parameter index values fts 0 position previous r = some r') : r' = r := by
  rw [leavesRun] at hrun
  exact (Option.some.inj hrun).symm

/-- **The chain at every leaf start of an accepted run.** -/
theorem leavesRun_chain (values : SlotCode → Nat) (fts : FtsSignature)
    (hvalues : ∀ s (hs : s < ftsOpenings), values (fts.perm ⟨s, hs⟩) < 2 ^ ftsTreeHeight) :
    ∀ (remaining position previous : Nat) (r r' : Run),
      leavesRun f parameter index values fts remaining position previous r = some r' →
      remaining + position = ftsOpenings → 0 < remaining → r'.heap = 1 → r'.stack = [] →
      ∀ hposition : position < ftsOpenings,
        Chain (r.stack.map Prod.snd) (2 ^ ftsTreeHeight + values (fts.perm ⟨position, hposition⟩)) := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _ _ _ h; omega
  | succ remaining ih =>
      intro position previous r r' hrun hsum _ hheap hstack hposition
      obtain ⟨r1, hleaf, hrest⟩ := leavesRun_succ_eq f parameter index values fts _ _ _ _ _ hposition hrun
      have hstart := two_pow_or_eq _ (hvalues position hposition)
      suffices hend : Chain (r1.stack.map Prod.snd) (r1.heap / 2) ∧ 1 ≤ r1.heap by
        have := segmentsRun_chain f parameter index _ _ _ _ _ hleaf hend.1 hend.2
        simpa [leafStart, hstart] using this
      by_cases hpush : position + 1 < ftsOpenings
      · rw [if_pos hpush] at hrest
        have hchain := ih (position + 1) _ _ _ hrest (by omega) (by omega) hheap hstack hpush
        obtain ⟨_, htwo, hrest'⟩ := hchain
        simp only at htwo hrest'
        rw [xor_one_div_two'] at hrest'
        refine ⟨hrest', ?_⟩
        rcases xor_one_cases r1.heap with ⟨_, hx⟩ | ⟨_, hx⟩ <;> omega
      · rw [if_neg hpush] at hrest
        have hzero : remaining = 0 := by omega
        subst hzero
        have := leavesRun_zero_eq f parameter index values fts _ _ _ _ hrest
        subst this
        rw [hstack, hheap]
        exact ⟨trivial, le_rfl⟩

/-! ### Every leaf climbs as high as the honest schedule's -/

/-- **The counts of an accepted run**: folds plus segments add up to the leaves' climbs, and one segment per
leaf and per push. -/
theorem leavesRun_count (values : SlotCode → Nat) (fts : FtsSignature)
    (hvalues : ∀ s (hs : s < ftsOpenings), values (fts.perm ⟨s, hs⟩) < 2 ^ ftsTreeHeight) :
    ∀ (remaining position previous : Nat) (r r' : Run),
      leavesRun f parameter index values fts remaining position previous r = some r' →
      remaining + position = ftsOpenings → 0 < remaining → r'.heap = 1 → r'.stack = [] →
      r'.folds + r'.segment = r.folds + r.segment
          + (∑ s ∈ Finset.Ico position (ftsOpenings - 1),
              bitLength (leafValue values fts s ^^^ leafValue values fts (s + 1))) + (ftsTreeHeight + 1)
        ∧ r'.segment + r'.stack.length + 1 = r.segment + r.stack.length + 2 * remaining := by
  intro remaining
  induction remaining with
  | zero => intro _ _ _ _ _ _ h; omega
  | succ remaining ih =>
      intro position previous r r' hrun hsum _ hheap hstack
      have hposition : position < ftsOpenings := by omega
      obtain ⟨r1, hleaf, hrest⟩ := leavesRun_succ_eq f parameter index values fts _ _ _ _ _ hposition hrun
      obtain ⟨popped, hpop, hseg, hfolds, hclimb, _⟩ :=
        segmentsRun_shape f parameter index _ _ _ _ _ hleaf
      have hv := hvalues position hposition
      simp only [two_pow_or_eq _ hv] at hpop hseg hfolds hclimb
      have hlen := congrArg List.length hpop
      rw [List.length_append] at hlen
      by_cases hpush : position + 1 < ftsOpenings
      · rw [if_pos hpush] at hrest
        obtain ⟨hih1, hih2⟩ := ih (position + 1) _ _ _ hrest (by omega) (by omega) hheap hstack
        -- the climb: the leaf's last node is the sibling of an ancestor of the next leaf
        have hchain := leavesRun_chain f parameter index values fts hvalues remaining (position + 1) _ _ _ hrest
          (by omega) (by omega) hheap hstack hpush
        obtain ⟨⟨b, hb⟩, htwo, _⟩ := hchain
        simp only at hb htwo
        rw [hclimb] at hb htwo
        obtain ⟨hk, _⟩ := climb_eq_of_sibling _ _ _ _ hv (hvalues _ hpush) hb htwo
        have hne : leafValue values fts position ^^^ leafValue values fts (position + 1) ≠ 0 := by
          intro h
          have := eq_of_xor_eq_zero h
          obtain ⟨hmono, _⟩ := leavesRun_order f parameter index values fts _ _ _ _ _ hrun (by omega)
          have := (leavesRun_order f parameter index values fts _ _ _ _ _ hrun (by omega)).2.1 position
            le_rfl hpush
          omega
        have hbit := bitLength_pos_of_ne _ hne
        rw [leafValue_of_lt values fts _ hposition, leafValue_of_lt values fts _ hpush] at hbit
        rw [Finset.sum_eq_sum_Ico_succ_bot (by omega)]
        rw [leafValue_of_lt values fts _ hposition, leafValue_of_lt values fts _ hpush]
        simp only [List.length_cons] at hih1 hih2
        constructor <;> omega
      · rw [if_neg hpush] at hrest
        have hzero : remaining = 0 := by omega
        subst hzero
        have := leavesRun_zero_eq f parameter index values fts _ _ _ _ hrest
        subst this
        have hlastpos : position = ftsOpenings - 1 := by omega
        rw [hheap] at hclimb
        -- the last leaf climbs to the root: `14` heights
        have hroot : (2 ^ ftsTreeHeight + values (fts.perm ⟨position, hposition⟩)) / 2 ^ ftsTreeHeight = 1 := by
          have := start_div_bounds _ ftsTreeHeight hv le_rfl
          simp only [Nat.sub_self, pow_zero, zero_add] at this
          omega
        have hk := start_div_inj _ ftsTreeHeight _ hv le_rfl (hroot.trans hclimb)
        rw [hlastpos, Finset.Ico_self, Finset.sum_empty]
        rw [hstack] at hlen ⊢
        simp only [List.length_nil] at hlen ⊢
        constructor <;> omega

/-! ### Admissibility (E2) -/

theorem sum_zipWith_tail (g : Nat → Nat → Nat) : ∀ l : List Nat,
    (List.zipWith g l l.tail).sum = ∑ i ∈ Finset.range (l.length - 1), g (l.getD i 0) (l.getD (i + 1) 0)
  | [] => by simp
  | [_] => by simp
  | a :: b :: rest => by
      have ih := sum_zipWith_tail g (b :: rest)
      simp only [List.tail_cons, List.zipWith_cons_cons, List.sum_cons, List.length_cons] at ih ⊢
      rw [ih, show rest.length + 1 + 1 - 1 = rest.length + 1 by omega, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_sub_cancel]
      omega

/-- The octopus of a list of `k` values, as a sum over consecutive pairs. -/
theorem octopusSize_ofFn (v : Fin ftsOpenings → Nat) (value : Nat → Nat)
    (hvalue : ∀ i (hi : i < ftsOpenings), value i = v ⟨i, hi⟩) :
    octopusSize (List.ofFn v)
      = ftsTreeHeight + 2 + (∑ i ∈ Finset.range (ftsOpenings - 1), bitLength (value i ^^^ value (i + 1)))
          - 2 * ftsOpenings := by
  have hsum := sum_zipWith_tail (fun a b => bitLength (a ^^^ b)) (List.ofFn v)
  have hget : ∀ i, i < ftsOpenings → (List.ofFn v).getD i 0 = value i := by
    intro i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp [hi, hvalue i hi]
  have hsum' : ∑ i ∈ Finset.range ((List.ofFn v).length - 1),
        bitLength ((List.ofFn v).getD i 0 ^^^ (List.ofFn v).getD (i + 1) 0)
      = ∑ i ∈ Finset.range (ftsOpenings - 1), bitLength (value i ^^^ value (i + 1)) := by
    rw [List.length_ofFn]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [hget i (by omega), hget (i + 1) (by omega)]
  rw [octopusSize, hsum, hsum', List.length_ofFn]

/-- Slots whose leaves increase strictly are the sorted slots. -/
theorem sortedSlots_eq (leaves : IndexGroup → FtsLeaf) (slot : Fin ftsOpenings → IndexGroup)
    (hslot : ∀ s t : Fin ftsOpenings, s < t → (leaves (slot s)).val < (leaves (slot t)).val) :
    sortedSlots leaves = List.ofFn slot := by
  have hinj : Function.Injective slot := by
    intro s t h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hslot s t hlt; rw [h] at this; omega
    · have := hslot t s hgt; rw [h] at this; omega
  have hsurj : Function.Surjective slot := Finite.injective_iff_surjective.mp hinj
  let le : IndexGroup → IndexGroup → Prop := fun r r' => (leaves r).val ≤ (leaves r').val
  have : Std.Total le := ⟨fun a b => le_total (leaves a).val (leaves b).val⟩
  have : IsTrans IndexGroup le := ⟨fun a b c hab hbc => le_trans hab hbc⟩
  apply List.Perm.eq_of_pairwise (le := le)
  · intro a b _ _ hab hba
    obtain ⟨s, rfl⟩ := hsurj a
    obtain ⟨t, rfl⟩ := hsurj b
    rcases lt_trichotomy s t with hlt | heq | hgt
    · have := hslot s t hlt; simp only [le] at hba; omega
    · rw [heq]
    · have := hslot t s hgt; simp only [le] at hab; omega
  · exact List.pairwise_insertionSort le _
  · rw [List.pairwise_ofFn]
    intro s t hst
    exact (hslot s t hst).le
  · refine (List.perm_insertionSort le _).trans ?_
    rw [List.perm_ext_iff_of_nodup (List.nodup_finRange _) (List.nodup_ofFn.mpr hinj)]
    intro a
    simp only [List.mem_finRange, true_iff, List.mem_ofFn]
    exact hsurj a

/-- **The structure of an accepted run (E2).** The permutation names the slots `slot s` (never the
sentinel), in the order of their leaves, so the slots are the sorted slots and the leaves are pairwise
distinct; the run used all `29` segments; its folds are exactly the octopus of the sorted leaves; and the
leaves are admissible. -/
theorem recoverRun_structure (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (r : Run)
    (hrun : recoverRun f parameter index (slotValue leaves) fts = some r) :
    ∃ slot : Fin ftsOpenings → IndexGroup,
      (∀ s, fts.perm s = (slot s).castSucc) ∧ sortedSlots leaves = List.ofFn slot ∧
      r.segment = ftsSegments ∧ r.folds = octopusSize (sortedLeaves leaves) ∧ AdmissibleLeaves leaves ∧
      Function.Bijective slot := by
  obtain ⟨hmono, hlt⟩ := recoverRun_order f parameter index (slotValue leaves) fts r hrun
  have hvalues : ∀ s (hs : s < ftsOpenings), slotValue leaves (fts.perm ⟨s, hs⟩) < 2 ^ ftsTreeHeight := by
    intro s hs
    have := hlt s hs
    rwa [leafValue_of_lt _ _ _ hs] at this
  -- the permutation never names the sentinel
  have hcode : ∀ s : Fin ftsOpenings, (fts.perm s).val < ftsOpenings := by
    intro s
    by_contra hge
    have := hvalues s.val s.isLt
    simp only [Fin.eta, slotValue, dif_neg hge] at this
    omega
  let slot : Fin ftsOpenings → IndexGroup := fun s => ⟨(fts.perm s).val, hcode s⟩
  have hslotValue : ∀ s (hs : s < ftsOpenings), leafValue (slotValue leaves) fts s = (leaves (slot ⟨s, hs⟩)).val := by
    intro s hs
    rw [leafValue_of_lt _ _ _ hs, slotValue, dif_pos (hcode ⟨s, hs⟩)]
  have hstrict : ∀ s t : Fin ftsOpenings, s < t → (leaves (slot s)).val < (leaves (slot t)).val := by
    intro s t hst
    rw [← hslotValue s.val s.isLt, ← hslotValue t.val t.isLt]
    have hle : ∀ d, s.val + d + 1 < ftsOpenings →
        leafValue (slotValue leaves) fts s.val < leafValue (slotValue leaves) fts (s.val + d + 1) := by
      intro d
      induction d with
      | zero => intro h; exact hmono s.val h
      | succ d ih => intro h; exact (ih (by omega)).trans (hmono _ h)
    have := hle (t.val - s.val - 1) (by omega)
    rwa [show s.val + (t.val - s.val - 1) + 1 = t.val by omega] at this
  have hsorted := sortedSlots_eq leaves slot hstrict
  have hsortedLeaves : sortedLeaves leaves = List.ofFn fun s => (leaves (slot s)).val := by
    rw [sortedLeaves, hsorted, List.map_ofFn]
    rfl
  -- the counts
  rw [recoverRun] at hrun
  rcases hleaves : leavesRun f parameter index (slotValue leaves) fts ftsOpenings 0 0 Run.initial with _ | r'
  · rw [hleaves] at hrun
    simp at hrun
  · rw [hleaves] at hrun
    dsimp only at hrun
    split_ifs at hrun with haccept
    cases hrun
    obtain ⟨hfolds, hheap, hstack⟩ := haccept
    obtain ⟨hcount, hsegments⟩ := leavesRun_count f parameter index (slotValue leaves) fts hvalues
      ftsOpenings 0 0 Run.initial r hleaves rfl (by decide) hheap hstack
    rw [hstack] at hsegments
    simp only [Run.initial, RecoverState.initial, List.length_nil] at hcount hsegments
    have hsegment : r.segment = ftsSegments := by
      simp only [ftsSegments, ftsOpenings] at hsegments ⊢
      omega
    have hoct := octopusSize_ofFn (fun s => (leaves (slot s)).val) (leafValue (slotValue leaves) fts)
      (fun i hi => hslotValue i hi)
    have hpairs : ∀ i ∈ Finset.range (ftsOpenings - 1),
        1 ≤ bitLength (leafValue (slotValue leaves) fts i ^^^ leafValue (slotValue leaves) fts (i + 1)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      apply bitLength_pos_of_ne
      intro h
      have := hmono i (by omega)
      rw [eq_of_xor_eq_zero h] at this
      omega
    have hsumge := Finset.card_nsmul_le_sum _ _ 1 hpairs
    simp only [Finset.card_range, smul_eq_mul, mul_one] at hsumge
    rw [← Finset.range_eq_Ico] at hcount
    have hfoldsEq : r.folds = octopusSize (sortedLeaves leaves) := by
      rw [hsortedLeaves, hoct]
      simp only [ftsSegments, ftsOpenings, ftsTreeHeight] at hcount hsegment hsumge ⊢
      omega
    have hinj : Function.Injective slot := by
      intro s t h
      by_contra hne
      rcases lt_or_gt_of_ne hne with hst | hst
      · have := hstrict s t hst; rw [h] at this; omega
      · have := hstrict t s hst; rw [h] at this; omega
    have hsurj : Function.Surjective slot := Finite.injective_iff_surjective.mp hinj
    refine ⟨slot, fun s => rfl, hsorted, hsegment, hfoldsEq, ⟨?_, ?_⟩, hinj, hsurj⟩
    · intro a b hab
      obtain ⟨s, rfl⟩ := hsurj a
      obtain ⟨t, rfl⟩ := hsurj b
      rcases lt_trichotomy s t with hst | heq | hst
      · have := hstrict s t hst; rw [hab] at this; omega
      · rw [heq]
      · have := hstrict t s hst; rw [hab] at this; omega
    · rw [← hfoldsEq]
      exact hfolds

/-- **E2.** An accepting `ftsRecover` run on a digest's leaves makes them admissible. -/
theorem ftsRecover_admissible (f : QueryImpl HashSpec Id) (parameter : PublicParameter) (index : Index)
    (leaves : IndexGroup → FtsLeaf) (fts : FtsSignature) (key : Digest)
    (hrecover : evalWithAnswerFn f (ftsRecover parameter index (slotValue leaves) fts) = some key) :
    AdmissibleLeaves leaves := by
  rw [eval_ftsRecover] at hrecover
  rcases hrun : recoverRun f parameter index (slotValue leaves) fts with _ | r
  · rw [hrun] at hrecover
    simp at hrecover
  · obtain ⟨_, _, _, _, _, hadmissible, _⟩ := recoverRun_structure f parameter index leaves fts r hrun
    exact hadmissible

end PorsMachine

end SphincsSecurity.Concrete
