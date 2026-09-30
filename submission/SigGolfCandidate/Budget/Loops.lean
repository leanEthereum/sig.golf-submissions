import SigGolfCandidate.Budget.Bytes

/-!
# Budget: the deterministic parts of keygen and sign

`Spec` facts (query predicate, compressions, results) for the reference functions: every
value is at most 16 bytes long, so every query length (and hence its block count) is bounded;
the tree builders only query tweak types `0..3` (hypertree) or `8..11` (FORS), the counter search
only type `4` at its layer, and the digest search only types `7` and `12`.

Compressions: a WOTS chain 8, an OTS leaf `42 * 8 + 11 = 347`, a tree of height `h`
`347 * 2^h + 2^h - 1`, a FORS tree `2 * 1024 + 1023 = 3071`, the FORS part `14 * 3071`, the roots
hash 4. (v5 values: leaf `21 + 294 + 11 = 326`, FORS tree `512·3 + 1023 = 2559`, keygen 674814.)
-/

namespace SigGolfCandidate.Budget
open SigGolf SigGolfCandidate.Ref OracleComp OracleSpec Finset

/-! ## Loops -/

theorem Spec.foldlM_list {P : Query → Prop} {γ β : Type} (l : List β)
    (f : γ → β → OracleComp HashSpec γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    (h0 : Inv 0 init)
    (hs : ∀ i (hi : i < l.length) acc, Inv i acc → Spec P (Inv (i + 1)) (cost i) (f acc l[i])) :
    Spec P (Inv l.length) (∑ i ∈ range l.length, cost i) (l.foldlM f init) := by
  induction l generalizing Inv cost init with
  | nil => exact Spec.pure _ _ h0
  | cons x l ih =>
    rw [List.foldlM_cons, List.length_cons]
    have h0' := hs 0 (by simp) init h0
    simp only [List.getElem_cons_zero] at h0'
    refine Spec.bind' h0' (fun a ha => ih (fun i => Inv (i + 1)) (fun i => cost (i + 1)) a ha
      (fun i hi acc hacc => hs (i + 1) (by simp; omega) acc hacc)) ?_
    rw [Finset.sum_range_succ' _ l.length]; omega

theorem Spec.foldlM_range {P : Query → Prop} {γ : Type} (n : Nat)
    (f : γ → Nat → OracleComp HashSpec γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Spec P (Inv (i + 1)) (cost i) (f acc i)) :
    Spec P (Inv n) (∑ i ∈ range n, cost i) ((List.range n).foldlM f init) := by
  have h := Spec.foldlM_list (P := P) (List.range n) f Inv cost init h0
    (fun i hi acc hacc => by
      simp only [List.getElem_range]; exact hs i (by simpa using hi) acc hacc)
  simpa using h

theorem Spec.foldlM_range' {P : Query → Prop} {γ : Type} (a n : Nat)
    (f : γ → Nat → OracleComp HashSpec γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Spec P (Inv (i + 1)) (cost i) (f acc (a + i))) :
    Spec P (Inv n) (∑ i ∈ range n, cost i) ((List.range' a n).foldlM f init) := by
  have h := Spec.foldlM_list (P := P) (List.range' a n) f Inv cost init h0
    (fun i hi acc hacc => by
      simp only [List.getElem_range', Nat.one_mul]; exact hs i (by simpa using hi) acc hacc)
  simpa using h

theorem Spec.foldlM_range_le {P : Query → Prop} {γ : Type} (n : Nat)
    (f : γ → Nat → OracleComp HashSpec γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    {Post : γ → Prop} {k : Nat} (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Spec P (Inv (i + 1)) (cost i) (f acc i))
    (hpost : ∀ acc, Inv n acc → Post acc) (hk : ∑ i ∈ range n, cost i ≤ k) :
    Spec P Post k ((List.range n).foldlM f init) :=
  ((Spec.foldlM_range n f Inv cost init h0 hs).mono (fun _ h => h) hpost).mono_k hk

theorem Spec.foldlM_range'_le {P : Query → Prop} {γ : Type} (a n : Nat)
    (f : γ → Nat → OracleComp HashSpec γ) (Inv : Nat → γ → Prop) (cost : Nat → Nat) (init : γ)
    {Post : γ → Prop} {k : Nat} (h0 : Inv 0 init)
    (hs : ∀ i, i < n → ∀ acc, Inv i acc → Spec P (Inv (i + 1)) (cost i) (f acc (a + i)))
    (hpost : ∀ acc, Inv n acc → Post acc) (hk : ∑ i ∈ range n, cost i ≤ k) :
    Spec P Post k ((List.range' a n).foldlM f init) :=
  ((Spec.foldlM_range' a n f Inv cost init h0 hs).mono (fun _ h => h) hpost).mono_k hk

theorem sum_const_range (n c : Nat) : ∑ _i ∈ range n, c = n * c := by simp

theorem sum_levels (h : Nat) : ∑ i ∈ range h, 2 ^ (h - i) / 2 = 2 ^ h - 1 := by
  induction h with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ']
    have : ∀ i ∈ range h, 2 ^ (h + 1 - (i + 1)) / 2 = 2 ^ (h - i) / 2 := by
      intro i _; rw [Nat.add_sub_add_right]
    rw [Finset.sum_congr rfl this, ih]
    simp only [Nat.sub_zero, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
    have : 1 ≤ 2 ^ h := Nat.one_le_two_pow
    omega

/-! ## Hashing -/

/-- All values at most 16 bytes. -/
def AllShort (l : List Val) : Prop := ∀ v ∈ l, v.length ≤ 16

theorem AllShort.nil : AllShort [] := by simp [AllShort]

theorem AllShort.append {l : List Val} {v : Val} (hl : AllShort l) (hv : v.length ≤ 16) :
    AllShort (l ++ [v]) := by
  intro w hw
  simp only [List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact hl w hw
  · exact hv

theorem spec_hash16 {P : Query → Prop} (x : List Byte) (k : Nat) (hP : P (fmt x))
    (hk : (fmt x).blocks ≤ k) : Spec P (fun v : Val => v.length = 16) k (hash16 x) := by
  show Spec P _ k (qry (fmt x) >>= fun a => Pure.pure (answerBytes 16 a))
  exact Spec.qry_bind hP (fun u => Spec.pure _ 0 (by simp)) (by omega)

theorem spec_hash16_bind {P : Query → Prop} {β : Type} {R : β → Prop} (x : List Byte)
    {f : Val → OracleComp HashSpec β} {kx l n : Nat} (hP : P (fmt x))
    (hk : (fmt x).blocks ≤ kx) (hf : ∀ v : Val, v.length = 16 → Spec P R l (f v))
    (hn : kx + l ≤ n) : Spec P R n (Ref.hash16 x >>= f) :=
  (spec_hash16 x kx hP hk).bind' hf hn

/-- Hypertree queries: tweak types `0..3`. -/
def PT (q : Query) : Prop := qbyte q 1 ≤ 3
/-- FORS queries: tweak types `8..11`. -/
def PF (q : Query) : Prop := 8 ≤ qbyte q 1 ∧ qbyte q 1 ≤ 11

/-! ## Trees -/

/-- A node format queries `P` and fits one block on short children. -/
def NodeOK (P : Query → Prop) (node : NodeFmt) : Prop :=
  ∀ lam j l r, l.length ≤ 16 → r.length ≤ 16 →
    P (fmt (node lam j l r)) ∧ (node lam j l r).length ≤ 64

theorem nodeOK_nodeInput (lay tau : Nat) : NodeOK PT (nodeInput lay tau) := by
  intro lam j l r hl hr
  refine ⟨?_, ?_⟩
  · unfold PT nodeInput; rw [qbyte_tag]
  · simp [nodeInput]; omega

theorem nodeOK_ftsNodeInput (k idx : Nat) : NodeOK PF (ftsNodeInput k idx) := by
  intro lam j l r hl hr
  refine ⟨?_, ?_⟩
  · unfold PF ftsNodeInput; rw [qbyte_tag]; omega
  · simp [ftsNodeInput]; omega

theorem spec_buildLevel {P : Query → Prop} {node : NodeFmt} (hn : NodeOK P node) (lam : Nat)
    (level : List Val) (hl : AllShort level) :
    Spec P (fun r => r.length = level.length / 2 ∧ AllShort r) (level.length / 2)
      (buildLevel node lam level) := by
  unfold buildLevel
  refine Spec.foldlM_range_le (P := P) (level.length / 2) _
    (fun i (acc : List Val) => acc.length = i ∧ AllShort acc) (fun _ => 1) [] ⟨rfl, AllShort.nil⟩
    (fun i _ acc hacc => ?_) (fun acc h => h) (by simp)
  obtain ⟨hn1, hn2⟩ := hn lam i (level.getD (2 * i) []) (level.getD (2 * i + 1) [])
    (getD_len_le hl _) (getD_len_le hl _)
  exact spec_hash16_bind (node lam i (level.getD (2 * i) []) (level.getD (2 * i + 1) []))
    hn1 (blocks_fmt_le _ 1 (by omega) le_rfl)
    (fun v hv => Spec.pure _ 0 ⟨by simp [hacc.1], hacc.2.append (by omega)⟩) le_rfl

theorem spec_levelStep {P : Query → Prop} {node : NodeFmt} (hn : NodeOK P node) (cap : Nat)
    (st : List Val × List Val) (lam : Nat) (hl : AllShort st.1) :
    Spec P (fun r => r.1.length = st.1.length / 2 ∧ AllShort r.1) (st.1.length / 2)
      (levelStep node cap st lam) := by
  unfold levelStep
  exact (spec_buildLevel hn lam st.1 hl).bind' (l := 0)
    (fun r hr => Spec.pure _ 0 hr) (by omega)

theorem spec_buildLevels {P : Query → Prop} {node : NodeFmt} (hn : NodeOK P node) (cap h : Nat)
    (leaves : List Val) (hlen : leaves.length = 2 ^ h) (hl : AllShort leaves) :
    Spec P (fun r => r.1.length ≤ 16) (2 ^ h - 1) (buildLevels node cap h leaves) := by
  unfold buildLevels
  rw [← sum_levels h]
  refine Spec.bind' (l := 0) (Spec.foldlM_range' (P := P) 1 h (levelStep node cap)
    (fun i (st : List Val × List Val) => st.1.length = 2 ^ (h - i) ∧ AllShort st.1)
    (fun i => 2 ^ (h - i) / 2) (leaves, []) ⟨by simpa using hlen, hl⟩
    (fun i hi st hst => ?_)) (fun st hst => Spec.pure _ 0 (getD_len_le hst.2 0)) (by omega)
  refine ((spec_levelStep hn cap st (1 + i) hst.2).mono_k (by rw [hst.1])).mono
    (fun _ h => h) (fun r hr => ⟨?_, hr.2⟩)
  rw [hr.1, hst.1]
  have : h - i = (h - (i + 1)) + 1 := by omega
  rw [this, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem prf_ok (S : List Byte) (hS : S.length = 32) (lay tau e i : Nat) :
    PT (fmt (prfInput S lay tau e i)) ∧ (fmt (prfInput S lay tau e i)).blocks ≤ 1 := by
  refine ⟨?_, blocks_fmt_le _ 1 (by simp [prfInput, hS]) le_rfl⟩
  unfold PT prfInput; rw [qbyte_tag]; omega

theorem spec_prf2 {P : Query → Prop} {β : Type} {R : β → Prop} (x : List Byte)
    {f : Val × Val → OracleComp HashSpec β} {kx l n : Nat} (hP : P (fmt x))
    (hk : (fmt x).blocks ≤ kx) (hf : ∀ v : Val × Val, v.1.length ≤ 16 → v.2.length ≤ 16 →
      Spec P R l (f v)) (hn : kx + l ≤ n) : Spec P R n (prf2 x >>= f) := by
  show Spec P R n ((qry (fmt x) >>= fun a => Pure.pure ((answerBytes 32 a).take 16,
    (answerBytes 32 a).drop 16)) >>= f)
  rw [bind_assoc]
  refine Spec.qry_bind hP (k := l) (fun u => ?_) (by omega)
  rw [pure_bind]
  exact hf _ (by simp) (by simp)

theorem spec_chainSteps (lay tau e i x : Nat) (v : Val) (hv : v.length ≤ 16) :
    Spec PT (fun r : Val × Val => r.1.length ≤ 16) 7 (chainSteps lay tau e i x v) := by
  unfold chainSteps
  refine Spec.foldlM_range'_le (P := PT) 1 7 _ (fun _ (st : Val × Val) => st.1.length ≤ 16)
    (fun _ => 1) (v, v) hv (fun i' _ st hst => ?_) (fun _ h => h) (by simp)
  refine spec_hash16_bind (chainInput lay tau e i (1 + i') st.1) ?_
    (blocks_fmt_le _ 1 (by simp [chainInput]; omega) le_rfl)
    (fun w hw => Spec.pure _ 0 (by simp [hw])) le_rfl
  unfold PT chainInput; rw [qbyte_tag]; omega

theorem spec_buildLeaf (S : List Byte) (hS : S.length = 32) (lay tau e : Nat) (x : List Nat) :
    Spec PT (fun r : Val × List Val => r.1.length ≤ 16) 326 (buildLeaf S lay tau e x) := by
  unfold buildLeaf
  refine Spec.bind' (Spec.foldlM_range (P := PT) (nChains / 2) _
    (fun i (st : List Val × List Val) => st.1.length = 2 * i ∧ AllShort st.1) (fun _ => 15)
    ([], []) ⟨rfl, AllShort.nil⟩ (fun k _ st hst => ?_)) (fun st hst => ?_)
    (show (∑ _i ∈ range (nChains / 2), 15) + 11 ≤ 326 by decide)
  · obtain ⟨h1, h2⟩ := prf_ok S hS lay tau e k
    refine spec_prf2 _ h1 h2 (l := 14) (fun s hs0 hs1 => ?_) (by omega)
    obtain ⟨s0, s1⟩ := s
    refine (spec_chainSteps lay tau e (2 * k) _ s0 hs0).bind' (l := 7) (fun r0 hr0 => ?_) le_rfl
    obtain ⟨v0, c0⟩ := r0
    refine (spec_chainSteps lay tau e (2 * k + 1) _ s1 hs1).bind' (l := 0)
      (fun r1 hr1 => ?_) (by omega)
    obtain ⟨v1, c1⟩ := r1
    refine Spec.pure _ 0 ⟨by simp [hst.1]; omega, fun w hw => ?_⟩
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with hw | rfl | rfl
    · exact hst.2 w hw
    · exact hr0
    · exact hr1
  refine spec_hash16_bind (leafInput lay tau e st.1) ?_ (blocks_fmt_le _ 11 ?_ (by omega))
    (fun v hv => Spec.pure _ 0 (by simp [hv])) (show 11 + 0 ≤ 11 by omega)
  · unfold PT leafInput; rw [qbyte_tag]; omega
  · have := length_flatten_le hst.2
    simp only [leafInput, length_thInput, length_tweak, hst.1] at this ⊢
    simp only [nChains] at this; omega

theorem spec_buildLeaves (S : List Byte) (hS : S.length = 32) (lay tau h cap : Nat)
    (x : List Nat) :
    Spec PT (fun r : List Val × List Val => r.1.length = 2 ^ h ∧ AllShort r.1) (2 ^ h * 326)
      (buildLeaves S lay tau h cap x) := by
  unfold buildLeaves
  refine Spec.foldlM_range_le (P := PT) (2 ^ h) _
    (fun i (st : List Val × List Val) => st.1.length = i ∧ AllShort st.1) (fun _ => 326) ([], [])
    ⟨rfl, AllShort.nil⟩ (fun i _ st hst => ?_) (fun _ h => h) (by simp)
  refine (spec_buildLeaf S hS lay tau i x).bind' (l := 0) (fun r hr => ?_) (by omega)
  obtain ⟨v, c⟩ := r
  exact Spec.pure _ 0 ⟨by simp [hst.1], hst.2.append hr⟩

/-- Compressions of a hypertree tree of height `h`. -/
def treeCost (h : Nat) : Nat := 2 ^ h * 326 + (2 ^ h - 1)

theorem spec_buildTree (S : List Byte) (hS : S.length = 32) (lay tau h cap : Nat)
    (x : List Nat) :
    Spec PT (fun r : Val × List Val × List Val => r.1.length ≤ 16) (treeCost h)
      (buildTree S lay tau h cap x) := by
  unfold buildTree treeCost
  refine (spec_buildLeaves S hS lay tau h cap x).bind (fun r hr => ?_)
  obtain ⟨leaves, vals⟩ := r
  refine (spec_buildLevels (nodeOK_nodeInput lay tau) cap h leaves hr.1 hr.2).bind' (l := 0)
    (fun r' hr' => ?_) (by omega)
  obtain ⟨root, path⟩ := r'
  exact Spec.pure _ 0 hr'

theorem treeCost_6 : treeCost 6 = 20927 := by decide
theorem treeCost_5 : treeCost 5 = 10463 := by decide

/-! ## keygen -/

/-- Keygen queries: hypertree types `0..3`, masks (13), the MAC (14). -/
def PK (q : Query) : Prop := qbyte q 1 ≤ 3 ∨ qbyte q 1 = 13 ∨ qbyte q 1 = 14

theorem getD_append_left' {α : Type} (l l' : List α) (d : α) (n : Nat) (h : n < l.length) :
    (l ++ l').getD n d = l.getD n d := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_single {α : Type} (l : List α) (a d : α) :
    (l ++ [a]).getD l.length d = a := by
  simp [List.getD_eq_getElem?_getD]

theorem spec_buildAllLevels {P : Query → Prop} {node : NodeFmt} (hn : NodeOK P node) (h : Nat)
    (leaves : List Val) (hlen : leaves.length = 2 ^ h) (hl : AllShort leaves) :
    Spec P (fun levels : List (List Val) => ∀ k, k ≤ h →
        (levels.getD k []).length = 2 ^ (h - k) ∧ AllShort (levels.getD k []))
      (2 ^ h - 1) (buildAllLevels node h leaves) := by
  unfold buildAllLevels
  rw [← sum_levels h]
  refine Spec.foldlM_range'_le (P := P) 1 h _
    (fun i (levels : List (List Val)) => levels.length = i + 1 ∧ ∀ k, k ≤ i →
      (levels.getD k []).length = 2 ^ (h - k) ∧ AllShort (levels.getD k []))
    (fun i => 2 ^ (h - i) / 2) [leaves] ⟨rfl, fun k hk => ?_⟩ (fun i hi levels hlv => ?_)
    (fun levels hlv k hk => hlv.2 k hk) le_rfl
  · have : k = 0 := by omega
    subst this; simp [hlen, hl]
  · have hi' : 1 + i - 1 = i := by omega
    rw [hi']
    obtain ⟨hA, hB⟩ := hlv.2 i le_rfl
    refine ((spec_buildLevel hn (1 + i) (levels.getD i []) hB).mono_k (by rw [hA])).bind'
      (l := 0) (fun level hlevel => Spec.pure _ 0 ⟨by simp [hlv.1], fun k hk => ?_⟩) (by omega)
    rcases Nat.lt_or_ge k (i + 1) with hk' | hk'
    · rw [getD_append_left' _ _ _ _ (by rw [hlv.1]; exact hk')]
      exact hlv.2 k (by omega)
    · have : k = levels.length := by rw [hlv.1]; omega
      rw [this, getD_append_single]
      refine ⟨?_, hlevel.2⟩
      rw [hlevel.1, hA, ← this, hlv.1] at *
      have e : h - i = (h - (i + 1)) + 1 := by omega
      rw [show k = i + 1 by omega, e, Nat.pow_succ, Nat.mul_div_cancel _ (by norm_num)]

theorem length_xorBytes_le (a b : List Byte) (hb : b.length = 16) : (xorBytes a b).length ≤ 16 := by
  unfold xorBytes; rw [List.length_zipWith]; omega

theorem mask_ok (S : List Byte) (hS : S.length = 32) (l j : Nat) :
    (13 = qbyte (fmt (maskInput S l j)) 1) ∧ (fmt (maskInput S l j)).blocks ≤ 1 := by
  refine ⟨?_, blocks_fmt_le _ 1 (by simp [maskInput, hS]) le_rfl⟩
  unfold maskInput; rw [qbyte_tag]

theorem spec_maskLevel {P : Query → Prop} (hP : ∀ q, qbyte q 1 = 13 → P q) (S : List Byte)
    (hS : S.length = 32) (l : Nat) (level : List Val) :
    Spec P (fun r : List Val => r.length = level.length ∧ AllShort r) level.length
      (maskLevel S l level) := by
  unfold maskLevel
  refine Spec.foldlM_range_le (P := P) level.length _
    (fun i (acc : List Val) => acc.length = i ∧ AllShort acc) (fun _ => 1) [] ⟨rfl, AllShort.nil⟩
    (fun j _ acc hacc => ?_) (fun _ h => h) (by simp)
  obtain ⟨h1, h2⟩ := mask_ok S hS l j
  exact spec_hash16_bind (maskInput S l j) (hP _ h1.symm) h2
    (fun mk hmk => Spec.pure _ 0 ⟨by simp [hacc.1], hacc.2.append (length_xorBytes_le _ _ hmk)⟩)
    le_rfl

theorem topH_eq : topH = 11 := by decide

theorem topN_succ (l : Nat) : topN (l + 1) = topN l + 2 ^ (topH - l) := by
  simp [topN, List.range_succ]

/-- Compressions of keygen: `2048 * 326 + 2047 + 4094 + 1025`. -/
def keygenCost : Nat := 2 ^ 11 * 326 + (2 ^ 11 - 1) + ∑ l ∈ range 11, 2 ^ (11 - l) + 1025

theorem keygenCost_eq : keygenCost = 674814 := by decide

theorem spec_keygenRef (sk : Bytes 32) :
    Spec PK (fun _ => True) keygenCost (keygenRef sk) := by
  have hS := length_toList sk
  have hPT : ∀ q, PT q → PK q := fun q h => Or.inl h
  unfold keygenRef keygenList keygenCost
  refine Spec.bind' (Q := fun _ => True) (l := 0) ?_ (fun _ _ => Spec.pure _ 0 trivial) le_rfl
  rw [topH_eq]
  refine Spec.bind' (((spec_buildLeaves (toList sk) hS 0 0 11 0 []).mono hPT fun _ h => h))
    (fun r hr => ?_) (show 2 ^ 11 * 326 + ((2 ^ 11 - 1) + ∑ l ∈ range 11, 2 ^ (11 - l) + 1025) ≤ _
      by omega)
  obtain ⟨leaves, _⟩ := r
  refine Spec.bind' ((spec_buildAllLevels (nodeOK_nodeInput 0 0) 11 leaves hr.1 hr.2).mono hPT
    fun _ h => h) (fun levels hlev => ?_) (show (2 ^ 11 - 1) + (∑ l ∈ range 11, 2 ^ (11 - l) + 1025)
      ≤ _ by omega)
  refine Spec.bind' (Spec.foldlM_range (P := PK) 11 _
    (fun l (acc : List Val) => acc.length = topN l ∧ AllShort acc) (fun l => 2 ^ (11 - l)) []
    ⟨rfl, AllShort.nil⟩ (fun l hl acc hacc => ?_)) (fun masked hm => ?_) le_rfl
  · obtain ⟨hL, hA⟩ := hlev l (by omega)
    refine ((spec_maskLevel (fun q h => Or.inr (Or.inl h)) (toList sk) hS l _ ).mono_k
      (k' := 2 ^ (11 - l)) (by rw [hL])).bind' (l := 0)
      (fun ml hml => Spec.pure _ 0 ⟨?_, fun w hw => ?_⟩) (by omega)
    · rw [List.length_append, hacc.1, hml.1, hL, topN_succ, topH_eq]
    · rw [List.mem_append] at hw
      rcases hw with hw | hw
      · exact hacc.2 w hw
      · exact hml.2 w hw
  · have hreg : masked.flatten.length ≤ 16 * 4094 := by
      have := length_flatten_le hm.2
      rw [hm.1, show topN 11 = 4094 by decide] at this
      omega
    show Spec PK _ _ (qry (fmt (macInput (toList sk) masked.flatten)) >>= fun tag => Pure.pure _)
    refine Spec.qry_bind (Or.inr (Or.inr ?_)) (fun u => Spec.pure _ 0 trivial)
      (blocks_fmt_le _ 1025 ?_ (by omega) |> fun h => by omega)
    · unfold macInput; rw [qbyte_tag]
    · simp only [macInput, length_thInput, length_tweak, List.length_append, hS]; omega

/-! ## FORS -/

theorem spec_buildFtsLeaves (S : List Byte) (hS : S.length = 32) (k idx a u : Nat) :
    Spec PF (fun r : List Val × Val => r.1.length = 2 * (2 ^ a / 2) ∧ AllShort r.1)
      (2 ^ a / 2 * 3) (buildFtsLeaves S k idx a u) := by
  unfold buildFtsLeaves
  refine Spec.foldlM_range_le (P := PF) (2 ^ a / 2) _
    (fun i (st : List Val × Val) => st.1.length = 2 * i ∧ AllShort st.1) (fun _ => 3) ([], [])
    ⟨rfl, AllShort.nil⟩ (fun j _ st hst => ?_) (fun _ h => h) (by simp)
  refine spec_prf2 (ftsPrfInput S k idx j) ?_
    (blocks_fmt_le _ 1 (by simp [ftsPrfInput, hS]) le_rfl) (l := 2)
    (fun s hs0 hs1 => ?_) (show 1 + 2 ≤ 3 by omega)
  · unfold PF ftsPrfInput; rw [qbyte_tag]; omega
  obtain ⟨s0, s1⟩ := s
  dsimp only at hs0 hs1 ⊢
  refine spec_hash16_bind (ftsLeafInput k idx (2 * j) s0) ?_
    (blocks_fmt_le _ 1 (by simp [ftsLeafInput]; omega) le_rfl) (l := 1)
    (fun l0 hl0 => ?_) le_rfl
  · unfold PF ftsLeafInput; rw [qbyte_tag]; omega
  refine spec_hash16_bind (ftsLeafInput k idx (2 * j + 1) s1) ?_
    (blocks_fmt_le _ 1 (by simp [ftsLeafInput]; omega) le_rfl)
    (fun l1 hl1 => Spec.pure _ 0 ⟨by simp [hst.1]; omega, fun w hw => ?_⟩) le_rfl
  · unfold PF ftsLeafInput; rw [qbyte_tag]; omega
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with hw | rfl | rfl
  · exact hst.2 w hw
  · omega
  · omega

/-- Compressions of a FORS tree of height `a`. -/
def ftsCost (a : Nat) : Nat := 2 ^ a / 2 * 3 + (2 ^ a - 1)

theorem spec_buildFtsTree (S : List Byte) (hS : S.length = 32) (k idx a u : Nat) (ha : 1 ≤ a) :
    Spec PF (fun r : Val × List Val × Val => r.2.2.length ≤ 16) (ftsCost a)
      (buildFtsTree S k idx a u) := by
  unfold buildFtsTree ftsCost
  refine (spec_buildFtsLeaves S hS k idx a u).bind (fun r hr => ?_)
  obtain ⟨leaves, s⟩ := r
  have hlen : leaves.length = 2 ^ a := by
    rw [hr.1]
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [pow_succ, Nat.mul_div_cancel _ (by norm_num), Nat.mul_comm]
  refine (spec_buildLevels (nodeOK_ftsNodeInput k idx) u a leaves hlen hr.2).bind' (l := 0)
    (fun r' hr' => ?_) (by omega)
  obtain ⟨root, path⟩ := r'
  exact Spec.pure _ 0 hr'

theorem spec_signFors (S : List Byte) (hS : S.length = 32) (N : Nat) :
    Spec PF (fun r : List (Val × List Val) × List Val => r.2.length = 14 ∧ AllShort r.2)
      (14 * ftsCost 10) (signFors S N) := by
  unfold signFors
  refine Spec.foldlM_range_le (P := PF) ftsTrees _
    (fun i (st : List (Val × List Val) × List Val) => st.2.length = i ∧ AllShort st.2)
    (fun _ => ftsCost 10) ([], []) ⟨rfl, AllShort.nil⟩ (fun i _ st hst => ?_)
    (fun _ h => by simpa [ftsTrees] using h) (by simp [ftsTrees])
  refine (spec_buildFtsTree S hS i (idxOf N) ftsA (uOf N i) (by decide)).bind' (l := 0)
    (fun r hr => ?_) (by simp [ftsA])
  obtain ⟨s, path, root⟩ := r
  exact Spec.pure _ 0 ⟨by simp [hst.1], hst.2.append hr⟩

theorem ftsCost_10 : ftsCost 10 = 2559 := by decide

/-- The FORS key hash: 4 blocks. -/
theorem roots_ok (idx : Nat) (roots : List Val) (h1 : roots.length = 14) (h2 : AllShort roots) :
    PF (fmt (rootsInput idx roots)) ∧ (fmt (rootsInput idx roots)).blocks ≤ 4 := by
  refine ⟨?_, blocks_fmt_le _ 4 ?_ (by omega)⟩
  · unfold PF rootsInput; rw [qbyte_tag]; omega
  · have := length_flatten_le h2
    simp only [rootsInput, length_thInput, length_tweak, h1] at this ⊢
    omega

/-! ## Searches -/

/-- Counter-search queries of layer `lay`. -/
def PC (lay : Nat) (q : Query) : Prop := qbyte q 1 = 4 ∧ qbyte q 2 = lay

/-- Digest-search queries. -/
def PD (q : Query) : Prop := qbyte q 1 = 7 ∨ qbyte q 1 = 12

theorem enc_ok (lay tau e : Nat) (M : Val) (hM : M.length ≤ 16) (c : Nat) (hlay : lay < 256) :
    PC lay (fmt (encInput lay tau e M c)) ∧ (fmt (encInput lay tau e M c)).blocks ≤ 1 := by
  refine ⟨⟨?_, ?_⟩, blocks_fmt_le _ 1 (by simp [encInput]; omega) le_rfl⟩
  · unfold encInput; rw [qbyte_tag]
  · unfold encInput; rw [qbyte_lay]; omega

theorem decodeDigits_some {v : Val} {x : List Nat} (h : decodeDigits v = some x) :
    x.length = 42 ∧ x.sum = targetSum := by
  unfold decodeDigits at h
  simp only at h
  split_ifs at h with h1 h2
  cases h
  exact ⟨by simp [digitsOfWord], h2⟩

/-- The counter search's results: accepted digit words. -/
def DigOK (o : Option (Nat × List Nat)) : Prop :=
  ∀ c x, o = some (c, x) → x.length = 42 ∧ x.sum = targetSum

theorem spec_searchCounter (lay tau e : Nat) (M : Val) (hM : M.length ≤ 16) (hlay : lay < 256) :
    ∀ fuel c, Spec (PC lay) DigOK fuel (searchCounter lay tau e M c fuel) := by
  intro fuel
  induction fuel with
  | zero => intro c; exact Spec.pure _ _ (by simp [DigOK])
  | succ n ih =>
    intro c
    unfold searchCounter
    obtain ⟨h1, h2⟩ := enc_ok lay tau e M hM c hlay
    refine spec_hash16_bind _ h1 h2 (l := n) (fun d _ => ?_) (by omega)
    split
    · next x hx =>
      exact Spec.pure _ _ (by
        intro c' x' h; cases h; exact decodeDigits_some hx)
    · exact ih (c + 1)

theorem rnd_ok (S m : List Byte) (hS : S.length = 32) (hm : m.length = 32) (a : Nat) :
    PD (fmt (rndInput S m a)) ∧ (fmt (rndInput S m a)).blocks ≤ 2 := by
  refine ⟨Or.inl ?_, blocks_fmt_le _ 2 (by simp [rndInput, hS, hm]) (by omega)⟩
  unfold rndInput; rw [qbyte_tag]

theorem dig_ok (rho m : List Byte) (hr : rho.length = 16) (hm : m.length = 32) :
    PD (fmt (digestInput rho m)) ∧ (fmt (digestInput rho m)).blocks ≤ 2 := by
  refine ⟨Or.inr ?_, blocks_fmt_le _ 2 (by simp [digestInput, hr, hm]) (by omega)⟩
  unfold digestInput; rw [qbyte_tag]

theorem spec_searchDigest (S m : List Byte) (hS : S.length = 32) (hm : m.length = 32) :
    ∀ fuel a, Spec PD (fun _ => True) (4 * fuel) (searchDigest S m a fuel) := by
  intro fuel
  induction fuel with
  | zero => intro a; exact Spec.pure _ _ trivial
  | succ n ih =>
    intro a
    unfold searchDigest
    obtain ⟨h1, h2⟩ := rnd_ok S m hS hm a
    refine spec_hash16_bind _ h1 h2 (l := 2 + 4 * n) (fun rho hrho => ?_) (by omega)
    obtain ⟨h3, h4⟩ := dig_ok rho m hrho hm
    show Spec PD _ _ (qry (fmt (digestInput rho m)) >>= fun b => Pure.pure (b.toNat % 2 ^ 184)
      >>= fun N => if admissible N = true then Pure.pure (some (rho, N))
        else searchDigest S m (a + 1) n)
    refine Spec.qry_bind h3 (k := 4 * n) (fun u => ?_) (by omega)
    rw [pure_bind]
    split
    · exact Spec.pure _ _ trivial
    · exact ih (a + 1)

end SigGolfCandidate.Budget
