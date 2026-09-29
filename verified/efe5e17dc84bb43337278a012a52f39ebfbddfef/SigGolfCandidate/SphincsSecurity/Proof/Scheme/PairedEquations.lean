import SigGolfCandidate.SphincsSecurity.Proof.IdealStatement

/-!
# The paired builders with table secrets

With table secrets, the paired builders make exactly the queries of the per-secret builders: a pair's
getter is a pure read, and walking member `2k` then member `2k + 1` for `k = 0, 1, …` walks every member in
order (`sequenceFin_pairs`). These equalities let the seeded signer, which derives a pair of secrets with
one query, erase to the proof's table signer, which uses the per-secret builders.
-/

namespace SphincsSecurity.Concrete

open OracleComp

variable {m : Type → Type} [Monad m] [LawfulMonad m]

/-- Spread pairs indexed by `Fin n` over `Fin N`, `N = 2n`: even members take the first component. -/
def unpairFin {α : Type} {n N : Nat} (hN : N = 2 * n) (p : Fin n → α × α) (i : Fin N) : α :=
  if i.val % 2 = 0 then (p ⟨i.val / 2, by have := i.isLt; omega⟩).1 else (p ⟨i.val / 2, by have := i.isLt; omega⟩).2

/-- The pair computation of a member computation. -/
def pairStep {α : Type} {n N : Nat} (hN : N = 2 * n) (f : Fin N → m α) (k : Fin n) : m (α × α) := do
  let a ← f ⟨2 * k.val, by have := k.isLt; omega⟩
  let b ← f ⟨2 * k.val + 1, by have := k.isLt; omega⟩
  pure (a, b)

theorem sequenceFin_pairs {α : Type} (n : Nat) :
    ∀ (N : Nat) (hN : N = 2 * n) (f : Fin N → m α),
      sequenceFin f = unpairFin hN <$> sequenceFin (pairStep hN f) := by
  induction n with
  | zero =>
      intro N hN f
      subst hN
      simp only [Nat.mul_zero, sequenceFin, map_pure]
      congr 1
      funext i
      exact i.elim0
  | succ n ih =>
      intro N hN f
      obtain rfl : N = (2 * n + 1) + 1 := by omega
      have htail := ih (2 * n) rfl (fun i => f i.succ.succ)
      conv_lhs => simp only [sequenceFin]
      rw [htail]
      conv_rhs => simp only [sequenceFin]
      simp only [pairStep, map_bind, bind_assoc, map_pure, pure_bind, bind_map_left]
      have e0 : (⟨2 * (0 : Fin (n + 1)).val, by omega⟩ : Fin (2 * n + 1 + 1)) = 0 := rfl
      have e1 : (⟨2 * (0 : Fin (n + 1)).val + 1, by omega⟩ : Fin (2 * n + 1 + 1)) = (0 : Fin (2 * n + 1)).succ := rfl
      rw [e0, e1]
      apply bind_congr
      intro a
      apply bind_congr
      intro b
      have hpairs : (pairStep (n := n) (N := 2 * n) rfl fun i => f i.succ.succ) =
          (fun k : Fin n => do
            let a ← f ⟨2 * (k.succ).val, by have := k.isLt; omega⟩
            let b ← f ⟨2 * (k.succ).val + 1, by have := k.isLt; omega⟩
            pure (a, b)) := by
        funext k
        simp only [pairStep]
        congr 2
      rw [hpairs]
      apply bind_congr
      intro rest
      congr 1
      funext i
      obtain ⟨i, hi⟩ := i
      match i, hi with
      | 0, _ =>
          rw [show (⟨0, by omega⟩ : Fin (2 * n + 1 + 1)) = 0 from rfl, Fin.cases_zero]
          simp [unpairFin]
      | 1, _ =>
          rw [show (⟨1, by omega⟩ : Fin (2 * n + 1 + 1)) = (0 : Fin (2 * n + 1)).succ from rfl, Fin.cases_succ,
            Fin.cases_zero]
          simp [unpairFin]
      | j + 2, hj =>
          rw [show (⟨j + 2, hj⟩ : Fin (2 * n + 1 + 1)) = (⟨j, by omega⟩ : Fin (2 * n)).succ.succ from rfl,
            Fin.cases_succ, Fin.cases_succ]
          have hidx : (⟨(j + 2) / 2, by omega⟩ : Fin (n + 1)) = (⟨j / 2, by omega⟩ : Fin n).succ :=
            Fin.ext (by simp only [Fin.val_succ]; omega)
          unfold unpairFin
          simp only [Fin.val_succ, show j + 1 + 1 = j + 2 from rfl, show (j + 2) % 2 = j % 2 by omega, hidx,
            Fin.cases_succ]

theorem numChains_eq_two_mul : numChains = 2 * (numChains / 2) := rfl

theorem ftsLeaves_eq_two_mul : 2 ^ ftsTreeHeight = 2 * (2 ^ (ftsTreeHeight - 1)) := rfl

theorem unpairChains_eq {α : Type} (pairs : ChainPair → α × α) :
    unpairChains pairs = unpairFin numChains_eq_two_mul pairs := by
  funext i
  rfl

theorem unpairFtsLeaves_eq {α : Type} (pairs : FtsPair → α × α) :
    unpairFtsLeaves pairs = unpairFin ftsLeaves_eq_two_mul pairs := by
  funext i
  rfl

variable [HasQuery HashSpec m]

/-- Chain secrets of a table, read per pair. -/
def pairOf (secret : ChainIndex → Digest) (pair : ChainPair) : Digest × Digest :=
  (secret (evenChain pair), secret (oddChain pair))

/-- Few-time secrets of a table, read per pair. -/
def ftsPairOf (secret : FtsLeaf → Digest) (pair : FtsPair) : Digest × Digest :=
  (secret (evenFtsLeaf pair), secret (oddFtsLeaf pair))

theorem buildLeafPaired_pure (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex) (leaf : LeafIndex)
    (secret : ChainIndex → Digest) (digits : Encoding) :
    (buildLeafPaired parameter lay tree leaf (fun pair => pure (pairOf secret pair)) digits : m _) =
      buildLeaf parameter lay tree leaf (fun chainIdx => pure (secret chainIdx)) digits := by
  unfold buildLeafPaired buildLeaf
  rw [sequenceFin_pairs (numChains / 2) numChains numChains_eq_two_mul, bind_map_left]
  simp only [pure_bind, unpairChains_eq]
  rfl

theorem buildLayerTablePaired_pure (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (digits : Encoding) :
    (buildLayerTablePaired parameter lay tree (fun leaf pair => pure (pairOf (secret leaf) pair)) leaf digits : m _) =
      buildLayerTable parameter lay tree (fun leaf chainIdx => pure (secret leaf chainIdx)) leaf digits := by
  unfold buildLayerTablePaired buildLayerTable
  simp only [buildLeafPaired_pure]

theorem buildLayerTreePaired_pure (parameter : PublicParameter) (lay : Layer) (tree : TreeIndex)
    (secret : LeafIndex → ChainIndex → Digest) (leaf : LeafIndex) (digits : Encoding) :
    (buildLayerTreePaired parameter lay tree (fun leaf pair => pure (pairOf (secret leaf) pair)) leaf digits : m _) =
      buildLayerTree parameter lay tree (fun leaf chainIdx => pure (secret leaf chainIdx)) leaf digits := by
  unfold buildLayerTreePaired
  rw [buildLayerTablePaired_pure]
  unfold buildLayerTree buildLayerTable
  simp only [bind_assoc, pure_bind]

theorem buildFtsTreePaired_pure (parameter : PublicParameter) (index : Index)
    (secret : FtsLeaf → Digest) :
    (buildFtsTreePaired parameter index (fun pair => pure (ftsPairOf secret pair)) : m _) =
      buildFtsTree parameter index (fun leaf => pure (secret leaf)) := by
  unfold buildFtsTreePaired buildFtsTree
  rw [sequenceFin_pairs (2 ^ (ftsTreeHeight - 1)) (2 ^ ftsTreeHeight) ftsLeaves_eq_two_mul, bind_map_left]
  simp only [pure_bind]
  have hstep : (fun pair : FtsPair => (do
      let first ← ftsLeafHash parameter index porsTree (evenFtsLeaf pair).val (ftsPairOf secret pair).1
      let second ← ftsLeafHash parameter index porsTree (oddFtsLeaf pair).val (ftsPairOf secret pair).2
      return (((ftsPairOf secret pair).1, first), ((ftsPairOf secret pair).2, second)) : m _)) =
      pairStep ftsLeaves_eq_two_mul (fun leafIdx : FtsLeaf => (do
        let hashed ← ftsLeafHash parameter index porsTree leafIdx.val (secret leafIdx)
        return (secret leafIdx, hashed) : m _)) := by
    funext pair
    simp only [pairStep, pure_bind, bind_assoc]
    rfl
  rw [hstep]
  simp only [unpairFtsLeaves_eq]

theorem signTopLayerPaired_pure (parameter : PublicParameter) (index : Index)
    (secret : LeafIndex → ChainIndex → Digest) (topNode : Nat → Nat → m Digest) (message : Digest) :
    signTopLayerPaired parameter index (fun leaf pair => pure (pairOf (secret leaf) pair)) topNode message =
      signTopLayer parameter index (fun leaf chainIdx => pure (secret leaf chainIdx)) topNode message := by
  unfold signTopLayerPaired signTopLayer
  apply bind_congr
  intro search
  rcases search with _ | ⟨counter, encoding⟩
  · rfl
  · dsimp only
    simp only [pure_bind]
    rw [sequenceFin_pairs (numChains / 2) numChains numChains_eq_two_mul, bind_map_left]
    simp only [unpairChains_eq]
    rfl

theorem signLayersPaired_pure (parameter : PublicParameter) (index : Index)
    (secret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest) (topNode : Nat → Nat → m Digest)
    (remaining : Nat) (message : Digest) :
    signLayersPaired parameter index (fun lay tree leaf pair => pure (pairOf (secret lay tree leaf) pair)) topNode
        remaining message =
      signLayers parameter index (fun lay tree leaf chainIdx => pure (secret lay tree leaf chainIdx)) topNode
        remaining message := by
  induction remaining generalizing message with
  | zero => rfl
  | succ remaining ih =>
      simp only [signLayersPaired, signLayers]
      split
      · split
        · rw [signTopLayerPaired_pure]
        · apply bind_congr
          intro search
          rcases search with _ | ⟨counter, encoding⟩
          · rfl
          · dsimp only
            rw [buildLayerTreePaired_pure (secret := secret _ _)]
            apply bind_congr
            intro built
            rw [ih]
      · rfl

theorem signFromPaired_pure (parameter : PublicParameter) (index : Index)
    (ftsSecret : FtsTree → FtsLeaf → Digest) (otsSecret : Layer → TreeIndex → LeafIndex → ChainIndex → Digest)
    (topNode : Nat → Nat → m Digest) (randomness : Randomness) (leaves : IndexGroup → FtsLeaf) :
    signFromPaired parameter index (fun tree pair => pure (ftsPairOf (ftsSecret tree) pair))
        (fun lay tree leaf pair => pure (pairOf (otsSecret lay tree leaf) pair)) topNode randomness leaves =
      signFrom parameter index (fun tree leaf => pure (ftsSecret tree leaf))
        (fun lay tree leaf chainIdx => pure (otsSecret lay tree leaf chainIdx)) topNode randomness leaves := by
  unfold signFromPaired signFrom
  rw [buildFtsTreePaired_pure]
  apply bind_congr
  rintro ⟨secrets, table⟩
  dsimp only
  rw [signLayersPaired_pure]

end SphincsSecurity.Concrete
