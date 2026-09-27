import SigGolfCandidate.Sign.Words

/-!
# Relocatable blocks and `Nat`-level normalization

* `kernel_theorem name : ∀ xs, lhs = rhs` : adds the theorem with proof `fun xs => Eq.refl lhs`,
  checked by the **kernel only** (no elaborator defeq). Used to run the symbolic executor at a
  *variable* pc: `symRun cfg seg pc n = some (relocated result)` holds for every `pc` when the
  block only uses pc for its final pc (no `AUIPC`/`JAL rd≠x0`), so block lemmas can be stated
  for any placement `CodeAt image (pcOf P) seg` (shared code in several images).
* `addN pc n = pc + 4 + … + 4` (the executor's pc after `n` instructions), `addN_ofNat`.
* `bvn` simp set: `BitVec.ofNat 64` arithmetic → `Nat` arithmetic (`ofNat a + ofNat b = ofNat (a+b)`,
  shifts, masks), `ofNat_eq_iff`, `accessValid_ofNat`.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

open Lean Elab Command Meta in
/-- `kernel_theorem name : ∀ xs, lhs = rhs` — proof `fun xs => Eq.refl lhs`, checked by the
kernel only. -/
elab "kernel_theorem " id:ident " : " t:term : command => do
  liftTermElabM do
    let ty ← Term.elabType t
    Term.synthesizeSyntheticMVarsNoPostponing
    let ty ← instantiateMVars ty
    if ty.hasMVar then throwError "kernel_theorem: statement has metavariables"
    let pf ← forallTelescope ty fun xs body => do
      let some (_, lhs, _) := body.eq? | throwError "kernel_theorem: not an equation"
      mkLambdaFVars xs (← mkEqRefl lhs)
    let base := (← getCurrNamespace) ++ id.getId
    addDecl <| Declaration.thmDecl { name := base, levelParams := [], type := ty, value := pf }

/-- The executor's pc after `n` instructions from `pc`. -/
def addN (pc : Word) : Nat → Word
  | 0 => pc
  | n + 1 => addN (pc + 4) n

/-- `pc` of instruction index `i` (image code starts at `0x1000`). -/
abbrev pcOf (i : Nat) : Word := BitVec.ofNat 64 (0x1000 + 4 * i)

theorem addN_ofNat (a n : Nat) : addN (BitVec.ofNat 64 a) n = BitVec.ofNat 64 (a + 4 * n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [addN, show BitVec.ofNat 64 a + 4 = BitVec.ofNat 64 (a + 4) from by
      apply BitVec.eq_of_toNat_eq; simp <;> omega, ih]
    congr 1; ring

theorem addN_pcOf (i n : Nat) : addN (pcOf i) n = pcOf (i + n) := by
  rw [addN_ofNat]; congr 1; ring

/-- Replace the two constant targets of a branch pc. -/
def retarget : E → Word → Word → E
  | .ite op x y _ _, a, b => .ite op x y (.c a) (.c b)
  | e, _, _ => e

/-! ## `BitVec.ofNat 64` arithmetic as `Nat` arithmetic -/

theorem ofNat_add_ofNat (a b : Nat) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  apply BitVec.eq_of_toNat_eq; simp

theorem ofNat_sub_ofNat (a b : Nat) (hb : b ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

theorem ofNat_shiftLeft (a k : Nat) :
    BitVec.ofNat 64 a <<< k = BitVec.ofNat 64 (a * 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod]

theorem ofNat_ushiftRight (a k : Nat) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a >>> k = BitVec.ofNat 64 (a / 2 ^ k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt ha]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.div_le_self _ _) ha)]

theorem ofNat_and_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a &&& BitVec.ofNat 64 b = BitVec.ofNat 64 (a &&& b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt Nat.and_le_left ha)]

theorem ofNat_or_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (a ||| b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_or, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.mod_eq_of_lt (Nat.or_lt_two_pow ha hb)]

theorem ofNat_xor_ofNat (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    BitVec.ofNat 64 a ^^^ BitVec.ofNat 64 b = BitVec.ofNat 64 (a ^^^ b) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_xor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rw [Nat.mod_eq_of_lt (Nat.xor_lt_two_pow ha hb)]

theorem ofNat_eq_iff (a b : Nat) :
    BitVec.ofNat 64 a = BitVec.ofNat 64 b ↔ a % 2 ^ 64 = b % 2 ^ 64 := by
  constructor
  · intro h; have := congrArg BitVec.toNat h; simpa using this
  · intro h; apply BitVec.eq_of_toNat_eq; simpa using h

theorem accessValid_ofNat (a w : Nat) :
    accessValid (BitVec.ofNat 64 a) w = true ↔ a % 2 ^ 64 + w ≤ 2 ^ 24 ∧ a % 2 ^ 64 % w = 0 := by
  simp [accessValid, rangeValid, MEMORY_BYTES]

theorem toNat_ofNat_64 (a : Nat) : (BitVec.ofNat 64 a).toNat = a % 2 ^ 64 := by simp

theorem ofNat_beq_ofNat (a b : Nat) :
    (BitVec.ofNat 64 a == BitVec.ofNat 64 b) = decide (a % 2 ^ 64 = b % 2 ^ 64) :=
  Bool.eq_iff_iff.mpr (by simp only [beq_iff_eq, ofNat_eq_iff, decide_eq_true_eq])

theorem ofNat_bne_ofNat (a b : Nat) :
    (BitVec.ofNat 64 a != BitVec.ofNat 64 b) = !decide (a % 2 ^ 64 = b % 2 ^ 64) := by
  rw [bne, ofNat_beq_ofNat]

/-- Signed comparison of small numbers. -/
theorem ofNat_slt_ofNat (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.slt (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  rw [BitVec.slt_eq_ult_of_msb_eq]
  · simp [BitVec.ult]; omega
  · simp [BitVec.msb_eq_decide, Nat.mod_eq_of_lt (by omega : a < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : b < 2 ^ 64)]; omega

/-- First tweak dword (independent of `j`). -/
def twWord0 (t lay tau p : Nat) : Word :=
  BitVec.ofNat 64 (1 + 256 * (t % 256) + 65536 * (lay % 256) + 2 ^ 24 * (tau / 2 ^ 32 % 256) +
    2 ^ 32 * (p % 2 ^ 32))

theorem twWords_eq (t lay tau p j : Nat) :
    twWords t lay tau p j = [twWord0 t lay tau p, BitVec.ofNat 64 (tau % 2 ^ 32 + 2 ^ 32 * (j % 2 ^ 32))] :=
  rfl

/-! ## 32-bit halves of dwords (`SW` merges) -/

/-- Low / high 32-bit half of a dword. -/
abbrev lo32 (w : Word) : BitVec 32 := w.extractLsb' 0 32
abbrev hi32 (w : Word) : BitVec 32 := w.extractLsb' 32 32

@[simp] theorem lo32_replace0 (w : Word) (v : BitVec 32) : lo32 (replaceWord32 w 0 v) = v := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp
@[simp] theorem hi32_replace0 (w : Word) (v : BitVec 32) : hi32 (replaceWord32 w 0 v) = hi32 w := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp
@[simp] theorem lo32_replace1 (w : Word) (v : BitVec 32) : lo32 (replaceWord32 w 1 v) = lo32 w := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp
@[simp] theorem hi32_replace1 (w : Word) (v : BitVec 32) : hi32 (replaceWord32 w 1 v) = v := by
  ext i hi; simp only [replaceWord32]; interval_cases i <;> simp

/-- A dword from its halves. -/
theorem word_of_halves (w : Word) (a b : Nat) (hlo : lo32 w = BitVec.ofNat 32 a)
    (hhi : hi32 w = BitVec.ofNat 32 b) : w = BitVec.ofNat 64 (a % 2 ^ 32 + 2 ^ 32 * (b % 2 ^ 32)) := by
  have h1 := congrArg BitVec.toNat hlo
  have h2 := congrArg BitVec.toNat hhi
  simp only [lo32, hi32, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at h1 h2
  apply BitVec.eq_of_toNat_eq
  have := w.isLt
  simp only [BitVec.toNat_ofNat]
  omega

@[simp] theorem lo32_ofNat (n : Nat) : lo32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [lo32, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_zero]
  omega

@[simp] theorem hi32_ofNat (n : Nat) : hi32 (BitVec.ofNat 64 n) = BitVec.ofNat 32 (n / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [hi32, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  omega

@[simp] theorem truncate32_ofNat (n : Nat) : (BitVec.ofNat 64 n).truncate 32 = BitVec.ofNat 32 n := by
  apply BitVec.eq_of_toNat_eq; simp <;> omega

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
/-- `rvs [hs]` : `rv_simp` plus constant folding, `ite` on `True/False`, and the `ofNat`
normalizations. -/
macro "rvs" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp only [rv_simp, ite_true, ite_false, if_true, if_false, Nat.reduceDiv, Nat.reduceMod,
      Nat.reduceAdd, Nat.reduceMul, Nat.reducePow, truncate32_ofNat, BitVec.toNat_ofNat,
      ofNat_add_ofNat, ofNat_shiftLeft, $ts',*])
end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
/-- `omega` after removing `% 2^64` of in-range terms (omega is incomplete with the huge
coefficients those produce). -/
macro "bvomega" : tactic =>
  `(tactic| ((try simp (disch := omega) only [Nat.reducePow, Nat.mod_eq_of_lt]); omega))
end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open RiscvZkvm.Rv64

/-- OR of values with disjoint bit ranges is addition. -/
theorem ofNat_or_disjoint (x b i : Nat) (hx : x % 2 ^ i = 0) (hb : b < 2 ^ i) (h : x + b < 2 ^ 64) :
    BitVec.ofNat 64 x ||| BitVec.ofNat 64 b = BitVec.ofNat 64 (x + b) := by
  rw [ofNat_or_ofNat _ _ (by omega) (by omega)]
  congr 1
  obtain ⟨q, rfl⟩ : ∃ q, x = 2 ^ i * q := ⟨x / 2 ^ i, by rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hx)]⟩
  rw [Nat.two_pow_add_eq_or_of_lt hb]

theorem ofNat_or_disjoint' (x b i : Nat) (hx : x % 2 ^ i = 0) (hb : b < 2 ^ i) (h : x + b < 2 ^ 64) :
    BitVec.ofNat 64 b ||| BitVec.ofNat 64 x = BitVec.ofNat 64 (x + b) := by
  rw [BitVec.or_comm, ofNat_or_disjoint x b i hx hb h]
end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
/-- `BitVec.ofNat 64` arithmetic → `Nat` arithmetic, side conditions by `omega`. Run after
`simp only [blk.res, rv_simp]` (whose `addNegLit` turns `x + (-c)` into `x - c`). -/
macro "bvsimp" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => do
  let ts' : Lean.Syntax.TSepArray [`Lean.Parser.Tactic.simpStar, `Lean.Parser.Tactic.simpErase,
    `Lean.Parser.Tactic.simpLemma] "," := ⟨ts.elemsAndSeps⟩
  `(tactic| simp (disch := omega) only [ofNat_add_ofNat, ofNat_sub_ofNat, ofNat_shiftLeft,
      ofNat_ushiftRight, ofNat_and_ofNat, ofNat_xor_ofNat, BitVec.toNat_ofNat, Nat.reduceMod,
      Nat.reducePow, Nat.reduceAdd, Nat.reduceMul, Nat.reduceDiv, Nat.reduceSub, truncate32_ofNat,
      ite_true, ite_false, if_true, if_false, BitVec.ofNat_eq_ofNat, Nat.add_sub_cancel,
      Nat.mod_eq_of_lt, Nat.reduceEqDiff, reduceIte, and_true, true_and, or_false, false_or, not_false_eq_true, $ts',*])
end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
theorem bne_cond (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    ((!decide (a % 2 ^ 64 = b % 2 ^ 64)) = true) ↔ a ≠ b := by
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]; simp
end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
theorem ofNat_congr {a b : Nat} (h : a = b) : BitVec.ofNat 64 a = BitVec.ofNat 64 b := h ▸ rfl
end SigGolfCandidate.Sign
