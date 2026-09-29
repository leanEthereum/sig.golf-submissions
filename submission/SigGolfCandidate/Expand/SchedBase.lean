import SigGolfCandidate.Expand.Pass
import SigGolfCandidate.Expand.Stream
import SigGolfCandidate.Expand.Mem

/-!
# `expand`: memory views used by the schedule loop

* `getByte_ofNat` : a byte is a byte of its aligned dword.
* `StackOK u stack` : `STK + 0 = 0` (bottom sentinel) and the stack entries at `STK + 8 ..`
  (top at `STK + 8 |stack|`).
* `StreamOK u l` : the stream area `WIT + 272 ..+2152` holds the bytes `l` (zero beyond).
* `SigOK u sig` : the signature buffer holds `sig`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-- `RegsEq` of a block result, by evaluation (the registers outside `l` are `.reg r`). -/
macro "regs_eq" : tactic => `(tactic| (apply regsEq_toState; intro x hx; cases x <;> first | (simp at hx; done) | rfl))

theorem getByte_ofNat (u : MachineState) (a : Nat) (ha : a < 2 ^ 64) :
    u.getByte (BitVec.ofNat 64 a) = extractByte (u.getMem (BitVec.ofNat 64 (a / 8 * 8))) (a % 8) := by
  simp only [MachineState.getByte]
  rw [Mem.byteOffset_ofNat ha]
  congr 2
  apply BitVec.eq_of_toNat_eq
  rw [alignToDword_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt (show a / 8 * 8 < 2 ^ 64 by omega)]
  omega

theorem extractByte_replaceByte0 (w : Word) (b : BitVec 8) (q : Nat) (hq : q < 8) :
    extractByte (replaceByte w 0 b) q = if q = 0 then b else extractByte w q := by
  interval_cases q <;> (simp only [extractByte, replaceByte]; ext i hi; interval_cases i <;> simp)

theorem truncate8_ofNat (n : Nat) : (BitVec.ofNat 64 n).truncate 8 = BitVec.ofNat 8 n := by
  apply BitVec.eq_of_toNat_eq; simp

/-- Writes of the schedule loop: the stack and the stream area. -/
def SW (a : Nat) : Prop := (0x760 ≤ a ∧ a < 0x7E0) ∨ (0x910 ≤ a ∧ a < 0x910 + 2152)

def StackOK (u : MachineState) (stack : List Nat) : Prop :=
  u.getMem (BitVec.ofNat 64 0x760) = 0 ∧
    ∀ i < stack.length, u.getMem (BitVec.ofNat 64 (0x760 + 8 * (stack.length - i))) =
      BitVec.ofNat 64 (stack.getD i 0)

def StreamOK (u : MachineState) (l : List Byte) : Prop :=
  ∀ i < 2152, u.getByte (BitVec.ofNat 64 (0x910 + i)) = l.getD i 0

def SigOK (u : MachineState) (sig : List Byte) : Prop :=
  ∀ j < 6100, u.getByte (BitVec.ofNat 64 (0x3300 + j)) = sig.getD j 0

theorem SigOK.frame {t u : MachineState} {sig : List Byte} {W : Nat → Prop} (h : SigOK t sig)
    (hf : Frame t u W) (hW : ∀ a, 0x3300 ≤ a → a < 0x3300 + 6104 → ¬ W a) : SigOK u sig := by
  intro j hj
  rw [getByte_ofNat _ _ (by omega), hf _ (by omega) (hW _ (by omega) (by omega)), ← getByte_ofNat _ _ (by omega)]
  exact h j hj

/-- A byte of a signature dword. -/
theorem sig_dword_byte {t : MachineState} {sig : List Byte} (h : SigOK t sig) (d k : Nat) (hd : d % 8 = 0)
    (hk : k < 8) (hdk : d + k < 6100) :
    extractByte (t.getMem (BitVec.ofNat 64 (0x3300 + d))) k = sig.getD (d + k) 0 := by
  rw [← h (d + k) hdk, getByte_ofNat _ _ (by omega)]
  congr 3 <;> omega

end SigGolfCandidate.Expand

namespace SigGolfCandidate.Expand
open SigGolfCandidate.Legacy SigGolfCandidate.Legacy.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## The reference schedule step, unfolded -/

theorem schedStep_merge (st : SchedState) (E cnt t h Q : Nat) (rest : List Nat)
    (hs : st.stack = Q :: rest) (hQ : Q = E) :
    schedStep (st, E, cnt, t) h =
      ({ st with segs := st.segs ++ [cnt ||| 16 ||| 32 * t], stack := rest }, E / 2, 0, E / 2 % 2) := by
  simp only [schedStep, hs, hQ, if_true]

theorem schedStep_fold (st : SchedState) (E cnt t h : Nat)
    (hs : ∀ Q rest, st.stack = Q :: rest → Q ≠ E) :
    schedStep (st, E, cnt, t) h =
      ({ st with reads := st.reads ++ [(h, (E ^^^ 1) - porsT / 2 ^ h)] }, E / 2, cnt + 1, t) := by
  simp only [schedStep]
  split
  · rename_i Q rest hQ; rw [if_neg (hs Q rest hQ)]
  · rfl

theorem schedStep_mono (x : SchedState × Nat × Nat × Nat) (h : Nat) :
    x.1.reads.length ≤ (schedStep x h).1.reads.length ∧ x.1.segs.length ≤ (schedStep x h).1.segs.length := by
  obtain ⟨st, E, cnt, t⟩ := x
  simp only [schedStep]
  split
  · split <;> simp
  · simp

theorem fold_mono (L : List Nat) : ∀ (x : SchedState × Nat × Nat × Nat),
    x.1.reads.length ≤ (L.foldl schedStep x).1.reads.length ∧
      x.1.segs.length ≤ (L.foldl schedStep x).1.segs.length := by
  induction L with
  | nil => intro x; simp
  | cons h L ih =>
    intro x; rw [List.foldl_cons]
    have h1 := schedStep_mono x h; have h2 := ih (schedStep x h); omega

/-- The segment byte of a merge (`b % 16 = cnt`). -/
theorem segByte_merge (cnt t : Nat) (hc : cnt < 16) (ht : t ≤ 1) :
    cnt ||| 16 ||| 32 * t = cnt + 16 + 32 * t := by
  have e1 : cnt ||| 16 = 16 + cnt := by
    have := Nat.two_pow_add_eq_or_of_lt (i := 4) (b := cnt) (by omega) 1
    rw [Nat.or_comm]; simpa using this.symm
  have e2 : (16 + cnt) ||| 32 * t = 32 * t + (16 + cnt) := by
    have := Nat.two_pow_add_eq_or_of_lt (i := 5) (b := 16 + cnt) (by omega) t
    rw [Nat.or_comm]; simpa using this.symm
  rw [e1, e2]; omega

theorem segByte_end (cnt t : Nat) (hc : cnt < 16) (ht : t ≤ 1) : cnt ||| 32 * t = cnt + 32 * t := by
  have := Nat.two_pow_add_eq_or_of_lt (i := 5) (b := cnt) (by omega) t
  rw [Nat.or_comm]; simp at this; omega


/-! ## Stream writes -/

/-- Two dword stores at `WIT + 272 + P` (`P` 8-aligned) append a 16-byte item. -/
theorem stream_sd2 {u u' : MachineState} {l item : List Byte} {P : Nat} {w0 w1 : Word}
    (hP : P % 8 = 0) (hPb : P + 16 ≤ 2152) (hl : l.length = P) (hitem : item.length = 16)
    (hS : StreamOK u l)
    (hm : ∀ y : Nat, y < 2 ^ 64 → u'.getMem (BitVec.ofNat 64 y) =
      if y = 0x910 + P + 8 then w1 else if y = 0x910 + P then w0 else u.getMem (BitVec.ofNat 64 y))
    (hw0 : ∀ k < 8, extractByte w0 k = item.getD k 0)
    (hw1 : ∀ k < 8, extractByte w1 k = item.getD (8 + k) 0) :
    StreamOK u' (l ++ item) := by
  intro i hi
  rw [getByte_ofNat _ _ (by omega), hm _ (by omega)]
  by_cases h1 : (0x910 + i) / 8 * 8 = 0x910 + P + 8
  · rw [if_pos h1, hw1 _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
    congr 1; omega
  · rw [if_neg h1]
    by_cases h2 : (0x910 + i) / 8 * 8 = 0x910 + P
    · rw [if_pos h2, hw0 _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      congr 1; omega
    · rw [if_neg h2, ← getByte_ofNat _ _ (by omega), hS i hi]
      by_cases h3 : i < l.length
      · rw [List.getD_append _ _ _ _ h3]
      · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by simp; omega)]

/-- A byte store at `WIT + 272 + P` (`P` 8-aligned). -/
theorem stream_sb {u u' : MachineState} {l l' : List Byte} {P : Nat} {b : BitVec 8}
    (hP : P % 8 = 0) (hPb : P < 2152) (hS : StreamOK u l)
    (hm : ∀ y : Nat, y < 2 ^ 64 → u'.getMem (BitVec.ofNat 64 y) =
      if y = 0x910 + P then replaceByte (u.getMem (BitVec.ofNat 64 y)) 0 b else u.getMem (BitVec.ofNat 64 y))
    (hl' : ∀ i, l'.getD i 0 = if i = P then b else l.getD i 0) :
    StreamOK u' l' := by
  intro i hi
  rw [getByte_ofNat _ _ (by omega), hm _ (by omega), hl' i]
  by_cases h1 : (0x910 + i) / 8 * 8 = 0x910 + P
  · rw [if_pos h1, extractByte_replaceByte0 _ _ _ (by omega)]
    by_cases h2 : i = P
    · rw [if_pos (by omega), if_pos h2]
    · rw [if_neg (by omega), if_neg h2, ← getByte_ofNat _ _ (by omega), hS i hi]
  · rw [if_neg h1, if_neg (by omega), ← getByte_ofNat _ _ (by omega), hS i hi]

/-- The memory of a block result whose writes are all in `W` keeps the frame. -/
theorem frame_of_writes {t0 u u' : MachineState} {W : Nat → Prop} (hf : Frame t0 u W)
    (hm : ∀ y : Nat, y < 2 ^ 64 → ¬ W y → u'.getMem (BitVec.ofNat 64 y) = u.getMem (BitVec.ofNat 64 y)) :
    Frame t0 u' W := fun a ha hW => by rw [hm a ha hW, hf a ha hW]

end SigGolfCandidate.Expand
