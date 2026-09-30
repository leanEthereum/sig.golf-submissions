import SigGolfCandidate.Sign.PackData
import SigGolfCandidate.Sign.Inv
import SigGolfCandidate.Expand.Mem

/-!
# The pack, chunk by chunk

The pack (instructions 614 .. 3394) is split into chunks (`PackC*.lean`, one symbolic block and
one file each, to keep the kernel's memory per file small). `PackStep a b f c n` says: from pc
`a`, `n` straight-line steps reach pc `b`, write the signature dwords `f .. f + c - 1`
(`packD + 8 j`) as `packDW t` of the table entries, and nothing else. `packStep_of` builds it
from a symbolic block, `PackStep.comp` chains chunks (the sources, below `0x3300`, are not
written by the pack).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Mem

/-- Destination of the pack: `SIG + 2480`. -/
abbrev packD : Nat := 0x3300 + 2176

/-- All sources lie below the signature buffer (checked by the kernel). -/
theorem packTab_src_ok : packTab.all (fun e => decide (e.2.1 < 0x3300 ∧ e.2.2 < 0x3300)) = true := by
  decide +kernel

theorem packTab_src (e : Nat × Nat × Nat) (he : e ∈ packTab) : e.2.1 < 0x3300 ∧ e.2.2 < 0x3300 := by
  have := List.all_eq_true.mp packTab_src_ok e he
  simpa using this

def PackStep (a b f c n : Nat) : Prop :=
  ∀ t : MachineState, t.pc = pcOf a → ∃ u, Steps image t n n u ∧ u.pc = pcOf b ∧
    u.readWords (BitVec.ofNat 64 (packD + 8 * f)) c = ((packTab.drop f).take c).map (packDW t) ∧
    Frame t u (fun x => packD + 8 * f ≤ x ∧ x < packD + 8 * (f + c))

theorem packStep_of {code : List (BitVec 32)} {a b f c n fuel : Nat} {r : Result}
    (hrun : symRun { noAlias := true } code (pcOf a) fuel = some r) (hcode : CodeAt image (pcOf a) code)
    (hobl : r.st.obl = []) (hpc : ∀ t : MachineState, (r.toState t).pc = pcOf b)
    (hs : r.steps = n) (hc : r.cycles = n)
    (hw : ∀ t : MachineState, (r.toState t).readWords (BitVec.ofNat 64 (packD + 8 * f)) c =
      ((packTab.drop f).take c).map (packDW t))
    (haddr : ∀ t : MachineState, r.st.mem.map (fun p => p.1.eval t) =
      ((List.range c).map (fun i => BitVec.ofNat 64 (packD + 8 * f + 8 * i))).reverse)
    (hb : packD + 8 * (f + c) < 2 ^ 64) : PackStep a b f c n := by
  intro t ht
  have hS := symRun_sound hrun hcode t ht (by simp only [Result.obligs, hobl, Oblig.all])
  rw [hs, hc] at hS
  refine ⟨_, hS, hpc t, hw t, frame_toState r t _ ?_⟩
  intro x hx hW p hp heq
  have hm : p.1.eval t ∈ r.st.mem.map (fun p => p.1.eval t) := List.mem_map_of_mem hp
  rw [haddr t, List.mem_reverse, List.mem_map] at hm
  obtain ⟨i, hi, hi'⟩ := hm
  rw [List.mem_range] at hi
  rw [← hi'] at heq
  have := congrArg BitVec.toNat heq
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt (by omega)] at this
  omega

theorem getMem_align_frame {t u : MachineState} {W : Nat → Prop} (h : Frame t u W) (x : Nat)
    (hx : x < 2 ^ 64) (hW : ¬ W (x / 8 * 8)) :
    u.getMem (alignToDword (BitVec.ofNat 64 x)) = t.getMem (alignToDword (BitVec.ofNat 64 x)) := by
  have : alignToDword (BitVec.ofNat 64 x) = BitVec.ofNat 64 (x / 8 * 8) := by
    apply BitVec.eq_of_toNat_eq
    rw [alignToDword_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := x) hx,
      Nat.mod_eq_of_lt (a := x / 8 * 8) (by omega)]
    omega
  rw [this]; exact h.getMem (by omega) hW

theorem packDW_frame {t u : MachineState} {W : Nat → Prop} (h : Frame t u W)
    (hW : ∀ x, x < 0x3300 → ¬ W x) (e : Nat × Nat × Nat) (he : e ∈ packTab) :
    packDW u e = packDW t e := by
  obtain ⟨h1, h2⟩ := packTab_src e he
  obtain ⟨k, lo, hi⟩ := e
  simp only at h1 h2
  have g1 := getMem_align_frame h lo (by omega) (hW _ (by omega))
  have g2 := getMem_align_frame h hi (by omega) (hW _ (by omega))
  rcases k with _ | _ | k
  · have : alignToDword (BitVec.ofNat 64 lo) = BitVec.ofNat 64 (lo / 8 * 8) := by
      apply BitVec.eq_of_toNat_eq
      rw [alignToDword_toNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := lo) (by omega),
        Nat.mod_eq_of_lt (a := lo / 8 * 8) (by omega)]
      omega
    simp only [packDW]
    by_cases h8 : lo % 8 = 0
    · rw [show lo = lo / 8 * 8 by omega]; exact h.getMem (by omega) (hW _ (by omega))
    · exact h.getMem (by omega) (hW _ (by omega))
  · simp only [packDW, g1, g2]
  · simp only [packDW, g1]

theorem PackStep.comp {a b d f c c' n n' : Nat} (h1 : PackStep a b f c n)
    (h2 : PackStep b d (f + c) c' n') (hb : packD + 8 * (f + c + c') < 2 ^ 64) :
    PackStep a d f (c + c') (n + n') := by
  intro t ht
  obtain ⟨u, hs1, pc1, w1, f1⟩ := h1 t ht
  obtain ⟨v, hs2, pc2, w2, f2⟩ := h2 u pc1
  refine ⟨v, hs1.trans hs2, pc2, ?_, f1.trans' f2 (fun x hx => by omega)⟩
  rw [readWords_ofNat_add, List.take_add, List.map_append, List.drop_drop,
    show packD + 8 * f + 8 * c = packD + 8 * (f + c) by ring, w2,
    f2.readWords _ _ (by omega) (fun i hi => by omega), w1]
  congr 1
  apply List.map_congr_left
  intro e he
  exact packDW_frame f1 (fun x hx h => by simp only [packD] at h; omega)
    e (List.mem_of_mem_drop (List.mem_of_mem_take he))

end SigGolfCandidate.Sign
