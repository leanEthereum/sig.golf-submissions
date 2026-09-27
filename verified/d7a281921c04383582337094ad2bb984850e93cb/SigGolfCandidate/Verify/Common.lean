import SigGolfCandidate.Verify.Post
import SigGolfCandidate.Verify.Arith

/-! # Generic helper lemmas shared by all segment proofs -/

set_option linter.unusedSimpArgs false

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

macro "bvne" : tactic => `(tactic| (intro h; have h' := congrArg BitVec.toNat h; simp only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat] at h'; omega))

def LBOk (acc : List Val) (s : MachineState) : Prop :=
  ∀ j, j < acc.length → s.getMem (BitVec.ofNat 64 (0x360 + 16 * j)) = vw0 (acc.getD j []) ∧
    s.getMem (BitVec.ofNat 64 (0x368 + 16 * j)) = vw1 (acc.getD j [])


theorem vw0_slice (l : List Byte) (off : Nat) : vw0 (slice l off 16) = w64 (slice l off 8) := by
  simp [vw0, slice, List.take_take]

theorem vw1_slice (l : List Byte) (off : Nat) :
    vw1 (slice l off 16) = w64 (slice l (off + 8) 8) := by
  simp only [vw1, slice, List.drop_take, List.drop_drop]


theorem wit_word {wl : List Byte} {s : MachineState} (hW : WitOK wl s) (off : Nat)
    (h8 : off % 8 = 0) (hoff : off < 7760) :
    s.getMem (BitVec.ofNat 64 (0x800 + off)) = w64 (slice wl off 8) := by
  have := hW (off / 8) (by omega)
  rwa [show 8 * (off / 8) = off by omega] at this

theorem length_slice16 (l : List Byte) (off : Nat) (h : off + 16 ≤ l.length) :
    (slice l off 16).length = 16 := by
  simp [slice]; omega


theorem pcOf_add4 (n : Nat) : pcOf n + 4 = pcOf (n + 1) := by
  unfold pcOf
  rw [show (4 : Word) = BitVec.ofNat 64 4 from rfl, BitVec.ofNat_add_ofNat]
  congr 1


theorem memEval_cons_ne (s : MachineState) (k : Word) (v : E) (ws : SymMem) (A : Word)
    (h : A ≠ k) : memEval s ((⟨none, k⟩, v) :: ws) A = memEval s ws A := by
  rw [memEval_cons, if_neg (by simpa [Addr.eval] using h)]

theorem memEval_cons_eq (s : MachineState) (k : Word) (v : E) (ws : SymMem) (A : Word)
    (h : A = k) : memEval s ((⟨none, k⟩, v) :: ws) A = v.eval s := by
  rw [memEval_cons, if_pos (by simpa [Addr.eval] using h)]

/-! ## LB slots -/

theorem LBOk_append {acc : List Val} {s : MachineState} (h : LBOk acc s) (v : Val)
    (h0 : s.getMem (BitVec.ofNat 64 (0x360 + 16 * acc.length)) = vw0 v)
    (h1 : s.getMem (BitVec.ofNat 64 (0x368 + 16 * acc.length)) = vw1 v) : LBOk (acc ++ [v]) s := by
  intro j hj
  simp only [List.length_append, List.length_singleton] at hj
  by_cases hjl : j < acc.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hjl, ← List.getD_eq_getElem?_getD]
    exact h j hjl
  · have : j = acc.length := by omega
    subst this
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _), Nat.sub_self]
    exact ⟨h0, h1⟩

theorem LBOk_frame {acc : List Val} {s t : MachineState} (h : LBOk acc s)
    (hf : ∀ j, j < acc.length → t.getMem (BitVec.ofNat 64 (0x360 + 16 * j)) =
      s.getMem (BitVec.ofNat 64 (0x360 + 16 * j)) ∧ t.getMem (BitVec.ofNat 64 (0x368 + 16 * j)) =
      s.getMem (BitVec.ofNat 64 (0x368 + 16 * j))) : LBOk acc t := by
  intro j hj
  rw [(hf j hj).1, (hf j hj).2]; exact h j hj


theorem Known_writeHash {known : List (Reg × Word)} {s : MachineState} (h : KnownOK known s)
    (a : BitVec 256) : KnownOK known (writeHash s a) := by
  intro p hp; rw [writeHash_getReg]; exact h p hp


theorem known_get {known : List (Reg × Word)} {s : MachineState} (h : KnownOK known s) {r : Reg}
    {v : Word} (hm : (r, v) ∈ known) : s.getReg r = v := h _ hm

theorem KnownOK_append {k1 k2 : List (Reg × Word)} {s : MachineState} :
    KnownOK (k1 ++ k2) s ↔ KnownOK k1 s ∧ KnownOK k2 s := by
  simp only [KnownOK, List.mem_append]
  constructor
  · intro h; exact ⟨fun p hp => h p (Or.inl hp), fun p hp => h p (Or.inr hp)⟩
  · rintro ⟨h1, h2⟩ p (hp | hp); exacts [h1 p hp, h2 p hp]

end SigGolfCandidate.Verify
