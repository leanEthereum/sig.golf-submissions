import SigGolfCandidate.Sign.Sched
import SigGolfCandidate.Sign.Bytes

/-!
# The signature head: `rho | 15 secrets | 120 auth slots` as stored by `sign`

`head_bytes` : if `rho` is at `SIG`, the captured secrets at `SIG + 16 + 16 s`, the reads of the
schedule at `SIG + 256 + 16 r` and the remaining auth slots are zero, then the first 2176
signature bytes are `rho ++ (porsOpening vs levels secrets).flatten`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

theorem length_porsOpening (vs : List Nat) (levels : List (List Val)) (secrets : List Val)
    (hvs : vs.length = 15) (hR : (schedule vs).2.length ≤ 120) :
    (porsOpening vs levels secrets).length = 135 := by
  unfold porsOpening porsK porsM
  simp only [List.length_append, List.length_map, List.length_replicate, hvs]
  omega

theorem head_slots (t : MachineState) (rho : Val) (vs : List Nat) (levels : List (List Val)) (secrets : List Val)
    (hvs : vs.length = 15) (hR : (schedule vs).2.length ≤ 120)
    (hrho : t.readWords (BitVec.ofNat 64 0x3300) 2 = wordsOf rho)
    (hsec : ∀ s < 15, t.readWords (BitVec.ofNat 64 (0x3310 + 16 * s)) 2 = wordsOf (secrets.getD (vs.getD s 0) []))
    (hrd : ∀ r (hr : r < (schedule vs).2.length),
      t.readWords (BitVec.ofNat 64 (0x3400 + 16 * r)) 2 = wordsOf (readVal levels (schedule vs).2[r]))
    (hz : ∀ i, (schedule vs).2.length ≤ i → i < 120 → t.readWords (BitVec.ofNat 64 (0x3400 + 16 * i)) 2 = [0, 0]) :
    Slots t 0x3300 (rho :: porsOpening vs levels secrets) := by
  apply Slots.cons hrho
  unfold porsOpening porsK porsM
  refine Slots.append (Slots.append ?_ ?_) ?_
  · intro i hi
    simp only [List.length_map] at hi
    rw [show 0x3300 + 16 + 16 * i = 0x3310 + 16 * i by ring, List.getElem_map, hsec i (by omega),
      List.getD_eq_getElem _ _ hi]
  · intro r hr
    simp only [List.length_map] at hr
    rw [List.length_map, hvs, show 0x3300 + 16 + 16 * 15 + 16 * r = 0x3400 + 16 * r by ring, List.getElem_map,
      hrd r hr]
    rfl
  · intro i hi
    simp only [List.length_replicate, List.length_append, List.length_map, hvs] at hi
    rw [List.getElem_replicate]
    simp only [List.length_append, List.length_map, hvs]
    rw [show 0x3300 + 16 + 16 * (15 + (schedule vs).2.length) + 16 * i =
        0x3400 + 16 * ((schedule vs).2.length + i) by ring, hz _ (by omega) (by omega),
      show (16 : Nat) = 8 * 2 from rfl, wordsOf_zeros]
    rfl

theorem length_porsOpening_vals (vs : List Nat) (levels : List (List Val)) (secrets : List Val)
    (hsecs : ∀ v ∈ secrets, v.length = 16) (hvsv : ∀ x ∈ vs, x < secrets.length)
    (hlv : ∀ hj ∈ (schedule vs).2, (readVal levels hj).length = 16) :
    ∀ v ∈ porsOpening vs levels secrets, v.length = 16 := by
  intro v hv
  unfold porsOpening at hv
  simp only [List.mem_append, List.mem_map, List.mem_replicate] at hv
  rcases hv with (⟨x, hx, rfl⟩ | ⟨hj, hhj, rfl⟩) | ⟨-, rfl⟩
  · rw [List.getD_eq_getElem _ _ (hvsv x hx)]; exact hsecs _ (List.getElem_mem _)
  · exact hlv hj hhj
  · simp [zeros]

/-- **The signature head** (2176 bytes). -/
theorem head_bytes (t : MachineState) (rho : Val) (hrho16 : rho.length = 16) (vs : List Nat)
    (levels : List (List Val)) (secrets : List Val)
    (hvs : vs.length = 15) (hR : (schedule vs).2.length ≤ 120)
    (hvals : ∀ v ∈ porsOpening vs levels secrets, v.length = 16)
    (hs : Slots t 0x3300 (rho :: porsOpening vs levels secrets)) :
    bytesAt t 0x3300 2176 = rho ++ (porsOpening vs levels secrets).flatten := by
  have hlen := length_porsOpening vs levels secrets hvs hR
  have hv : ∀ v ∈ rho :: porsOpening vs levels secrets, v.length = 16 := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | hv; exact hrho16; exact hvals v hv
  have hw := readWords_slots t 0x3300 _ hs
  rw [← wordsOf_flatten _ hv] at hw
  rw [show (2176 : Nat) = 8 * (2 * (rho :: porsOpening vs levels secrets).length) by simp [hlen]]
  refine (bytesAt_of_readWords t _ _ _ (by norm_num) (by simp [hlen]) ?_ hw).trans (by simp)
  rw [length_flatten_vals _ hv]; simp [hlen]

end SigGolfCandidate.Sign
