import SigGolfCandidate.Sign.Head
import SigGolfCandidate.Sign.Layer
import SigGolfCandidate.Sign.Pack

/-!
# `sign`: layer-loop entry (296 .. 315) and the signature's layer bytes

* `layer_entry` : the layer constants (`LIM = 2^22`, the SWAR masks, `LAY = 4`, `SIGL` = stage 4).
* `stage_bytes`, `layers_bytes` : the packed layer region `SIG + 2176 ..` from the stages.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem layer_entry (S cache : List Byte) (idx : Nat) (hidx : idx < 2 ^ 34) (M : Val) (hM : M.length = 16)
    (t : MachineState) (tpc : t.pc = pcOf 296) (t5 : t.getReg .x5 = 0)
    (t22 : t.getReg .x22 = BitVec.ofNat 64 idx) (heb : t.readWords (BitVec.ofNat 64 0x120) 2 = wordsOf M)
    (hst : Statics S t) (hrg : RegionOk cache t) :
    ∃ t', Steps image t 20 20 t' ∧ LayHead S cache idx 4 M t' ∧ (∀ z, t'.getMem z = t.getMem z) ∧
      RegsEq t t' [.x7, .x8, .x18, .x26, .x27] := by
  have hs := symRun_sound blk296 codeAt_296 t tpc (by simp only [blk296.res, rv_simp])
  have hc : blk296.res.cycles = 20 := rfl
  have hk : blk296.res.steps = 20 := rfl
  rw [hc, hk] at hs
  set t' := blk296.res.toState t with ht'
  have m : ∀ z, t'.getMem z = t.getMem z := fun z => by
    rw [ht', Result.toState_getMem, show blk296.res.st.mem = [] from rfl, memEval_nil]
  have r : RegsEq t t' [.x7, .x8, .x18, .x26, .x27] := by
    intro q hq; rw [ht', Result.toState_getReg]
    cases q <;> first | exact absurd (by decide) hq | rfl
  have f : Frame t t' (fun _ => False) := fun a _ _ => m _
  refine ⟨t', hs, ⟨by norm_num, hidx, hM, by simp only [ht', blk296.res, rv_simp],
    by rw [r.get .x5, t5], by simp only [ht', blk296.res, rv_simp]; rfl, by simp only [ht', blk296.res, rv_simp],
    by simp only [ht', blk296.res, rv_simp], by rw [r.get .x22, t22],
    by simp only [ht', blk296.res, rv_simp], by simp only [ht', blk296.res, rv_simp],
    by rw [readWords_congr t t' _ 2 (fun k _ => m _), heb],
    hst.frame f (fun _ _ h => h), hrg.frame f (fun _ _ h => h)⟩, m, r⟩

theorem pack_full : (packTab.drop 0).take 491 = packTab := by
  rw [List.drop_zero]; exact List.take_of_length_le (by rw [packTab_length])

theorem le32_bytes (t : MachineState) (a c : Nat) (ha : a % 8 = 0) (hb : a + 8 < 2 ^ 64)
    (hc : c < 2 ^ 32) (h : t.getMem (BitVec.ofNat 64 a) = BitVec.ofNat 64 c) :
    bytesAt t a 4 = le32 c := by
  apply List.ext_getElem (by simp [le32])
  intro i h1 h2
  simp only [length_bytesAt] at h1
  simp only [bytesAt, List.getElem_map, List.getElem_range, le32, leBytes]
  rw [getByte_aligned' t a i ha (by omega) hb, h]
  apply BitVec.eq_of_toNat_eq
  rw [extractByte_toNat', byte_toNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega),
    show (256 : Nat) ^ i = 2 ^ (8 * i) by rw [Nat.pow_mul]]

theorem stage_bytes (t : MachineState) (l : Nat) (hl : l < 5) (ls : LayerSig) (h : StageAt t l ls) :
    bytesAt t (0x900 + 856 * l) 4 ++ bytesAt t (0x900 + 856 * l + 8) (672 + 16 * height l) =
      le32 ls.1 ++ ls.2.1.flatten ++ ls.2.2.flatten := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hh := height_le l (by omega)
  rw [le32_bytes t _ ls.1 (by omega) (by omega) (by omega) h1, List.append_assoc]
  congr 1
  have hv : ∀ v ∈ ls.2.1 ++ ls.2.2, v.length = 16 := by
    intro v hv; rcases List.mem_append.mp hv with hv | hv; exact h4 v hv; exact h7 v hv
  have hsl : Slots t (0x900 + 856 * l + 8) (ls.2.1 ++ ls.2.2) :=
    Slots.append h5 (by rw [h3, show 0x900 + 856 * l + 8 + 16 * 42 = 0x900 + 856 * l + 680 by ring]; exact h8)
  have hw := readWords_slots t _ _ hsl
  rw [← wordsOf_flatten _ hv, List.flatten_append] at hw
  have hlen : (ls.2.1 ++ ls.2.2).length = 42 + height l := by simp [h3, h6]
  rw [show 672 + 16 * height l = 8 * (2 * (ls.2.1 ++ ls.2.2).length) by rw [hlen]; ring]
  refine bytesAt_of_readWords t _ _ _ (by omega) (by rw [hlen]; omega) ?_ hw
  rw [List.length_append, length_flatten_vals _ h4, length_flatten_vals _ h7, hlen, h3, h6]; ring

theorem flatMap_range_eq {β γ : Type} (xs : List β) (g : Nat → List γ) (f : β → List γ)
    (h : ∀ l (hl : l < xs.length), g l = f xs[l]) :
    (List.range xs.length).flatMap g = (xs.map f).flatten := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.length_append, List.length_singleton, List.range_succ, List.flatMap_append,
      ih (fun l hl => by rw [h l (by simp; omega), List.getElem_append_left hl]),
      List.map_append, List.flatten_append]
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil]
    rw [h xs.length (by simp), List.getElem_append_right (le_refl _)]
    simp

set_option maxRecDepth 100000 in
/-- The signature bytes after the pack. -/
theorem final_bytes (t4 : MachineState) (rho : Val) (fts : List Val) (lays : List LayerSig)
    (hhead : bytesAt t4 0x3300 2176 = rho ++ fts.flatten)
    (hll : lays.length = 5) (hst : ∀ l (hl : l < lays.length), StageAt t4 l lays[l]) (t5 : MachineState)
    (hw5 : t5.readWords (BitVec.ofNat 64 (0x3300 + 2176)) 491 = packTab.map (packDW t4))
    (hf5 : Frame t4 t5 (fun x => packD ≤ x ∧ x < packD + 8 * 491)) :
    bytesAt t5 0x3300 6100 = serialize rho fts lays := by
  rw [show (6100 : Nat) = 2176 + 3924 from rfl, bytesAt_add, pack_layers t4 t5 hw5]
  unfold serialize
  congr 1
  · rw [← hhead]
    unfold bytesAt; apply List.map_congr_left; intro i hi
    simp only [List.mem_range] at hi
    simp only [MachineState.getByte]
    have h8 : alignToDword (BitVec.ofNat 64 (0x3300 + i)) = BitVec.ofNat 64 ((0x3300 + i) / 8 * 8) := by
      rw [← alignToDword_ofNat_aligned (x := (0x3300 + i) / 8 * 8) (by omega) (by omega)]
      exact (alignToDword_ofNat_eq (by omega) (by omega)).mpr (by omega)
    rw [h8, hf5.getMem (by omega) (by simp only [packD]; omega)]
  · rw [← hll]
    refine flatMap_range_eq lays _ _ (fun l hl => ?_)
    rw [List.append_assoc]
    exact (stage_bytes t4 l (by omega) lays[l] (hst l hl)).trans (by rw [List.append_assoc])

end SigGolfCandidate.Sign
