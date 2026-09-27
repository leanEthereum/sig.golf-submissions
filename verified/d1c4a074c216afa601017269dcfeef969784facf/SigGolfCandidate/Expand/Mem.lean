import SigGolfCandidate.Rv
import SigGolfCandidate.Ref

/-!
# Byte-level memory lemmas for the organizer machine (used by `expand` and `keygen`)

* `Steps.micro` : one ordinary step from a `classify`d instruction.
* `getByte_copyWord` : bytes after an `LWU`+`SW` word copy.
* `getByte_setMem`, `getByte_writeBytesAsWords` (the loader), `extractByte_bytesToWordLE`.
* `readBuffer_eq` : `readBuffer` as `leNat` of the bytes.
-/

namespace SigGolfCandidate.Mem
open RiscvZkvm.Rv64 SigGolf SigGolf.Riscv SigGolfCandidate.Rv SigGolfCandidate.Ref


theorem ofNat_toNat_lt {a : Nat} (h : a < 2 ^ 64) : (BitVec.ofNat 64 a).toNat = a := by
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem extractByte_or8 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (j : Nat) (hj : j < 8) :
    extractByte (b0.zeroExtend 64 ||| (b1.zeroExtend 64 <<< (8 : Word)) ||| (b2.zeroExtend 64 <<< (16 : Word)) |||
      (b3.zeroExtend 64 <<< (24 : Word)) ||| (b4.zeroExtend 64 <<< (32 : Word)) ||| (b5.zeroExtend 64 <<< (40 : Word)) |||
      (b6.zeroExtend 64 <<< (48 : Word)) ||| (b7.zeroExtend 64 <<< (56 : Word))) j = [b0, b1, b2, b3, b4, b5, b6, b7].getD j 0 := by
  interval_cases j <;> (simp only [extractByte]; ext i hi; interval_cases i <;> simp)

theorem extractByte_bytesToWordLE (bs : List (BitVec 8)) (j : Nat) (hj : j < 8) :
    extractByte (bytesToWordLE bs) j = bs.getD j 0 := by
  simp only [bytesToWordLE]
  rw [extractByte_or8 _ _ _ _ _ _ _ _ j hj]
  simp only [List.getD_eq_getElem?_getD]
  interval_cases j <;> rfl

theorem alignToDword_ofNat_eq {x y : Nat} (hx : x < 2 ^ 64) (hy : y < 2 ^ 64) :
    alignToDword (BitVec.ofNat 64 x) = alignToDword (BitVec.ofNat 64 y) ↔ x / 8 = y / 8 := by
  rw [← BitVec.toNat_inj, alignToDword_toNat, alignToDword_toNat, ofNat_toNat_lt hx,
    ofNat_toNat_lt hy]
  omega

theorem byteOffset_ofNat {x : Nat} (hx : x < 2 ^ 64) : byteOffset (BitVec.ofNat 64 x) = x % 8 := by
  rw [byteOffset_eq, ofNat_toNat_lt hx]

theorem alignToDword_ofNat_aligned {x : Nat} (hx : x < 2 ^ 64) (h8 : x % 8 = 0) :
    alignToDword (BitVec.ofNat 64 x) = BitVec.ofNat 64 x := by
  apply BitVec.eq_of_toNat_eq
  rw [alignToDword_toNat, ofNat_toNat_lt hx]; omega

theorem getByte_setMem (s : MachineState) (B a : Nat) (w : Word) (hB : B < 2 ^ 64) (h8 : B % 8 = 0)
    (ha : a < 2 ^ 64) :
    (s.setMem (BitVec.ofNat 64 B) w).getByte (BitVec.ofNat 64 a) =
      if a / 8 = B / 8 then extractByte w (a % 8) else s.getByte (BitVec.ofNat 64 a) := by
  simp only [MachineState.getByte, MachineState.setMem, MachineState.getMem]
  rw [byteOffset_ofNat ha]
  by_cases h : a / 8 = B / 8
  · have := (alignToDword_ofNat_eq ha hB).mpr h
    rw [alignToDword_ofNat_aligned hB h8] at this
    simp [this, h]
  · have : ¬ alignToDword (BitVec.ofNat 64 a) = BitVec.ofNat 64 B := by
      rw [← alignToDword_ofNat_aligned hB h8, alignToDword_ofNat_eq ha hB]; exact h
    simp [this, h]

theorem getByte_writeBytesAsWords (l : List (BitVec 8)) : ∀ (s : MachineState) (base a : Nat),
    base % 8 = 0 → base + 8 * ((l.length + 7) / 8) < 2 ^ 64 → a < 2 ^ 64 →
    (s.writeBytesAsWords (BitVec.ofNat 64 base) l).getByte (BitVec.ofNat 64 a) =
      if base ≤ a ∧ a < base + 8 * ((l.length + 7) / 8) then l.getD (a - base) 0
      else s.getByte (BitVec.ofNat 64 a) := by
  induction l using WellFounded.induction (r := fun x y : List (BitVec 8) => x.length < y.length) with
  | hwf => exact (measure List.length).wf
  | h l ih =>
    intro s base a h8 hlen ha
    match l with
    | [] => simp
    | b :: bs =>
      unfold MachineState.writeBytesAsWords
      simp only
      have hadd : BitVec.ofNat 64 base + 8 = BitVec.ofNat 64 (base + 8) := by
        apply BitVec.eq_of_toNat_eq; simp
      simp only [List.length_cons] at hlen
      rw [hadd, ih _ (by simp only [List.length_drop, List.length_cons]; omega) _ (base + 8) a (by omega) (by simp only [List.length_drop, List.length_cons]; omega) ha,
        getByte_setMem _ _ _ _ (by omega) h8 ha]
      simp only [List.length_drop, List.length_cons]
      by_cases h1 : base ≤ a ∧ a < base + 8
      · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega),
          extractByte_bytesToWordLE _ _ (by omega)]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take]
        rw [if_pos (by omega), show a % 8 = a - base by omega]
      · by_cases h2 : base + 8 ≤ a ∧ a < base + 8 + 8 * ((bs.length + 1 - 8 + 7) / 8)
        · rw [if_pos h2, if_pos (by omega)]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_drop]
          congr 2; omega
        · rw [if_neg h2, if_neg (by omega), if_neg (by omega)]


theorem Steps.micro {image : Image} {pc : Word} {w : BitVec 32} {ws : List (BitVec 32)}
    {s t u : MachineState} (m : Micro) {k c : Nat}
    (hc : CodeAt image pc (w :: ws)) (hpc : s.pc = pc)
    (hd : ∃ i, decodeInstruction w = some i ∧ classify i = some m ∧ instructionCycles i = 1)
    (hex : m.exec s = some t) (tail : Steps image t k c u) : Steps image s (k + 1) (1 + c) u := by
  obtain ⟨i, h1, h2, h3⟩ := hd
  have := Steps.step (hc.fetch s hpc ▸ h1) ((classify_sound h2 s).trans hex) tail
  rwa [h3] at this

theorem Micro.exec_load {s : MachineState} {k : LoadKind} {rd rs : Reg} {off : Word}
    (h : accessValid (s.getReg rs + off) k.width = true) :
    (Micro.load k rd rs off).exec s = some ((s.setReg rd (k.read s (s.getReg rs + off))).setPC (s.pc + 4)) := by
  simp [Micro.exec, h]

theorem Micro.exec_store {s : MachineState} {k : StoreKind} {rs1 rs2 : Reg} {off : Word}
    (h : accessValid (s.getReg rs1 + off) k.width = true) :
    (Micro.store k rs1 rs2 off).exec s = some ((k.write s (s.getReg rs1 + off) (s.getReg rs2)).setPC (s.pc + 4)) := by
  simp [Micro.exec, h]

theorem getReg_setReg' (s : MachineState) (r r' : Reg) (v : Word) :
    (s.setReg r v).getReg r' = if r' = r ∧ r ≠ .x0 then v else s.getReg r' := by
  cases r <;> cases r' <;> rfl

theorem getByte_setReg (s : MachineState) (r : Reg) (v : Word) (a : Word) :
    (s.setReg r v).getByte a = s.getByte a := by simp [MachineState.getByte]
theorem getByte_setPC (s : MachineState) (v : Word) (a : Word) :
    (s.setPC v).getByte a = s.getByte a := by simp [MachineState.getByte]

@[simp] theorem pc_setPC (s : MachineState) (v : Word) : (s.setPC v).pc = v := rfl

theorem extractByte_rw32 (w w' : Word) (p q j : Nat) (hp : p < 2) (hq : q < 2) (hj : j < 8) :
    extractByte (replaceWord32 w p (extractWord32 w' q)) j =
      if j / 4 = p then extractByte w' (4 * q + j % 4) else extractByte w j := by
  obtain rfl | rfl : p = 0 ∨ p = 1 := by omega
  all_goals obtain rfl | rfl : q = 0 ∨ q = 1 := by omega
  all_goals (interval_cases j <;> (simp only [extractByte, replaceWord32, extractWord32]; ext i hi; interval_cases i <;> simp))

theorem getByte_copyWord (s t : MachineState) (hts : ∀ x, t.getMem x = s.getMem x) (src dst a : Nat) (hs : src % 4 = 0) (hd : dst % 4 = 0)
    (hsb : src < 2 ^ 60) (hdb : dst < 2 ^ 60) (ha : a < 2 ^ 64) :
    (t.setWord32 (BitVec.ofNat 64 dst) (s.getWord32 (BitVec.ofNat 64 src))).getByte (BitVec.ofNat 64 a) =
      if dst ≤ a ∧ a < dst + 4 then s.getByte (BitVec.ofNat 64 (a - dst + src))
      else s.getByte (BitVec.ofNat 64 a) := by
  simp only [MachineState.getByte, MachineState.setWord32, MachineState.getWord32,
    MachineState.setMem, hts]
  simp only [MachineState.getMem]
  have hA : ∀ x y : Nat, x < 2 ^ 64 → y < 2 ^ 64 →
      (alignToDword (BitVec.ofNat 64 x) = alignToDword (BitVec.ofNat 64 y) ↔ x / 8 = y / 8) := by
    intro x y hx hy
    rw [← BitVec.toNat_inj, alignToDword_toNat, alignToDword_toNat, ofNat_toNat_lt hx,
      ofNat_toNat_lt hy]
    omega
  have hO : ∀ x : Nat, x < 2 ^ 64 → byteOffset (BitVec.ofNat 64 x) = x % 8 := by
    intro x hx; rw [byteOffset_eq, ofNat_toNat_lt hx]
  rw [hO a ha, hO dst (by omega), hO src (by omega)]
  by_cases h1 : a / 8 = dst / 8
  · have e1 := (hA a dst ha (by omega)).mpr h1
    simp only [e1, beq_self_eq_true, if_true]
    rw [extractByte_rw32 _ _ (dst % 8 / 4) (src % 8 / 4) (a % 8) (by omega) (by omega) (by omega)]
    by_cases h2 : dst ≤ a ∧ a < dst + 4
    · rw [if_pos (by omega), if_pos h2, hO _ (by omega)]
      have e2 := (hA (a - dst + src) src (by omega) (by omega)).mpr (by omega)
      rw [e2]; congr 1; omega
    · rw [if_neg (by omega), if_neg h2]
  · have e1 : ¬ alignToDword (BitVec.ofNat 64 a) = alignToDword (BitVec.ofNat 64 dst) :=
      fun h => h1 ((hA a dst ha (by omega)).mp h)
    simp only [beq_iff_eq, e1, if_false]
    rw [if_neg (by omega)]
    exact congrArg (extractByte · _) (hts _)

@[simp] theorem getReg_setWord32 (s : MachineState) (a : Word) (v : BitVec 32) (r : Reg) :
    (s.setWord32 a v).getReg r = s.getReg r := by cases r <;> rfl



theorem leNat_append_single (l : List Byte) (b : Byte) :
    leNat (l ++ [b]) = leNat l + 256 ^ l.length * b.toNat := by
  induction l with
  | nil => simp [leNat]
  | cons x xs ih => simp [leNat, ih, pow_succ]; ring

theorem foldl_bytes_eq_leNat (g : Nat → Byte) (n : Nat) :
    (List.range n).foldl (fun acc i => acc + (g i).toNat * 2 ^ (8 * i)) 0 =
      leNat ((List.range n).map g) := by
  induction n with
  | zero => simp [leNat]
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih, List.map_append, List.map_singleton, leNat_append_single]
    simp only [List.foldl_cons, List.foldl_nil, List.length_map, List.length_range]
    rw [pow_mul]; norm_num; ring

theorem readBuffer_eq (t : MachineState) (addr n : Nat) :
    readBuffer t addr n =
      BitVec.ofNat (8 * n) (leNat ((List.range n).map fun i => t.getByte (BitVec.ofNat 64 (addr + i)))) := by
  unfold readBuffer
  rw [foldl_bytes_eq_leNat (fun i => t.getByte (BitVec.ofNat 64 (addr + i)))]

theorem getD_bytes {n : Nat} (x : Bytes n) (j : Nat) (hj : j < n) :
    (SigGolf.bytes x).getD j 0 = x.extractLsb' (8 * j) 8 := by
  simp [SigGolf.bytes, hj]

end SigGolfCandidate.Mem
