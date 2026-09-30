import SigGolfCandidate.Sign.Enc
import SigGolfCandidate.Sign.TreeStep
import SigGolfCandidate.Sign.Pair

/-!
# `sign`, layer 0 (the cached top tree): `top_layer` (instructions 572 .. 638)

* `topChains_sim` : chains `i = 0 .. 41` of leaf `e` up to position `x_i` only (`chainTo`); chain
  value `i` staged at `STG + 8 + 16 i`.
* `topPath_sim` : the path from the cache: for `l = 0 .. 10`, `mask(l, s)` with
  `s = (e >> l) ^ 1`, path node `cache node (l, s) xor mask` staged at `STG + 680 + 16 l`.
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref

/-! ## Bytewise XOR as dwords -/

theorem xor_byte_add (x y A B : Nat) (hx : x < 256) (hy : y < 256) :
    (x + 256 * A) ^^^ (y + 256 * B) = (x ^^^ y) + 256 * (A ^^^ B) := by
  have hxy : x ^^^ y < 2 ^ 8 := Nat.xor_lt_two_pow (by omega) (by omega)
  rw [show x + 256 * A = 2 ^ 8 * A + x by ring, show y + 256 * B = 2 ^ 8 * B + y by ring,
    show (x ^^^ y) + 256 * (A ^^^ B) = 2 ^ 8 * (A ^^^ B) + (x ^^^ y) by ring]
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_xor, Nat.testBit_two_pow_mul_add _ (by omega : x < 2 ^ 8),
    Nat.testBit_two_pow_mul_add _ (by omega : y < 2 ^ 8), Nat.testBit_two_pow_mul_add _ hxy]
  split <;> simp [Nat.testBit_xor]

theorem leNat_xorBytes : ∀ (a b : List Byte), a.length = b.length →
    leNat (xorBytes a b) = leNat a ^^^ leNat b
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: as, y :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    have ih := leNat_xorBytes as bs h
    simp only [xorBytes, List.zipWith_cons_cons, leNat] at ih ⊢
    rw [ih, BitVec.toNat_xor, xor_byte_add _ _ _ _ x.isLt y.isLt]

theorem length_xorBytes' (a b : List Byte) (h : a.length = b.length) :
    (xorBytes a b).length = a.length := by
  simp [xorBytes, h]

theorem xorBytes_append (a1 a2 b1 b2 : List Byte) (h : a1.length = b1.length) :
    xorBytes (a1 ++ a2) (b1 ++ b2) = xorBytes a1 b1 ++ xorBytes a2 b2 := by
  simp [xorBytes, List.zipWith_append h]

theorem wordsOf_xorBytes (u v : Val) (hu : u.length = 16) (hv : v.length = 16) (u0 u1 v0 v1 : Word)
    (hwu : wordsOf u = [u0, u1]) (hwv : wordsOf v = [v0, v1]) :
    wordsOf (xorBytes u v) = [u0 ^^^ v0, u1 ^^^ v1] := by
  have su : u = u.take 8 ++ u.drop 8 := (List.take_append_drop 8 u).symm
  have sv : v = v.take 8 ++ v.drop 8 := (List.take_append_drop 8 v).symm
  rw [su, wordsOf_append _ _ (by simp; omega), wordsOf_eight _ (by simp; omega),
    wordsOf_eight _ (by simp; omega)] at hwu
  rw [sv, wordsOf_append _ _ (by simp; omega), wordsOf_eight _ (by simp; omega),
    wordsOf_eight _ (by simp; omega)] at hwv
  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true] at hwu hwv
  rw [su, sv, xorBytes_append _ _ _ _ (by simp; omega),
    wordsOf_append _ _ (by rw [length_xorBytes' _ _ (by simp; omega)]; simp; omega),
    wordsOf_eight _ (by rw [length_xorBytes' _ _ (by simp; omega)]; simp; omega),
    wordsOf_eight _ (by rw [length_xorBytes' _ _ (by simp; omega)]; simp; omega),
    leNat_xorBytes _ _ (by simp; omega), leNat_xorBytes _ _ (by simp; omega),
    BitVec.ofNat_xor, BitVec.ofNat_xor, hwu.1, hwu.2, hwv.1, hwv.2]
  rfl

/-! ## The context at `top_layer` -/

/-- Facts at `top_layer` (instruction 572): layer 0, leaf `e`, digits `x`. -/
structure TopCtx (S cache : List Byte) (x : List Nat) (tau e : Nat) (t : MachineState) : Prop where
  htau : tau < 2 ^ 30
  he : e < 2048
  hx : ∀ i, x.getD i 0 < 8
  x5 : t.getReg .x5 = 0
  x13 : t.getReg .x13 = BitVec.ofNat 64 e
  x18 : t.getReg .x18 = BitVec.ofNat 64 0x900
  x31 : t.getReg .x31 = BitVec.ofNat 64 (tau + 2 ^ 32 * e)
  dig : ∀ i < 42, t.getMem (BitVec.ofNat 64 (0x780 + 8 * i)) = BitVec.ofNat 64 (x.getD i 0)
  pbP : t.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cbP : t.readWords (BitVec.ofNat 64 0xD0) 2 = [0, 0]
  node : ∀ l j, l < 11 → j < 2 ^ (11 - l) →
    t.readWords (BitVec.ofNat 64 (0x44A0 + cacheNodeOff l j)) 2 = wordsOf (cacheNode cache l j)
  nodeLen : ∀ l j, l < 11 → j < 2 ^ (11 - l) → (cacheNode cache l j).length = 16

/-- Addresses written by the top layer. -/
def topW (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ (0xE0 ≤ a ∧ a < 0x110) ∨ (0x140 ≤ a ∧ a < 0x160) ∨
    (0x908 ≤ a ∧ a < 0x908 + 672) ∨ (0xBA8 ≤ a ∧ a < 0xBA8 + 176)

theorem topN_eq (l : Nat) (hl : l ≤ 11) : topN l = 4096 - 2 ^ (12 - l) := by
  interval_cases l <;> rfl

theorem topN_succ (l : Nat) (hl : l < 11) : topN (l + 1) = topN l + 2 ^ (11 - l) := by
  interval_cases l <;> rfl

theorem topN_add_lt (l j : Nat) (hl : l < 11) (hj : j < 2 ^ (11 - l)) : topN l + j < 4094 := by
  rw [topN_eq l (by omega)]
  interval_cases l <;> norm_num at hj ⊢ <;> omega

theorem cacheNodeOff_lt (l j : Nat) (hl : l < 11) (hj : j < 2 ^ (11 - l)) :
    cacheNodeOff l j + 16 ≤ 32 + 65504 := by
  have h := topN_add_lt l j hl hj
  unfold cacheNodeOff; omega


/-! ## Chains up to `x_i` -/

/-- The chain buffers during the top chains (fixed for the whole phase). -/
structure TopMem (S : List Byte) (x : List Nat) (tau e : Nat) (t : MachineState) : Prop where
  htau : tau < 2 ^ 30
  he : e < 2048
  hx : ∀ i, x.getD i 0 < 8
  x5 : t.getReg .x5 = 0
  x18 : t.getReg .x18 = BitVec.ofNat 64 0x900
  dig : ∀ i < 42, t.getMem (BitVec.ofNat 64 (0x780 + 8 * i)) = BitVec.ofNat 64 (x.getD i 0)
  pb0 : lo32 (t.getMem (BitVec.ofNat 64 0x6A0)) = BitVec.ofNat 32 1
  pb8 : t.getMem (BitVec.ofNat 64 0x6A8) = BitVec.ofNat 64 (tau + 2 ^ 32 * e)
  pbP : t.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  cb0 : lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 0x101
  cb8 : t.getMem (BitVec.ofNat 64 0xC8) = BitVec.ofNat 64 (tau + 2 ^ 32 * e)
  cbP : t.readWords (BitVec.ofNat 64 0xD0) 4 = [0, 0, 0, 0]

/-- Addresses written by a top chain. -/
def tchainW (a : Nat) : Prop :=
  a = 0x6A0 ∨ a = 0xC0 ∨ (0xF0 ≤ a ∧ a < 0x110) ∨ (0x140 ≤ a ∧ a < 0x160) ∨ (0x908 ≤ a ∧ a < 0x908 + 672)

/-- The words `twWord0 t 0 tau p` for `tau < 2^32`. -/
theorem twWord0_top (tt tau p : Nat) (htau : tau < 2 ^ 32) :
    twWord0 tt 0 tau p = BitVec.ofNat 64 (1 + 256 * (tt % 256) + 2 ^ 32 * (p % 2 ^ 32)) := by
  unfold twWord0; congr 1; rw [Nat.div_eq_of_lt htau]; omega

theorem mem_top_frame {S : List Byte} {x : List Nat} {tau e : Nat} {s t : MachineState}
    (h : TopMem S x tau e s) (hf : Frame s t tchainW) (h5 : t.getReg .x5 = 0) (h18 : t.getReg .x18 = BitVec.ofNat 64 0x900)
    (hpb0 : lo32 (t.getMem (BitVec.ofNat 64 0x6A0)) = BitVec.ofNat 32 1)
    (hcb0 : lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 0x101) : TopMem S x tau e t := by
  refine ⟨h.htau, h.he, h.hx, h5, h18, fun i hi => ?_, hpb0, ?_, ?_, ?_, hcb0, ?_, ?_⟩
  · rw [hf.getMem (by omega) (by simp only [tchainW]; omega), h.dig i hi]
  · rw [hf.getMem (by norm_num) (by simp only [tchainW]; omega), h.pb8]
  · rw [hf.readWords _ _ (by norm_num) (by intro i hi; simp only [tchainW]; omega), h.pbP]
  · rw [hf.readWords _ _ (by norm_num) (by intro i hi; simp only [tchainW]; omega), h.pbS]
  · rw [hf.getMem (by norm_num) (by simp only [tchainW]; omega), h.cb8]
  · rw [hf.readWords _ _ (by norm_num) (by intro i hi; simp only [tchainW]; omega), h.cbP]

/-- Step-loop invariant of chain `i` after `j` steps (value `v` at `CB+48`). -/
def TStepInv (S : List Byte) (x : List Nat) (tau e i : Nat) (ts : MachineState) (j : Nat) (v : Val)
    (t : MachineState) : Prop :=
  j ≤ x.getD i 0 ∧ v.length = 16 ∧ t.pc = pcOf 617 ∧ t.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf v ∧
  t.getReg .x23 = BitVec.ofNat 64 j ∧ t.getReg .x24 = BitVec.ofNat 64 (8 * i + j) ∧
  t.getReg .x25 = BitVec.ofNat 64 (x.getD i 0) ∧
  t.getReg .x11 = BitVec.ofNat 64 64 ∧ t.getReg .x12 = BitVec.ofNat 64 0xF0 ∧
  RegsEq ts t [.x10, .x23, .x24] ∧ Frame ts t (fun a => a = 0xC0 ∨ (0xF0 ≤ a ∧ a < 0x110)) ∧
  lo32 (t.getMem (BitVec.ofNat 64 0xC0)) = BitVec.ofNat 32 0x101

theorem tstep_body (S : List Byte) (x : List Nat) (tau e i : Nat) (hi : i < 42) (ts : MachineState)
    (hm : TopMem S x tau e ts) (j : Nat) (hj : j < x.getD i 0) (v : Val) (t : MachineState)
    (hinv : TStepInv S x tau e i ts j v t) :
    Sim image t 14 (hash16 (chainInput 0 tau e i (1 + j) v)) (TStepInv S x tau e i ts (j + 1)) := by
  obtain ⟨-, hvl, tpc, tv, t23, t24, t25, t11, t12, tregs, tframe, tlo⟩ := hinv
  have htau := hm.htau
  have he := hm.he
  have hxi := hm.hx i
  -- block 590: loop test
  have hs0 := symRun_sound blk617 codeAt_617 t tpc (by simp only [blk617.res, rv_simp])
  have hc0 : blk617.res.cycles = 1 := rfl
  rw [hc0] at hs0
  set t0 := blk617.res.toState t with ht0
  have pc0 : t0.pc = pcOf 618 := by
    simp only [ht0, blk617.res, rv_simp, t23, t25, ofNat_beq_ofNat]
    rw [if_neg (by rw [decide_eq_true_eq, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)]
  have m0 : ∀ z, t0.getMem z = t.getMem z := fun z => by
    rw [ht0, Result.toState_getMem, show blk617.res.st.mem = [] from rfl, memEval_nil]
  have r0 : RegsEq t t0 [] := by
    intro r hr; rw [ht0, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  -- block 591: step tweak, HASH
  have hs1 := symRun_sound blk618 codeAt_618 t0 pc0 (by simp only [blk618.res, rv_simp])
  have hc1 : blk618.res.cycles = 2 := rfl
  rw [hc1] at hs1
  set t1 := blk618.res.toState t0 with ht1
  have f1 : Frame t0 t1 (fun x => x = 0xC0) := by
    apply frame_toState; intro x hx hW
    simp only [blk618.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t0 t1 [.x10] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk618 codeAt_618 t0 (by simp only [blk618.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0xC0 := by simp only [ht1, blk618.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by rw [r1.get .x11, r0.get .x11, t11]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0xF0 := by rw [r1.get .x12, r0.get .x12, t12]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, r0.get .x5, tregs.get .x5, hm.x5]
  have pc1 : t1.pc = pcOf 620 := by simp only [ht1, blk618.res, rv_simp]
  have mC0 : t1.getMem (BitVec.ofNat 64 0xC0) = twWord0 1 0 tau (8 * i + j) := by
    simp only [ht1, blk618.res, rv_simp, r0.get .x24, t24]
    bvsimp []
    rw [twWord0_top _ _ _ (by omega)]
    refine (word_of_halves _ 0x101 (8 * i + j) (by rw [lo32_replace1, m0, tlo])
      (by rw [hi32_replace1])).trans ?_
    congr 1
  have hq : hashInput t1 = fmt (chainInput 0 tau e i (1 + j) v) := by
    refine hashInput_eq_chain t1 _ _ _ _ _ _ hvl x11 (by rw [x10]; decide) ?_
    rw [x10, show (8 : Nat) = 1 + 1 + 4 + 2 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, mC0, f1.getMem (by norm_num) (by norm_num), m0,
      tframe.getMem (by norm_num) (by omega), hm.cb8,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      readWords_congr _ _ _ _ (fun k hk => m0 _), readWords_congr _ _ 0xF0 2 (fun k hk => m0 _),
      tframe.readWords _ _ (by norm_num) (by intro i hi; omega), hm.cbP, tv]
    simp only [twWords_eq, show 8 * i + (1 + j) - 1 = 8 * i + j by omega]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
    congr 1; omega
  have hb : (pad64 (chainInput 0 tau e i (1 + j) v)).blocks = 1 :=
    congrArg (· + 1) (words_th16 1 0 tau (8 * i + (1 + j) - 1) e v hvl).1
  have hstep : hash16 (chainInput 0 tau e i (1 + j) v) =
      hash16 (chainInput 0 tau e i (1 + j) v) >>= fun w => pure w := by rw [bind_pure]
  rw [hstep]
  refine (Sim.steps hs0 (Sim.steps hs1 (Sim.hash16_bindF (W := 3) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fun a => ?_)))).mono (by rw [hb]) (fun _ _ h => h)
  set w := answerBytes 16 a with hw
  have hwl : w.length = 16 := by simp [hw]
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0xF0 ≤ x ∧ x < 0xF0 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have v2 : t2.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf w := writeHash_readWords_val t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 621 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have r2 : ∀ q, t2.getReg q = t1.getReg q := fun q => by rw [ht2, writeHash_getReg]
  have r2' : RegsEq t1 t2 [] := fun q _ => r2 q
  -- block 594: counters, back to the loop test
  have hs3 := symRun_sound blk621 codeAt_621 t2 pc2 (by simp only [blk621.res, rv_simp])
  have hc3 : blk621.res.cycles = 3 := rfl
  rw [hc3] at hs3
  set t3 := blk621.res.toState t2 with ht3
  have m3 : ∀ z, t3.getMem z = t2.getMem z := fun z => by
    rw [ht3, Result.toState_getMem, show blk621.res.st.mem = [] from rfl, memEval_nil]
  have r3 : RegsEq t2 t3 [.x23, .x24] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft3 : Frame t t3 (fun a => a = 0xC0 ∨ (0xF0 ≤ a ∧ a < 0x110)) := by
    intro z hz hW
    rw [m3, f2.getMem hz (by omega), f1.getMem hz (by omega), m0]
  refine Sim.pure_steps hs3 ⟨by omega, hwl, by simp only [ht3, blk621.res, rv_simp],
    by rw [readWords_congr _ _ 0xF0 2 (fun k hk => m3 _), v2], ?_, ?_, ?_, ?_, ?_, ?_,
    (tframe.trans ft3).mono (by intro z hz; omega), ?_⟩
  · simp only [ht3, blk621.res, rv_simp, r2, r1.get .x23, r0.get .x23, t23, ofNat_add_ofNat]
  · simp only [ht3, blk621.res, rv_simp, r2, r1.get .x24, r0.get .x24, t24, ofNat_add_ofNat]
    exact ofNat_congr (by omega)
  · rw [r3.get .x25, r2, r1.get .x25, r0.get .x25, t25]
  · rw [r3.get .x11, r2, x11]
  · rw [r3.get .x12, r2, x12]
  · exact ((((tregs.trans r0).trans r1).trans r2').trans r3).mono (by decide)
  · rw [m3, f2.getMem (by norm_num) (by omega), mC0]
    simp only [twWord0, lo32_ofNat]
    apply BitVec.eq_of_toNat_eq; simp; omega

def topRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x21, .x23, .x24, .x25]

/-- Chain-loop invariant after `i` chains. -/
def TChainInv (S : List Byte) (x : List Nat) (tau e : Nat) (tm : MachineState) (i : Nat) (acc : List Val)
    (t : MachineState) : Prop :=
  i ≤ 42 ∧ acc.length = i ∧ (∀ v ∈ acc, v.length = 16) ∧ Slots t 0x908 acc ∧
  t.pc = (if i < 42 then pcOf 598 else pcOf 633) ∧ t.getReg .x21 = BitVec.ofNat 64 i ∧
  TopMem S x tau e t ∧ RegsEq tm t topRegs ∧ Frame tm t tchainW

/-- `SEC` untouched. -/
def TSec (s t : MachineState) : Prop :=
  ∀ x, x < 2 ^ 64 → 0x140 ≤ x → x < 0x160 → t.getMem (BitVec.ofNat 64 x) = s.getMem (BitVec.ofNat 64 x)

/-- Chain `i` of the top leaf from `prf_have` (instruction 606): its secret `s` at `SEC + 16 (i & 1)`. -/
theorem tchain_B (S : List Byte) (x : List Nat) (tau e : Nat) (tm : MachineState)
    (i : Nat) (hi : i < 42) (s : Val) (hs : s.length = 16) (acc : List Val) (hl1 : acc.length = i)
    (hv1 : ∀ v ∈ acc, v.length = 16) (t : MachineState) (hsl : Slots t 0x908 acc)
    (tpc : t.pc = pcOf 606) (t21 : t.getReg .x21 = BitVec.ofNat 64 i) (t11 : t.getReg .x11 = BitVec.ofNat 64 64)
    (tsec : t.readWords (BitVec.ofNat 64 (0x140 + 16 * (i % 2))) 2 = wordsOf s)
    (hm : TopMem S x tau e t) (tregs : RegsEq tm t topRegs) (tframe : Frame tm t tchainW) :
    Sim image t 120 (chainTo 0 tau e i (x.getD i 0) s >>= fun v => pure (acc ++ [v]))
      (fun r t' => TChainInv S x tau e tm (i + 1) r t' ∧ t'.getReg .x11 = BitVec.ofNat 64 64 ∧ TSec t t') := by
  have htau := hm.htau
  have he := hm.he
  have hxi := hm.hx i
  have hi2 : i % 2 < 2 := Nat.mod_lt _ (by norm_num)
  -- block 606: secret → CB+48, digit, step counters
  have hs3 := symRun_sound blk606 codeAt_606 t tpc (by
    simp only [blk606.res, rv_simp]
    rw [t21, secAddr i (by omega) 328 (by norm_num), secAddr i (by omega) 320 (by norm_num)]
    bvsimp [accessValid_ofNat, ne_eq, ofNat_eq_iff]; omega)
  have hc3 : blk606.res.cycles = 11 := rfl
  rw [hc3] at hs3
  set t3 := blk606.res.toState t with ht3
  have f3 : Frame t t3 (fun x => x = 0xF0 ∨ x = 0xF8) := by
    apply frame_toState; intro x hx hW
    simp only [blk606.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r3 : RegsEq t t3 [.x1, .x2, .x3, .x12, .x23, .x24, .x25] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have v3 : t3.readWords (BitVec.ofNat 64 0xF0) 2 = wordsOf s := by
    rw [← tsec, readWords_ofNat_two, readWords_ofNat_two]
    simp only [ht3, blk606.res, rv_simp, t21]
    rw [secAddr i (by omega) 328 (by norm_num), secAddr i (by omega) 320 (by norm_num)]
    simp (config := { decide := true }) only [↓reduceIte]
    rw [show 328 + 16 * (i % 2) = 0x140 + 16 * (i % 2) + 8 by omega]
  have ft3 : Frame t t3 (fun x => 0xF0 ≤ x ∧ x < 0x110) := f3.mono (by intro x hx; omega)
  have hm3 : TopMem S x tau e t3 := mem_top_frame hm (ft3.mono (by intro z hz; simp only [tchainW]; omega))
    (by rw [r3.get .x5, hm.x5]) (by rw [r3.get .x18, hm.x18])
    (by rw [ft3.getMem (by norm_num) (by omega), hm.pb0])
    (by rw [ft3.getMem (by norm_num) (by omega), hm.cb0])
  have x325 : t3.getReg .x25 = BitVec.ofNat 64 (x.getD i 0) := by
    simp only [ht3, blk606.res, rv_simp, t21]; bvsimp []
    rw [show i * 8 + 1920 = 0x780 + 8 * i by ring, hm.dig i hi]
  have h0 : TStepInv S x tau e i t3 0 s t3 := by
    refine ⟨by omega, hs, by simp only [ht3, blk606.res, rv_simp], v3, ?_, ?_, x325, ?_, ?_,
      RegsEq.refl _ _, Frame.refl _ _, hm3.cb0⟩
    · simp only [ht3, blk606.res, rv_simp]
    · simp only [ht3, blk606.res, rv_simp, t21]; bvsimp []; exact ofNat_congr (by omega)
    · rw [r3.get .x11, t11]
    · simp only [ht3, blk606.res, rv_simp]
  have hsteps := Sim.foldlM_range' 1 (x.getD i 0) (fun v mu => hash16 (chainInput 0 tau e i mu v)) s
    (TStepInv S x tau e i t3) 14 (fun j hj v t h => tstep_body S x tau e i hi t3 hm3 j hj v t h) h0
  unfold chainTo
  refine (Sim.steps hs3 (Sim.bind (W₂ := 10) hsteps (fun v t4 h4 => ?_))).mono
    (by have := Nat.mul_le_mul_right 14 (show x.getD i 0 ≤ 7 by omega); omega) (fun _ _ h => h)
  obtain ⟨-, hvl, pc4, v4, x423, x424, x425, x411, x412, r4, f4, lo4⟩ := h4
  -- block 617: exit
  have hs5 := symRun_sound blk617 codeAt_617 t4 pc4 (by simp only [blk617.res, rv_simp])
  have hc5 : blk617.res.cycles = 1 := rfl
  rw [hc5] at hs5
  set t5 := blk617.res.toState t4 with ht5
  have pc5 : t5.pc = pcOf 624 := by
    simp only [ht5, blk617.res, rv_simp, x423, x425, ofNat_beq_ofNat]
    rw [if_pos (by simp)]
  have m5 : ∀ z, t5.getMem z = t4.getMem z := fun z => by
    rw [ht5, Result.toState_getMem, show blk617.res.st.mem = [] from rfl, memEval_nil]
  have r5 : RegsEq t4 t5 [] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  -- block 624: stage the value, next chain
  have rt5 : RegsEq t t5 ([.x1, .x2, .x3, .x12, .x23, .x24, .x25] ++ [.x10, .x23, .x24] ++ []) :=
    (r3.trans r4).trans r5
  have y21 : t5.getReg .x21 = BitVec.ofNat 64 i := by rw [rt5.get .x21, t21]
  have y18 : t5.getReg .x18 = BitVec.ofNat 64 0x900 := by rw [rt5.get .x18, hm.x18]
  have hs6 := symRun_sound blk624 codeAt_624 t5 pc5 (by
    simp only [blk624.res, rv_simp]; bvsimp [y21, y18, accessValid_ofNat]; omega)
  have hc6 : blk624.res.cycles = 9 := rfl
  rw [hc6] at hs6
  set t6 := blk624.res.toState t5 with ht6
  have f6 : Frame t5 t6 (fun z => z = 0x908 + 16 * i ∨ z = 0x908 + 16 * i + 8) := by
    apply frame_toState; intro z hz hW
    simp only [blk624.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [y21, y18, ofNat_eq_iff]
    omega
  have r6 : RegsEq t5 t6 [.x1, .x2, .x3, .x21] := by
    intro r hr; rw [ht6, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft5 : Frame t t5 (fun z => z = 0xC0 ∨ (0xF0 ≤ z ∧ z < 0x110)) := by
    intro z hz hW
    rw [m5, f4.getMem hz (by omega), ft3.getMem hz (by omega)]
  have ft6 : Frame t t6 tchainW := by
    intro z hz hW
    simp only [tchainW] at hW
    rw [f6.getMem hz (by omega), m5, f4.getMem hz (by omega), ft3.getMem hz (by omega)]
  refine Sim.pure_steps (hs5.trans hs6) ⟨⟨by omega, by simp [hl1], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    by rw [r6.get .x11, r5.get .x11, x411], fun z hz h1 h2 => by
      rw [f6.getMem hz (by omega), m5, f4.getMem hz (by omega), ft3.getMem hz (by omega)]⟩
  · intro w hw; rcases List.mem_append.mp hw with hw | hw
    · exact hv1 w hw
    · simp at hw; subst hw; exact hvl
  · apply Slots.snoc
    · exact hsl.frame (ft5.trans f6) (by omega) (by intro k hk; constructor <;> omega)
    · rw [hl1, readWords_ofNat_two, show 0x908 + 16 * i + 8 = 0x908 + 16 * i + 8 from rfl]
      rw [← v4, readWords_ofNat_two]
      simp only [ht6, blk624.res, rv_simp, m5]
      bvsimp [y21, y18, ofNat_eq_iff]
      simp (disch := bvomega) only [if_pos, if_neg]
  · simp only [ht6, blk624.res, rv_simp, y21, ofNat_add_ofNat, ofNat_bne_ofNat]
    by_cases h : i + 1 < 42
    · rw [if_pos h, if_pos (by rw [bne_cond _ _ (by omega) (by norm_num)]; omega)]
    · rw [if_neg h, if_neg (by rw [bne_cond _ _ (by omega) (by norm_num)]; omega)]
  · simp only [ht6, blk624.res, rv_simp, y21, ofNat_add_ofNat]
  · exact mem_top_frame hm ft6 (by rw [r6.get .x5, rt5.get .x5, hm.x5]) (by rw [r6.get .x18, y18])
      (by rw [f6.getMem (by norm_num) (by omega), m5, f4.getMem (by norm_num) (by omega),
            ft3.getMem (by norm_num) (by omega)]; exact hm.pb0)
      (by rw [f6.getMem (by norm_num) (by omega), m5, lo4])
  · exact ((tregs.trans rt5).trans r6).mono (by decide)
  · exact (tframe.trans ft6).mono (by intro z hz; rcases hz with h | h <;> exact h)

theorem top_pair_spec (S : List Byte) (tau e k : Nat) (x : List Nat) (acc : List Val) :
    (do
      let (s0, s1) ← prf2 (prfInput S 0 tau e k)
      let v0 ← chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) s0
      let v1 ← chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
      pure (acc ++ [v0, v1]) : OracleComp HashSpec (List Val)) =
    H (prfInput S 0 tau e k) >>= fun a =>
      (chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) (answerBytes 16 a) >>= fun v => pure (acc ++ [v])) >>= fun r =>
      chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) (hiVal a) >>= fun v => pure (r ++ [v]) := by
  simp only [prf2_eq, bind_assoc, pure_bind, List.append_assoc, List.cons_append, List.nil_append]

theorem tchain_pair (S : List Byte) (hS : S.length = 32) (x : List Nat) (tau e : Nat) (tm : MachineState)
    (k : Nat) (hk : k < 21) (acc : List Val) (t : MachineState) (hinv : TChainInv S x tau e tm (2 * k) acc t) :
    Sim image t 257 (do
        let (s0, s1) ← prf2 (prfInput S 0 tau e k)
        let v0 ← chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) s0
        let v1 ← chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (acc ++ [v0, v1])) (TChainInv S x tau e tm (2 * k + 2)) := by
  rw [top_pair_spec]
  obtain ⟨-, hl1, hv1, hsl, tpc, t21, hm, tregs, tframe⟩ := hinv
  have htau := hm.htau
  have he := hm.he
  have tpc' : t.pc = pcOf 598 := by rw [tpc, if_pos (by omega)]
  -- block 598: even
  have hs0 := symRun_sound blk598 codeAt_598 t tpc' (by simp only [blk598.res, rv_simp])
  have hc0 : blk598.res.cycles = 2 := rfl
  rw [hc0] at hs0
  set t1 := blk598.res.toState t with ht1
  have m1 : ∀ z, t1.getMem z = t.getMem z := fun z => by
    rw [ht1, Result.toState_getMem, show blk598.res.st.mem = [] from rfl, memEval_nil]
  have r1 : RegsEq t t1 [.x3] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc1 : t1.pc = pcOf 600 := by
    simp only [ht1, blk598.res, rv_simp, t21]
    rw [and_one_ofNat _ (by omega), if_neg (by rw [ofNat_bne_ofNat]; simp)]
  -- block 600: the paired prf query
  have hs2 := symRun_sound blk600 codeAt_600 t1 pc1 (by simp only [blk600.res, rv_simp])
  have hc2 : blk600.res.cycles = 5 := rfl
  rw [hc2] at hs2
  set t2 := blk600.res.toState t1 with ht2
  have f2 : Frame t1 t2 (fun x => x = 0x6A0) := by
    apply frame_toState; intro x hx hW
    simp only [blk600.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r2 : RegsEq t1 t2 [.x3, .x10, .x11, .x12] := by
    intro r hr; rw [ht2, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e2 := symRun_ecall blk600 codeAt_600 t1 (by simp only [blk600.res, rv_simp]) rfl
  have x10 : t2.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht2, blk600.res, rv_simp]
  have x11 : t2.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht2, blk600.res, rv_simp]
  have x12 : t2.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht2, blk600.res, rv_simp]
  have x5 : t2.getReg .x5 = 0 := by rw [r2.get .x5, r1.get .x5, hm.x5]
  have pc2 : t2.pc = pcOf 605 := by simp only [ht2, blk600.res, rv_simp]
  have t121 : t1.getReg .x21 = BitVec.ofNat 64 (2 * k) := by rw [r1.get .x21, t21]
  have m6A0 : t2.getMem (BitVec.ofNat 64 0x6A0) = twWord0 0 0 tau k := by
    simp only [ht2, blk600.res, rv_simp, t121]
    bvsimp []
    rw [show 2 * k / 2 = k by omega, twWord0_top _ _ _ (by omega)]
    refine (word_of_halves _ 1 k (by rw [lo32_replace1, m1, hm.pb0]) (by rw [hi32_replace1])).trans ?_
    congr 1
  have ft2 : Frame t t2 (fun x => x = 0x6A0) := fun z hz hW => by rw [f2.getMem hz hW, m1]
  have hq : hashInput t2 = pad64 (prfInput S 0 tau e k) := by
    obtain ⟨hn, hw⟩ := words_prfInput S hS 0 tau e k
    refine hashInput_eq_pad64 t2 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one, m6A0, ft2.getMem (by norm_num) (by norm_num), hm.pb8,
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega),
      ft2.readWords _ _ (by norm_num) (by intro i hi; omega), hm.pbP, hm.pbS]
    simp only [twWords_eq, List.cons_append, List.nil_append, List.cons.injEq, and_true, true_and]
    congr 1; omega
  have hb : (pad64 (prfInput S 0 tau e k)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_prfInput S hS 0 tau e k).1]
  refine (Sim.steps hs0 (Sim.steps hs2 (Sim.query_bind (W := 120 + (2 + 120)) e2 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) (hq.trans (fmt_thInput _ _ _ _ _ _ (by decide)).symm) (fun a => ?_)))).mono
    (by rw [blocks_fmt, show prfInput S 0 tau e k = thInput (tweak 0 0 tau k e) S from rfl] at *
        rw [hb])
    (fun _ _ h => h)
  set t3 := writeHash t2 a with ht3
  have f3 : Frame t2 t3 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t2 a _ x12 (by norm_num)
  have pc3 : t3.pc = pcOf 606 := by rw [ht3, writeHash_pc, pc2]; apply BitVec.eq_of_toNat_eq; simp
  have g3 : ∀ q, t3.getReg q = t2.getReg q := fun q => by rw [ht3, writeHash_getReg]
  have ft3 : Frame t t3 (fun x => x = 0x6A0 ∨ (0x140 ≤ x ∧ x < 0x140 + 32)) := ft2.trans f3
  have rt3 : RegsEq tm t3 topRegs := ((tregs.trans r1).trans r2 |>.trans
    (show RegsEq t2 t3 [] from fun q _ => g3 q)).mono (by decide)
  have hm3 : TopMem S x tau e t3 := mem_top_frame hm (ft3.mono (by intro z hz; simp only [tchainW]; omega))
    (by rw [g3, r2.get .x5, r1.get .x5, hm.x5]) (by rw [g3, r2.get .x18, r1.get .x18, hm.x18])
    (by rw [f3.getMem (by norm_num) (by omega), m6A0]; simp only [twWord0, lo32_ofNat]
        apply BitVec.eq_of_toNat_eq; simp; omega)
    (by rw [ft3.getMem (by norm_num) (by omega), hm.cb0])
  have hA := tchain_B S x tau e tm (2 * k) (by omega) (answerBytes 16 a) (by simp) acc hl1 hv1 t3
    (hsl.frame ft3 (by omega) (by intro i hi; constructor <;> omega))
    pc3 (by rw [g3, r2.get .x21, t121]) (by rw [g3, x11])
    (by rw [show 0x140 + 16 * (2 * k % 2) = 0x140 by omega]; exact sec_lo t2 a x12)
    hm3 rt3 ((tframe.trans ft3).mono (by intro x hx; simp only [tchainW] at hx ⊢; omega))
  refine Sim.bind hA (fun r t4 h4 => ?_)
  obtain ⟨⟨-, hl14, hv14, hsl4, tpc4, t421, hm4, tregs4, tframe4⟩, x411, sec4⟩ := h4
  -- block 598: odd
  have hs5 := symRun_sound blk598 codeAt_598 t4 (by rw [tpc4, if_pos (by omega)])
    (by simp only [blk598.res, rv_simp])
  have hc5 : blk598.res.cycles = 2 := rfl
  rw [hc5] at hs5
  set t5 := blk598.res.toState t4 with ht5
  have m5 : ∀ z, t5.getMem z = t4.getMem z := fun z => by
    rw [ht5, Result.toState_getMem, show blk598.res.st.mem = [] from rfl, memEval_nil]
  have r5 : RegsEq t4 t5 [.x3] := by
    intro r hr; rw [ht5, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have pc5 : t5.pc = pcOf 606 := by
    simp only [ht5, blk598.res, rv_simp, t421]
    rw [and_one_ofNat _ (by omega), if_pos (by rw [ofNat_bne_ofNat]; simp)]
  have fr5 : Frame t4 t5 (fun _ => False) := fun z _ _ => m5 _
  have hB := tchain_B S x tau e tm (2 * k + 1) (by omega) (hiVal a) (by simp) r hl14 hv14 t5
    (hsl4.frame fr5 (by omega) (by simp)) pc5 (by rw [r5.get .x21, t421]) (by rw [r5.get .x11, x411])
    (by
      rw [show 0x140 + 16 * ((2 * k + 1) % 2) = 0x150 by omega, readWords_ofNat_two, m5, m5,
        sec4 _ (by norm_num) (by norm_num) (by norm_num), sec4 _ (by norm_num) (by norm_num) (by norm_num),
        ← readWords_ofNat_two]
      exact sec_hi t2 a x12)
    (mem_top_frame hm4 (fr5.mono (by intro z hz; exact hz.elim)) (by rw [r5.get .x5, hm4.x5])
      (by rw [r5.get .x18, hm4.x18]) (by rw [m5, hm4.pb0]) (by rw [m5, hm4.cb0]))
    ((tregs4.trans r5).mono (by decide))
    ((tframe4.trans fr5).mono (by intro x hx; rcases hx with h | h; exact h; exact h.elim))
  exact (Sim.steps hs5 hB).mono (by norm_num) (fun _ _ h => h.1)

/-- **Top chains** `i = 0 .. 41` (pairs `k = 0 .. 20`, up to `x_i`). -/
theorem topChains_sim (S : List Byte) (hS : S.length = 32) (x : List Nat) (tau e : Nat) (tm : MachineState)
    (h0 : TChainInv S x tau e tm 0 [] tm) :
    Sim image tm (21 * 257) ((List.range (nChains / 2)).foldlM (fun (acc : List Val) k => do
        let (s0, s1) ← prf2 (prfInput S 0 tau e k)
        let v0 ← chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) s0
        let v1 ← chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (acc ++ [v0, v1])) []) (TChainInv S x tau e tm 42) := by
  unfold nChains
  exact Sim.foldlM_range 21 _ [] (fun k => TChainInv S x tau e tm (2 * k)) 257
    (fun k hk acc t h => by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring]; exact tchain_pair S hS x tau e tm k hk acc t h) h0

/-- The entry block of the top layer (572 .. 580): PB / CB tweaks, `CB+32..48` cleared. -/
theorem top_entry (S cache : List Byte) (x : List Nat) (tau e : Nat) (t : MachineState)
    (hc : TopCtx S cache x tau e t) (tpc : t.pc = pcOf 589) :
    ∃ u, Steps image t 9 9 u ∧ TChainInv S x tau e u 0 [] u ∧
      RegsEq t u [.x3, .x21] ∧
      Frame t u (fun a => a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ a = 0xE0 ∨ a = 0xE8) := by
  have hs := symRun_sound blk589 codeAt_589 t tpc (by simp only [blk589.res, rv_simp])
  have hk : blk589.res.cycles = 9 := rfl
  have hk' : blk589.res.steps = 9 := rfl
  rw [hk, hk'] at hs
  set u := blk589.res.toState t with hu
  have f : Frame t u (fun a => a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ a = 0xE0 ∨ a = 0xE8) := by
    apply frame_toState; intro x hx hW
    simp only [blk589.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r : RegsEq t u [.x3, .x21] := by
    intro r hr; rw [hu, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  refine ⟨u, hs, ⟨by norm_num, rfl, by simp, Slots.nil _ _, by rw [if_pos (by norm_num)]; simp only [hu, blk589.res, rv_simp],
    by simp only [hu, blk589.res, rv_simp], ?_, RegsEq.refl _ _, Frame.refl _ _⟩, r, f⟩
  refine ⟨hc.htau, hc.he, hc.hx, by rw [r.get .x5, hc.x5], by rw [r.get .x18, hc.x18], fun i hi => ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f.getMem (by omega) (by omega), hc.dig i hi]
  · simp (config := { decide := true }) only [hu, blk589.res, rv_simp, ↓reduceIte]
  · simp (config := { decide := true }) only [hu, blk589.res, rv_simp, hc.x31, ↓reduceIte]
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), hc.pbP]
  · rw [f.readWords _ _ (by norm_num) (by intro i hi; omega), hc.pbS]
  · simp (config := { decide := true }) only [hu, blk589.res, rv_simp, ↓reduceIte, Nat.zero_div]
    rw [lo32_replace0]; rfl
  · simp (config := { decide := true }) only [hu, blk589.res, rv_simp, hc.x31, ↓reduceIte]
  · rw [show (4 : Nat) = 2 + 2 from rfl, readWords_ofNat_add,
      f.readWords _ _ (by norm_num) (by intro i hi; omega), hc.cbP, readWords_ofNat_two]
    simp only [hu, blk589.res, rv_simp]; rfl

/-! ## The path from the cache -/

theorem words_maskInput (S : List Byte) (hS : S.length = 32) (l j : Nat) :
    padBlocks (maskInput S l j).length = 0 ∧
    wordsOf (padTo64 (maskInput S l j)) = twWords 13 0 0 l j ++ [0, 0] ++ wordsOf S := by
  obtain ⟨h1, h2⟩ := padTo64_eq (maskInput S l j) 0 (by simp [maskInput, hS])
    (by simp [maskInput, hS])
  refine ⟨h1, ?_⟩
  rw [h2, maskInput, wordsOf_thInput_pad]
  simp [hS, zeros]

/-- Addresses written by the path loop. -/
def tpathW (a : Nat) : Prop := a = 0x6A0 ∨ a = 0x6A8 ∨ (0x140 ≤ a ∧ a < 0x160) ∨ (0xBA8 ≤ a ∧ a < 0xBA8 + 176)

def pathRegs : List Reg := [.x1, .x2, .x3, .x10, .x11, .x12, .x15, .x16, .x17, .x19, .x29]

/-- Path-loop invariant after `l` levels. -/
def TPathInv (S cache : List Byte) (e : Nat) (tp : MachineState) (l : Nat) (acc : List Val)
    (t : MachineState) : Prop :=
  l ≤ 11 ∧ acc.length = l ∧ (∀ v ∈ acc, v.length = 16) ∧ Slots t 0xBA8 acc ∧
  t.pc = (if l < 11 then pcOf 637 else pcOf 666) ∧ t.getReg .x15 = BitVec.ofNat 64 l ∧
  t.getReg .x19 = BitVec.ofNat 64 (0x44C0 + 16 * topN l) ∧
  t.getReg .x17 = BitVec.ofNat 64 (16 * 2 ^ (11 - l)) ∧
  RegsEq tp t pathRegs ∧ Frame tp t tpathW

/-- The facts the path loop needs (fixed). -/
structure PathCtx (S cache : List Byte) (e : Nat) (t : MachineState) : Prop where
  he : e < 2048
  x5 : t.getReg .x5 = 0
  x13 : t.getReg .x13 = BitVec.ofNat 64 e
  x18 : t.getReg .x18 = BitVec.ofNat 64 0x900
  pbP : t.readWords (BitVec.ofNat 64 0x6B0) 2 = [0, 0]
  pbS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf S
  node : ∀ l j, l < 11 → j < 2 ^ (11 - l) →
    t.readWords (BitVec.ofNat 64 (0x44A0 + cacheNodeOff l j)) 2 = wordsOf (cacheNode cache l j)
  nodeLen : ∀ l j, l < 11 → j < 2 ^ (11 - l) → (cacheNode cache l j).length = 16

theorem sib_lt (e l : Nat) (he : e < 2048) (hl : l < 11) : (e / 2 ^ l) ^^^ 1 < 2 ^ (11 - l) := by
  have h1 : e / 2 ^ l < 2 ^ (11 - l) := by
    rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, show 11 - l + l = 11 by omega]; omega
  exact Nat.xor_lt_two_pow h1 (Nat.one_lt_two_pow (by omega))

theorem tpath_body (S cache : List Byte) (hS : S.length = 32) (e : Nat) (tp : MachineState)
    (pc : PathCtx S cache e tp) (l : Nat) (hl : l < 11) (acc : List Val) (t : MachineState)
    (hinv : TPathInv S cache e tp l acc t) :
    Sim image t 36 (do
        let mk ← hash16 (maskInput S l ((e / 2 ^ l) ^^^ 1))
        pure (acc ++ [xorBytes (cacheNode cache l ((e / 2 ^ l) ^^^ 1)) mk]))
      (TPathInv S cache e tp (l + 1)) := by
  obtain ⟨-, hl1, hv1, hsl, tpc, t15, t19, t17, tregs, tframe⟩ := hinv
  have he := pc.he
  set sb := (e / 2 ^ l) ^^^ 1 with hsb
  have hsbl : sb < 2 ^ (11 - l) := sib_lt e l he hl
  have hp11 : 2 ^ (11 - l) ≤ 2048 := by
    calc 2 ^ (11 - l) ≤ 2 ^ 11 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 2048 := by norm_num
  have tpc' : t.pc = pcOf 637 := by rw [tpc, if_pos hl]
  have t13 : t.getReg .x13 = BitVec.ofNat 64 e := by rw [tregs.get .x13, pc.x13]
  -- block 610: mask tweak, HASH
  have hs1 := symRun_sound blk637 codeAt_637 t tpc' (by simp only [blk637.res, rv_simp])
  have hc1 : blk637.res.cycles = 11 := rfl
  rw [hc1] at hs1
  set t1 := blk637.res.toState t with ht1
  have f1 : Frame t t1 (fun x => x = 0x6A0 ∨ x = 0x6A8) := by
    apply frame_toState; intro x hx hW
    simp only [blk637.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq, ofNat_eq_iff]
    omega
  have r1 : RegsEq t t1 [.x3, .x10, .x11, .x12, .x16] := by
    intro r hr; rw [ht1, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have e1 := symRun_ecall blk637 codeAt_637 t (by simp only [blk637.res, rv_simp]) rfl
  have x10 : t1.getReg .x10 = BitVec.ofNat 64 0x6A0 := by simp only [ht1, blk637.res, rv_simp]
  have x11 : t1.getReg .x11 = BitVec.ofNat 64 64 := by simp only [ht1, blk637.res, rv_simp]
  have x12 : t1.getReg .x12 = BitVec.ofNat 64 0x140 := by simp only [ht1, blk637.res, rv_simp]
  have x5 : t1.getReg .x5 = 0 := by rw [r1.get .x5, tregs.get .x5, pc.x5]
  have pc1 : t1.pc = pcOf 648 := by simp only [ht1, blk637.res, rv_simp]
  have hsbw : (t.getReg .x13 >>> ((BitVec.ofNat 64 l).toNat % 64) ^^^ 1#64) = BitVec.ofNat 64 sb := by
    rw [t13]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_xor, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    simp only [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (a := e) (by omega), Nat.mod_eq_of_lt (a := l) (by omega),
      Nat.mod_eq_of_lt (a := l) (by omega), Nat.mod_eq_of_lt (a := sb) (by omega)]
  have x16 : t1.getReg .x16 = BitVec.ofNat 64 sb := by
    simp only [ht1, blk637.res, rv_simp, t15, hsbw]
  have hq : hashInput t1 = pad64 (maskInput S l sb) := by
    obtain ⟨hn, hw⟩ := words_maskInput S hS l sb
    refine hashInput_eq_pad64 t1 _ 0 hn (by rw [x11]) (by norm_num) (by rw [x10]; decide) ?_
    rw [hw, x10, show 8 * (0 + 1) = 1 + 1 + 2 + 4 from rfl]
    rw [readWords_ofNat_add, readWords_ofNat_add, readWords_ofNat_add]
    simp only [Nat.reduceMul, Nat.reduceAdd]
    rw [readWords_ofNat_one, readWords_ofNat_one,
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      f1.readWords _ _ (by norm_num) (by intro i hi; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [tpathW]; omega),
      tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [tpathW]; omega), pc.pbP, pc.pbS]
    simp (config := { decide := true }) only [ht1, blk637.res, rv_simp, t15, twWords_eq, twWord0,
      ↓reduceIte, hsbw]
    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
    bvsimp []
    constructor <;> apply ofNat_congr <;> omega
  have hb : (pad64 (maskInput S l sb)).blocks = 1 := by
    simp [pad64, Query.blocks, (words_maskInput S hS l sb).1]
  have hnode := pc.node l sb hl hsbl
  have hnl := pc.nodeLen l sb hl hsbl
  have hoff := cacheNodeOff_lt l sb hl hsbl
  have htn := topN_add_lt l sb hl hsbl
  refine (Sim.steps hs1 (Sim.hash16_bind (W := 17) e1 x5
    (hashArgs_of x10 x11 x12 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num)) hq (fmt_thInput _ _ _ _ _ _ (by decide)) (fun a => ?_))).mono (by rw [hb]) (fun _ _ h => h)
  set mk := answerBytes 16 a with hmk
  set t2 := writeHash t1 a with ht2
  have f2 : Frame t1 t2 (fun x => 0x140 ≤ x ∧ x < 0x140 + 32) := frame_writeHash t1 a _ x12 (by norm_num)
  have pc2 : t2.pc = pcOf 649 := by rw [ht2, writeHash_pc, pc1]; apply BitVec.eq_of_toNat_eq; simp
  have r2 : RegsEq t1 t2 [] := fun q _ => by rw [ht2, writeHash_getReg]
  have w0 : t2.getMem (BitVec.ofNat 64 0x140) = a.extractLsb' 0 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x140 x12 (by norm_num) (by norm_num)]; simp
  have w1 : t2.getMem (BitVec.ofNat 64 0x148) = a.extractLsb' 64 64 := by
    rw [ht2, writeHash_getMem_ofNat t1 a 0x140 0x148 x12 (by norm_num) (by norm_num)]; simp
  have ft2 : Frame t t2 (fun x => x = 0x6A0 ∨ x = 0x6A8 ∨ (0x140 ≤ x ∧ x < 0x160)) :=
    (f1.trans f2).mono (by intro x hx; omega)
  -- the node words (region untouched)
  have nw : t2.readWords (BitVec.ofNat 64 (0x44A0 + cacheNodeOff l sb)) 2 = wordsOf (cacheNode cache l sb) := by
    rw [ft2.readWords _ _ (by unfold cacheNodeOff; omega) (by intro i hi; unfold cacheNodeOff; omega),
      tframe.readWords _ _ (by unfold cacheNodeOff; omega) (by intro i hi; simp only [tpathW]; unfold cacheNodeOff; omega),
      hnode]
  rw [readWords_ofNat_two] at nw
  obtain ⟨n0, n1, hn⟩ : ∃ n0 n1, wordsOf (cacheNode cache l sb) = [n0, n1] := by
    rw [← nw]; exact ⟨_, _, rfl⟩
  rw [hn] at nw
  simp only [List.cons.injEq, and_true] at nw
  obtain ⟨nw0, nw1⟩ := nw
  -- block 622: store node xor mask, next level
  have y15 : t2.getReg .x15 = BitVec.ofNat 64 l := by rw [r2.get .x15, r1.get .x15, t15]
  have y16 : t2.getReg .x16 = BitVec.ofNat 64 sb := by rw [r2.get .x16, x16]
  have y18 : t2.getReg .x18 = BitVec.ofNat 64 0x900 := by rw [r2.get .x18, r1.get .x18, tregs.get .x18, pc.x18]
  have y19 : t2.getReg .x19 = BitVec.ofNat 64 (0x44C0 + 16 * topN l) := by rw [r2.get .x19, r1.get .x19, t19]
  have y17 : t2.getReg .x17 = BitVec.ofNat 64 (16 * 2 ^ (11 - l)) := by rw [r2.get .x17, r1.get .x17, t17]
  have hs3 := symRun_sound blk649 codeAt_649 t2 pc2 (by
    simp only [blk649.res, rv_simp]; bvsimp [y15, y16, y18, y19, accessValid_ofNat, ne_eq, ofNat_eq_iff]
    omega)
  have hc3 : blk649.res.cycles = 17 := rfl
  rw [hc3] at hs3
  set t3 := blk649.res.toState t2 with ht3
  have f3 : Frame t2 t3 (fun z => z = 0xBA8 + 16 * l ∨ z = 0xBA8 + 16 * l + 8) := by
    apply frame_toState; intro z hz hW
    simp only [blk649.res, rv_simp, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true, ne_eq]
    bvsimp [y15, y18, ofNat_eq_iff]
    omega
  have r3 : RegsEq t2 t3 [.x1, .x2, .x3, .x15, .x17, .x19, .x29] := by
    intro r hr; rw [ht3, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have hxor : wordsOf (xorBytes (cacheNode cache l sb) mk) =
      [n0 ^^^ a.extractLsb' 0 64, n1 ^^^ a.extractLsb' 64 64] :=
    wordsOf_xorBytes _ _ hnl (by simp [hmk]) _ _ _ _ hn (by rw [hmk, wordsOf_answerBytes_16])
  refine Sim.pure_steps hs3 ⟨by omega, by simp [hl1], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; rcases List.mem_append.mp hw with hw | hw
    · exact hv1 w hw
    · simp at hw; subst hw; rw [length_xorBytes' _ _ (by simp [hmk, hnl])]; exact hnl
  · apply Slots.snoc
    · exact hsl.frame (ft2.trans f3) (by omega) (by intro k hk; constructor <;> omega)
    · rw [hl1, hxor, readWords_ofNat_two]
      simp only [ht3, blk649.res, rv_simp]
      bvsimp [y15, y16, y18, y19, ofNat_eq_iff]
      simp (disch := bvomega) only [if_pos, if_neg]
      rw [show sb * 16 + (17600 + 16 * topN l) = 0x44A0 + cacheNodeOff l sb by unfold cacheNodeOff; ring,
        show 0x44A0 + cacheNodeOff l sb + 8 = 0x44A0 + cacheNodeOff l sb + 8 from rfl, nw0, nw1,
        show (320#64 : Word) = BitVec.ofNat 64 0x140 from rfl, show (328#64 : Word) = BitVec.ofNat 64 0x148 from rfl,
        w0, w1]
  · simp only [ht3, blk649.res, rv_simp, y15, ofNat_add_ofNat, ofNat_bne_ofNat]
    by_cases h : l + 1 < 11
    · rw [if_pos h, if_pos (by rw [bne_cond _ _ (by omega) (by norm_num)]; omega)]
    · rw [if_neg h, if_neg (by rw [bne_cond _ _ (by omega) (by norm_num)]; omega)]
  · simp only [ht3, blk649.res, rv_simp, y15, ofNat_add_ofNat]
  · simp only [ht3, blk649.res, rv_simp, y19, y17, ofNat_add_ofNat]
    rw [topN_succ l hl]; exact ofNat_congr (by ring_nf)
  · simp only [ht3, blk649.res, rv_simp, y17]; bvsimp []
    exact ofNat_congr (by
      rw [show 11 - l = (11 - (l + 1)) + 1 by omega, Nat.pow_succ]; omega)
  · exact (((tregs.trans r1).trans r2).trans r3).mono (by decide)
  · exact (tframe.trans (ft2.trans f3)).mono (by
      intro z hz; simp only [tpathW] at hz ⊢; omega)

/-- **Top path** `l = 0 .. 10`. -/
theorem topPath_sim (S cache : List Byte) (hS : S.length = 32) (e : Nat) (tp : MachineState)
    (pc : PathCtx S cache e tp) (h0 : TPathInv S cache e tp 0 [] tp) :
    Sim image tp (11 * 36) (topPath S cache e) (TPathInv S cache e tp 11) := by
  unfold topPath
  rw [show topH = 11 from rfl]
  exact Sim.foldlM_range 11 _ [] (TPathInv S cache e tp) 36
    (fun l hl acc t h => tpath_body S cache hS e tp pc l hl acc t h) h0

/-- Result of the top layer. -/
def TopPost (t0 : MachineState) (r : List Val × List Val) (t : MachineState) : Prop :=
  r.1.length = 42 ∧ (∀ v ∈ r.1, v.length = 16) ∧ Slots t 0x908 r.1 ∧
  r.2.length = 11 ∧ (∀ v ∈ r.2, v.length = 16) ∧ Slots t 0xBA8 r.2 ∧
  t.pc = pcOf 666 ∧ t.getReg .x5 = 0 ∧ Frame t0 t topW

/-- **The top layer** (chains up to `x_i`, path from the cache). -/
theorem top_sim (S cache : List Byte) (hS : S.length = 32) (x : List Nat) (tau e : Nat) (t : MachineState)
    (hc : TopCtx S cache x tau e t) (tpc : t.pc = pcOf 589) :
    Sim image t (9 + (21 * 257 + (4 + 11 * 36)))
      ((List.range (nChains / 2)).foldlM (fun (acc : List Val) k => do
        let (s0, s1) ← prf2 (prfInput S 0 tau e k)
        let v0 ← chainTo 0 tau e (2 * k) (x.getD (2 * k) 0) s0
        let v1 ← chainTo 0 tau e (2 * k + 1) (x.getD (2 * k + 1) 0) s1
        pure (acc ++ [v0, v1])) [] >>= fun vals => topPath S cache e >>= fun path => pure (vals, path))
      (TopPost t) := by
  obtain ⟨u, hsu, hu0, ru, fu⟩ := top_entry S cache x tau e t hc tpc
  refine Sim.steps hsu (Sim.bind (topChains_sim S hS x tau e u hu0) (fun vals t1 h1 => ?_))
  obtain ⟨-, hl1, hv1, hsl1, pc1, -, hm1, r1, f1⟩ := h1
  have pc1' : t1.pc = pcOf 633 := by rw [pc1]; rfl
  -- block 606: path loop setup
  have hs2 := symRun_sound blk633 codeAt_633 t1 pc1' (by simp only [blk633.res, rv_simp])
  have hc2 : blk633.res.cycles = 4 := rfl
  rw [hc2] at hs2
  set t2 := blk633.res.toState t1 with ht2
  have m2 : ∀ z, t2.getMem z = t1.getMem z := fun z => by
    rw [ht2, Result.toState_getMem, show blk633.res.st.mem = [] from rfl, memEval_nil]
  have r2 : RegsEq t1 t2 [.x15, .x17, .x19] := by
    intro r hr; rw [ht2, Result.toState_getReg]
    cases r <;> first | exact absurd (by decide) hr | rfl
  have ft2 : Frame t t2 (fun a => (a = 0x6A0 ∨ a = 0x6A8 ∨ a = 0xC0 ∨ a = 0xC8 ∨ a = 0xE0 ∨ a = 0xE8) ∨
      tchainW a) := fun z hz hW => by rw [m2, (fu.trans f1).getMem hz hW]
  have rt2 : RegsEq t t2 ([.x3, .x21] ++ topRegs ++ [.x15, .x17, .x19]) := (ru.trans r1).trans r2
  have pc : PathCtx S cache e t2 := by
    refine ⟨hc.he, by rw [rt2.get .x5, hc.x5], by rw [rt2.get .x13, hc.x13], by rw [rt2.get .x18, hc.x18],
      ?_, ?_, fun l j hl hj => ?_, hc.nodeLen⟩
    · rw [ft2.readWords _ _ (by norm_num) (by intro i hi; simp only [tchainW]; omega), hc.pbP]
    · rw [ft2.readWords _ _ (by norm_num) (by intro i hi; simp only [tchainW]; omega), hc.pbS]
    · have := cacheNodeOff_lt l j hl hj
      have : 32 ≤ cacheNodeOff l j := by unfold cacheNodeOff; omega
      rw [ft2.readWords _ _ (by omega) (by intro i hi; simp only [tchainW]; omega), hc.node l j hl hj]
  have h0 : TPathInv S cache e t2 0 [] t2 := by
    refine ⟨by norm_num, rfl, by simp, Slots.nil _ _,
      by rw [if_pos (by norm_num)]; simp only [ht2, blk633.res, rv_simp],
      by simp only [ht2, blk633.res, rv_simp], ?_, ?_, RegsEq.refl _ _, Frame.refl _ _⟩
    · simp only [ht2, blk633.res, rv_simp]; rfl
    · simp only [ht2, blk633.res, rv_simp]; rfl
  refine Sim.steps hs2 (Sim.bind (W₂ := 0) (topPath_sim S cache hS e t2 pc h0) (fun path t3 h3 => ?_))
  obtain ⟨-, hl3, hv3, hsl3, pc3, -, -, -, r3, f3⟩ := h3
  refine Sim.pure ⟨hl1, hv1, ?_, hl3, hv3, hsl3, by rw [pc3]; rfl, ?_, ?_⟩
  · have fr : Frame t1 t3 tpathW := fun z hz hW => by rw [f3.getMem hz hW, m2]
    exact hsl1.frame fr (by omega) (by intro k hk; simp only [tpathW]; constructor <;> omega)
  · rw [r3.get .x5, rt2.get .x5, hc.x5]
  · exact (ft2.trans f3).mono (by intro z hz; simp only [tchainW, tpathW, topW] at hz ⊢; omega)

end SigGolfCandidate.Sign
