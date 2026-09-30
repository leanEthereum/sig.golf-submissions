import SigGolfCandidate.Sign.Setup
import SigGolfCandidate.Sign.DigOk
import SigGolfCandidate.Sign.Roots
import SigGolfCandidate.Sign.Pack

/-!
# `sign` refines `signRef` (main theorems)
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem decode_ecall : decodeInstruction 0x00000073#32 = some (.base .ECALL) := rfl

theorem fetch_ecall (t : MachineState) (i : Nat) (hi : image.code[i]? = some 0x00000073#32)
    (hlt : 0x1000 + 4 * i < 2 ^ 64) (hpc : t.pc = pcOf i) : fetch image t = some (.base .ECALL) := by
  unfold fetch
  rw [hpc]
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  rw [if_neg (by simp <;> omega), show (0x1000 + 4 * i - 0x1000) / 4 = i by omega, hi]
  exact decode_ecall

theorem code83 : image.code[83]? = some 0x00000073#32 := by decide +kernel
theorem code86 : image.code[86]? = some 0x00000073#32 := by decide +kernel
theorem code329 : image.code[329]? = some 0x00000073#32 := by decide +kernel
theorem code2962 : image.code[2962]? = some 0x00000073#32 := by decide +kernel

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem openAt_words (t : MachineState) (B : Nat) (o : Val × List Val) (h : OpenAt t B o) :
    t.readWords (BitVec.ofNat 64 B) 22 = wordsOf (o.1 ++ o.2.flatten) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hv : ∀ v ∈ o.1 :: o.2, v.length = 16 := by
    intro v hv; rcases List.mem_cons.mp hv with rfl | hv; exact h1; exact h3 v hv
  rw [show (22 : Nat) = 2 * (o.1 :: o.2).length by simp [h2], readWords_slots t B _ h4,
    ← wordsOf_flatten _ hv, List.flatten_cons]

theorem fors_words (t : MachineState) : ∀ (fors : List (Val × List Val)) (B : Nat),
    (∀ i (hi : i < fors.length), OpenAt t (B + 176 * i) fors[i]) →
    t.readWords (BitVec.ofNat 64 B) (22 * fors.length) =
      wordsOf (fors.map (fun o => o.1 ++ o.2.flatten)).flatten := by
  intro fors
  induction fors with
  | nil => intro B _; simp [wordsOf_nil]
  | cons o os ih =>
    intro B h
    have h0 := h 0 (by simp)
    simp only [Nat.mul_zero, Nat.add_zero, List.getElem_cons_zero] at h0
    rw [List.length_cons, show 22 * (os.length + 1) = 22 + 22 * os.length by ring, readWords_ofNat_add,
      openAt_words t B o h0, ih (B + 176) (fun i hi => by
        have := h (i + 1) (by simp; omega)
        rw [show B + 176 + 176 * i = B + 176 * (i + 1) by ring]; simpa using this),
      List.map_cons, List.flatten_cons, wordsOf_append (o.1 ++ o.2.flatten) _ (by
        obtain ⟨h1, h2, h3, _⟩ := h0
        simp [h1, length_flatten_vals o.2 h3, h2])]

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

theorem stage_bytes (t : MachineState) (l : Nat) (hl : l < 6) (ls : LayerSig) (h : StageAt t l ls) :
    bytesAt t (0x900 + 856 * l) 4 ++ bytesAt t (0x900 + 856 * l + 8) (672 + 16 * height l) =
      le32 ls.1 ++ ls.2.1.flatten ++ ls.2.2.flatten := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  have hh := height_le l hl
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

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

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
theorem final_bytes (t4 : MachineState) (rho : Val) (fors : List (Val × List Val)) (lays : List LayerSig)
    (hrho : rho.length = 16) (hrw : t4.readWords (BitVec.ofNat 64 0x2650) 2 = wordsOf rho)
    (hfl : fors.length = 14)
    (hopen : ∀ i (hi : i < fors.length), OpenAt t4 (0x2650 + 16 + 176 * i) fors[i])
    (hll : lays.length = 6) (hst : ∀ l (hl : l < lays.length), StageAt t4 l lays[l]) (t5 : MachineState)
    (hw5 : t5.readWords (BitVec.ofNat 64 (0x2650 + 2480)) 575 = packTab.map (packDW t4))
    (hf5 : Frame t4 t5 (fun x => packD ≤ x ∧ x < packD + 8 * 575)) :
    bytesAt t5 0x2650 7080 = serialize rho fors lays := by
  have hfb : (fors.map (fun o => o.1 ++ o.2.flatten)).flatten.length = 2464 := by
    have : ∀ os : List (Val × List Val), (∀ i (hi : i < os.length), OpenAt t4 (0x2650 + 16 + 176 * i) os[i]) →
        True := fun _ _ => trivial
    rw [List.length_flatten, List.map_map]
    have hlen : ∀ o ∈ fors, (o.1 ++ o.2.flatten).length = 176 := by
      intro o ho
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
      obtain ⟨h1, h2, h3, _⟩ := hopen i hi
      simp [h1, length_flatten_vals _ h3, h2]
    rw [List.map_congr_left (fun o ho => by simp only [Function.comp]; exact hlen o ho)]
    simp [hfl]
  rw [show (7080 : Nat) = 2480 + 4600 from rfl, bytesAt_add, pack_layers t4 t5 hw5]
  unfold serialize
  congr 1
  · have hw : t5.readWords (BitVec.ofNat 64 0x2650) 310 =
        wordsOf (rho ++ (fors.map (fun o => o.1 ++ o.2.flatten)).flatten) := by
      rw [hf5.readWords _ _ (by norm_num) (fun i hi => by simp only [packD]; omega), show (310 : Nat) = 2 + 22 * fors.length by rw [hfl], readWords_ofNat_add, hrw,
        fors_words t4 fors _ hopen, wordsOf_append rho _ (by omega)]
    rw [show (2480 : Nat) = 8 * 310 from rfl]
    exact bytesAt_of_readWords _ 310 _ _ (by norm_num) (by norm_num) (by simp [hrho, hfb]) hw
  · rw [← hll]
    refine flatMap_range_eq lays _ _ (fun l hl => ?_)
    rw [List.append_assoc]
    exact (stage_bytes t4 l (by omega) lays[l] (hst l hl)).trans (by rw [List.append_assoc])

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

theorem OpenAt.frame {s t : MachineState} {W : Nat → Prop} {B : Nat} {o : Val × List Val}
    (h : OpenAt s B o) (hf : Frame s t W) (hB : B + 176 + 16 < 2 ^ 64)
    (hW : ∀ a, B ≤ a → a < B + 176 → ¬ W a) : OpenAt t B o := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1, h2, h3, h4.frame hf (by simp [h2]; omega) (fun i hi => ?_)⟩
  simp [h2] at hi
  exact ⟨hW _ (by omega) (by omega), hW _ (by omega) (by omega)⟩

/-- `signList` after the MAC check. -/
def signRest (S cache m : List Byte) : OracleComp HashSpec (Option (List Byte)) :=
  searchDigest S m 0 (2 ^ 20 - 1 + 1) >>= fun r =>
    match r with
    | none => pure none
    | some (rho, N) =>
      signFors S N >>= fun p =>
        hash16 (rootsInput (idxOf N) p.2) >>= fun M =>
          signLayers S cache (idxOf N) 5 M >>= fun r2 =>
            match r2 with
            | none => pure none
            | some lays => pure (some (serialize rho p.1 lays))

theorem signList_eq (S cache m : List Byte) :
    signList S cache m = (H (macInput S (cacheRegion cache)) >>= fun tag =>
      if toList (n := 32) tag = cacheTag cache then signRest S cache m else pure none) := by
  simp only [signList, signRest]
  rfl

/-- Result of `signList`: at a HALT, `a0 = 1` (failure) or `a0 = 0` and the signature. -/
def ListPost (r : Option (List Byte)) (t : MachineState) : Prop :=
  fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
  match r with
  | none => t.getReg .x10 = 1
  | some l => t.getReg .x10 = 0 ∧ readBuffer t 0x2650 7080 = ofList 7080 l

/-- The zero buffers used as padding / P slots, never written by `sign` after the setup. -/
def ZA (a : Nat) : Prop :=
  (0x110 ≤ a ∧ a < 0x120) ∨ (0x6B0 ≤ a ∧ a < 0x6C0) ∨ (0xD0 ≤ a ∧ a < 0xE0) ∨
    (0x350 ≤ a ∧ a < 0x360) ∨ (0x1D0 ≤ a ∧ a < 0x1E0) ∨ (0x230 ≤ a ∧ a < 0x240)

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

/-- Cycle bound after the MAC check (digest search, dig_ok, FORS, roots, layers, pack, HALT prep). -/
def restW : Nat :=
  (2 ^ 20 - 1 + 1) * 46 + 2 + (66 + (14 * forsTreeW + (10 + (8 * 4 + 20) + (5 * layCyc + topCyc + (2321 + 2)))))

/-- Cycle bound of `signList`. -/
def signW : Nat := 54 + (8 * 1025 + (10 + restW))

theorem region_s0 (sk : SecretKey) (cache : Cache) (m : Message) :
    RegionOk (toList cache) (s0 sk cache m) := by
  intro l j hl hj
  have := cacheNodeOff_lt l j hl hj
  have h8 : cacheNodeOff l j % 8 = 0 := by unfold cacheNodeOff; omega
  rw [s0_readWords_cache sk cache m _ 2 h8 (by omega)]; rfl

theorem signRest_sim (sk : SecretKey) (cache : Cache) (m : Message) (u : MachineState)
    (hu : MacOk sk cache m u) :
    Sim image u restW (signRest (toList sk) (toList cache) (toList m)) ListPost := by
  have hS : (toList sk).length = 32 := length_toList sk
  have hcache : (toList cache).length = 131072 := by simp [toList, SigGolf.bytes]; rfl
  have dmem := hu.mem
  have u5 := hu.x5
  have u7 := hu.x7
  have dinv := hu.inv
  have upbS := hu.pbS
  have fs0 := hu.frame
  unfold signRest restW
  refine Sim.bind (digLoop_sim sk m u dmem u5 u7 (2 ^ 20 - 1) 0 u (by norm_num) dinv)
    (fun r t h => ?_)
  rcases r with _ | ⟨rho, N⟩
  · obtain ⟨tpc, t5, t10⟩ := h
    exact (Sim.pure ⟨fetch_ecall t 83 code83 (by norm_num) tpc, t5, t10⟩).mono (by omega)
      (fun _ _ h => h)
  · obtain ⟨tpc, tregs, tframe, hrl, hrw, ⟨ans, hN, hd⟩, hadm⟩ := h
    subst hN
    set N := ans.toNat % 2 ^ 184 with hNdef
    set idx := idxOf N with hidxdef
    have hidx : idx < 2 ^ 34 := Nat.mod_lt _ (by norm_num)
    -- the zero buffers at `t`
    have z0 : ∀ a, a % 8 = 0 → ZA a → (s0 sk cache m).getMem (BitVec.ofNat 64 a) = 0 := by
      intro a h8 hz; simp only [ZA] at hz; exact s0_zero sk cache m a h8 (by omega) (by omega)
    have zt : ∀ a, a % 8 = 0 → ZA a → t.getMem (BitVec.ofNat 64 a) = 0 := by
      intro a h8 hz
      have : ¬ macW a := by simp only [ZA] at hz; simp only [macW, setupW]; omega
      have : ¬ digW a := by simp only [ZA] at hz; simp only [digW]; omega
      rw [tframe.getMem (by simp only [ZA] at hz; omega) (by assumption),
        fs0.getMem (by simp only [ZA] at hz; omega) (by assumption), z0 a h8 hz]
    have zrw : ∀ a, a % 8 = 0 → ZA a → ZA (a + 8) → t.readWords (BitVec.ofNat 64 a) 2 = [0, 0] := by
      intro a h8 h1 h2
      rw [readWords_ofNat_two, zt a h8 h1, zt (a + 8) (by omega) h2]
    have tS : t.readWords (BitVec.ofNat 64 0x6C0) 4 = wordsOf (toList sk) := by
      rw [tframe.readWords _ _ (by norm_num) (by intro i hi; simp only [digW]; omega), upbS]
    have rgt : RegionOk (toList cache) t :=
      ((region_s0 sk cache m).frame fs0 (by intro a ha; simp only [regionA] at ha; simp only [macW, setupW]; omega)).frame
        tframe (by intro a ha; simp only [regionA] at ha; simp only [digW]; omega)
    obtain ⟨tF, hsF, ctx, pcF, x8F, x18F, x22F, sigF, lo228, hi228, rF, fF⟩ :=
      digok_run (toList sk) rho ans t tpc (by rw [tregs.get .x5, u5]) hd
        (zrw _ (by norm_num) (by simp [ZA]) (by simp [ZA])) tS
        (zrw _ (by norm_num) (by simp [ZA]) (by simp [ZA])) (zrw _ (by norm_num) (by simp [ZA]) (by simp [ZA]))
    have zF : ∀ a, a % 8 = 0 → ZA a → tF.getMem (BitVec.ofNat 64 a) = 0 := by
      intro a h8 hz
      rw [fF.getMem (by simp only [ZA] at hz; omega) (by simp only [ZA] at hz; simp only [digokW]; omega),
        zt a h8 hz]
    have rgF : RegionOk (toList cache) tF :=
      rgt.frame fF (by intro a ha; simp only [regionA] at ha; simp only [digokW]; omega)
    refine Sim.steps hsF (Sim.bind (fors_sim (toList sk) hS N tF ctx pcF x8F x18F) (fun p t2 h2 => ?_))
    obtain ⟨-, hl1, hl2, hopen, hrv, hroots, pc2, -, -, fregs, fframe, -, -, -, -, -⟩ := h2
    have pc2' : t2.pc = pcOf 232 := by rw [pc2]; rfl
    have z2 : ∀ a, a % 8 = 0 → ZA a → t2.getMem (BitVec.ofNat 64 a) = 0 := by
      intro a h8 hz
      rw [fframe.getMem (by simp only [ZA] at hz; omega) (by simp only [ZA] at hz; simp only [forsW]; omega),
        zF a h8 hz]
    have z2rw : ∀ a, a % 8 = 0 → ZA a → ZA (a + 8) → t2.readWords (BitVec.ofNat 64 a) 2 = [0, 0] := by
      intro a h8 h1 h2
      rw [readWords_ofNat_two, z2 a h8 h1, z2 (a + 8) (by omega) h2]
    have st2 : Statics (toList sk) t2 := by
      refine ⟨z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]), z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]),
        ?_, z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]), z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA]),
        z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA])⟩
      rw [fframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega),
        fF.readWords _ _ (by norm_num) (by intro i hi; simp only [digokW]; omega), tS]
    have rg2 : RegionOk (toList cache) t2 :=
      rgF.frame fframe (by intro a ha; simp only [regionA] at ha; simp only [forsW]; omega)
    have h228 := fframe.getMem (a := 0x228) (by norm_num) (by simp only [forsW]; omega)
    refine Sim.bind (roots_sim (toList sk) (toList cache) idx hidx p.2 (by rw [hl2]) hrv t2 pc2'
      (by rw [fregs.get .x5, ctx.x5]) (by rw [fregs.get .x22, x22F]) hroots (by rw [h228, lo228])
      (by rw [h228, hi228, tframe.getMem (by norm_num) (by simp only [digW]; omega),
        fs0.getMem (by norm_num) (by simp only [macW, setupW]; omega),
        s0_zero sk cache m 0x228 (by norm_num) (by norm_num) (by omega)]; rfl)
      (z2rw _ (by norm_num) (by simp [ZA]) (by simp [ZA])) st2 rg2) (fun M t3 h3 => ?_)
    obtain ⟨hhead, rframe⟩ := h3
    refine Sim.bind (layers_sim (toList sk) (toList cache) hS hcache idx hidx 5 (le_refl _) M t3 hhead)
      (fun r2 t4 h4 => ?_)
    rcases r2 with _ | lays
    · obtain ⟨pc4, x45, x410⟩ := h4
      exact (Sim.pure ⟨fetch_ecall t4 329 code329 (by norm_num) pc4, x45, x410⟩).mono (by omega)
        (fun _ _ h => h)
    · obtain ⟨hll, hst, pc4, x45, lframe⟩ := h4
      obtain ⟨t5, hs5, pc5, hw5, hf5⟩ := pack_run t4 pc4
      rw [List.drop_zero, List.take_of_length_le (by rw [packTab_length])] at hw5
      have hf5' : Frame t4 t5 (fun x => packD ≤ x ∧ x < packD + 8 * 575) :=
        hf5.mono (fun x hx => by simp only [packD] at hx ⊢; omega)
      have hs6 := symRun_sound blk2960 codeAt_2960 t5 pc5 (by simp only [blk2960.res, rv_simp])
      set t6 := blk2960.res.toState t5 with ht6
      have hc : 2321 + blk2960.res.cycles = 2321 + 2 := rfl
      have mem6 : ∀ a, t6.getMem a = t5.getMem a := by
        intro a; rw [ht6, Result.toState_getMem, show blk2960.res.st.mem = [] from rfl, memEval_nil]
      have by6 : bytesAt t6 0x2650 7080 = bytesAt t5 0x2650 7080 := by
        unfold bytesAt; apply List.map_congr_left; intro i _
        simp only [MachineState.getByte, mem6]
      -- the rho and FORS parts at `t4`
      have ft24 : Frame t2 t4 (fun a => (a = 0x220 ∨ (0x120 ≤ a ∧ a < 0x140)) ∨ layW 5 a) :=
        rframe.trans lframe
      have hrho4 : t4.readWords (BitVec.ofNat 64 0x2650) 2 = wordsOf rho := by
        rw [ft24.readWords _ _ (by norm_num) (by intro i hi; simp only [layW]; omega),
          fframe.readWords _ _ (by norm_num) (by intro i hi; simp only [forsW]; omega), sigF, hrw]
      have hopen4 : ∀ i (hi : i < p.1.length), OpenAt t4 (0x2650 + 16 + 176 * i) p.1[i] := by
        intro i hi
        rw [hl1] at hi
        exact (hopen i (by rw [hl1]; exact hi)).frame ft24 (by omega) (by
          intro a h1 h2; simp only [layW]; omega)
      refine (Sim.pure_steps (hs5.trans hs6) ⟨fetch_ecall t6 2962 code2962 (by norm_num) rfl,
        by simp only [ht6, blk2960.res, rv_simp], by simp only [ht6, blk2960.res, rv_simp], ?_⟩).mono
        (by rw [hc]) (fun _ _ h => h)
      rw [readBuffer_bytesAt, by6, final_bytes t4 rho p.1 lays hrl hrho4 hl1 hopen4 hll hst t5 hw5 hf5']

theorem signList_sim (sk : SecretKey) (cache : Cache) (m : Message) :
    Sim image (s0 sk cache m) signW (signList (toList sk) (toList cache) (toList m)) ListPost := by
  rw [signList_eq]
  exact mac_sim sk cache m _ restW ListPost (fun u hu => signRest_sim sk cache m u hu)
    (fun t tpc t5 t10 => ⟨fetch_ecall t 86 code86 (by norm_num) tpc, t5, t10⟩)

end SigGolfCandidate.Sign

namespace SigGolfCandidate.Sign
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv SigGolfCandidate.Ref SigGolfCandidate.Mem

/-- Final states: at a HALT whose output is `signRef`'s value. -/
def SignPost (a : Option (Bytes 7080)) (t : MachineState) : Prop :=
  fetch image t = some (.base .ECALL) ∧ t.getReg .x5 = 1 ∧
  a = if t.getReg .x10 = 0 then some (readBuffer t 0x2650 7080) else none
set_option maxRecDepth 100000 in

theorem signRef_sim (sk : SecretKey) (cache : Cache) (m : Message) :
    Sim image (s0 sk cache m) signW (signRef sk cache m) SignPost := by
  unfold signRef
  refine (Sim.bind (signList_sim sk cache m) (fun r t h => Sim.pure ?_)).mono (by omega) (fun _ _ h => h)
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h2, ?_⟩
  rcases r with _ | l
  · simp only at h3; rw [h3]; simp
  · obtain ⟨h4, h5⟩ := h3
    rw [h4, if_pos rfl, h5]; rfl

theorem signW_lt : signW + 1 < CYCLE_LIMIT := by
  unfold signW restW forsTreeW layCyc topCyc treeCyc tleafCyc CYCLE_LIMIT; norm_num

set_option maxRecDepth 100000 in
/-- **Refinement** (value, #hash calls, #compressions) of the `sign` phase. -/
theorem sign_refines (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => (r.value, r.hashCalls, r.hashCompressions)) <$> submission.run .sign (sk, cache, m) =
      countBoth (signRef sk cache m) :=
  (Sim.run_eq submission .sign (sk, cache, m) (initialState_eq sk cache m) (signRef_sim sk cache m)
    (by have := signW_lt; omega) id (fun a t h => ⟨h.1, h.2.1, h.2.2⟩)).trans (id_map _)

set_option maxRecDepth 100000 in
/-- **Refinement** including `finished = true`. -/
theorem sign_refines_finished (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => (r.value, r.finished, r.hashCalls, r.hashCompressions)) <$>
        submission.run .sign (sk, cache, m) =
      (fun p => (p.1, true, p.2.1, p.2.2)) <$> countBoth (signRef sk cache m) :=
  Sim.run_eq_fin submission .sign (sk, cache, m) (initialState_eq sk cache m) (signRef_sim sk cache m)
    (by have := signW_lt; omega) id (fun a t h => ⟨h.1, h.2.1, h.2.2⟩)

set_option maxRecDepth 100000 in
/-- **Termination** of `sign` for every fixed oracle and input. -/
theorem sign_terminates (hash : Hash) (sk : SecretKey) (cache : Cache) (m : Message) :
    (submission.runWith hash .sign (sk, cache, m)).finished = true ∧
      (submission.runWith hash .sign (sk, cache, m)).cycles < CYCLE_LIMIT := by
  obtain ⟨h1, h2⟩ := Sim.runWith submission .sign (sk, cache, m) (initialState_eq sk cache m)
    (signRef_sim sk cache m) signW_lt (fun a t h => ⟨h.1, h.2.1⟩) hash
  exact ⟨h1, by have := signW_lt; omega⟩

theorem proj_map {α β γ : Type} (x : OracleComp HashSpec α) (y : OracleComp HashSpec β) (g : α → β)
    (f : β → γ) (h : g <$> x = y) : (fun r => f (g r)) <$> x = f <$> y := by
  subst h; rw [Functor.map_map]

set_option maxRecDepth 100000 in
/-- Calls and compressions separately (`countCalls`, `countBlocks` of `Ref.Count`). -/
theorem sign_calls (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => (r.value, r.hashCalls)) <$> submission.run .sign (sk, cache, m) =
      countCalls (signRef sk cache m) := by
  rw [← countBoth_calls]; exact proj_map _ _ _ (fun p => (p.1, p.2.1)) (sign_refines sk cache m)

set_option maxRecDepth 100000 in
theorem sign_blocks (sk : SecretKey) (cache : Cache) (m : Message) :
    (fun r => (r.value, r.hashCompressions)) <$> submission.run .sign (sk, cache, m) =
      countBlocks (signRef sk cache m) := by
  rw [← countBoth_blocks]; exact proj_map _ _ _ (fun p => (p.1, p.2.2)) (sign_refines sk cache m)

end SigGolfCandidate.Sign
