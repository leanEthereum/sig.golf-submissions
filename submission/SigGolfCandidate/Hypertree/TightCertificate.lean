import SigGolfCandidate.Hypertree.Certificate

/-!
A sharper certificate for the existing images. The old bound charges all 160
layers as WOTS layers. The bottom layer instead uses a single hash leaf
(116 rather than 36,144 cycles), skips digit encoding (5 rather than 460
instructions), and advances in 17 rather than 18 instructions. Retaining
these three distinctions saves 36,484 cycles in the universal bound.

This changes the proved bound, not the algorithm or its measured runtime.
The existing completeness, termination, budgets, and security proofs are reused.
-/

namespace SigGolfCandidate.Hypertree.TightVerifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying
set_option maxRecDepth 4096
attribute [local instance] Classical.propDecidable

theorem recover_leaf_call (hash : Hash) (s : MachineState) (level tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (data : LayerData s level tree base side message signature)
    (leaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (small : level < 160) (aligned : base % 8 = 0) (bound : base+752 ≤ 0x80000) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 33795 ∧ cycles ≤ (if level = 0 then 116 else 36144) ∧ calls ≤ 323 ∧ blocks ≤ 334 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.recoverLeaf hash level tree side message signature).extractLsb' (64*i.val) 64) ∧
      (∀ a, a ≠ 0xffffe0 → OutsideUpperLeaf side a → final.getMem a = s.getMem a) := by
  by_cases zero : level = 0
  · subst level
    obtain ⟨final, run, fpc, fsp, output, frame⟩ := KeygenVerifyBottom.call hash s tree side base message signature pc sp
      (data.bottom s tree base side message signature leaf) aligned (by omega)
    refine ⟨final, 109, 116, 1, 1, run, by decide, by decide, by decide, by decide, fpc, fsp, output, ?_⟩
    intro a hs outside
    apply frame a hs outside.1.2.2.2.2.1 outside.1.2.2.2.2.2
    exact ⟨fun i => outside.1.1 ⟨i.val, by have := i.isLt; omega⟩, outside.1.2.1, outside.1.2.2.1, outside.2⟩
  · have nonzero : BitVec.ofNat 64 level ≠ 0 := by
      intro eq
      have h := congrArg BitVec.toNat eq
      change level % 2^64 = 0 at h
      omega
    obtain ⟨final, steps, cycles, calls, run, hsteps, hcycles, hcalls, fpc, fsp, output, frame⟩ :=
      upper_leaf_call hash s level tree side base message signature pc sp
        (data.upper s level tree base side message signature zero leaf) nonzero aligned (by omega)
    exact ⟨final, steps, cycles, calls+1, calls+12, run, hsteps, by simpa [zero] using hcycles, by omega, by omega, fpc, fsp, output, frame⟩

theorem prepare_tree (s : MachineState) (level index : Nat) (side : Bool)
    (current : Reference.Digest) (witness : Bytes signatureBytes)
    (pc : s.pc = 0x11bc) (small : level < 160)
    (data : LoopData s level index current witness)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber side)) :
    ∃ ready steps, OrdinarySteps verify s steps ready ∧ steps ≤ (if level = 0 then 5 else 460) ∧
      ready.pc = 0x12f0 ∧ ready.getReg .x1 = 0x11d4 ∧ ready.getReg .x2 = 0x1000000 ∧
      LayerData ready level index (0x3d3b0+layerOffset level) side current (wireLayer witness level) ∧
      LowFrame s ready := by
  obtain ⟨ready, run, readyPC, readyRA, readySP, digits, frame⟩ :=
    dispatch_to_tree verify 0x11bc verify_dispatch_code verify_encode_code (by decide) s current pc
      data.stack (data.currentEq 0) (data.currentEq 1)
  have words (address : Nat) (aligned : address % 8 = 0) (bound : address+8 < 2^64)
      (separate : address+8 ≤ 0x80600 ∨ 0x80630 ≤ address) (saved : address ≠ 0xfffff0) :
      ready.getMem (BitVec.ofNat 64 address) = s.getMem (BitVec.ofNat 64 address) :=
    dispatch_frame_words s ready data.stack frame address aligned bound separate saved
  have lowFrame : LowFrame s ready := by
    intro address aligned bound
    exact words address aligned (by omega) (Or.inl (by omega)) (by omega)
  have stored : WitnessStored ready witness := data.witnessEq.transfer_words s ready witness lowFrame
  refine ⟨ready, _, run, ?_, readyPC, readyRA, readySP.trans data.stack, ?_, lowFrame⟩
  · rw [data.levelEq]
    simp only [level_word_zero level small]
    split <;> decide
  · constructor
    · exact (words 0x80400 (by decide) (by decide) (by decide) (by decide)).trans data.levelEq
    · intro i
      have keep := words (0x80408+8*i.val) (by omega) (by have := i.isLt; omega)
        (Or.inl (by have := i.isLt; omega)) (by have := i.isLt; omega)
      change ready.getMem (wordAddress 0x80408 i.val) = s.getMem (wordAddress 0x80408 i.val) at keep
      rw [keep]
      exact data.indexEq i
    · exact (words 0x80448 (by decide) (by decide) (by decide) (by decide)).trans data.pointerEq
    · exact (words 0x80420 (by decide) (by decide) (by decide) (by decide)).trans selector
    · intro chain relevant i
      simpa only [Nat.add_assoc] using wire_layer_value ready witness stored level small chain relevant i
    · intro nonzero chain
      apply digits ?_ chain
      rw [data.levelEq]
      exact (level_word_zero level small).not.mpr nonzero
    · intro i
      simpa only [Nat.add_assoc] using wire_layer_sibling ready witness stored level small i

theorem recover_tree_call (hash : Hash) (s : MachineState) (level tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x12f0) (sp : s.getReg .x2 = 0x1000000)
    (data : LayerData s level tree base side message signature)
    (small : level < 160) (aligned : base % 8 = 0) (bound : base+752 ≤ 0x80000) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 33908 ∧ cycles ≤ (if level = 0 then 236 else 36264) ∧ calls ≤ 324 ∧ blocks ≤ 335 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (wordAddress 0x80500 i.val) =
        (Reference.recoverLayer hash level tree side message signature).extractLsb' (64*i.val) 64) ∧
      (∀ a, Verifying.OutsideTreeWork a → final.getMem a = s.getMem a) := by
  have pre := VerifyTreeEntry.block s pc sp
  have entryData := tree_entry_context s level tree base side message signature sp data bound
  have entryLeaf : (VerifyTreeEntry.ready s).getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side) := by
    rw [VerifyTreeEntry.leaf s sp]
    exact data.selectorEq
  obtain ⟨recovered, leafSteps, leafCycles, leafCalls, leafBlocks, leafRun, hsteps, hcycles, hcalls, hblocks,
    leafPC, leafSP, output, leafFrame⟩ := recover_leaf_call hash (VerifyTreeEntry.ready s) level tree base side
      message signature (VerifyTreeEntry.pc s pc) (VerifyTreeEntry.stack s sp) entryData entryLeaf small aligned bound
  have recoveredPC : recovered.pc = 0x1314 := by rw [leafPC, VerifyTreeEntry.ra s pc]; rfl
  have recoveredSP : recovered.getReg .x2 = 0xfffff0 := leafSP.trans (VerifyTreeEntry.stack s sp)
  have recoveredData : LayerData recovered level tree base side message signature := by
    apply entryData.transfer _ _ level tree base side message signature bound
    intro a outside
    exact leafFrame a outside.2.2.2.2.1 ⟨outside.1, outside.2.1 side⟩
  obtain ⟨final, postSteps, postCycles, post, psteps, pcycles, finalPC, finalSP, current, postFrame⟩ :=
    finish_tree hash recovered level tree base side message signature recoveredPC recoveredSP small aligned bound
      recoveredData.levelEq recoveredData.indexEq recoveredData.pointerEq recoveredData.selectorEq output recoveredData.siblingEq
  refine ⟨final, 9+leafSteps+postSteps, 9+leafCycles+postCycles, leafCalls+1, leafBlocks+1,
    ?_, by omega, by split_ifs at * <;> omega, by omega, by omega, ?_, ?_, current, ?_⟩
  · simpa only [Nat.zero_add] using (pre.trace.trans leafRun).trans post
  · rw [finalPC, leafFrame _ (by decide) (by unfold OutsideUpperLeaf Verifying.OutsideLeafWork; cases side <;> decide),
      VerifyTreeEntry.saved s sp]
  · rw [finalSP, sp]
  · intro a outside
    have parent : OutsideParentWork side a :=
      ⟨fun i => outside.1.1 ⟨i.val, by have := i.isLt; omega⟩, outside.1.2.1, outside.2.2.1, outside.2.1 (!side)⟩
    rw [postFrame a parent, leafFrame a outside.2.2.2.2.1 ⟨outside.1, outside.2.1 side⟩,
      VerifyTreeEntry.frame s sp a outside.2.2.2.1 outside.2.2.2.2.2]

theorem verify_layer_tree (hash : Hash) (s : MachineState) (level index : Nat) (side : Bool)
    (current : Reference.Digest) (witness : Bytes signatureBytes)
    (pc : s.pc = 0x11bc) (small : level < 160)
    (data : LoopData s level index current witness)
    (selector : s.getMem 0x80420 = BitVec.ofNat 64 (Reference.sideNumber side)) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 34368 ∧ cycles ≤ (if level = 0 then 241 else 36724) ∧ calls ≤ 324 ∧ blocks ≤ 335 ∧
      final.pc = 0x11d4 ∧
      LoopData final level index (Reference.recoverLayer hash level index side current (wireLayer witness level)) witness ∧
      LowFrame s final := by
  obtain ⟨ready, preSteps, pre, preBound, rpc, rra, rsp, readyData, preFrame⟩ :=
    prepare_tree s level index side current witness pc small data selector
  have bound := layer_pointer_bound 0x3d3b0 level (by decide) small
  obtain ⟨final, steps, cycles, calls, blocks, run, hsteps, hcycles, hcalls, hblocks, fpc, fsp, output, frame⟩ :=
    recover_tree_call hash ready level index (0x3d3b0+layerOffset level) side current (wireLayer witness level)
      rpc rsp readyData small (layer_pointer_aligned _ _ (by decide)) bound
  have finalData := readyData.transfer ready final level index (0x3d3b0+layerOffset level) side current
    (wireLayer witness level) bound frame
  have treeFrame : LowFrame ready final := by
    intro address _ low
    exact frame _ (outside_tree_low _ (by change address % 2^64 < 0x80000; omega))
  have totalFrame := preFrame.trans s ready final treeFrame
  refine ⟨final, preSteps+steps, preSteps+cycles, calls, blocks, ?_, by split_ifs at * <;> omega, by split_ifs at * <;> omega, hcalls, hblocks, ?_, ?_, totalFrame⟩
  · simpa only [Nat.zero_add] using pre.trace.trans run
  · rw [fpc, rra]; rfl
  · exact ⟨fsp.trans rsp, finalData.levelEq, finalData.indexEq, finalData.pointerEq,
      output, data.witnessEq.transfer_words s final witness totalFrame⟩

theorem verify_layer (hash : Hash) (s : MachineState) (level index : Nat)
    (current : Reference.Digest) (witness : Bytes signatureBytes)
    (pc : s.pc = 0x1148) (small : level < 160) (indexSmall : index < 2^192)
    (data : LoopData s level index current witness) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 34415 ∧ cycles ≤ (if level = 0 then 287 else 36771) ∧ calls ≤ 324 ∧ blocks ≤ 335 ∧
      final.pc = (if level+1 = 160 then 0x1220 else 0x1148) ∧
      LoopData final (level+1) (index/2)
        (Reference.recoverLayer hash level (index/2) (index%2 == 1) current (wireLayer witness level)) witness ∧
      LowFrame s final := by
  have pre := Verifying.shiftIndexState_block s pc
  have shiftedPC : (shiftIndexState s).pc = 0x11bc := by rw [shiftIndexState_pc, pc]; rfl
  have shiftedData := data.shift s level index current witness indexSmall
  have selected := (shift_index_nat s index indexSmall data.indexEq).2
  obtain ⟨recovered, steps, cycles, calls, blocks, run, hsteps, hcycles, hcalls, hblocks, recoveredPC, recoveredData, frame⟩ :=
    verify_layer_tree hash (shiftIndexState s) level (index/2) (index%2 == 1) current witness shiftedPC small shiftedData selected
  have post := advance_block verify 0x11d4 verify_advance_code recovered recoveredPC
  have finalData := recoveredData.advance recovered level (index/2) _ witness small
  have finalPC := advanceState_layer_pc recovered 0x11d4 level recoveredPC small recoveredData.levelEq
  let n := if recovered.getMem 0x80400 = 0 then 17 else 18
  have hn : n ≤ (if level = 0 then 17 else 18) := by
    simp only [n, recoveredData.levelEq, level_word_zero level small, Nat.le_refl]
  refine ⟨advanceState recovered, 29+steps+n, 29+cycles+n, calls, blocks, ?_, by split_ifs at * <;> omega, by split_ifs at * <;> omega, hcalls, hblocks,
    ?_, finalData, ?_⟩
  · simpa only [Nat.zero_add, Nat.add_zero] using (pre.trace.trans run).trans post.trace
  · simpa using finalPC
  · exact ((shift_low_frame s).trans s _ recovered frame).trans s recovered _ (advance_low_frame recovered)

theorem verify_layers (hash : Hash) (witness : Bytes signatureBytes) (count level index : Nat)
    (s : MachineState) (current : Reference.Digest)
    (remaining : level+count = 160) (indexSmall : index < 2^192)
    (pc : s.pc = if count = 0 then 0x1220 else 0x1148)
    (data : LoopData s level index current witness) :
    ∃ final steps cycles calls blocks lastIndex, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 34415*count ∧ cycles ≤ 36771*count - (if level = 0 then 36484 else 0) ∧ calls ≤ 324*count ∧ blocks ≤ 335*count ∧
      final.pc = 0x1220 ∧
      LoopData final 160 lastIndex (Reference.recoverLayers hash level index current (wireLayers witness count level)) witness ∧
      LowFrame s final := by
  induction count generalizing level index s current with
  | zero =>
    have levelEq : level = 160 := by omega
    subst level
    exact ⟨s, 0, 0, 0, 0, index, Trace.refl _, by decide, by decide, by decide, by decide, by simpa using pc, data,
      fun _ _ _ => rfl⟩
  | succ count ih =>
    have small : level < 160 := by omega
    obtain ⟨next, steps, cycles, calls, blocks, run, hsteps, hcycles, hcalls, hblocks, nextPC, nextData, frame⟩ :=
      verify_layer hash s level index current witness (by simpa using pc) small indexSmall data
    have nextPC' : next.pc = if count = 0 then 0x1220 else 0x1148 := by
      have eq : level+1 = 160 ↔ count = 0 := by omega
      simpa only [eq] using nextPC
    obtain ⟨final, tailSteps, tailCycles, tailCalls, tailBlocks, lastIndex, tailRun, tsteps, tcycles, tcalls, tblocks,
      finalPC, finalData, tailFrame⟩ := ih (level+1) (index/2) next
        (Reference.recoverLayer hash level (index/2) (index%2 == 1) current (wireLayer witness level))
        (by omega) (by omega) nextPC' nextData
    refine ⟨final, steps+tailSteps, cycles+tailCycles, calls+tailCalls, blocks+tailBlocks, lastIndex,
      run.trans tailRun, ?_, ?_, ?_, ?_, finalPC, finalData, frame.trans s next final tailFrame⟩
    all_goals split_ifs at * <;> omega

theorem loaded_recovery (hash : Hash) (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes) :
    ∃ initial recovered steps cycles calls blocks,
      initialState submission .verify (message, pk, witness) = some initial ∧
      Trace hash verify initial steps cycles calls blocks recovered ∧
      steps ≤ 5506530 ∧ cycles ≤ 5847021 ∧ calls ≤ 51841 ∧ blocks ≤ 53602 ∧
      recovered.pc = 0x1220 ∧
      (RootMatches recovered ↔ Reference.verify hash pk message (SignatureEncoding.decode witness).toReference) := by
  obtain ⟨initial, ready, loaded, pre, pc, data, preFrame⟩ := loaded_loop_data hash pk message witness
  let index := (Reference.indexOf hash message (SignatureEncoding.decode witness).randomizer).toNat
  have indexSmall : index < 2^192 := by
    have h := (Reference.indexOf hash message (SignatureEncoding.decode witness).randomizer).isLt
    dsimp [index]
    omega
  obtain ⟨recovered, steps, cycles, calls, blocks, lastIndex, run, hsteps, hcycles, hcalls, hblocks, finalPC, finalData, frame⟩ :=
    verify_layers hash witness 160 0 index ready 0 rfl indexSmall (by simpa using pc) data
  change cycles ≤ 5846876 at hcycles
  have allFrame := preFrame.trans initial ready recovered frame
  have pkWords : ∀ i : Fin 2, recovered.getMem (wordAddress 0x40 i.val) = pk.extractLsb' (64*i.val) 64 := by
    intro i
    have same := allFrame (0x40+8*i.val) (by omega) (by have := i.isLt; omega)
    change recovered.getMem (wordAddress 0x40 i.val) = initial.getMem (wordAddress 0x40 i.val) at same
    rw [same]
    exact loaded_publicKey_word pk message witness initial loaded i
  have matchRoot := root_matches_iff recovered _ pk finalData.currentEq pkWords
  refine ⟨initial, recovered, 130+steps, 145+cycles, 1+calls, 2+blocks,
    loaded, pre.trans run, by omega, by omega, by omega, by omega, finalPC, ?_⟩
  rw [matchRoot, wire_layers_decode]
  have length : (SignatureEncoding.decode witness).toReference.layers.length = 160 := by
    simp [SignatureEncoding.decode, SignatureEncoding.Compact.toReference]
  simp only [Reference.verify, length, true_and]
  rfl

theorem run_refines (hash : Hash) (pk : PublicKey) (message : Message) (witness : Bytes signatureBytes) :
    ∃ cycles calls blocks, cycles ≤ 5847036 ∧ calls ≤ 51841 ∧ blocks ≤ 53602 ∧
      submission.runWith hash .verify (message, pk, witness) =
        ⟨if Reference.verify hash pk message (SignatureEncoding.decode witness).toReference then some () else none,
          true, cycles, calls, blocks⟩ := by
  classical
  obtain ⟨initial, recovered, steps, cycles, calls, blocks, loaded, run, hsteps, hcycles, hcalls, hblocks, pc, accepted⟩ :=
    loaded_recovery hash pk message witness
  obtain ⟨tailSteps, final, tailBound, tailRun, _⟩ := verify_footer_executes hash recovered pc
  have execution := run.then_executes tailRun
  have actual := runWith_of_executes submission hash .verify (message, pk, witness) initial (steps+tailSteps)
    _ loaded execution (by change steps+tailSteps ≤ 2^32; omega)
  refine ⟨cycles+tailSteps, calls, blocks, by omega, hcalls, hblocks, ?_⟩
  rw [actual]
  by_cases yes : RootMatches recovered
  · have valid := accepted.mp yes
    simp only [if_pos yes, if_pos valid, Execution.charge, Nat.add_zero]
    rfl
  · have invalid : ¬Reference.verify hash pk message (SignatureEncoding.decode witness).toReference :=
      fun h => yes (accepted.mpr h)
    simp only [if_neg yes, if_neg invalid, Execution.charge, Nat.add_zero]
    rfl

end SigGolfCandidate.Hypertree.TightVerifying

namespace SigGolfCandidate.Hypertree.TightCandidate
open SigGolf OracleComp KeygenOrganizer SignatureEncoding Candidate
set_option maxRecDepth 4096

theorem honest_exact (hash : Hash) (secretKey : SecretKey) (message : Message) :
    ∃ cycles calls blocks, cycles≤5847036 ∧ calls≤51841 ∧ blocks≤53602 ∧
      evalWithAnswerFn hash (submission.honest secretKey message)=
        ⟨true,fun phase => match phase with | .keygen => 761 | .sign => 121008 | .expand => 0 | .verify => blocks,cycles⟩ := by
  let pk := Reference.keygen hash secretKey
  let signature := (signCompact hash secretKey message).wire (signCompact_valid hash secretKey message)
  obtain ⟨signCycles,_,signRun⟩ := Signing.sign_run_refines hash secretKey KeygenFunctional.zeroCache message
  obtain ⟨cycles,calls,blocks,cycleBound,callBound,blockBound,verifyRun⟩ := TightVerifying.run_refines hash pk message signature
  have correct : Reference.verify hash pk message (decode signature).toReference := by
    rw [wire_decode]
    exact signCompact_correct hash secretKey message
  rw [if_pos correct] at verifyRun
  refine ⟨cycles,calls,blocks,cycleBound,callBound,blockBound,?_⟩
  rw [honest_eq_pipeline]
  exact pipeline_success hash (submission.run .keygen secretKey)
    (fun _ c => submission.run .sign (secretKey,c,message))
    (fun p sig => submission.run .expand (message,p,sig))
    (fun p wit => submission.run .verify (message,p,wit)) pk KeygenFunctional.zeroCache signature signature
    82446 739 761 signCycles 117508 121008 89733 0 0 cycles calls blocks
    (KeygenFunctional.run_exact hash secretKey) signRun (expand_exact hash message pk signature) verifyRun

theorem verificationBound : submission.VerificationBound 5847036 := by
  intro hash secretKey message
  dsimp only
  intro _
  obtain ⟨cycles,calls,blocks,cycleBound,_,_,run⟩ := honest_exact hash secretKey message
  rw [run]
  exact cycleBound

/-- Tighter certificate for exactly the original program images: the bottom layer has no WOTS chains. -/
theorem certificate : SigGolf.Certificate submission 5847036 :=
  ⟨admitted, Candidate.termination, Candidate.completeness, Candidate.compressionBounds,
    Candidate.security, verificationBound⟩

/-- info: 'SigGolfCandidate.Hypertree.TightCandidate.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate

end SigGolfCandidate.Hypertree.TightCandidate
