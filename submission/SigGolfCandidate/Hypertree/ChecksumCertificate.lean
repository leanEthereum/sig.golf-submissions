import SigGolfCandidate.Hypertree.ChecksumBound

/-!
Propagate the checksum-aware chain bound through the exact original bytecode.
Each upper layer saves 14 × 103 = 1,442 cycles relative to TightCertificate,
and there are 159 such layers. The bottom-layer bound remains 287 cycles.
This lowers the certificate by 229,278 cycles without changing any image.
-/

namespace SigGolfCandidate.Hypertree.ChecksumVerifying
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Signing Verifying KeygenVerifyCount
set_option maxRecDepth 4096
attribute [local instance] Classical.propDecidable

theorem leaf_loop_exact (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest) (start remaining : Nat)
    (length : start+remaining = 46) (pc : s.pc = if start = 46 then 0x1690 else 0x1490)
    (data : LeafData s level tree side base message values) (counter : s.getMem 0x80430 = BitVec.ofNat 64 start)
    (completed : EndpointPrefix s (recoveredEndpoint hash level tree side message values) start)
    (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles calls calls final ∧
      steps ≤ 721*remaining ∧ cycles = 103*calls + 49*remaining ∧ calls ≤ 7*remaining ∧ final.pc = 0x1690 ∧
      final.getMem 0x80430 = 46 ∧ LeafData final level tree side base message values ∧
      EndpointPrefix final (recoveredEndpoint hash level tree side message values) 46 ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, Verifying.OutsideLeafWork a → final.getMem a = s.getMem a) ∧
      calls + chainPrefix message start = chainPrefix message 46 := by
  induction remaining generalizing s start with
  | zero =>
    have startEq : start = 46 := by omega
    subst start
    refine ⟨s, 0, 0, 0, Trace.refl s, by omega, by omega, by omega, ?_, ?_, data, completed, rfl, rfl, ?_, by simp⟩
    · simpa using pc
    · exact counter
    · intro _ _; rfl
  | succ remaining ih =>
    have startLt : start < 46 := by omega
    let chain : Reference.Chain := ⟨start, startLt⟩
    have atLoop : s.pc = 0x1490 := by simpa only [if_neg (by omega : start ≠ 46)] using pc
    obtain ⟨next, pre, nextPC, nextCounter, nextData, output, nextRA, nextSP, nextFrame⟩ :=
      leaf_step hash s level tree side base message values chain atLoop data counter aligned bound
    have nextPrefix : EndpointPrefix next (recoveredEndpoint hash level tree side message values) (start+1) := by
      intro c hc i
      by_cases same : c.val = start
      · have eq : c = chain := Fin.ext same
        subst c
        exact output i
      · have before : c.val < start := by omega
        have neCounter : KeygenEndpoint.endpointAddress c.val i.val ≠ 0x80430 := by
          intro eq
          have h := congrArg BitVec.toNat eq
          have hc := c.isLt
          have hi := i.isLt
          change (0x80800+16*c.val+8*i.val) % 2^64 = 0x80430 at h
          omega
        rw [nextFrame _ (endpoint_outside_chain c i) neCounter]
        · exact completed c before i
        · intro j
          exact endpointAddress_ne c chain i j (fun eq => same (congrArg Fin.val eq))
    obtain ⟨final, steps, cycles, calls, run, hsteps, hcycles, hcalls, finalPC, finalCounter,
      finalData, finalPrefix, finalRA, finalSP, finalFrame, exactCalls⟩ :=
      ih next (start+1) (by omega) nextPC nextData nextCounter nextPrefix
    refine ⟨final, (96*(7-(Reference.digit message chain).val)+49)+steps,
      (103*(7-(Reference.digit message chain).val)+49)+cycles,
      (7-(Reference.digit message chain).val)+calls, pre.trans run, ?_, ?_, ?_,
      finalPC, finalCounter, finalData, finalPrefix, finalRA.trans nextRA, finalSP.trans nextSP, ?_, ?_⟩
    · omega
    · omega
    · omega
    · intro a outside
      exact (finalFrame a outside).trans (nextFrame a (outside_leaf_chain a outside)
        outside.2.2.2.2.1 (outside_leaf_endpoint a outside chain))

    · rw [chainPrefix_succ message start startLt] at exactCalls
      change (7-(Reference.digit message ⟨start,startLt⟩).val)+calls+chainPrefix message start = _
      omega

theorem recover_all_chains (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest)
    (pc : s.pc = 0x1490) (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = 0) (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles calls calls final ∧
      steps ≤ 33166 ∧ cycles ≤ 33978 ∧ calls ≤ 322 ∧ final.pc = 0x1690 ∧
      final.getMem 0x80430 = 46 ∧ LeafData final level tree side base message values ∧
      (∀ chain : Reference.Chain, ∀ i : Fin 2,
        final.getMem (KeygenEndpoint.endpointAddress chain.val i.val) =
          (recoveredEndpoint hash level tree side message values chain).extractLsb' (64*i.val) 64) ∧
      final.getReg .x1 = s.getReg .x1 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ a, Verifying.OutsideLeafWork a → final.getMem a = s.getMem a) := by
  obtain ⟨final, steps, cycles, calls, run, hsteps, hcycles, hcalls, finalPC, finalCounter,
    finalData, endpoints, finalRA, finalSP, frame, exactCalls⟩ := leaf_loop_exact hash s level tree side base message values 0 46 rfl pc
      data counter (by intro c hc; omega) aligned bound
  have callsBound : calls ≤ 308 := by
    simpa only [chainPrefix_zero, Nat.add_zero] using exactCalls.le.trans (chainPrefix_bound message)
  exact ⟨final, steps, cycles, calls, run, hsteps, by omega, hcalls, finalPC, finalCounter,
    finalData, fun c => endpoints c c.isLt, finalRA, finalSP, frame⟩

theorem upper_leaf_body (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (values : Reference.Chain → Reference.Digest)
    (pc : s.pc = 0x1490) (data : LeafData s level tree side base message values)
    (counter : s.getMem 0x80430 = 0) (sp : s.getReg .x2 = 0xffffe0)
    (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles (calls+1) (calls+12) final ∧
      steps ≤ 33781 ∧ cycles ≤ 34688 ∧ calls ≤ 322 ∧
      final.pc = s.getMem 0xffffe0 &&& ~~~1#64 ∧ final.getReg .x2 = 0xfffff0 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.compressLeaf hash level tree side (recoveredEndpoint hash level tree side message values)).extractLsb' (64*i.val) 64) ∧
      (∀ a, OutsideUpperLeaf side a → final.getMem a = s.getMem a) := by
  obtain ⟨ready, steps, cycles, calls, loop, hsteps, hcycles, hcalls, readyPC, _,
    readyData, endpoints, _, readySP, loopFrame⟩ := recover_all_chains hash s level tree side base message values
      pc data counter aligned bound
  have words : ∀ i : Fin 92, ready.getMem (wordAddress 0x80800 i.val) =
      KeygenLeafHeader.endpointWord (recoveredEndpoint hash level tree side message values) i := by
    intro i
    have addr : KeygenEndpoint.endpointAddress (i.val/2) (i.val%2) = wordAddress 0x80800 i.val := by
      unfold KeygenEndpoint.endpointAddress wordAddress
      apply congrArg (BitVec.ofNat 64)
      omega
    rw [← addr]
    exact endpoints ⟨i.val/2, by have := i.isLt; omega⟩ ⟨i.val%2, by omega⟩
  have stack : ready.getReg .x2 = 0xffffe0 := readySP.trans sp
  obtain ⟨final, suffix, finalPC, finalSP, output, suffixFrame⟩ := KeygenLeaf.compute_return verify hash 0x1690
    verify_leaf_hash_code leaf_return_code ready readyPC level tree side
    (recoveredEndpoint hash level tree side message values) readyData.levelEq readyData.leafEq readyData.indexEq words
    (by rw [stack]; decide) (by rw [stack]; decide) (by rw [stack]; decide)
    (by rw [stack]; cases side <;> decide)
  refine ⟨final, steps+615, cycles+710, calls, loop.trans suffix, by omega, by omega, hcalls, ?_, ?_, output, ?_⟩
  · rw [finalPC, stack, loopFrame _ (by unfold Verifying.OutsideLeafWork; decide)]
  · rw [finalSP, stack]; rfl
  · intro a outside
    exact (suffixFrame a outside.1.1 outside.1.2.1 outside.2).trans (loopFrame a outside.1)

theorem upper_leaf_call (hash : Hash) (s : MachineState) (level tree : Nat) (side : Bool) (base : Nat)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (data : LeafData s level tree side base message signature.values)
    (nonzero : BitVec.ofNat 64 level ≠ 0) (aligned : base % 8 = 0) (bound : base+736 ≤ 0x80000) :
    ∃ final steps cycles calls, Trace hash verify s steps cycles (calls+1) (calls+12) final ∧
      steps ≤ 33795 ∧ cycles ≤ 34702 ∧ calls ≤ 322 ∧
      final.pc = s.getReg .x1 &&& ~~~1#64 ∧ final.getReg .x2 = s.getReg .x2 ∧
      (∀ i : Fin 2, final.getMem (KeygenSavePublic.wordAddress side i.val) =
        (Reference.recoverLeaf hash level tree side message signature).extractLsb' (64*i.val) 64) ∧
      (∀ a, a ≠ 0xffffe0 → OutsideUpperLeaf side a → final.getMem a = s.getMem a) := by
  obtain ⟨ready, pre, rpc, rdata, counter, rsp, saved, entryFrame⟩ :=
    prepare_upper_leaf hash s level tree side base message signature pc sp data nonzero aligned bound
  obtain ⟨final, steps, cycles, calls, body, hsteps, hcycles, hcalls, finalPC, finalSP, output, frame⟩ :=
    upper_leaf_body hash ready level tree side base message signature.values rpc rdata counter rsp aligned bound
  refine ⟨final, 14+steps, 14+cycles, calls, ?_, by omega, by omega, hcalls, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add] using pre.trans body
  · rw [finalPC, saved]
  · rw [finalSP, sp]
  · intro i
    have nz : level ≠ 0 := by intro eq; apply nonzero; rw [eq]; rfl
    rw [Reference.recoverLeaf, if_neg nz]
    change final.getMem (KeygenSavePublic.wordAddress side i.val) =
      (Reference.compressLeaf hash level tree side (recoveredEndpoint hash level tree side message signature.values)).extractLsb' (64*i.val) 64
    exact output i
  · intro a hs outside
    rw [frame a outside, entryFrame a hs outside.1.2.2.2.2.1 outside.1.2.2.2.2.2]

theorem recover_leaf_call (hash : Hash) (s : MachineState) (level tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x1458) (sp : s.getReg .x2 = 0xfffff0)
    (data : LayerData s level tree base side message signature)
    (leaf : s.getMem 0x80428 = BitVec.ofNat 64 (Reference.sideNumber side))
    (small : level < 160) (aligned : base % 8 = 0) (bound : base+752 ≤ 0x80000) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 33795 ∧ cycles ≤ (if level = 0 then 116 else 34702) ∧ calls ≤ 323 ∧ blocks ≤ 334 ∧
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

theorem recover_tree_call (hash : Hash) (s : MachineState) (level tree base : Nat) (side : Bool)
    (message : Reference.Digest) (signature : Reference.LayerSignature)
    (pc : s.pc = 0x12f0) (sp : s.getReg .x2 = 0x1000000)
    (data : LayerData s level tree base side message signature)
    (small : level < 160) (aligned : base % 8 = 0) (bound : base+752 ≤ 0x80000) :
    ∃ final steps cycles calls blocks, Trace hash verify s steps cycles calls blocks final ∧
      steps ≤ 33908 ∧ cycles ≤ (if level = 0 then 236 else 34822) ∧ calls ≤ 324 ∧ blocks ≤ 335 ∧
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
      steps ≤ 34368 ∧ cycles ≤ (if level = 0 then 241 else 35282) ∧ calls ≤ 324 ∧ blocks ≤ 335 ∧
      final.pc = 0x11d4 ∧
      LoopData final level index (Reference.recoverLayer hash level index side current (wireLayer witness level)) witness ∧
      LowFrame s final := by
  obtain ⟨ready, preSteps, pre, preBound, rpc, rra, rsp, readyData, preFrame⟩ :=
    TightVerifying.prepare_tree s level index side current witness pc small data selector
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
      steps ≤ 34415 ∧ cycles ≤ (if level = 0 then 287 else 35329) ∧ calls ≤ 324 ∧ blocks ≤ 335 ∧
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
      steps ≤ 34415*count ∧ cycles ≤ 35329*count - (if level = 0 then 35042 else 0) ∧ calls ≤ 324*count ∧ blocks ≤ 335*count ∧
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
      steps ≤ 5506530 ∧ cycles ≤ 5617743 ∧ calls ≤ 51841 ∧ blocks ≤ 53602 ∧
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
  change cycles ≤ 5617598 at hcycles
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
    ∃ cycles calls blocks, cycles ≤ 5617758 ∧ calls ≤ 51841 ∧ blocks ≤ 53602 ∧
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

end SigGolfCandidate.Hypertree.ChecksumVerifying

namespace SigGolfCandidate.Hypertree.ChecksumCandidate
open SigGolf OracleComp KeygenOrganizer SignatureEncoding Candidate
set_option maxRecDepth 4096

theorem honest_exact (hash : Hash) (secretKey : SecretKey) (message : Message) :
    ∃ cycles calls blocks, cycles≤5617758 ∧ calls≤51841 ∧ blocks≤53602 ∧
      evalWithAnswerFn hash (submission.honest secretKey message)=
        ⟨true,fun phase => match phase with | .keygen => 761 | .sign => 121008 | .expand => 0 | .verify => blocks,cycles⟩ := by
  let pk := Reference.keygen hash secretKey
  let signature := (signCompact hash secretKey message).wire (signCompact_valid hash secretKey message)
  obtain ⟨signCycles,_,signRun⟩ := Signing.sign_run_refines hash secretKey KeygenFunctional.zeroCache message
  obtain ⟨cycles,calls,blocks,cycleBound,callBound,blockBound,verifyRun⟩ := ChecksumVerifying.run_refines hash pk message signature
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

theorem verificationBound : submission.VerificationBound 5617758 := by
  intro hash secretKey message
  dsimp only
  intro _
  obtain ⟨cycles,calls,blocks,cycleBound,_,_,run⟩ := honest_exact hash secretKey message
  rw [run]
  exact cycleBound

/-- Checksum-aware certificate for the original images, retaining the cheap bottom-layer bound. -/
theorem certificate : SigGolf.Certificate submission 5617758 :=
  ⟨admitted, Candidate.termination, Candidate.completeness, Candidate.compressionBounds,
    Candidate.security, verificationBound⟩

/-- info: 'SigGolfCandidate.Hypertree.ChecksumCandidate.certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms certificate

end SigGolfCandidate.Hypertree.ChecksumCandidate
