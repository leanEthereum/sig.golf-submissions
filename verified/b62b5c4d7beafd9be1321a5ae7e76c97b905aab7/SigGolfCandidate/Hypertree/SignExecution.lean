import SigGolfCandidate.Hypertree.SignExecutionSetup
import SigGolfCandidate.Hypertree.SignFinish

namespace SigGolfCandidate.Hypertree.Signing
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 Keygen Verifying
set_option maxRecDepth 4096

/-- Actual universal signer execution, with an exact compression count and reference output words.
Signing succeeds for every secret key, cache, and message. -/
theorem sign_execution (hash : Hash) (secretKey : SecretKey) (cache : Cache) (message : Message) :
    ∃ initial final instructions cycles,
      initialState submission .sign (secretKey,cache,message)=some initial ∧
      Executes hash sign initial instructions ⟨.success,final,cycles,117508,121008⟩ ∧
      instructions≤16066973 ∧ cycles≤16922843 ∧
      LayersStored final 0 (Reference.sign hash secretKey message).layers ∧
      (∀ i : Fin 4, final.getMem (wordAddress 0x20060 i.val)=
        (Reference.sign hash secretKey message).randomizer.extractLsb' (64*i.val) 64) := by
  obtain ⟨initial,ready,loaded,pre,readyPC,data,randomizer⟩ := loaded_loop_data hash secretKey cache message
  let index := Reference.indexOf hash message (Reference.randomizer hash secretKey message)
  have small : index.toNat<2^192 := by have := index.isLt; omega
  obtain ⟨done,n,c,body,nb,cb,donePC,_,stored,frame⟩ :=
    sign_layers hash secretKey 160 ready 0 index.toNat 0 (by decide) small (by simpa using readyPC) data
  obtain ⟨final,footer,footerFrame⟩ := sign_footer_executes hash done donePC
  have all := (pre.trans body).then_executes footer
  have execution : Executes hash sign initial (238+n+3) ⟨.success,final,268+c+3,117508,121008⟩ := by
    simpa only [Execution.charge,show loopCalls 160 0=117506 by rfl,show loopBlocks 160 0=121004 by rfl,
      Nat.reduceAdd,Nat.zero_add,Nat.add_zero,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using all
  refine ⟨initial,final,238+n+3,268+c+3,loaded,execution,by omega,by omega,?_,?_⟩
  · have transport : ∀ (level : Nat) (signatures : List Reference.LayerSignature),
        LayersStored done level signatures → LayersStored final level signatures := by
      intro level signatures
      induction signatures generalizing level with
      | nil => intro _; trivial
      | cons signature rest ih =>
        intro h
        refine ⟨?_,ih (level+1) h.2⟩
        have hstored := h.1
        unfold LayerStored at hstored ⊢
        split at hstored <;> rename_i zero
        · rw [if_pos zero]
          exact ⟨fun i => (footerFrame _).trans (hstored.1 i),fun i => (footerFrame _).trans (hstored.2 i)⟩
        · rw [if_neg zero]
          exact ⟨fun chain i => (footerFrame _).trans (hstored.1 chain i),fun i => (footerFrame _).trans (hstored.2 i)⟩
    exact transport 0 _ stored
  · intro i
    rw [footerFrame]
    rw [show wordAddress 0x20060 i.val=BitVec.ofNat 64 (0x20060+8*i.val) by rfl,
      frame _ (by have := i.isLt; omega) (by omega) (by have := i.isLt; change 0x20060+8*i.val<0x20080; omega)]
    exact randomizer i

/-- info: 'SigGolfCandidate.Hypertree.Signing.sign_execution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sign_execution
end SigGolfCandidate.Hypertree.Signing
