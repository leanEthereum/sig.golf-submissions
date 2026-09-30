import SigGolfCandidate.Verify.Exec

/-! # Fast instruction lookup in the verify image (chunks of 256 words) -/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

abbrev image : Image := Images.verifyImage

theorem image_eq : submission.image .verify = image := rfl

def vChunks : List (List (BitVec 32)) := [Images.verifyCode_0, Images.verifyCode_1, Images.verifyCode_2, Images.verifyCode_3, Images.verifyCode_4, Images.verifyCode_5, Images.verifyCode_6, Images.verifyCode_7, Images.verifyCode_8, Images.verifyCode_9, Images.verifyCode_10, Images.verifyCode_11, Images.verifyCode_12, Images.verifyCode_13, Images.verifyCode_14, Images.verifyCode_15, Images.verifyCode_16, Images.verifyCode_17, Images.verifyCode_18, Images.verifyCode_19, Images.verifyCode_20, Images.verifyCode_21, Images.verifyCode_22, Images.verifyCode_23, Images.verifyCode_24, Images.verifyCode_25, Images.verifyCode_26, Images.verifyCode_27, Images.verifyCode_28, Images.verifyCode_29, Images.verifyCode_30, Images.verifyCode_31, Images.verifyCode_32, Images.verifyCode_33, Images.verifyCode_34, Images.verifyCode_35, Images.verifyCode_36, Images.verifyCode_37, Images.verifyCode_38, Images.verifyCode_39, Images.verifyCode_40, Images.verifyCode_41, Images.verifyCode_42, Images.verifyCode_43, Images.verifyCode_44, Images.verifyCode_45, Images.verifyCode_46, Images.verifyCode_47, Images.verifyCode_48, Images.verifyCode_49, Images.verifyCode_50, Images.verifyCode_51, Images.verifyCode_52, Images.verifyCode_53, Images.verifyCode_54, Images.verifyCode_55, Images.verifyCode_56, Images.verifyCode_57, Images.verifyCode_58, Images.verifyCode_59, Images.verifyCode_60, Images.verifyCode_61, Images.verifyCode_62, Images.verifyCode_63, Images.verifyCode_64, Images.verifyCode_65, Images.verifyCode_66, Images.verifyCode_67, Images.verifyCode_68, Images.verifyCode_69, Images.verifyCode_70, Images.verifyCode_71, Images.verifyCode_72, Images.verifyCode_73, Images.verifyCode_74, Images.verifyCode_75, Images.verifyCode_76, Images.verifyCode_77, Images.verifyCode_78]

def vlook (n : Nat) : Option (BitVec 32) :=
  match vChunks[n / 256]? with
  | some c => c[n % 256]?
  | none => none

theorem lookup_chunks : ∀ (cs : List (List (BitVec 32))) (n : Nat) (w : BitVec 32),
    (cs.dropLast.all fun c => c.length == 256) = true →
    (match cs[n / 256]? with | some c => c[n % 256]? | none => none) = some w →
    cs.flatten[n]? = some w := by
  intro cs
  induction cs with
  | nil => intro n w _ h; simp at h
  | cons c cs ih =>
    intro n w hall h
    by_cases hn : n < 256
    · have h0 : n / 256 = 0 := Nat.div_eq_of_lt hn
      have h1 : n % 256 = n := Nat.mod_eq_of_lt hn
      rw [h0, h1] at h
      simp only [List.getElem?_cons_zero] at h
      simp only [List.flatten_cons]
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
      exact h
    · cases cs with
      | nil =>
        have : n / 256 ≠ 0 := by omega
        obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero this
        rw [hk] at h; simp at h
      | cons c' cs' =>
        have hlen : c.length = 256 := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == 256) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have hdiv : n / 256 = (n - 256) / 256 + 1 := by omega
        have hmod : n % 256 = (n - 256) % 256 := by omega
        rw [hdiv, hmod, List.getElem?_cons_succ] at h
        have := ih (n - 256) w hall' h
        simp only [List.flatten_cons]
        rw [List.getElem?_append_right (by omega), hlen]
        simpa using this

theorem vChunks_ok : (vChunks.dropLast.all fun c => c.length == 256) = true := by decide +kernel

set_option maxHeartbeats 4000000 in
theorem verifyCode_eq : Images.verifyCode = vChunks.flatten := by
  unfold Images.verifyCode vChunks
  simp only [ List.flatten_cons, List.flatten_nil, List.append_nil,
    List.append_assoc]

theorem vlook_ok : LookOK image vlook := by
  intro n w h
  show Images.verifyCode[n]? = some w
  rw [verifyCode_eq]
  exact lookup_chunks vChunks n w vChunks_ok h

end SigGolfCandidate.Verify
