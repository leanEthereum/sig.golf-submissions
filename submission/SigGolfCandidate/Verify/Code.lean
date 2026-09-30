import SigGolfCandidate.Verify.Exec

/-! # Fast instruction lookup in the verify image (chunks of 256 words) -/

namespace SigGolfCandidate.Verify
open SigGolf SigGolf.Riscv RiscvZkvm.Rv64 SigGolfCandidate.Rv

abbrev image : Image := Images.verifyImage

theorem image_eq : submission.image .verify = image := rfl

def vChunks : List (List (BitVec 32)) := [Images.verifyCode_0, Images.verifyCode_1, Images.verifyCode_2, Images.verifyCode_3, Images.verifyCode_4, Images.verifyCode_5, Images.verifyCode_6, Images.verifyCode_7, Images.verifyCode_8, Images.verifyCode_9, Images.verifyCode_10, Images.verifyCode_11, Images.verifyCode_12, Images.verifyCode_13, Images.verifyCode_14, Images.verifyCode_15, Images.verifyCode_16, Images.verifyCode_17, Images.verifyCode_18, Images.verifyCode_19, Images.verifyCode_20, Images.verifyCode_21, Images.verifyCode_22, Images.verifyCode_23, Images.verifyCode_24, Images.verifyCode_25, Images.verifyCode_26, Images.verifyCode_27, Images.verifyCode_28, Images.verifyCode_29, Images.verifyCode_30, Images.verifyCode_31, Images.verifyCode_32, Images.verifyCode_33, Images.verifyCode_34, Images.verifyCode_35, Images.verifyCode_36, Images.verifyCode_37, Images.verifyCode_38, Images.verifyCode_39, Images.verifyCode_40, Images.verifyCode_41, Images.verifyCode_42, Images.verifyCode_43, Images.verifyCode_44, Images.verifyCode_45, Images.verifyCode_46, Images.verifyCode_47, Images.verifyCode_48, Images.verifyCode_49, Images.verifyCode_50, Images.verifyCode_51, Images.verifyCode_52, Images.verifyCode_53, Images.verifyCode_54, Images.verifyCode_55, Images.verifyCode_56, Images.verifyCode_57, Images.verifyCode_58, Images.verifyCode_59, Images.verifyCode_60, Images.verifyCode_61, Images.verifyCode_62, Images.verifyCode_63, Images.verifyCode_64, Images.verifyCode_65, Images.verifyCode_66, Images.verifyCode_67, Images.verifyCode_68, Images.verifyCode_69, Images.verifyCode_70, Images.verifyCode_71, Images.verifyCode_72, Images.verifyCode_73, Images.verifyCode_74, Images.verifyCode_75, Images.verifyCode_76, Images.verifyCode_77, Images.verifyCode_78, Images.verifyCode_79, Images.verifyCode_80, Images.verifyCode_81, Images.verifyCode_82, Images.verifyCode_83, Images.verifyCode_84, Images.verifyCode_85, Images.verifyCode_86, Images.verifyCode_87, Images.verifyCode_88, Images.verifyCode_89, Images.verifyCode_90, Images.verifyCode_91, Images.verifyCode_92, Images.verifyCode_93, Images.verifyCode_94, Images.verifyCode_95, Images.verifyCode_96, Images.verifyCode_97, Images.verifyCode_98, Images.verifyCode_99, Images.verifyCode_100, Images.verifyCode_101, Images.verifyCode_102, Images.verifyCode_103, Images.verifyCode_104, Images.verifyCode_105, Images.verifyCode_106, Images.verifyCode_107, Images.verifyCode_108, Images.verifyCode_109, Images.verifyCode_110, Images.verifyCode_111, Images.verifyCode_112, Images.verifyCode_113, Images.verifyCode_114, Images.verifyCode_115, Images.verifyCode_116, Images.verifyCode_117, Images.verifyCode_118, Images.verifyCode_119, Images.verifyCode_120, Images.verifyCode_121, Images.verifyCode_122, Images.verifyCode_123, Images.verifyCode_124, Images.verifyCode_125, Images.verifyCode_126, Images.verifyCode_127, Images.verifyCode_128, Images.verifyCode_129, Images.verifyCode_130, Images.verifyCode_131, Images.verifyCode_132, Images.verifyCode_133, Images.verifyCode_134, Images.verifyCode_135, Images.verifyCode_136, Images.verifyCode_137, Images.verifyCode_138, Images.verifyCode_139, Images.verifyCode_140, Images.verifyCode_141, Images.verifyCode_142, Images.verifyCode_143, Images.verifyCode_144, Images.verifyCode_145, Images.verifyCode_146, Images.verifyCode_147, Images.verifyCode_148, Images.verifyCode_149, Images.verifyCode_150, Images.verifyCode_151, Images.verifyCode_152, Images.verifyCode_153, Images.verifyCode_154, Images.verifyCode_155, Images.verifyCode_156, Images.verifyCode_157, Images.verifyCode_158, Images.verifyCode_159, Images.verifyCode_160, Images.verifyCode_161, Images.verifyCode_162, Images.verifyCode_163, Images.verifyCode_164, Images.verifyCode_165, Images.verifyCode_166, Images.verifyCode_167, Images.verifyCode_168, Images.verifyCode_169, Images.verifyCode_170, Images.verifyCode_171, Images.verifyCode_172, Images.verifyCode_173, Images.verifyCode_174, Images.verifyCode_175, Images.verifyCode_176, Images.verifyCode_177, Images.verifyCode_178, Images.verifyCode_179, Images.verifyCode_180, Images.verifyCode_181, Images.verifyCode_182, Images.verifyCode_183, Images.verifyCode_184, Images.verifyCode_185, Images.verifyCode_186, Images.verifyCode_187, Images.verifyCode_188, Images.verifyCode_189, Images.verifyCode_190, Images.verifyCode_191, Images.verifyCode_192, Images.verifyCode_193, Images.verifyCode_194, Images.verifyCode_195, Images.verifyCode_196, Images.verifyCode_197, Images.verifyCode_198, Images.verifyCode_199, Images.verifyCode_200, Images.verifyCode_201, Images.verifyCode_202, Images.verifyCode_203, Images.verifyCode_204, Images.verifyCode_205, Images.verifyCode_206, Images.verifyCode_207, Images.verifyCode_208, Images.verifyCode_209, Images.verifyCode_210, Images.verifyCode_211, Images.verifyCode_212, Images.verifyCode_213, Images.verifyCode_214, Images.verifyCode_215, Images.verifyCode_216, Images.verifyCode_217, Images.verifyCode_218, Images.verifyCode_219, Images.verifyCode_220, Images.verifyCode_221, Images.verifyCode_222, Images.verifyCode_223, Images.verifyCode_224, Images.verifyCode_225, Images.verifyCode_226, Images.verifyCode_227, Images.verifyCode_228, Images.verifyCode_229, Images.verifyCode_230, Images.verifyCode_231, Images.verifyCode_232, Images.verifyCode_233, Images.verifyCode_234, Images.verifyCode_235, Images.verifyCode_236, Images.verifyCode_237, Images.verifyCode_238, Images.verifyCode_239, Images.verifyCode_240, Images.verifyCode_241, Images.verifyCode_242, Images.verifyCode_243, Images.verifyCode_244, Images.verifyCode_245, Images.verifyCode_246, Images.verifyCode_247, Images.verifyCode_248, Images.verifyCode_249, Images.verifyCode_250, Images.verifyCode_251, Images.verifyCode_252, Images.verifyCode_253, Images.verifyCode_254, Images.verifyCode_255, Images.verifyCode_256, Images.verifyCode_257, Images.verifyCode_258, Images.verifyCode_259, Images.verifyCode_260, Images.verifyCode_261, Images.verifyCode_262, Images.verifyCode_263, Images.verifyCode_264, Images.verifyCode_265, Images.verifyCode_266, Images.verifyCode_267, Images.verifyCode_268, Images.verifyCode_269, Images.verifyCode_270, Images.verifyCode_271, Images.verifyCode_272, Images.verifyCode_273, Images.verifyCode_274]

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

set_option maxRecDepth 100000 in
theorem vChunks_ok : (vChunks.dropLast.all fun c => c.length == 256) = true := by decide +kernel

theorem foldl_append_flatten : ∀ (l : List (List (BitVec 32))) (a : List (BitVec 32)),
    l.foldl (· ++ ·) a = a ++ l.flatten
  | [], a => by simp
  | c :: l, a => by simp [foldl_append_flatten l (a ++ c)]

set_option maxRecDepth 100000 in
theorem verifyCode_foldl : Images.verifyCode = vChunks.foldl (· ++ ·) [] := by
  delta Images.verifyCode vChunks
  rfl

theorem verifyCode_eq : Images.verifyCode = vChunks.flatten := by
  rw [verifyCode_foldl, foldl_append_flatten, List.nil_append]

theorem vlook_ok : LookOK image vlook := by
  intro n w h
  show Images.verifyCode[n]? = some w
  rw [verifyCode_eq]
  exact lookup_chunks vChunks n w vChunks_ok h

/-! ## Sequential code access (for runs over consecutive table entries) -/

/-- `verifyCode.drop i`, computed through the chunks. -/
def codeFrom (i : Nat) : List (BitVec 32) := ((vChunks.drop (i / 256)).flatten).drop (i % 256)

theorem drop_chunks : ∀ (cs : List (List (BitVec 32))) (k : Nat),
    (cs.dropLast.all fun c => c.length == 256) = true → k < cs.length →
    cs.flatten.drop (256 * k) = (cs.drop k).flatten := by
  intro cs
  induction cs with
  | nil => intro k _ hk; simp at hk
  | cons c cs ih =>
    intro k hall hk
    cases k with
    | zero => simp
    | succ k =>
      cases cs with
      | nil => simp at hk
      | cons c' cs' =>
        have hlen : c.length = 256 := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
          exact hall.1
        have hall' : ((c' :: cs').dropLast.all fun c => c.length == 256) = true := by
          simp only [List.dropLast_cons_cons, List.all_cons, Bool.and_eq_true] at hall
          exact hall.2
        have := ih k hall' (by simp at hk ⊢; omega)
        simp only [List.flatten_cons, List.drop_succ_cons] at this ⊢
        rw [show 256 * (k + 1) = c.length + 256 * k by rw [hlen]; ring, ← List.drop_drop,
          List.drop_left]
        exact this

set_option maxRecDepth 100000 in
theorem vChunks_length : vChunks.length = 275 := by decide +kernel

theorem codeFrom_eq (i : Nat) (hi : i / 256 < 275) : codeFrom i = Images.verifyCode.drop i := by
  unfold codeFrom
  rw [verifyCode_eq, ← drop_chunks vChunks (i / 256) vChunks_ok (by rw [vChunks_length]; exact hi),
    List.drop_drop]
  congr 1; omega

set_option maxRecDepth 100000 in
theorem vChunks_le : (vChunks.all fun c => decide (c.length ≤ 256)) = true := by decide +kernel

theorem flatten_len_le : ∀ (cs : List (List (BitVec 32))),
    (cs.all fun c => decide (c.length ≤ 256)) = true → cs.flatten.length ≤ 256 * cs.length
  | [], _ => by simp
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
    have := flatten_len_le cs h.2
    simp only [List.flatten_cons, List.length_append, List.length_cons]
    omega

theorem verifyCode_length : Images.verifyCode.length ≤ 256 * 275 := by
  rw [verifyCode_eq, ← vChunks_length]; exact flatten_len_le _ vChunks_le

end SigGolfCandidate.Verify
