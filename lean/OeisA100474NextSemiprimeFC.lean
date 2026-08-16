import FormalConjecturesForMathlib.NumberTheory.Semiprime
import FormalConjecturesUtil.Answer
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.NumberTheory.LucasPrimality
import Mathlib.Tactic
import OeisA100474KernelModular
import OeisA100474PrimeCertificate

/-!
# OEIS A100474: Lean proof of `next_semiprime`

This file mirrors the exact definitions in
`FormalConjectures/OEIS/100474.lean`.  It proves only the numerical
`next_semiprime` target; the separate prime-occurrence conjecture remains open.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474

def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    (Finset.Ico (triangular (n + 1) - 1) (triangular (n + 2) - 1)).prod
      (Nat.nth Nat.Prime) - a (n + 1)

namespace NextSemiprimeProof

open KernelModular

/- Sequential evaluation keeps every recurrence value reusable. -/
theorem a_0 : OeisA100474.a 0 = 0 := by rfl

theorem a_1 : OeisA100474.a 1 = 1 := by rfl

theorem a_2 : OeisA100474.a 2 = 5 := by
  change (Finset.Ico 0 2).prod (Nat.nth Nat.Prime) - OeisA100474.a 1 = 5
  rw [a_1]
  rw [Finset.prod_Ico_succ_top (by norm_num : 0 ≤ 1)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 0 ≤ 0)]
  norm_num

theorem a_3 : OeisA100474.a 3 = 380 := by
  change (Finset.Ico 2 5).prod (Nat.nth Nat.Prime) - OeisA100474.a 2 = 380
  rw [a_2]
  rw [Finset.prod_Ico_succ_top (by norm_num : 2 ≤ 4)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 2 ≤ 3)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 2 ≤ 2)]
  norm_num

theorem a_4 : OeisA100474.a 4 = 96197 := by
  change (Finset.Ico 5 9).prod (Nat.nth Nat.Prime) - OeisA100474.a 3 = 96197
  rw [a_3]
  rw [Finset.prod_Ico_succ_top (by norm_num : 5 ≤ 8)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 5 ≤ 7)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 5 ≤ 6)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 5 ≤ 5)]
  simp [PrimeCertificate.nth_5, PrimeCertificate.nth_6, PrimeCertificate.nth_7, PrimeCertificate.nth_8]

theorem a_5 : OeisA100474.a 5 = 58546472 := by
  change (Finset.Ico 9 14).prod (Nat.nth Nat.Prime) - OeisA100474.a 4 = 58546472
  rw [a_4]
  rw [Finset.prod_Ico_succ_top (by norm_num : 9 ≤ 13)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 9 ≤ 12)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 9 ≤ 11)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 9 ≤ 10)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 9 ≤ 9)]
  simp [PrimeCertificate.nth_9, PrimeCertificate.nth_10, PrimeCertificate.nth_11, PrimeCertificate.nth_12, PrimeCertificate.nth_13]

theorem a_6 : OeisA100474.a 6 = 42588477041 := by
  change (Finset.Ico 14 20).prod (Nat.nth Nat.Prime) - OeisA100474.a 5 = 42588477041
  rw [a_5]
  rw [Finset.prod_Ico_succ_top (by norm_num : 14 ≤ 19)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 14 ≤ 18)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 14 ≤ 17)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 14 ≤ 16)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 14 ≤ 15)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 14 ≤ 14)]
  simp [PrimeCertificate.nth_14, PrimeCertificate.nth_15, PrimeCertificate.nth_16, PrimeCertificate.nth_17, PrimeCertificate.nth_18, PrimeCertificate.nth_19]

theorem a_7 : OeisA100474.a 7 = 42945524659398 := by
  change (Finset.Ico 20 27).prod (Nat.nth Nat.Prime) - OeisA100474.a 6 = 42945524659398
  rw [a_6]
  rw [Finset.prod_Ico_succ_top (by norm_num : 20 ≤ 26)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 20 ≤ 25)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 20 ≤ 24)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 20 ≤ 23)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 20 ≤ 22)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 20 ≤ 21)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 20 ≤ 20)]
  simp [PrimeCertificate.nth_20, PrimeCertificate.nth_21, PrimeCertificate.nth_22, PrimeCertificate.nth_23, PrimeCertificate.nth_24, PrimeCertificate.nth_25, PrimeCertificate.nth_26]

theorem a_8 : OeisA100474.a 8 = 62170660055541623 := by
  change (Finset.Ico 27 35).prod (Nat.nth Nat.Prime) - OeisA100474.a 7 = 62170660055541623
  rw [a_7]
  rw [Finset.prod_Ico_succ_top (by norm_num : 27 ≤ 34)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 27 ≤ 33)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 27 ≤ 32)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 27 ≤ 31)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 27 ≤ 30)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 27 ≤ 29)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 27 ≤ 28)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 27 ≤ 27)]
  simp [PrimeCertificate.nth_27, PrimeCertificate.nth_28, PrimeCertificate.nth_29, PrimeCertificate.nth_30, PrimeCertificate.nth_31, PrimeCertificate.nth_32, PrimeCertificate.nth_33, PrimeCertificate.nth_34]

theorem a_9 : OeisA100474.a 9 = 133274332258941430724 := by
  change (Finset.Ico 35 44).prod (Nat.nth Nat.Prime) - OeisA100474.a 8 = 133274332258941430724
  rw [a_8]
  rw [Finset.prod_Ico_succ_top (by norm_num : 35 ≤ 43)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 35 ≤ 42)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 35 ≤ 41)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 35 ≤ 40)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 35 ≤ 39)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 35 ≤ 38)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 35 ≤ 37)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 35 ≤ 36)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 35 ≤ 35)]
  simp [PrimeCertificate.nth_35, PrimeCertificate.nth_36, PrimeCertificate.nth_37, PrimeCertificate.nth_38, PrimeCertificate.nth_39, PrimeCertificate.nth_40, PrimeCertificate.nth_41, PrimeCertificate.nth_42, PrimeCertificate.nth_43]

theorem a_10 : OeisA100474.a 10 = 322874181064180119947025 := by
  change (Finset.Ico 44 54).prod (Nat.nth Nat.Prime) - OeisA100474.a 9 = 322874181064180119947025
  rw [a_9]
  rw [Finset.prod_Ico_succ_top (by norm_num : 44 ≤ 53)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 44 ≤ 52)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 44 ≤ 51)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 44 ≤ 50)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 44 ≤ 49)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 44 ≤ 48)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 44 ≤ 47)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 44 ≤ 46)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 44 ≤ 45)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 44 ≤ 44)]
  simp [PrimeCertificate.nth_44, PrimeCertificate.nth_45, PrimeCertificate.nth_46, PrimeCertificate.nth_47, PrimeCertificate.nth_48, PrimeCertificate.nth_49, PrimeCertificate.nth_50, PrimeCertificate.nth_51, PrimeCertificate.nth_52, PrimeCertificate.nth_53]

theorem a_11 : OeisA100474.a 11 = 950049250593734799731643802 := by
  change (Finset.Ico 54 65).prod (Nat.nth Nat.Prime) - OeisA100474.a 10 = 950049250593734799731643802
  rw [a_10]
  rw [Finset.prod_Ico_succ_top (by norm_num : 54 ≤ 64)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 54 ≤ 63)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 54 ≤ 62)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 54 ≤ 61)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 54 ≤ 60)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 54 ≤ 59)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 54 ≤ 58)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 54 ≤ 57)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 54 ≤ 56)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 54 ≤ 55)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 54 ≤ 54)]
  simp [PrimeCertificate.nth_54, PrimeCertificate.nth_55, PrimeCertificate.nth_56, PrimeCertificate.nth_57, PrimeCertificate.nth_58, PrimeCertificate.nth_59, PrimeCertificate.nth_60, PrimeCertificate.nth_61, PrimeCertificate.nth_62, PrimeCertificate.nth_63, PrimeCertificate.nth_64]

theorem a_12 : OeisA100474.a 12 = 4193776877793643794299905615515 := by
  change (Finset.Ico 65 77).prod (Nat.nth Nat.Prime) - OeisA100474.a 11 = 4193776877793643794299905615515
  rw [a_11]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 76)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 75)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 74)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 73)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 72)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 71)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 70)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 69)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 68)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 67)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 66)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 65 ≤ 65)]
  simp [PrimeCertificate.nth_65, PrimeCertificate.nth_66, PrimeCertificate.nth_67, PrimeCertificate.nth_68, PrimeCertificate.nth_69, PrimeCertificate.nth_70, PrimeCertificate.nth_71, PrimeCertificate.nth_72, PrimeCertificate.nth_73, PrimeCertificate.nth_74, PrimeCertificate.nth_75, PrimeCertificate.nth_76]

theorem a_13 : OeisA100474.a 13 = 18252922295145311344311573454036768 := by
  change (Finset.Ico 77 90).prod (Nat.nth Nat.Prime) - OeisA100474.a 12 = 18252922295145311344311573454036768
  rw [a_12]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 89)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 88)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 87)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 86)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 85)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 84)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 83)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 82)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 81)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 80)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 79)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 78)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 77 ≤ 77)]
  simp [PrimeCertificate.nth_77, PrimeCertificate.nth_78, PrimeCertificate.nth_79, PrimeCertificate.nth_80, PrimeCertificate.nth_81, PrimeCertificate.nth_82, PrimeCertificate.nth_83, PrimeCertificate.nth_84, PrimeCertificate.nth_85, PrimeCertificate.nth_86, PrimeCertificate.nth_87, PrimeCertificate.nth_88, PrimeCertificate.nth_89]

theorem a_14 : OeisA100474.a 14 = 98303365890044935918733151055398911539 := by
  change (Finset.Ico 90 104).prod (Nat.nth Nat.Prime) - OeisA100474.a 13 = 98303365890044935918733151055398911539
  rw [a_13]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 103)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 102)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 101)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 100)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 99)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 98)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 97)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 96)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 95)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 94)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 93)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 92)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 91)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 90 ≤ 90)]
  simp [PrimeCertificate.nth_90, PrimeCertificate.nth_91, PrimeCertificate.nth_92, PrimeCertificate.nth_93, PrimeCertificate.nth_94, PrimeCertificate.nth_95, PrimeCertificate.nth_96, PrimeCertificate.nth_97, PrimeCertificate.nth_98, PrimeCertificate.nth_99, PrimeCertificate.nth_100, PrimeCertificate.nth_101, PrimeCertificate.nth_102, PrimeCertificate.nth_103]

theorem a_15 : OeisA100474.a 15 = 644585579089797905630274588927120249529678 := by
  change (Finset.Ico 104 119).prod (Nat.nth Nat.Prime) - OeisA100474.a 14 = 644585579089797905630274588927120249529678
  rw [a_14]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 118)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 117)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 116)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 115)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 114)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 113)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 112)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 111)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 110)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 109)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 108)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 107)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 106)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 105)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 104 ≤ 104)]
  simp [PrimeCertificate.nth_104, PrimeCertificate.nth_105, PrimeCertificate.nth_106, PrimeCertificate.nth_107, PrimeCertificate.nth_108, PrimeCertificate.nth_109, PrimeCertificate.nth_110, PrimeCertificate.nth_111, PrimeCertificate.nth_112, PrimeCertificate.nth_113, PrimeCertificate.nth_114, PrimeCertificate.nth_115, PrimeCertificate.nth_116, PrimeCertificate.nth_117, PrimeCertificate.nth_118]

theorem a_16 : OeisA100474.a 16 = 4236512963035908032147187661879545010869829675 := by
  change (Finset.Ico 119 135).prod (Nat.nth Nat.Prime) - OeisA100474.a 15 = 4236512963035908032147187661879545010869829675
  rw [a_15]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 134)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 133)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 132)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 131)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 130)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 129)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 128)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 127)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 126)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 125)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 124)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 123)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 122)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 121)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 120)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 119 ≤ 119)]
  simp [PrimeCertificate.nth_119, PrimeCertificate.nth_120, PrimeCertificate.nth_121, PrimeCertificate.nth_122, PrimeCertificate.nth_123, PrimeCertificate.nth_124, PrimeCertificate.nth_125, PrimeCertificate.nth_126, PrimeCertificate.nth_127, PrimeCertificate.nth_128, PrimeCertificate.nth_129, PrimeCertificate.nth_130, PrimeCertificate.nth_131, PrimeCertificate.nth_132, PrimeCertificate.nth_133, PrimeCertificate.nth_134]

theorem a_17 : OeisA100474.a 17 = 39804882898356761662830663307471022496463088245948 := by
  change (Finset.Ico 135 152).prod (Nat.nth Nat.Prime) - OeisA100474.a 16 = 39804882898356761662830663307471022496463088245948
  rw [a_16]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 151)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 150)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 149)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 148)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 147)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 146)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 145)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 144)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 143)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 142)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 141)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 140)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 139)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 138)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 137)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 136)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 135 ≤ 135)]
  simp [PrimeCertificate.nth_135, PrimeCertificate.nth_136, PrimeCertificate.nth_137, PrimeCertificate.nth_138, PrimeCertificate.nth_139, PrimeCertificate.nth_140, PrimeCertificate.nth_141, PrimeCertificate.nth_142, PrimeCertificate.nth_143, PrimeCertificate.nth_144, PrimeCertificate.nth_145, PrimeCertificate.nth_146, PrimeCertificate.nth_147, PrimeCertificate.nth_148, PrimeCertificate.nth_149, PrimeCertificate.nth_150, PrimeCertificate.nth_151]

theorem a_18 : OeisA100474.a 18 = 400344013203440370463080152761919471238633364904618169 := by
  change (Finset.Ico 152 170).prod (Nat.nth Nat.Prime) - OeisA100474.a 17 = 400344013203440370463080152761919471238633364904618169
  rw [a_17]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 169)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 168)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 167)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 166)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 165)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 164)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 163)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 162)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 161)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 160)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 159)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 158)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 157)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 156)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 155)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 154)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 153)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 152 ≤ 152)]
  simp [PrimeCertificate.nth_152, PrimeCertificate.nth_153, PrimeCertificate.nth_154, PrimeCertificate.nth_155, PrimeCertificate.nth_156, PrimeCertificate.nth_157, PrimeCertificate.nth_158, PrimeCertificate.nth_159, PrimeCertificate.nth_160, PrimeCertificate.nth_161, PrimeCertificate.nth_162, PrimeCertificate.nth_163, PrimeCertificate.nth_164, PrimeCertificate.nth_165, PrimeCertificate.nth_166, PrimeCertificate.nth_167, PrimeCertificate.nth_168, PrimeCertificate.nth_169]

theorem a_19 : OeisA100474.a 19 = 3769188924512487717336609048939926748508781652209964218710 := by
  change (Finset.Ico 170 189).prod (Nat.nth Nat.Prime) - OeisA100474.a 18 = 3769188924512487717336609048939926748508781652209964218710
  rw [a_18]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 188)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 187)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 186)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 185)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 184)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 183)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 182)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 181)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 180)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 179)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 178)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 177)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 176)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 175)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 174)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 173)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 172)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 171)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 170 ≤ 170)]
  simp [PrimeCertificate.nth_170, PrimeCertificate.nth_171, PrimeCertificate.nth_172, PrimeCertificate.nth_173, PrimeCertificate.nth_174, PrimeCertificate.nth_175, PrimeCertificate.nth_176, PrimeCertificate.nth_177, PrimeCertificate.nth_178, PrimeCertificate.nth_179, PrimeCertificate.nth_180, PrimeCertificate.nth_181, PrimeCertificate.nth_182, PrimeCertificate.nth_183, PrimeCertificate.nth_184, PrimeCertificate.nth_185, PrimeCertificate.nth_186, PrimeCertificate.nth_187, PrimeCertificate.nth_188]

theorem a_20 : OeisA100474.a 20 = 52093140684376347816086875820266389543747394482154080151117521 := by
  change (Finset.Ico 189 209).prod (Nat.nth Nat.Prime) - OeisA100474.a 19 = 52093140684376347816086875820266389543747394482154080151117521
  rw [a_19]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 208)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 207)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 206)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 205)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 204)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 203)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 202)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 201)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 200)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 199)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 198)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 197)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 196)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 195)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 194)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 193)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 192)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 191)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 190)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 189 ≤ 189)]
  simp [PrimeCertificate.nth_189, PrimeCertificate.nth_190, PrimeCertificate.nth_191, PrimeCertificate.nth_192, PrimeCertificate.nth_193, PrimeCertificate.nth_194, PrimeCertificate.nth_195, PrimeCertificate.nth_196, PrimeCertificate.nth_197, PrimeCertificate.nth_198, PrimeCertificate.nth_199, PrimeCertificate.nth_200, PrimeCertificate.nth_201, PrimeCertificate.nth_202, PrimeCertificate.nth_203, PrimeCertificate.nth_204, PrimeCertificate.nth_205, PrimeCertificate.nth_206, PrimeCertificate.nth_207, PrimeCertificate.nth_208]

theorem a_21 : OeisA100474.a 21 = 749334030989952441033301647611463590800205333061971743334460456440 := by
  change (Finset.Ico 209 230).prod (Nat.nth Nat.Prime) - OeisA100474.a 20 = 749334030989952441033301647611463590800205333061971743334460456440
  rw [a_20]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 229)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 228)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 227)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 226)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 225)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 224)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 223)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 222)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 221)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 220)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 219)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 218)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 217)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 216)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 215)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 214)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 213)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 212)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 211)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 210)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 209 ≤ 209)]
  simp [PrimeCertificate.nth_209, PrimeCertificate.nth_210, PrimeCertificate.nth_211, PrimeCertificate.nth_212, PrimeCertificate.nth_213, PrimeCertificate.nth_214, PrimeCertificate.nth_215, PrimeCertificate.nth_216, PrimeCertificate.nth_217, PrimeCertificate.nth_218, PrimeCertificate.nth_219, PrimeCertificate.nth_220, PrimeCertificate.nth_221, PrimeCertificate.nth_222, PrimeCertificate.nth_223, PrimeCertificate.nth_224, PrimeCertificate.nth_225, PrimeCertificate.nth_226, PrimeCertificate.nth_227, PrimeCertificate.nth_228, PrimeCertificate.nth_229]

theorem a_22 : OeisA100474.a 22 = 10885438985133796161203080773340101221981710352805352858124511315609381 := by
  change (Finset.Ico 230 252).prod (Nat.nth Nat.Prime) - OeisA100474.a 21 = 10885438985133796161203080773340101221981710352805352858124511315609381
  rw [a_21]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 251)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 250)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 249)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 248)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 247)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 246)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 245)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 244)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 243)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 242)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 241)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 240)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 239)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 238)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 237)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 236)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 235)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 234)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 233)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 232)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 231)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 230 ≤ 230)]
  simp [PrimeCertificate.nth_230, PrimeCertificate.nth_231, PrimeCertificate.nth_232, PrimeCertificate.nth_233, PrimeCertificate.nth_234, PrimeCertificate.nth_235, PrimeCertificate.nth_236, PrimeCertificate.nth_237, PrimeCertificate.nth_238, PrimeCertificate.nth_239, PrimeCertificate.nth_240, PrimeCertificate.nth_241, PrimeCertificate.nth_242, PrimeCertificate.nth_243, PrimeCertificate.nth_244, PrimeCertificate.nth_245, PrimeCertificate.nth_246, PrimeCertificate.nth_247, PrimeCertificate.nth_248, PrimeCertificate.nth_249, PrimeCertificate.nth_250, PrimeCertificate.nth_251]

theorem a_23 : OeisA100474.a 23 = 159667043218569634759169807042834548053731077980635799927462890153839588538 := by
  change (Finset.Ico 252 275).prod (Nat.nth Nat.Prime) - OeisA100474.a 22 = 159667043218569634759169807042834548053731077980635799927462890153839588538
  rw [a_22]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 274)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 273)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 272)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 271)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 270)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 269)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 268)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 267)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 266)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 265)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 264)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 263)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 262)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 261)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 260)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 259)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 258)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 257)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 256)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 255)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 254)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 253)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 252 ≤ 252)]
  simp [PrimeCertificate.nth_252, PrimeCertificate.nth_253, PrimeCertificate.nth_254, PrimeCertificate.nth_255, PrimeCertificate.nth_256, PrimeCertificate.nth_257, PrimeCertificate.nth_258, PrimeCertificate.nth_259, PrimeCertificate.nth_260, PrimeCertificate.nth_261, PrimeCertificate.nth_262, PrimeCertificate.nth_263, PrimeCertificate.nth_264, PrimeCertificate.nth_265, PrimeCertificate.nth_266, PrimeCertificate.nth_267, PrimeCertificate.nth_268, PrimeCertificate.nth_269, PrimeCertificate.nth_270, PrimeCertificate.nth_271, PrimeCertificate.nth_272, PrimeCertificate.nth_273, PrimeCertificate.nth_274]

theorem a_24 : OeisA100474.a 24 = 3573304817028179236086868100986262868704407337104265684114982210007761803540849 := by
  change (Finset.Ico 275 299).prod (Nat.nth Nat.Prime) - OeisA100474.a 23 = 3573304817028179236086868100986262868704407337104265684114982210007761803540849
  rw [a_23]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 298)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 297)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 296)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 295)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 294)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 293)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 292)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 291)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 290)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 289)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 288)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 287)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 286)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 285)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 284)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 283)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 282)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 281)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 280)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 279)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 278)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 277)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 276)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 275 ≤ 275)]
  simp [PrimeCertificate.nth_275, PrimeCertificate.nth_276, PrimeCertificate.nth_277, PrimeCertificate.nth_278, PrimeCertificate.nth_279, PrimeCertificate.nth_280, PrimeCertificate.nth_281, PrimeCertificate.nth_282, PrimeCertificate.nth_283, PrimeCertificate.nth_284, PrimeCertificate.nth_285, PrimeCertificate.nth_286, PrimeCertificate.nth_287, PrimeCertificate.nth_288, PrimeCertificate.nth_289, PrimeCertificate.nth_290, PrimeCertificate.nth_291, PrimeCertificate.nth_292, PrimeCertificate.nth_293, PrimeCertificate.nth_294, PrimeCertificate.nth_295, PrimeCertificate.nth_296, PrimeCertificate.nth_297, PrimeCertificate.nth_298]

theorem a_25 : OeisA100474.a 25 = 74284913499662726822649203369473644832776105355288983463979532101781189808925674838 := by
  change (Finset.Ico 299 324).prod (Nat.nth Nat.Prime) - OeisA100474.a 24 = 74284913499662726822649203369473644832776105355288983463979532101781189808925674838
  rw [a_24]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 323)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 322)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 321)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 320)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 319)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 318)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 317)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 316)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 315)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 314)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 313)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 312)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 311)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 310)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 309)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 308)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 307)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 306)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 305)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 304)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 303)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 302)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 301)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 300)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 299 ≤ 299)]
  simp [PrimeCertificate.nth_299, PrimeCertificate.nth_300, PrimeCertificate.nth_301, PrimeCertificate.nth_302, PrimeCertificate.nth_303, PrimeCertificate.nth_304, PrimeCertificate.nth_305, PrimeCertificate.nth_306, PrimeCertificate.nth_307, PrimeCertificate.nth_308, PrimeCertificate.nth_309, PrimeCertificate.nth_310, PrimeCertificate.nth_311, PrimeCertificate.nth_312, PrimeCertificate.nth_313, PrimeCertificate.nth_314, PrimeCertificate.nth_315, PrimeCertificate.nth_316, PrimeCertificate.nth_317, PrimeCertificate.nth_318, PrimeCertificate.nth_319, PrimeCertificate.nth_320, PrimeCertificate.nth_321, PrimeCertificate.nth_322, PrimeCertificate.nth_323]

theorem a_26 : OeisA100474.a 26 = 1744804175264642871201675233382910837418563395797083426750490217803815057167567230701971 := by
  change (Finset.Ico 324 350).prod (Nat.nth Nat.Prime) - OeisA100474.a 25 = 1744804175264642871201675233382910837418563395797083426750490217803815057167567230701971
  rw [a_25]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 349)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 348)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 347)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 346)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 345)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 344)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 343)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 342)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 341)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 340)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 339)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 338)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 337)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 336)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 335)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 334)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 333)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 332)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 331)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 330)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 329)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 328)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 327)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 326)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 325)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 324 ≤ 324)]
  simp [PrimeCertificate.nth_324, PrimeCertificate.nth_325, PrimeCertificate.nth_326, PrimeCertificate.nth_327, PrimeCertificate.nth_328, PrimeCertificate.nth_329, PrimeCertificate.nth_330, PrimeCertificate.nth_331, PrimeCertificate.nth_332, PrimeCertificate.nth_333, PrimeCertificate.nth_334, PrimeCertificate.nth_335, PrimeCertificate.nth_336, PrimeCertificate.nth_337, PrimeCertificate.nth_338, PrimeCertificate.nth_339, PrimeCertificate.nth_340, PrimeCertificate.nth_341, PrimeCertificate.nth_342, PrimeCertificate.nth_343, PrimeCertificate.nth_344, PrimeCertificate.nth_345, PrimeCertificate.nth_346, PrimeCertificate.nth_347, PrimeCertificate.nth_348, PrimeCertificate.nth_349]

theorem a_27 : OeisA100474.a 27 = 38374307958399202617281799135222577150966839675745096814372327368233117929913586806201239696 := by
  change (Finset.Ico 350 377).prod (Nat.nth Nat.Prime) - OeisA100474.a 26 = 38374307958399202617281799135222577150966839675745096814372327368233117929913586806201239696
  rw [a_26]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 376)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 375)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 374)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 373)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 372)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 371)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 370)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 369)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 368)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 367)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 366)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 365)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 364)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 363)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 362)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 361)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 360)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 359)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 358)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 357)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 356)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 355)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 354)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 353)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 352)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 351)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 350 ≤ 350)]
  simp [PrimeCertificate.nth_350, PrimeCertificate.nth_351, PrimeCertificate.nth_352, PrimeCertificate.nth_353, PrimeCertificate.nth_354, PrimeCertificate.nth_355, PrimeCertificate.nth_356, PrimeCertificate.nth_357, PrimeCertificate.nth_358, PrimeCertificate.nth_359, PrimeCertificate.nth_360, PrimeCertificate.nth_361, PrimeCertificate.nth_362, PrimeCertificate.nth_363, PrimeCertificate.nth_364, PrimeCertificate.nth_365, PrimeCertificate.nth_366, PrimeCertificate.nth_367, PrimeCertificate.nth_368, PrimeCertificate.nth_369, PrimeCertificate.nth_370, PrimeCertificate.nth_371, PrimeCertificate.nth_372, PrimeCertificate.nth_373, PrimeCertificate.nth_374, PrimeCertificate.nth_375, PrimeCertificate.nth_376]

theorem a_28 : OeisA100474.a 28 = 1099472140608503697222544856638520532011160464878071201467348103664411788083190854916541387698701 := by
  change (Finset.Ico 377 405).prod (Nat.nth Nat.Prime) - OeisA100474.a 27 = 1099472140608503697222544856638520532011160464878071201467348103664411788083190854916541387698701
  rw [a_27]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 404)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 403)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 402)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 401)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 400)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 399)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 398)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 397)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 396)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 395)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 394)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 393)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 392)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 391)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 390)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 389)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 388)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 387)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 386)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 385)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 384)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 383)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 382)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 381)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 380)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 379)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 378)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 377 ≤ 377)]
  simp [PrimeCertificate.nth_377, PrimeCertificate.nth_378, PrimeCertificate.nth_379, PrimeCertificate.nth_380, PrimeCertificate.nth_381, PrimeCertificate.nth_382, PrimeCertificate.nth_383, PrimeCertificate.nth_384, PrimeCertificate.nth_385, PrimeCertificate.nth_386, PrimeCertificate.nth_387, PrimeCertificate.nth_388, PrimeCertificate.nth_389, PrimeCertificate.nth_390, PrimeCertificate.nth_391, PrimeCertificate.nth_392, PrimeCertificate.nth_393, PrimeCertificate.nth_394, PrimeCertificate.nth_395, PrimeCertificate.nth_396, PrimeCertificate.nth_397, PrimeCertificate.nth_398, PrimeCertificate.nth_399, PrimeCertificate.nth_400, PrimeCertificate.nth_401, PrimeCertificate.nth_402, PrimeCertificate.nth_403, PrimeCertificate.nth_404]

theorem a_29 : OeisA100474.a 29 = 26495604807374915239194638389679834374398101831616785466226530891339437978361797774083416863607425112 := by
  change (Finset.Ico 405 434).prod (Nat.nth Nat.Prime) - OeisA100474.a 28 = 26495604807374915239194638389679834374398101831616785466226530891339437978361797774083416863607425112
  rw [a_28]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 433)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 432)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 431)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 430)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 429)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 428)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 427)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 426)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 425)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 424)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 423)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 422)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 421)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 420)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 419)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 418)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 417)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 416)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 415)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 414)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 413)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 412)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 411)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 410)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 409)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 408)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 407)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 406)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 405 ≤ 405)]
  simp [PrimeCertificate.nth_405, PrimeCertificate.nth_406, PrimeCertificate.nth_407, PrimeCertificate.nth_408, PrimeCertificate.nth_409, PrimeCertificate.nth_410, PrimeCertificate.nth_411, PrimeCertificate.nth_412, PrimeCertificate.nth_413, PrimeCertificate.nth_414, PrimeCertificate.nth_415, PrimeCertificate.nth_416, PrimeCertificate.nth_417, PrimeCertificate.nth_418, PrimeCertificate.nth_419, PrimeCertificate.nth_420, PrimeCertificate.nth_421, PrimeCertificate.nth_422, PrimeCertificate.nth_423, PrimeCertificate.nth_424, PrimeCertificate.nth_425, PrimeCertificate.nth_426, PrimeCertificate.nth_427, PrimeCertificate.nth_428, PrimeCertificate.nth_429, PrimeCertificate.nth_430, PrimeCertificate.nth_431, PrimeCertificate.nth_432, PrimeCertificate.nth_433]

theorem a_30 : OeisA100474.a 30 = 1039250469792233698103415884118132409812435350760635319998528923334451080746769649808071967101401202489071 := by
  change (Finset.Ico 434 464).prod (Nat.nth Nat.Prime) - OeisA100474.a 29 = 1039250469792233698103415884118132409812435350760635319998528923334451080746769649808071967101401202489071
  rw [a_29]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 463)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 462)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 461)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 460)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 459)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 458)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 457)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 456)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 455)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 454)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 453)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 452)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 451)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 450)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 449)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 448)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 447)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 446)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 445)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 444)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 443)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 442)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 441)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 440)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 439)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 438)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 437)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 436)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 435)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 434 ≤ 434)]
  simp [PrimeCertificate.nth_434, PrimeCertificate.nth_435, PrimeCertificate.nth_436, PrimeCertificate.nth_437, PrimeCertificate.nth_438, PrimeCertificate.nth_439, PrimeCertificate.nth_440, PrimeCertificate.nth_441, PrimeCertificate.nth_442, PrimeCertificate.nth_443, PrimeCertificate.nth_444, PrimeCertificate.nth_445, PrimeCertificate.nth_446, PrimeCertificate.nth_447, PrimeCertificate.nth_448, PrimeCertificate.nth_449, PrimeCertificate.nth_450, PrimeCertificate.nth_451, PrimeCertificate.nth_452, PrimeCertificate.nth_453, PrimeCertificate.nth_454, PrimeCertificate.nth_455, PrimeCertificate.nth_456, PrimeCertificate.nth_457, PrimeCertificate.nth_458, PrimeCertificate.nth_459, PrimeCertificate.nth_460, PrimeCertificate.nth_461, PrimeCertificate.nth_462, PrimeCertificate.nth_463]

theorem a_31 : OeisA100474.a 31 = 35618807662621303514903063362257172733135994657300288138037479150019850088429151461293005253493445382703670656 := by
  change (Finset.Ico 464 495).prod (Nat.nth Nat.Prime) - OeisA100474.a 30 = 35618807662621303514903063362257172733135994657300288138037479150019850088429151461293005253493445382703670656
  rw [a_30]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 494)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 493)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 492)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 491)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 490)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 489)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 488)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 487)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 486)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 485)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 484)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 483)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 482)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 481)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 480)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 479)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 478)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 477)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 476)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 475)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 474)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 473)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 472)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 471)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 470)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 469)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 468)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 467)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 466)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 465)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 464 ≤ 464)]
  simp [PrimeCertificate.nth_464, PrimeCertificate.nth_465, PrimeCertificate.nth_466, PrimeCertificate.nth_467, PrimeCertificate.nth_468, PrimeCertificate.nth_469, PrimeCertificate.nth_470, PrimeCertificate.nth_471, PrimeCertificate.nth_472, PrimeCertificate.nth_473, PrimeCertificate.nth_474, PrimeCertificate.nth_475, PrimeCertificate.nth_476, PrimeCertificate.nth_477, PrimeCertificate.nth_478, PrimeCertificate.nth_479, PrimeCertificate.nth_480, PrimeCertificate.nth_481, PrimeCertificate.nth_482, PrimeCertificate.nth_483, PrimeCertificate.nth_484, PrimeCertificate.nth_485, PrimeCertificate.nth_486, PrimeCertificate.nth_487, PrimeCertificate.nth_488, PrimeCertificate.nth_489, PrimeCertificate.nth_490, PrimeCertificate.nth_491, PrimeCertificate.nth_492, PrimeCertificate.nth_493, PrimeCertificate.nth_494]

theorem a_32 : OeisA100474.a 32 = 1082074482632576692801041371284576394193692019503799432959734270608270086249399901277101192408010446141114718254377 := by
  change (Finset.Ico 495 527).prod (Nat.nth Nat.Prime) - OeisA100474.a 31 = 1082074482632576692801041371284576394193692019503799432959734270608270086249399901277101192408010446141114718254377
  rw [a_31]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 526)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 525)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 524)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 523)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 522)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 521)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 520)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 519)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 518)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 517)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 516)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 515)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 514)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 513)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 512)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 511)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 510)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 509)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 508)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 507)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 506)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 505)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 504)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 503)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 502)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 501)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 500)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 499)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 498)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 497)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 496)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 495 ≤ 495)]
  simp [PrimeCertificate.nth_495, PrimeCertificate.nth_496, PrimeCertificate.nth_497, PrimeCertificate.nth_498, PrimeCertificate.nth_499, PrimeCertificate.nth_500, PrimeCertificate.nth_501, PrimeCertificate.nth_502, PrimeCertificate.nth_503, PrimeCertificate.nth_504, PrimeCertificate.nth_505, PrimeCertificate.nth_506, PrimeCertificate.nth_507, PrimeCertificate.nth_508, PrimeCertificate.nth_509, PrimeCertificate.nth_510, PrimeCertificate.nth_511, PrimeCertificate.nth_512, PrimeCertificate.nth_513, PrimeCertificate.nth_514, PrimeCertificate.nth_515, PrimeCertificate.nth_516, PrimeCertificate.nth_517, PrimeCertificate.nth_518, PrimeCertificate.nth_519, PrimeCertificate.nth_520, PrimeCertificate.nth_521, PrimeCertificate.nth_522, PrimeCertificate.nth_523, PrimeCertificate.nth_524, PrimeCertificate.nth_525, PrimeCertificate.nth_526]

theorem a_33 : OeisA100474.a 33 = 40723707588193082097886378622779217022064679393370194279714543532401335032135570137677250141534201081868180189228546560 := by
  change (Finset.Ico 527 560).prod (Nat.nth Nat.Prime) - OeisA100474.a 32 = 40723707588193082097886378622779217022064679393370194279714543532401335032135570137677250141534201081868180189228546560
  rw [a_32]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 559)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 558)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 557)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 556)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 555)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 554)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 553)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 552)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 551)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 550)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 549)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 548)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 547)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 546)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 545)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 544)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 543)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 542)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 541)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 540)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 539)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 538)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 537)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 536)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 535)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 534)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 533)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 532)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 531)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 530)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 529)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 528)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 527 ≤ 527)]
  simp [PrimeCertificate.nth_527, PrimeCertificate.nth_528, PrimeCertificate.nth_529, PrimeCertificate.nth_530, PrimeCertificate.nth_531, PrimeCertificate.nth_532, PrimeCertificate.nth_533, PrimeCertificate.nth_534, PrimeCertificate.nth_535, PrimeCertificate.nth_536, PrimeCertificate.nth_537, PrimeCertificate.nth_538, PrimeCertificate.nth_539, PrimeCertificate.nth_540, PrimeCertificate.nth_541, PrimeCertificate.nth_542, PrimeCertificate.nth_543, PrimeCertificate.nth_544, PrimeCertificate.nth_545, PrimeCertificate.nth_546, PrimeCertificate.nth_547, PrimeCertificate.nth_548, PrimeCertificate.nth_549, PrimeCertificate.nth_550, PrimeCertificate.nth_551, PrimeCertificate.nth_552, PrimeCertificate.nth_553, PrimeCertificate.nth_554, PrimeCertificate.nth_555, PrimeCertificate.nth_556, PrimeCertificate.nth_557, PrimeCertificate.nth_558, PrimeCertificate.nth_559]

theorem a_34 : OeisA100474.a 34 = 1635175563153819628227752166686719441868871909970284368365983989650013921335399301408971667333268887790905013036049331507297 := by
  change (Finset.Ico 560 594).prod (Nat.nth Nat.Prime) - OeisA100474.a 33 = 1635175563153819628227752166686719441868871909970284368365983989650013921335399301408971667333268887790905013036049331507297
  rw [a_33]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 593)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 592)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 591)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 590)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 589)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 588)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 587)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 586)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 585)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 584)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 583)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 582)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 581)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 580)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 579)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 578)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 577)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 576)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 575)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 574)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 573)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 572)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 571)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 570)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 569)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 568)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 567)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 566)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 565)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 564)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 563)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 562)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 561)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 560 ≤ 560)]
  simp [PrimeCertificate.nth_560, PrimeCertificate.nth_561, PrimeCertificate.nth_562, PrimeCertificate.nth_563, PrimeCertificate.nth_564, PrimeCertificate.nth_565, PrimeCertificate.nth_566, PrimeCertificate.nth_567, PrimeCertificate.nth_568, PrimeCertificate.nth_569, PrimeCertificate.nth_570, PrimeCertificate.nth_571, PrimeCertificate.nth_572, PrimeCertificate.nth_573, PrimeCertificate.nth_574, PrimeCertificate.nth_575, PrimeCertificate.nth_576, PrimeCertificate.nth_577, PrimeCertificate.nth_578, PrimeCertificate.nth_579, PrimeCertificate.nth_580, PrimeCertificate.nth_581, PrimeCertificate.nth_582, PrimeCertificate.nth_583, PrimeCertificate.nth_584, PrimeCertificate.nth_585, PrimeCertificate.nth_586, PrimeCertificate.nth_587, PrimeCertificate.nth_588, PrimeCertificate.nth_589, PrimeCertificate.nth_590, PrimeCertificate.nth_591, PrimeCertificate.nth_592, PrimeCertificate.nth_593]

theorem a_35 : OeisA100474.a 35 = 78500839301193328816989423551091310320915084258144608975951089524649670606948737065100260183180017202710377177610716399118211540 := by
  change (Finset.Ico 594 629).prod (Nat.nth Nat.Prime) - OeisA100474.a 34 = 78500839301193328816989423551091310320915084258144608975951089524649670606948737065100260183180017202710377177610716399118211540
  rw [a_34]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 628)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 627)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 626)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 625)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 624)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 623)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 622)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 621)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 620)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 619)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 618)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 617)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 616)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 615)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 614)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 613)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 612)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 611)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 610)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 609)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 608)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 607)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 606)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 605)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 604)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 603)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 602)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 601)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 600)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 599)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 598)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 597)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 596)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 595)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 594 ≤ 594)]
  simp [PrimeCertificate.nth_594, PrimeCertificate.nth_595, PrimeCertificate.nth_596, PrimeCertificate.nth_597, PrimeCertificate.nth_598, PrimeCertificate.nth_599, PrimeCertificate.nth_600, PrimeCertificate.nth_601, PrimeCertificate.nth_602, PrimeCertificate.nth_603, PrimeCertificate.nth_604, PrimeCertificate.nth_605, PrimeCertificate.nth_606, PrimeCertificate.nth_607, PrimeCertificate.nth_608, PrimeCertificate.nth_609, PrimeCertificate.nth_610, PrimeCertificate.nth_611, PrimeCertificate.nth_612, PrimeCertificate.nth_613, PrimeCertificate.nth_614, PrimeCertificate.nth_615, PrimeCertificate.nth_616, PrimeCertificate.nth_617, PrimeCertificate.nth_618, PrimeCertificate.nth_619, PrimeCertificate.nth_620, PrimeCertificate.nth_621, PrimeCertificate.nth_622, PrimeCertificate.nth_623, PrimeCertificate.nth_624, PrimeCertificate.nth_625, PrimeCertificate.nth_626, PrimeCertificate.nth_627, PrimeCertificate.nth_628]

theorem a_36 : OeisA100474.a 36 = 3852669607062814427999374038085094563026983841699038416757537720951140990693348082633155462564082456461927363575765861495986901576629 := by
  change (Finset.Ico 629 665).prod (Nat.nth Nat.Prime) - OeisA100474.a 35 = 3852669607062814427999374038085094563026983841699038416757537720951140990693348082633155462564082456461927363575765861495986901576629
  rw [a_35]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 664)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 663)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 662)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 661)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 660)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 659)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 658)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 657)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 656)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 655)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 654)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 653)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 652)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 651)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 650)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 649)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 648)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 647)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 646)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 645)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 644)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 643)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 642)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 641)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 640)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 639)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 638)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 637)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 636)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 635)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 634)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 633)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 632)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 631)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 630)]
  rw [Finset.prod_Ico_succ_top (by norm_num : 629 ≤ 629)]
  simp [PrimeCertificate.nth_629, PrimeCertificate.nth_630, PrimeCertificate.nth_631, PrimeCertificate.nth_632, PrimeCertificate.nth_633, PrimeCertificate.nth_634, PrimeCertificate.nth_635, PrimeCertificate.nth_636, PrimeCertificate.nth_637, PrimeCertificate.nth_638, PrimeCertificate.nth_639, PrimeCertificate.nth_640, PrimeCertificate.nth_641, PrimeCertificate.nth_642, PrimeCertificate.nth_643, PrimeCertificate.nth_644, PrimeCertificate.nth_645, PrimeCertificate.nth_646, PrimeCertificate.nth_647, PrimeCertificate.nth_648, PrimeCertificate.nth_649, PrimeCertificate.nth_650, PrimeCertificate.nth_651, PrimeCertificate.nth_652, PrimeCertificate.nth_653, PrimeCertificate.nth_654, PrimeCertificate.nth_655, PrimeCertificate.nth_656, PrimeCertificate.nth_657, PrimeCertificate.nth_658, PrimeCertificate.nth_659, PrimeCertificate.nth_660, PrimeCertificate.nth_661, PrimeCertificate.nth_662, PrimeCertificate.nth_663, PrimeCertificate.nth_664]

theorem prime_of_lucas_certificate
    (p a : ℕ) (factors : List ℕ)
    (hp : 1 < p)
    (hprod : factors.prod = p - 1)
    (hprime : ∀ q ∈ factors, q.Prime)
    (hcheck : (a : ZMod p) ^ (p - 1) = 1 ∧
      factors.Forall (fun q => (a : ZMod p) ^ ((p - 1) / q) ≠ 1)) :
    p.Prime := by
  apply lucas_primality p (a : ZMod p) hcheck.1
  intro q hq hqdiv
  have hmem : q ∈ (p - 1).primeFactorsList :=
    (Nat.mem_primeFactorsList_iff_dvd (by omega) hq).2 hqdiv
  have hperm : factors.Perm (p - 1).primeFactorsList :=
    Nat.primeFactorsList_unique hprod hprime
  exact (List.forall_iff_forall_mem.mp hcheck.2) q (hperm.mem_iff.mpr hmem)

theorem lucas_73098925036309721 :
    (73098925036309721 : ℕ).Prime := by
  apply prime_of_lucas_certificate 73098925036309721 3
    [2, 2, 2, 5, 3433, 4373, 10513, 11579]
  · norm_num
  · norm_num
  · norm_num
  · exact lucas_hcheck_0

theorem lucas_584791400290477769 :
    (584791400290477769 : ℕ).Prime := by
  apply prime_of_lucas_certificate 584791400290477769 3
    [2, 2, 2, 73098925036309721]
  · norm_num
  · norm_num
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp]
    refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    intro q hq
    subst q
    exact lucas_73098925036309721
  · exact lucas_hcheck_1

theorem lucas_1190470901 : (1190470901 : ℕ).Prime := by
  apply prime_of_lucas_certificate 1190470901 2
    [2, 2, 5, 5, 17, 700277]
  · norm_num
  · norm_num
  · norm_num
  · exact lucas_hcheck_2

theorem lucas_23879310566597711 : (23879310566597711 : ℕ).Prime := by
  apply prime_of_lucas_certificate 23879310566597711 17
    [2, 5, 7, 286553, 1190470901]
  · norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl | rfl | rfl)
    all_goals first | exact lucas_1190470901 | norm_num
  · exact lucas_hcheck_3

theorem lucas_907413801530713019 : (907413801530713019 : ℕ).Prime := by
  apply prime_of_lucas_certificate 907413801530713019 2
    [2, 19, 23879310566597711]
  · norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl)
    all_goals first | exact lucas_23879310566597711 | norm_num
  · exact lucas_hcheck_4

theorem lucas_8221702988651068092612692539039 :
    (8221702988651068092612692539039 : ℕ).Prime := by
  apply prime_of_lucas_certificate 8221702988651068092612692539039 3
    [2, 3, 7, 7, 139493, 220931, 907413801530713019]
  · norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | exact lucas_907413801530713019 | norm_num
  · exact lucas_hcheck_5

theorem lucas_597359177 : (597359177 : ℕ).Prime := by
  apply prime_of_lucas_certificate 597359177 5
    [2, 2, 2, 41, 653, 2789]
  · norm_num
  · norm_num
  · norm_num
  · exact lucas_hcheck_6

theorem lucas_8352730279367 : (8352730279367 : ℕ).Prime := by
  apply prime_of_lucas_certificate 8352730279367 5
    [2, 11, 60961, 6228073]
  · norm_num
  · norm_num
  · norm_num
  · exact lucas_hcheck_7

theorem lucas_1430667954174411546959 :
    (1430667954174411546959 : ℕ).Prime := by
  apply prime_of_lucas_certificate 1430667954174411546959 7
    [2, 7, 13, 887, 1061, 8352730279367]
  · norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first | exact lucas_8352730279367 | norm_num
  · exact lucas_hcheck_8

theorem lucas_461667964804357559734387547 :
    (461667964804357559734387547 : ℕ).Prime := by
  apply prime_of_lucas_certificate 461667964804357559734387547 2
    [2, 17, 9491, 1430667954174411546959]
  · norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl | rfl)
    all_goals first | exact lucas_1430667954174411546959 | norm_num
  · exact lucas_hcheck_9

theorem lucas_227868403652723591 : (227868403652723591 : ℕ).Prime := by
  apply prime_of_lucas_certificate 227868403652723591 7
    [2, 5, 31, 43, 43, 59, 131, 4651, 11059]
  · norm_num
  · norm_num
  · norm_num
  · exact lucas_hcheck_10

theorem lucas_186983349423540748034761849124579521373412534080233 :
    (186983349423540748034761849124579521373412534080233 : ℕ).Prime := by
  apply prime_of_lucas_certificate
    186983349423540748034761849124579521373412534080233 5
    [2, 2, 2, 3, 31, 2389, 227868403652723591, 461667964804357559734387547]
  · norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first
      | exact lucas_227868403652723591
      | exact lucas_461667964804357559734387547
      | norm_num
  · exact lucas_hcheck_11

theorem lucas_103172769879062304819188940336438602413290547478314441733587841 :
    (103172769879062304819188940336438602413290547478314441733587841 : ℕ).Prime := by
  apply prime_of_lucas_certificate
    103172769879062304819188940336438602413290547478314441733587841 3
    [2, 2, 2, 2, 2, 2, 2, 5, 7, 97, 1269733,
      186983349423540748034761849124579521373412534080233]
  · norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first
      | exact lucas_186983349423540748034761849124579521373412534080233
      | norm_num
  · exact lucas_hcheck_12

theorem lucas_6910083712423065615559090169408100783675718253484998976398609599303612568353159 :
    (6910083712423065615559090169408100783675718253484998976398609599303612568353159 : ℕ).Prime := by
  apply prime_of_lucas_certificate
    6910083712423065615559090169408100783675718253484998976398609599303612568353159 3
    [2, 3, 3, 23, 270821, 597359177,
      103172769879062304819188940336438602413290547478314441733587841]
  · norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first
      | exact lucas_597359177
      | exact lucas_103172769879062304819188940336438602413290547478314441733587841
      | norm_num
  · exact lucas_hcheck_13

theorem lucas_largePrimeFactor :
    (15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 : ℕ).Prime := by
  apply prime_of_lucas_certificate
    15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 3
    [2, 3, 7, 11, 584791400290477769, 8221702988651068092612692539039,
      6910083712423065615559090169408100783675718253484998976398609599303612568353159]
  · norm_num
  · norm_num
  · intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals first
      | exact lucas_584791400290477769
      | exact lucas_8221702988651068092612692539039
      | exact lucas_6910083712423065615559090169408100783675718253484998976398609599303612568353159
      | norm_num
  · exact lucas_hcheck_14

theorem largePrimeFactor_prime :
    (15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 : ℕ).Prime :=
  lucas_largePrimeFactor

theorem semiprime_251_mul_prime {p : ℕ} (hp : p.Prime) :
    (251 * p).IsSemiprime := by
  unfold Nat.IsSemiprime
  constructor
  · have hp1 := hp.one_lt
    omega
  · have h251 : (251 : ℕ).Prime := by norm_num
    have hperm := Nat.perm_primeFactorsList_mul
      (by norm_num : (251 : ℕ) ≠ 0) hp.ne_zero
    calc
      (251 * p).primeFactorsList.length =
          ((251 : ℕ).primeFactorsList ++ p.primeFactorsList).length := hperm.length_eq
      _ = 2 := by
        rw [Nat.primeFactorsList_prime h251, Nat.primeFactorsList_prime hp]
        rfl

theorem a_36_semiprime : (OeisA100474.a 36).IsSemiprime := by
  rw [a_36]
  rw [show (3852669607062814427999374038085094563026983841699038416757537720951140990693348082633155462564082456461927363575765861495986901576629 : ℕ) = 251 * 15349281303039101306770414494362926545924238413143579349631624386259525859336048137980699054040169149250706627791895862533812356879 by norm_num]
  exact semiprime_251_mul_prime largePrimeFactor_prime

theorem not_semiprime_of_eq_mul_three
    {n x y z : ℕ} (hn : n = x * y * z)
    (hx : 1 < x) (hy : 1 < y) (hz : 1 < z) :
    ¬n.IsSemiprime := by
  intro hsemi
  have hxlen : 0 < x.primeFactorsList.length :=
    List.length_pos_iff.mpr ((Nat.primeFactorsList_ne_nil x).2 hx)
  have hylen : 0 < y.primeFactorsList.length :=
    List.length_pos_iff.mpr ((Nat.primeFactorsList_ne_nil y).2 hy)
  have hzlen : 0 < z.primeFactorsList.length :=
    List.length_pos_iff.mpr ((Nat.primeFactorsList_ne_nil z).2 hz)
  have hxy := Nat.perm_primeFactorsList_mul (by omega : x ≠ 0) (by omega : y ≠ 0)
  have hxyz := Nat.perm_primeFactorsList_mul
    (by positivity : x * y ≠ 0) (by omega : z ≠ 0)
  have hlenxy := hxy.length_eq
  have hlenxyz := hxyz.length_eq
  rw [hn] at hsemi
  unfold Nat.IsSemiprime at hsemi
  simp only [List.length_append] at hlenxy hlenxyz
  omega

theorem a_12_not_semiprime : ¬(OeisA100474.a 12).IsSemiprime := by
  rw [a_12]
  apply not_semiprime_of_eq_mul_three (x := 3) (y := 5) (z := 279585125186242919619993707701)
  all_goals norm_num

theorem a_13_not_semiprime : ¬(OeisA100474.a 13).IsSemiprime := by
  rw [a_13]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 2) (z := 4563230573786327836077893363509192)
  all_goals norm_num

theorem a_14_not_semiprime : ¬(OeisA100474.a 14).IsSemiprime := by
  rw [a_14]
  apply not_semiprime_of_eq_mul_three (x := 73) (y := 109) (z := 12354325234390465743211405184793127)
  all_goals norm_num

theorem a_15_not_semiprime : ¬(OeisA100474.a 15).IsSemiprime := by
  rw [a_15]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 79) (z := 4079655563859480415381484740045064870441)
  all_goals norm_num

theorem a_16_not_semiprime : ¬(OeisA100474.a 16).IsSemiprime := by
  rw [a_16]
  apply not_semiprime_of_eq_mul_three (x := 5) (y := 5) (z := 169460518521436321285887506475181800434793187)
  all_goals norm_num

theorem a_17_not_semiprime : ¬(OeisA100474.a 17).IsSemiprime := by
  rw [a_17]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 2) (z := 9951220724589190415707665826867755624115772061487)
  all_goals norm_num

theorem a_18_not_semiprime : ¬(OeisA100474.a 18).IsSemiprime := by
  rw [a_18]
  apply not_semiprime_of_eq_mul_three (x := 3) (y := 3) (z := 44482668133715596718120016973546607915403707211624241)
  all_goals norm_num

theorem a_19_not_semiprime : ¬(OeisA100474.a 19).IsSemiprime := by
  rw [a_19]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 5) (z := 376918892451248771733660904893992674850878165220996421871)
  all_goals norm_num

theorem a_20_not_semiprime : ¬(OeisA100474.a 20).IsSemiprime := by
  rw [a_20]
  apply not_semiprime_of_eq_mul_three (x := 3) (y := 556051102090019213) (z := 31228029515377755031432132115654277374826439)
  all_goals norm_num

theorem a_21_not_semiprime : ¬(OeisA100474.a 21).IsSemiprime := by
  rw [a_21]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 2) (z := 187333507747488110258325411902865897700051333265492935833615114110)
  all_goals norm_num

theorem a_22_not_semiprime : ¬(OeisA100474.a 22).IsSemiprime := by
  rw [a_22]
  apply not_semiprime_of_eq_mul_three (x := 3) (y := 3) (z := 1209493220570421795689231197037789024664634483645039206458279035067709)
  all_goals norm_num

theorem a_23_not_semiprime : ¬(OeisA100474.a 23).IsSemiprime := by
  rw [a_23]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 17) (z := 4696089506428518669387347265965722001580325822959876468454790886877634957)
  all_goals norm_num

theorem a_24_not_semiprime : ¬(OeisA100474.a 24).IsSemiprime := by
  rw [a_24]
  apply not_semiprime_of_eq_mul_three (x := 276557) (y := 721014487) (z := 17920140834594745851519735812904805640512596477756570571934333011)
  all_goals norm_num

theorem a_25_not_semiprime : ¬(OeisA100474.a 25).IsSemiprime := by
  rw [a_25]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 29) (z := 1280774370683840117631882816715062841944415609573947990758267794858296376015959911)
  all_goals norm_num

theorem a_26_not_semiprime : ¬(OeisA100474.a 26).IsSemiprime := by
  rw [a_26]
  apply not_semiprime_of_eq_mul_three (x := 3) (y := 11) (z := 52872853795898268824293188890391237497532224115063134143954249024358032035380825172787)
  all_goals norm_num

theorem a_27_not_semiprime : ¬(OeisA100474.a 27).IsSemiprime := by
  rw [a_27]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 2) (z := 9593576989599800654320449783805644287741709918936274203593081842058279482478396701550309924)
  all_goals norm_num

theorem a_28_not_semiprime : ¬(OeisA100474.a 28).IsSemiprime := by
  rw [a_28]
  apply not_semiprime_of_eq_mul_three (x := 553139) (y := 306063620836037) (z := 6494388086485189230961422292297098004638490889853702235387326675856960153907)
  all_goals norm_num

theorem a_29_not_semiprime : ¬(OeisA100474.a 29).IsSemiprime := by
  rw [a_29]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 2) (z := 6623901201843728809798659597419958593599525457904196366556632722834859494590449443520854215901856278)
  all_goals norm_num

theorem a_30_not_semiprime : ¬(OeisA100474.a 30).IsSemiprime := by
  rw [a_30]
  apply not_semiprime_of_eq_mul_three (x := 11) (y := 17) (z := 5557489143273976995205432535391082405414092784816231657746143975050540538752778875978994476478081296733)
  all_goals norm_num

theorem a_31_not_semiprime : ¬(OeisA100474.a 31).IsSemiprime := by
  rw [a_31]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 2) (z := 8904701915655325878725765840564293183283998664325072034509369787504962522107287865323251313373361345675917664)
  all_goals norm_num

theorem a_32_not_semiprime : ¬(OeisA100474.a 32).IsSemiprime := by
  rw [a_32]
  apply not_semiprime_of_eq_mul_three (x := 29) (y := 146837) (z := 254111110920454534690716487948183781122932235557419506208205596637009906656853588597326003384003431940863049)
  all_goals norm_num

theorem a_33_not_semiprime : ¬(OeisA100474.a 33).IsSemiprime := by
  rw [a_33]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 2) (z := 10180926897048270524471594655694804255516169848342548569928635883100333758033892534419312535383550270467045047307136640)
  all_goals norm_num

theorem a_34_not_semiprime : ¬(OeisA100474.a 34).IsSemiprime := by
  rw [a_34]
  apply not_semiprime_of_eq_mul_three (x := 11) (y := 17) (z := 8744254348416147744533434046453045143683807005188686461850181762834299044574327815021238862744753410646550871850531184531)
  all_goals norm_num

theorem a_35_not_semiprime : ¬(OeisA100474.a 35).IsSemiprime := by
  rw [a_35]
  apply not_semiprime_of_eq_mul_three (x := 2) (y := 2) (z := 19625209825298332204247355887772827580228771064536152243987772381162417651737184266275065045795004300677594294402679099779552885)
  all_goals norm_num

theorem no_semiprime_before_36 :
    ∀ n : ℕ, 11 < n → n < 36 → ¬(OeisA100474.a n).IsSemiprime := by
  intro n hn_lower hn_upper
  interval_cases n
  case «12» => exact a_12_not_semiprime
  case «13» => exact a_13_not_semiprime
  case «14» => exact a_14_not_semiprime
  case «15» => exact a_15_not_semiprime
  case «16» => exact a_16_not_semiprime
  case «17» => exact a_17_not_semiprime
  case «18» => exact a_18_not_semiprime
  case «19» => exact a_19_not_semiprime
  case «20» => exact a_20_not_semiprime
  case «21» => exact a_21_not_semiprime
  case «22» => exact a_22_not_semiprime
  case «23» => exact a_23_not_semiprime
  case «24» => exact a_24_not_semiprime
  case «25» => exact a_25_not_semiprime
  case «26» => exact a_26_not_semiprime
  case «27» => exact a_27_not_semiprime
  case «28» => exact a_28_not_semiprime
  case «29» => exact a_29_not_semiprime
  case «30» => exact a_30_not_semiprime
  case «31» => exact a_31_not_semiprime
  case «32» => exact a_32_not_semiprime
  case «33» => exact a_33_not_semiprime
  case «34» => exact a_34_not_semiprime
  case «35» => exact a_35_not_semiprime

theorem least_semiprime_index :
    sInf {n : ℕ | 11 < n ∧ (OeisA100474.a n).IsSemiprime} = 36 := by
  apply IsLeast.csInf_eq
  constructor
  · exact ⟨by norm_num, a_36_semiprime⟩
  · intro n hn
    by_contra hnot
    have hnlt : n < 36 := by omega
    exact no_semiprime_before_36 n hn.1 hnlt hn.2

end NextSemiprimeProof

open NextSemiprimeProof

theorem next_semiprime :
    answer(3852669607062814427999374038085094563026983841699038416757537720951140990693348082633155462564082456461927363575765861495986901576629) =
      a (sInf {n : ℕ | 11 < n ∧ (a n).IsSemiprime}) := by
  rw [least_semiprime_index, a_36]

#print axioms OeisA100474.next_semiprime

end OeisA100474
