import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Tactic

/-! Kernel prime/count certificate, chunk 00 (0–24). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem count_2 : Nat.count Nat.Prime 2 = 0 := by
  simpa only [Nat.nth_prime_zero_eq_two] using
    (Nat.count_nth_zero (p := Nat.Prime))

theorem prime_2 : (2 : Nat).Prime := by norm_num

theorem nth_0 : Nat.nth Nat.Prime 0 = 2 := by
  rw [← count_2]
  exact Nat.nth_count prime_2

theorem count_3 : Nat.count Nat.Prime 3 = 1 := by
  rw [show 3 = 2 + 1 by norm_num, Nat.count_succ]
  rw [count_2]
  simp [prime_2]

theorem prime_3 : (3 : Nat).Prime := by norm_num

theorem nth_1 : Nat.nth Nat.Prime 1 = 3 := by
  rw [← count_3]
  exact Nat.nth_count prime_3

theorem not_prime_4 : ¬Nat.Prime 4 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2) (n := 4)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_5 : Nat.count Nat.Prime 5 = 2 := by
  rw [show 5 = 4 + 1 by norm_num, Nat.count_succ]
  rw [show 4 = 3 + 1 by norm_num, Nat.count_succ]
  rw [count_3]
  simp [prime_3, not_prime_4]

theorem prime_5 : (5 : Nat).Prime := by norm_num

theorem nth_2 : Nat.nth Nat.Prime 2 = 5 := by
  rw [← count_5]
  exact Nat.nth_count prime_5

theorem not_prime_6 : ¬Nat.Prime 6 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 3) (n := 6)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_7 : Nat.count Nat.Prime 7 = 3 := by
  rw [show 7 = 6 + 1 by norm_num, Nat.count_succ]
  rw [show 6 = 5 + 1 by norm_num, Nat.count_succ]
  rw [count_5]
  simp [prime_5, not_prime_6]

theorem prime_7 : (7 : Nat).Prime := by norm_num

theorem nth_3 : Nat.nth Nat.Prime 3 = 7 := by
  rw [← count_7]
  exact Nat.nth_count prime_7

theorem not_prime_8 : ¬Nat.Prime 8 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 4) (n := 8)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_9 : ¬Nat.Prime 9 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 3) (n := 9)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_10 : ¬Nat.Prime 10 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 5) (n := 10)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_11 : Nat.count Nat.Prime 11 = 4 := by
  rw [show 11 = 10 + 1 by norm_num, Nat.count_succ]
  rw [show 10 = 9 + 1 by norm_num, Nat.count_succ]
  rw [show 9 = 8 + 1 by norm_num, Nat.count_succ]
  rw [show 8 = 7 + 1 by norm_num, Nat.count_succ]
  rw [count_7]
  simp [prime_7, not_prime_8, not_prime_9, not_prime_10]

theorem prime_11 : (11 : Nat).Prime := by norm_num

theorem nth_4 : Nat.nth Nat.Prime 4 = 11 := by
  rw [← count_11]
  exact Nat.nth_count prime_11

theorem not_prime_12 : ¬Nat.Prime 12 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 6) (n := 12)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_13 : Nat.count Nat.Prime 13 = 5 := by
  rw [show 13 = 12 + 1 by norm_num, Nat.count_succ]
  rw [show 12 = 11 + 1 by norm_num, Nat.count_succ]
  rw [count_11]
  simp [prime_11, not_prime_12]

theorem prime_13 : (13 : Nat).Prime := by norm_num

theorem nth_5 : Nat.nth Nat.Prime 5 = 13 := by
  rw [← count_13]
  exact Nat.nth_count prime_13

theorem not_prime_14 : ¬Nat.Prime 14 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 7) (n := 14)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_15 : ¬Nat.Prime 15 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 5) (n := 15)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_16 : ¬Nat.Prime 16 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 8) (n := 16)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_17 : Nat.count Nat.Prime 17 = 6 := by
  rw [show 17 = 16 + 1 by norm_num, Nat.count_succ]
  rw [show 16 = 15 + 1 by norm_num, Nat.count_succ]
  rw [show 15 = 14 + 1 by norm_num, Nat.count_succ]
  rw [show 14 = 13 + 1 by norm_num, Nat.count_succ]
  rw [count_13]
  simp [prime_13, not_prime_14, not_prime_15, not_prime_16]

theorem prime_17 : (17 : Nat).Prime := by norm_num

theorem nth_6 : Nat.nth Nat.Prime 6 = 17 := by
  rw [← count_17]
  exact Nat.nth_count prime_17

theorem not_prime_18 : ¬Nat.Prime 18 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 9) (n := 18)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_19 : Nat.count Nat.Prime 19 = 7 := by
  rw [show 19 = 18 + 1 by norm_num, Nat.count_succ]
  rw [show 18 = 17 + 1 by norm_num, Nat.count_succ]
  rw [count_17]
  simp [prime_17, not_prime_18]

theorem prime_19 : (19 : Nat).Prime := by norm_num

theorem nth_7 : Nat.nth Nat.Prime 7 = 19 := by
  rw [← count_19]
  exact Nat.nth_count prime_19

theorem not_prime_20 : ¬Nat.Prime 20 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 10) (n := 20)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_21 : ¬Nat.Prime 21 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 7) (n := 21)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_22 : ¬Nat.Prime 22 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 11) (n := 22)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_23 : Nat.count Nat.Prime 23 = 8 := by
  rw [show 23 = 22 + 1 by norm_num, Nat.count_succ]
  rw [show 22 = 21 + 1 by norm_num, Nat.count_succ]
  rw [show 21 = 20 + 1 by norm_num, Nat.count_succ]
  rw [show 20 = 19 + 1 by norm_num, Nat.count_succ]
  rw [count_19]
  simp [prime_19, not_prime_20, not_prime_21, not_prime_22]

theorem prime_23 : (23 : Nat).Prime := by norm_num

theorem nth_8 : Nat.nth Nat.Prime 8 = 23 := by
  rw [← count_23]
  exact Nat.nth_count prime_23

theorem not_prime_24 : ¬Nat.Prime 24 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 12) (n := 24)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_25 : ¬Nat.Prime 25 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 5) (n := 25)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_26 : ¬Nat.Prime 26 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 13) (n := 26)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_27 : ¬Nat.Prime 27 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 9) (n := 27)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_28 : ¬Nat.Prime 28 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 14) (n := 28)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_29 : Nat.count Nat.Prime 29 = 9 := by
  rw [show 29 = 28 + 1 by norm_num, Nat.count_succ]
  rw [show 28 = 27 + 1 by norm_num, Nat.count_succ]
  rw [show 27 = 26 + 1 by norm_num, Nat.count_succ]
  rw [show 26 = 25 + 1 by norm_num, Nat.count_succ]
  rw [show 25 = 24 + 1 by norm_num, Nat.count_succ]
  rw [show 24 = 23 + 1 by norm_num, Nat.count_succ]
  rw [count_23]
  simp [prime_23, not_prime_24, not_prime_25, not_prime_26, not_prime_27, not_prime_28]

theorem prime_29 : (29 : Nat).Prime := by norm_num

theorem nth_9 : Nat.nth Nat.Prime 9 = 29 := by
  rw [← count_29]
  exact Nat.nth_count prime_29

theorem not_prime_30 : ¬Nat.Prime 30 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 15) (n := 30)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_31 : Nat.count Nat.Prime 31 = 10 := by
  rw [show 31 = 30 + 1 by norm_num, Nat.count_succ]
  rw [show 30 = 29 + 1 by norm_num, Nat.count_succ]
  rw [count_29]
  simp [prime_29, not_prime_30]

theorem prime_31 : (31 : Nat).Prime := by norm_num

theorem nth_10 : Nat.nth Nat.Prime 10 = 31 := by
  rw [← count_31]
  exact Nat.nth_count prime_31

theorem not_prime_32 : ¬Nat.Prime 32 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 16) (n := 32)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_33 : ¬Nat.Prime 33 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 11) (n := 33)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_34 : ¬Nat.Prime 34 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 17) (n := 34)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_35 : ¬Nat.Prime 35 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 7) (n := 35)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_36 : ¬Nat.Prime 36 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 18) (n := 36)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_37 : Nat.count Nat.Prime 37 = 11 := by
  rw [show 37 = 36 + 1 by norm_num, Nat.count_succ]
  rw [show 36 = 35 + 1 by norm_num, Nat.count_succ]
  rw [show 35 = 34 + 1 by norm_num, Nat.count_succ]
  rw [show 34 = 33 + 1 by norm_num, Nat.count_succ]
  rw [show 33 = 32 + 1 by norm_num, Nat.count_succ]
  rw [show 32 = 31 + 1 by norm_num, Nat.count_succ]
  rw [count_31]
  simp [prime_31, not_prime_32, not_prime_33, not_prime_34, not_prime_35, not_prime_36]

theorem prime_37 : (37 : Nat).Prime := by norm_num

theorem nth_11 : Nat.nth Nat.Prime 11 = 37 := by
  rw [← count_37]
  exact Nat.nth_count prime_37

theorem not_prime_38 : ¬Nat.Prime 38 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 19) (n := 38)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_39 : ¬Nat.Prime 39 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 13) (n := 39)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_40 : ¬Nat.Prime 40 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 20) (n := 40)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_41 : Nat.count Nat.Prime 41 = 12 := by
  rw [show 41 = 40 + 1 by norm_num, Nat.count_succ]
  rw [show 40 = 39 + 1 by norm_num, Nat.count_succ]
  rw [show 39 = 38 + 1 by norm_num, Nat.count_succ]
  rw [show 38 = 37 + 1 by norm_num, Nat.count_succ]
  rw [count_37]
  simp [prime_37, not_prime_38, not_prime_39, not_prime_40]

theorem prime_41 : (41 : Nat).Prime := by norm_num

theorem nth_12 : Nat.nth Nat.Prime 12 = 41 := by
  rw [← count_41]
  exact Nat.nth_count prime_41

theorem not_prime_42 : ¬Nat.Prime 42 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 21) (n := 42)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_43 : Nat.count Nat.Prime 43 = 13 := by
  rw [show 43 = 42 + 1 by norm_num, Nat.count_succ]
  rw [show 42 = 41 + 1 by norm_num, Nat.count_succ]
  rw [count_41]
  simp [prime_41, not_prime_42]

theorem prime_43 : (43 : Nat).Prime := by norm_num

theorem nth_13 : Nat.nth Nat.Prime 13 = 43 := by
  rw [← count_43]
  exact Nat.nth_count prime_43

theorem not_prime_44 : ¬Nat.Prime 44 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 22) (n := 44)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_45 : ¬Nat.Prime 45 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 15) (n := 45)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_46 : ¬Nat.Prime 46 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 23) (n := 46)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_47 : Nat.count Nat.Prime 47 = 14 := by
  rw [show 47 = 46 + 1 by norm_num, Nat.count_succ]
  rw [show 46 = 45 + 1 by norm_num, Nat.count_succ]
  rw [show 45 = 44 + 1 by norm_num, Nat.count_succ]
  rw [show 44 = 43 + 1 by norm_num, Nat.count_succ]
  rw [count_43]
  simp [prime_43, not_prime_44, not_prime_45, not_prime_46]

theorem prime_47 : (47 : Nat).Prime := by norm_num

theorem nth_14 : Nat.nth Nat.Prime 14 = 47 := by
  rw [← count_47]
  exact Nat.nth_count prime_47

theorem not_prime_48 : ¬Nat.Prime 48 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 24) (n := 48)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_49 : ¬Nat.Prime 49 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 7) (n := 49)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_50 : ¬Nat.Prime 50 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 25) (n := 50)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_51 : ¬Nat.Prime 51 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 17) (n := 51)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_52 : ¬Nat.Prime 52 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 26) (n := 52)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_53 : Nat.count Nat.Prime 53 = 15 := by
  rw [show 53 = 52 + 1 by norm_num, Nat.count_succ]
  rw [show 52 = 51 + 1 by norm_num, Nat.count_succ]
  rw [show 51 = 50 + 1 by norm_num, Nat.count_succ]
  rw [show 50 = 49 + 1 by norm_num, Nat.count_succ]
  rw [show 49 = 48 + 1 by norm_num, Nat.count_succ]
  rw [show 48 = 47 + 1 by norm_num, Nat.count_succ]
  rw [count_47]
  simp [prime_47, not_prime_48, not_prime_49, not_prime_50, not_prime_51, not_prime_52]

theorem prime_53 : (53 : Nat).Prime := by norm_num

theorem nth_15 : Nat.nth Nat.Prime 15 = 53 := by
  rw [← count_53]
  exact Nat.nth_count prime_53

theorem not_prime_54 : ¬Nat.Prime 54 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 27) (n := 54)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_55 : ¬Nat.Prime 55 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 11) (n := 55)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_56 : ¬Nat.Prime 56 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 28) (n := 56)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_57 : ¬Nat.Prime 57 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 19) (n := 57)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_58 : ¬Nat.Prime 58 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 29) (n := 58)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_59 : Nat.count Nat.Prime 59 = 16 := by
  rw [show 59 = 58 + 1 by norm_num, Nat.count_succ]
  rw [show 58 = 57 + 1 by norm_num, Nat.count_succ]
  rw [show 57 = 56 + 1 by norm_num, Nat.count_succ]
  rw [show 56 = 55 + 1 by norm_num, Nat.count_succ]
  rw [show 55 = 54 + 1 by norm_num, Nat.count_succ]
  rw [show 54 = 53 + 1 by norm_num, Nat.count_succ]
  rw [count_53]
  simp [prime_53, not_prime_54, not_prime_55, not_prime_56, not_prime_57, not_prime_58]

theorem prime_59 : (59 : Nat).Prime := by norm_num

theorem nth_16 : Nat.nth Nat.Prime 16 = 59 := by
  rw [← count_59]
  exact Nat.nth_count prime_59

theorem not_prime_60 : ¬Nat.Prime 60 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 30) (n := 60)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_61 : Nat.count Nat.Prime 61 = 17 := by
  rw [show 61 = 60 + 1 by norm_num, Nat.count_succ]
  rw [show 60 = 59 + 1 by norm_num, Nat.count_succ]
  rw [count_59]
  simp [prime_59, not_prime_60]

theorem prime_61 : (61 : Nat).Prime := by norm_num

theorem nth_17 : Nat.nth Nat.Prime 17 = 61 := by
  rw [← count_61]
  exact Nat.nth_count prime_61

theorem not_prime_62 : ¬Nat.Prime 62 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 31) (n := 62)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_63 : ¬Nat.Prime 63 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 21) (n := 63)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_64 : ¬Nat.Prime 64 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 32) (n := 64)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_65 : ¬Nat.Prime 65 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 13) (n := 65)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_66 : ¬Nat.Prime 66 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 33) (n := 66)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_67 : Nat.count Nat.Prime 67 = 18 := by
  rw [show 67 = 66 + 1 by norm_num, Nat.count_succ]
  rw [show 66 = 65 + 1 by norm_num, Nat.count_succ]
  rw [show 65 = 64 + 1 by norm_num, Nat.count_succ]
  rw [show 64 = 63 + 1 by norm_num, Nat.count_succ]
  rw [show 63 = 62 + 1 by norm_num, Nat.count_succ]
  rw [show 62 = 61 + 1 by norm_num, Nat.count_succ]
  rw [count_61]
  simp [prime_61, not_prime_62, not_prime_63, not_prime_64, not_prime_65, not_prime_66]

theorem prime_67 : (67 : Nat).Prime := by norm_num

theorem nth_18 : Nat.nth Nat.Prime 18 = 67 := by
  rw [← count_67]
  exact Nat.nth_count prime_67

theorem not_prime_68 : ¬Nat.Prime 68 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 34) (n := 68)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_69 : ¬Nat.Prime 69 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 23) (n := 69)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_70 : ¬Nat.Prime 70 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 35) (n := 70)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_71 : Nat.count Nat.Prime 71 = 19 := by
  rw [show 71 = 70 + 1 by norm_num, Nat.count_succ]
  rw [show 70 = 69 + 1 by norm_num, Nat.count_succ]
  rw [show 69 = 68 + 1 by norm_num, Nat.count_succ]
  rw [show 68 = 67 + 1 by norm_num, Nat.count_succ]
  rw [count_67]
  simp [prime_67, not_prime_68, not_prime_69, not_prime_70]

theorem prime_71 : (71 : Nat).Prime := by norm_num

theorem nth_19 : Nat.nth Nat.Prime 19 = 71 := by
  rw [← count_71]
  exact Nat.nth_count prime_71

theorem not_prime_72 : ¬Nat.Prime 72 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 36) (n := 72)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_73 : Nat.count Nat.Prime 73 = 20 := by
  rw [show 73 = 72 + 1 by norm_num, Nat.count_succ]
  rw [show 72 = 71 + 1 by norm_num, Nat.count_succ]
  rw [count_71]
  simp [prime_71, not_prime_72]

theorem prime_73 : (73 : Nat).Prime := by norm_num

theorem nth_20 : Nat.nth Nat.Prime 20 = 73 := by
  rw [← count_73]
  exact Nat.nth_count prime_73

theorem not_prime_74 : ¬Nat.Prime 74 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 37) (n := 74)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_75 : ¬Nat.Prime 75 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 25) (n := 75)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_76 : ¬Nat.Prime 76 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 38) (n := 76)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_77 : ¬Nat.Prime 77 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 11) (n := 77)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_78 : ¬Nat.Prime 78 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 39) (n := 78)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_79 : Nat.count Nat.Prime 79 = 21 := by
  rw [show 79 = 78 + 1 by norm_num, Nat.count_succ]
  rw [show 78 = 77 + 1 by norm_num, Nat.count_succ]
  rw [show 77 = 76 + 1 by norm_num, Nat.count_succ]
  rw [show 76 = 75 + 1 by norm_num, Nat.count_succ]
  rw [show 75 = 74 + 1 by norm_num, Nat.count_succ]
  rw [show 74 = 73 + 1 by norm_num, Nat.count_succ]
  rw [count_73]
  simp [prime_73, not_prime_74, not_prime_75, not_prime_76, not_prime_77, not_prime_78]

theorem prime_79 : (79 : Nat).Prime := by norm_num

theorem nth_21 : Nat.nth Nat.Prime 21 = 79 := by
  rw [← count_79]
  exact Nat.nth_count prime_79

theorem not_prime_80 : ¬Nat.Prime 80 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 40) (n := 80)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_81 : ¬Nat.Prime 81 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 27) (n := 81)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_82 : ¬Nat.Prime 82 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 41) (n := 82)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_83 : Nat.count Nat.Prime 83 = 22 := by
  rw [show 83 = 82 + 1 by norm_num, Nat.count_succ]
  rw [show 82 = 81 + 1 by norm_num, Nat.count_succ]
  rw [show 81 = 80 + 1 by norm_num, Nat.count_succ]
  rw [show 80 = 79 + 1 by norm_num, Nat.count_succ]
  rw [count_79]
  simp [prime_79, not_prime_80, not_prime_81, not_prime_82]

theorem prime_83 : (83 : Nat).Prime := by norm_num

theorem nth_22 : Nat.nth Nat.Prime 22 = 83 := by
  rw [← count_83]
  exact Nat.nth_count prime_83

theorem not_prime_84 : ¬Nat.Prime 84 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 42) (n := 84)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_85 : ¬Nat.Prime 85 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 17) (n := 85)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_86 : ¬Nat.Prime 86 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 43) (n := 86)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_87 : ¬Nat.Prime 87 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 29) (n := 87)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_88 : ¬Nat.Prime 88 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 44) (n := 88)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_89 : Nat.count Nat.Prime 89 = 23 := by
  rw [show 89 = 88 + 1 by norm_num, Nat.count_succ]
  rw [show 88 = 87 + 1 by norm_num, Nat.count_succ]
  rw [show 87 = 86 + 1 by norm_num, Nat.count_succ]
  rw [show 86 = 85 + 1 by norm_num, Nat.count_succ]
  rw [show 85 = 84 + 1 by norm_num, Nat.count_succ]
  rw [show 84 = 83 + 1 by norm_num, Nat.count_succ]
  rw [count_83]
  simp [prime_83, not_prime_84, not_prime_85, not_prime_86, not_prime_87, not_prime_88]

theorem prime_89 : (89 : Nat).Prime := by norm_num

theorem nth_23 : Nat.nth Nat.Prime 23 = 89 := by
  rw [← count_89]
  exact Nat.nth_count prime_89

theorem not_prime_90 : ¬Nat.Prime 90 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 45) (n := 90)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_91 : ¬Nat.Prime 91 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 13) (n := 91)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_92 : ¬Nat.Prime 92 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 46) (n := 92)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_93 : ¬Nat.Prime 93 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 31) (n := 93)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_94 : ¬Nat.Prime 94 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 47) (n := 94)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_95 : ¬Nat.Prime 95 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 19) (n := 95)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_96 : ¬Nat.Prime 96 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 48) (n := 96)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_97 : Nat.count Nat.Prime 97 = 24 := by
  rw [show 97 = 96 + 1 by norm_num, Nat.count_succ]
  rw [show 96 = 95 + 1 by norm_num, Nat.count_succ]
  rw [show 95 = 94 + 1 by norm_num, Nat.count_succ]
  rw [show 94 = 93 + 1 by norm_num, Nat.count_succ]
  rw [show 93 = 92 + 1 by norm_num, Nat.count_succ]
  rw [show 92 = 91 + 1 by norm_num, Nat.count_succ]
  rw [show 91 = 90 + 1 by norm_num, Nat.count_succ]
  rw [show 90 = 89 + 1 by norm_num, Nat.count_succ]
  rw [count_89]
  simp [prime_89, not_prime_90, not_prime_91, not_prime_92, not_prime_93, not_prime_94, not_prime_95, not_prime_96]

theorem prime_97 : (97 : Nat).Prime := by norm_num

theorem nth_24 : Nat.nth Nat.Prime 24 = 97 := by
  rw [← count_97]
  exact Nat.nth_count prime_97

end OeisA100474.PrimeCertificate
