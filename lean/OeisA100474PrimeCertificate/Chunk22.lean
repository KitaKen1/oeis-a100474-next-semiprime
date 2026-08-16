import OeisA100474PrimeCertificate.Chunk21

/-! Kernel prime/count certificate, chunk 22 (550–574). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_3990 : ¬Nat.Prime 3990 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1995) (n := 3990)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3991 : ¬Nat.Prime 3991 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 307) (n := 3991)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3992 : ¬Nat.Prime 3992 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1996) (n := 3992)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3993 : ¬Nat.Prime 3993 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1331) (n := 3993)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3994 : ¬Nat.Prime 3994 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1997) (n := 3994)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3995 : ¬Nat.Prime 3995 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 799) (n := 3995)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3996 : ¬Nat.Prime 3996 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1998) (n := 3996)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3997 : ¬Nat.Prime 3997 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 571) (n := 3997)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3998 : ¬Nat.Prime 3998 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1999) (n := 3998)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3999 : ¬Nat.Prime 3999 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1333) (n := 3999)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4000 : ¬Nat.Prime 4000 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2000) (n := 4000)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4001 : Nat.count Nat.Prime 4001 = 550 := by
  rw [show 4001 = 4000 + 1 by norm_num, Nat.count_succ]
  rw [show 4000 = 3999 + 1 by norm_num, Nat.count_succ]
  rw [show 3999 = 3998 + 1 by norm_num, Nat.count_succ]
  rw [show 3998 = 3997 + 1 by norm_num, Nat.count_succ]
  rw [show 3997 = 3996 + 1 by norm_num, Nat.count_succ]
  rw [show 3996 = 3995 + 1 by norm_num, Nat.count_succ]
  rw [show 3995 = 3994 + 1 by norm_num, Nat.count_succ]
  rw [show 3994 = 3993 + 1 by norm_num, Nat.count_succ]
  rw [show 3993 = 3992 + 1 by norm_num, Nat.count_succ]
  rw [show 3992 = 3991 + 1 by norm_num, Nat.count_succ]
  rw [show 3991 = 3990 + 1 by norm_num, Nat.count_succ]
  rw [show 3990 = 3989 + 1 by norm_num, Nat.count_succ]
  rw [count_3989]
  simp [prime_3989, not_prime_3990, not_prime_3991, not_prime_3992, not_prime_3993, not_prime_3994, not_prime_3995, not_prime_3996, not_prime_3997, not_prime_3998, not_prime_3999, not_prime_4000]

theorem prime_4001 : (4001 : Nat).Prime := by norm_num

theorem nth_550 : Nat.nth Nat.Prime 550 = 4001 := by
  rw [← count_4001]
  exact Nat.nth_count prime_4001

theorem not_prime_4002 : ¬Nat.Prime 4002 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2001) (n := 4002)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4003 : Nat.count Nat.Prime 4003 = 551 := by
  rw [show 4003 = 4002 + 1 by norm_num, Nat.count_succ]
  rw [show 4002 = 4001 + 1 by norm_num, Nat.count_succ]
  rw [count_4001]
  simp [prime_4001, not_prime_4002]

theorem prime_4003 : (4003 : Nat).Prime := by norm_num

theorem nth_551 : Nat.nth Nat.Prime 551 = 4003 := by
  rw [← count_4003]
  exact Nat.nth_count prime_4003

theorem not_prime_4004 : ¬Nat.Prime 4004 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2002) (n := 4004)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4005 : ¬Nat.Prime 4005 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1335) (n := 4005)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4006 : ¬Nat.Prime 4006 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2003) (n := 4006)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4007 : Nat.count Nat.Prime 4007 = 552 := by
  rw [show 4007 = 4006 + 1 by norm_num, Nat.count_succ]
  rw [show 4006 = 4005 + 1 by norm_num, Nat.count_succ]
  rw [show 4005 = 4004 + 1 by norm_num, Nat.count_succ]
  rw [show 4004 = 4003 + 1 by norm_num, Nat.count_succ]
  rw [count_4003]
  simp [prime_4003, not_prime_4004, not_prime_4005, not_prime_4006]

theorem prime_4007 : (4007 : Nat).Prime := by norm_num

theorem nth_552 : Nat.nth Nat.Prime 552 = 4007 := by
  rw [← count_4007]
  exact Nat.nth_count prime_4007

theorem not_prime_4008 : ¬Nat.Prime 4008 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2004) (n := 4008)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4009 : ¬Nat.Prime 4009 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 211) (n := 4009)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4010 : ¬Nat.Prime 4010 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2005) (n := 4010)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4011 : ¬Nat.Prime 4011 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1337) (n := 4011)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4012 : ¬Nat.Prime 4012 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2006) (n := 4012)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4013 : Nat.count Nat.Prime 4013 = 553 := by
  rw [show 4013 = 4012 + 1 by norm_num, Nat.count_succ]
  rw [show 4012 = 4011 + 1 by norm_num, Nat.count_succ]
  rw [show 4011 = 4010 + 1 by norm_num, Nat.count_succ]
  rw [show 4010 = 4009 + 1 by norm_num, Nat.count_succ]
  rw [show 4009 = 4008 + 1 by norm_num, Nat.count_succ]
  rw [show 4008 = 4007 + 1 by norm_num, Nat.count_succ]
  rw [count_4007]
  simp [prime_4007, not_prime_4008, not_prime_4009, not_prime_4010, not_prime_4011, not_prime_4012]

theorem prime_4013 : (4013 : Nat).Prime := by norm_num

theorem nth_553 : Nat.nth Nat.Prime 553 = 4013 := by
  rw [← count_4013]
  exact Nat.nth_count prime_4013

theorem not_prime_4014 : ¬Nat.Prime 4014 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2007) (n := 4014)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4015 : ¬Nat.Prime 4015 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 803) (n := 4015)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4016 : ¬Nat.Prime 4016 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2008) (n := 4016)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4017 : ¬Nat.Prime 4017 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1339) (n := 4017)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4018 : ¬Nat.Prime 4018 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2009) (n := 4018)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4019 : Nat.count Nat.Prime 4019 = 554 := by
  rw [show 4019 = 4018 + 1 by norm_num, Nat.count_succ]
  rw [show 4018 = 4017 + 1 by norm_num, Nat.count_succ]
  rw [show 4017 = 4016 + 1 by norm_num, Nat.count_succ]
  rw [show 4016 = 4015 + 1 by norm_num, Nat.count_succ]
  rw [show 4015 = 4014 + 1 by norm_num, Nat.count_succ]
  rw [show 4014 = 4013 + 1 by norm_num, Nat.count_succ]
  rw [count_4013]
  simp [prime_4013, not_prime_4014, not_prime_4015, not_prime_4016, not_prime_4017, not_prime_4018]

theorem prime_4019 : (4019 : Nat).Prime := by norm_num

theorem nth_554 : Nat.nth Nat.Prime 554 = 4019 := by
  rw [← count_4019]
  exact Nat.nth_count prime_4019

theorem not_prime_4020 : ¬Nat.Prime 4020 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2010) (n := 4020)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4021 : Nat.count Nat.Prime 4021 = 555 := by
  rw [show 4021 = 4020 + 1 by norm_num, Nat.count_succ]
  rw [show 4020 = 4019 + 1 by norm_num, Nat.count_succ]
  rw [count_4019]
  simp [prime_4019, not_prime_4020]

theorem prime_4021 : (4021 : Nat).Prime := by norm_num

theorem nth_555 : Nat.nth Nat.Prime 555 = 4021 := by
  rw [← count_4021]
  exact Nat.nth_count prime_4021

theorem not_prime_4022 : ¬Nat.Prime 4022 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2011) (n := 4022)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4023 : ¬Nat.Prime 4023 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1341) (n := 4023)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4024 : ¬Nat.Prime 4024 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2012) (n := 4024)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4025 : ¬Nat.Prime 4025 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 805) (n := 4025)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4026 : ¬Nat.Prime 4026 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2013) (n := 4026)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4027 : Nat.count Nat.Prime 4027 = 556 := by
  rw [show 4027 = 4026 + 1 by norm_num, Nat.count_succ]
  rw [show 4026 = 4025 + 1 by norm_num, Nat.count_succ]
  rw [show 4025 = 4024 + 1 by norm_num, Nat.count_succ]
  rw [show 4024 = 4023 + 1 by norm_num, Nat.count_succ]
  rw [show 4023 = 4022 + 1 by norm_num, Nat.count_succ]
  rw [show 4022 = 4021 + 1 by norm_num, Nat.count_succ]
  rw [count_4021]
  simp [prime_4021, not_prime_4022, not_prime_4023, not_prime_4024, not_prime_4025, not_prime_4026]

theorem prime_4027 : (4027 : Nat).Prime := by norm_num

theorem nth_556 : Nat.nth Nat.Prime 556 = 4027 := by
  rw [← count_4027]
  exact Nat.nth_count prime_4027

theorem not_prime_4028 : ¬Nat.Prime 4028 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2014) (n := 4028)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4029 : ¬Nat.Prime 4029 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1343) (n := 4029)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4030 : ¬Nat.Prime 4030 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2015) (n := 4030)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4031 : ¬Nat.Prime 4031 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 139) (n := 4031)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4032 : ¬Nat.Prime 4032 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2016) (n := 4032)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4033 : ¬Nat.Prime 4033 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 109) (n := 4033)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4034 : ¬Nat.Prime 4034 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2017) (n := 4034)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4035 : ¬Nat.Prime 4035 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1345) (n := 4035)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4036 : ¬Nat.Prime 4036 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2018) (n := 4036)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4037 : ¬Nat.Prime 4037 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 367) (n := 4037)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4038 : ¬Nat.Prime 4038 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2019) (n := 4038)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4039 : ¬Nat.Prime 4039 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 577) (n := 4039)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4040 : ¬Nat.Prime 4040 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2020) (n := 4040)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4041 : ¬Nat.Prime 4041 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1347) (n := 4041)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4042 : ¬Nat.Prime 4042 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2021) (n := 4042)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4043 : ¬Nat.Prime 4043 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 311) (n := 4043)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4044 : ¬Nat.Prime 4044 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2022) (n := 4044)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4045 : ¬Nat.Prime 4045 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 809) (n := 4045)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4046 : ¬Nat.Prime 4046 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2023) (n := 4046)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4047 : ¬Nat.Prime 4047 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1349) (n := 4047)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4048 : ¬Nat.Prime 4048 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2024) (n := 4048)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4049 : Nat.count Nat.Prime 4049 = 557 := by
  rw [show 4049 = 4048 + 1 by norm_num, Nat.count_succ]
  rw [show 4048 = 4047 + 1 by norm_num, Nat.count_succ]
  rw [show 4047 = 4046 + 1 by norm_num, Nat.count_succ]
  rw [show 4046 = 4045 + 1 by norm_num, Nat.count_succ]
  rw [show 4045 = 4044 + 1 by norm_num, Nat.count_succ]
  rw [show 4044 = 4043 + 1 by norm_num, Nat.count_succ]
  rw [show 4043 = 4042 + 1 by norm_num, Nat.count_succ]
  rw [show 4042 = 4041 + 1 by norm_num, Nat.count_succ]
  rw [show 4041 = 4040 + 1 by norm_num, Nat.count_succ]
  rw [show 4040 = 4039 + 1 by norm_num, Nat.count_succ]
  rw [show 4039 = 4038 + 1 by norm_num, Nat.count_succ]
  rw [show 4038 = 4037 + 1 by norm_num, Nat.count_succ]
  rw [show 4037 = 4036 + 1 by norm_num, Nat.count_succ]
  rw [show 4036 = 4035 + 1 by norm_num, Nat.count_succ]
  rw [show 4035 = 4034 + 1 by norm_num, Nat.count_succ]
  rw [show 4034 = 4033 + 1 by norm_num, Nat.count_succ]
  rw [show 4033 = 4032 + 1 by norm_num, Nat.count_succ]
  rw [show 4032 = 4031 + 1 by norm_num, Nat.count_succ]
  rw [show 4031 = 4030 + 1 by norm_num, Nat.count_succ]
  rw [show 4030 = 4029 + 1 by norm_num, Nat.count_succ]
  rw [show 4029 = 4028 + 1 by norm_num, Nat.count_succ]
  rw [show 4028 = 4027 + 1 by norm_num, Nat.count_succ]
  rw [count_4027]
  simp [prime_4027, not_prime_4028, not_prime_4029, not_prime_4030, not_prime_4031, not_prime_4032, not_prime_4033, not_prime_4034, not_prime_4035, not_prime_4036, not_prime_4037, not_prime_4038, not_prime_4039, not_prime_4040, not_prime_4041, not_prime_4042, not_prime_4043, not_prime_4044, not_prime_4045, not_prime_4046, not_prime_4047, not_prime_4048]

theorem prime_4049 : (4049 : Nat).Prime := by norm_num

theorem nth_557 : Nat.nth Nat.Prime 557 = 4049 := by
  rw [← count_4049]
  exact Nat.nth_count prime_4049

theorem not_prime_4050 : ¬Nat.Prime 4050 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2025) (n := 4050)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4051 : Nat.count Nat.Prime 4051 = 558 := by
  rw [show 4051 = 4050 + 1 by norm_num, Nat.count_succ]
  rw [show 4050 = 4049 + 1 by norm_num, Nat.count_succ]
  rw [count_4049]
  simp [prime_4049, not_prime_4050]

theorem prime_4051 : (4051 : Nat).Prime := by norm_num

theorem nth_558 : Nat.nth Nat.Prime 558 = 4051 := by
  rw [← count_4051]
  exact Nat.nth_count prime_4051

theorem not_prime_4052 : ¬Nat.Prime 4052 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2026) (n := 4052)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4053 : ¬Nat.Prime 4053 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1351) (n := 4053)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4054 : ¬Nat.Prime 4054 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2027) (n := 4054)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4055 : ¬Nat.Prime 4055 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 811) (n := 4055)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4056 : ¬Nat.Prime 4056 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2028) (n := 4056)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4057 : Nat.count Nat.Prime 4057 = 559 := by
  rw [show 4057 = 4056 + 1 by norm_num, Nat.count_succ]
  rw [show 4056 = 4055 + 1 by norm_num, Nat.count_succ]
  rw [show 4055 = 4054 + 1 by norm_num, Nat.count_succ]
  rw [show 4054 = 4053 + 1 by norm_num, Nat.count_succ]
  rw [show 4053 = 4052 + 1 by norm_num, Nat.count_succ]
  rw [show 4052 = 4051 + 1 by norm_num, Nat.count_succ]
  rw [count_4051]
  simp [prime_4051, not_prime_4052, not_prime_4053, not_prime_4054, not_prime_4055, not_prime_4056]

theorem prime_4057 : (4057 : Nat).Prime := by norm_num

theorem nth_559 : Nat.nth Nat.Prime 559 = 4057 := by
  rw [← count_4057]
  exact Nat.nth_count prime_4057

theorem not_prime_4058 : ¬Nat.Prime 4058 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2029) (n := 4058)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4059 : ¬Nat.Prime 4059 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1353) (n := 4059)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4060 : ¬Nat.Prime 4060 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2030) (n := 4060)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4061 : ¬Nat.Prime 4061 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 131) (n := 4061)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4062 : ¬Nat.Prime 4062 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2031) (n := 4062)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4063 : ¬Nat.Prime 4063 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 239) (n := 4063)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4064 : ¬Nat.Prime 4064 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2032) (n := 4064)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4065 : ¬Nat.Prime 4065 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1355) (n := 4065)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4066 : ¬Nat.Prime 4066 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2033) (n := 4066)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4067 : ¬Nat.Prime 4067 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 581) (n := 4067)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4068 : ¬Nat.Prime 4068 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2034) (n := 4068)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4069 : ¬Nat.Prime 4069 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 313) (n := 4069)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4070 : ¬Nat.Prime 4070 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2035) (n := 4070)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4071 : ¬Nat.Prime 4071 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1357) (n := 4071)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4072 : ¬Nat.Prime 4072 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2036) (n := 4072)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4073 : Nat.count Nat.Prime 4073 = 560 := by
  rw [show 4073 = 4072 + 1 by norm_num, Nat.count_succ]
  rw [show 4072 = 4071 + 1 by norm_num, Nat.count_succ]
  rw [show 4071 = 4070 + 1 by norm_num, Nat.count_succ]
  rw [show 4070 = 4069 + 1 by norm_num, Nat.count_succ]
  rw [show 4069 = 4068 + 1 by norm_num, Nat.count_succ]
  rw [show 4068 = 4067 + 1 by norm_num, Nat.count_succ]
  rw [show 4067 = 4066 + 1 by norm_num, Nat.count_succ]
  rw [show 4066 = 4065 + 1 by norm_num, Nat.count_succ]
  rw [show 4065 = 4064 + 1 by norm_num, Nat.count_succ]
  rw [show 4064 = 4063 + 1 by norm_num, Nat.count_succ]
  rw [show 4063 = 4062 + 1 by norm_num, Nat.count_succ]
  rw [show 4062 = 4061 + 1 by norm_num, Nat.count_succ]
  rw [show 4061 = 4060 + 1 by norm_num, Nat.count_succ]
  rw [show 4060 = 4059 + 1 by norm_num, Nat.count_succ]
  rw [show 4059 = 4058 + 1 by norm_num, Nat.count_succ]
  rw [show 4058 = 4057 + 1 by norm_num, Nat.count_succ]
  rw [count_4057]
  simp [prime_4057, not_prime_4058, not_prime_4059, not_prime_4060, not_prime_4061, not_prime_4062, not_prime_4063, not_prime_4064, not_prime_4065, not_prime_4066, not_prime_4067, not_prime_4068, not_prime_4069, not_prime_4070, not_prime_4071, not_prime_4072]

theorem prime_4073 : (4073 : Nat).Prime := by norm_num

theorem nth_560 : Nat.nth Nat.Prime 560 = 4073 := by
  rw [← count_4073]
  exact Nat.nth_count prime_4073

theorem not_prime_4074 : ¬Nat.Prime 4074 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2037) (n := 4074)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4075 : ¬Nat.Prime 4075 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 815) (n := 4075)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4076 : ¬Nat.Prime 4076 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2038) (n := 4076)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4077 : ¬Nat.Prime 4077 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1359) (n := 4077)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4078 : ¬Nat.Prime 4078 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2039) (n := 4078)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4079 : Nat.count Nat.Prime 4079 = 561 := by
  rw [show 4079 = 4078 + 1 by norm_num, Nat.count_succ]
  rw [show 4078 = 4077 + 1 by norm_num, Nat.count_succ]
  rw [show 4077 = 4076 + 1 by norm_num, Nat.count_succ]
  rw [show 4076 = 4075 + 1 by norm_num, Nat.count_succ]
  rw [show 4075 = 4074 + 1 by norm_num, Nat.count_succ]
  rw [show 4074 = 4073 + 1 by norm_num, Nat.count_succ]
  rw [count_4073]
  simp [prime_4073, not_prime_4074, not_prime_4075, not_prime_4076, not_prime_4077, not_prime_4078]

theorem prime_4079 : (4079 : Nat).Prime := by norm_num

theorem nth_561 : Nat.nth Nat.Prime 561 = 4079 := by
  rw [← count_4079]
  exact Nat.nth_count prime_4079

theorem not_prime_4080 : ¬Nat.Prime 4080 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2040) (n := 4080)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4081 : ¬Nat.Prime 4081 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 583) (n := 4081)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4082 : ¬Nat.Prime 4082 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2041) (n := 4082)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4083 : ¬Nat.Prime 4083 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1361) (n := 4083)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4084 : ¬Nat.Prime 4084 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2042) (n := 4084)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4085 : ¬Nat.Prime 4085 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 817) (n := 4085)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4086 : ¬Nat.Prime 4086 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2043) (n := 4086)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4087 : ¬Nat.Prime 4087 :=
  Nat.not_prime_of_mul_eq (a := 61) (b := 67) (n := 4087)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4088 : ¬Nat.Prime 4088 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2044) (n := 4088)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4089 : ¬Nat.Prime 4089 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1363) (n := 4089)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4090 : ¬Nat.Prime 4090 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2045) (n := 4090)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4091 : Nat.count Nat.Prime 4091 = 562 := by
  rw [show 4091 = 4090 + 1 by norm_num, Nat.count_succ]
  rw [show 4090 = 4089 + 1 by norm_num, Nat.count_succ]
  rw [show 4089 = 4088 + 1 by norm_num, Nat.count_succ]
  rw [show 4088 = 4087 + 1 by norm_num, Nat.count_succ]
  rw [show 4087 = 4086 + 1 by norm_num, Nat.count_succ]
  rw [show 4086 = 4085 + 1 by norm_num, Nat.count_succ]
  rw [show 4085 = 4084 + 1 by norm_num, Nat.count_succ]
  rw [show 4084 = 4083 + 1 by norm_num, Nat.count_succ]
  rw [show 4083 = 4082 + 1 by norm_num, Nat.count_succ]
  rw [show 4082 = 4081 + 1 by norm_num, Nat.count_succ]
  rw [show 4081 = 4080 + 1 by norm_num, Nat.count_succ]
  rw [show 4080 = 4079 + 1 by norm_num, Nat.count_succ]
  rw [count_4079]
  simp [prime_4079, not_prime_4080, not_prime_4081, not_prime_4082, not_prime_4083, not_prime_4084, not_prime_4085, not_prime_4086, not_prime_4087, not_prime_4088, not_prime_4089, not_prime_4090]

theorem prime_4091 : (4091 : Nat).Prime := by norm_num

theorem nth_562 : Nat.nth Nat.Prime 562 = 4091 := by
  rw [← count_4091]
  exact Nat.nth_count prime_4091

theorem not_prime_4092 : ¬Nat.Prime 4092 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2046) (n := 4092)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4093 : Nat.count Nat.Prime 4093 = 563 := by
  rw [show 4093 = 4092 + 1 by norm_num, Nat.count_succ]
  rw [show 4092 = 4091 + 1 by norm_num, Nat.count_succ]
  rw [count_4091]
  simp [prime_4091, not_prime_4092]

theorem prime_4093 : (4093 : Nat).Prime := by norm_num

theorem nth_563 : Nat.nth Nat.Prime 563 = 4093 := by
  rw [← count_4093]
  exact Nat.nth_count prime_4093

theorem not_prime_4094 : ¬Nat.Prime 4094 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2047) (n := 4094)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4095 : ¬Nat.Prime 4095 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1365) (n := 4095)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4096 : ¬Nat.Prime 4096 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2048) (n := 4096)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4097 : ¬Nat.Prime 4097 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 241) (n := 4097)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4098 : ¬Nat.Prime 4098 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2049) (n := 4098)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4099 : Nat.count Nat.Prime 4099 = 564 := by
  rw [show 4099 = 4098 + 1 by norm_num, Nat.count_succ]
  rw [show 4098 = 4097 + 1 by norm_num, Nat.count_succ]
  rw [show 4097 = 4096 + 1 by norm_num, Nat.count_succ]
  rw [show 4096 = 4095 + 1 by norm_num, Nat.count_succ]
  rw [show 4095 = 4094 + 1 by norm_num, Nat.count_succ]
  rw [show 4094 = 4093 + 1 by norm_num, Nat.count_succ]
  rw [count_4093]
  simp [prime_4093, not_prime_4094, not_prime_4095, not_prime_4096, not_prime_4097, not_prime_4098]

theorem prime_4099 : (4099 : Nat).Prime := by norm_num

theorem nth_564 : Nat.nth Nat.Prime 564 = 4099 := by
  rw [← count_4099]
  exact Nat.nth_count prime_4099

theorem not_prime_4100 : ¬Nat.Prime 4100 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2050) (n := 4100)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4101 : ¬Nat.Prime 4101 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1367) (n := 4101)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4102 : ¬Nat.Prime 4102 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2051) (n := 4102)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4103 : ¬Nat.Prime 4103 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 373) (n := 4103)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4104 : ¬Nat.Prime 4104 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2052) (n := 4104)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4105 : ¬Nat.Prime 4105 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 821) (n := 4105)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4106 : ¬Nat.Prime 4106 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2053) (n := 4106)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4107 : ¬Nat.Prime 4107 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1369) (n := 4107)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4108 : ¬Nat.Prime 4108 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2054) (n := 4108)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4109 : ¬Nat.Prime 4109 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 587) (n := 4109)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4110 : ¬Nat.Prime 4110 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2055) (n := 4110)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4111 : Nat.count Nat.Prime 4111 = 565 := by
  rw [show 4111 = 4110 + 1 by norm_num, Nat.count_succ]
  rw [show 4110 = 4109 + 1 by norm_num, Nat.count_succ]
  rw [show 4109 = 4108 + 1 by norm_num, Nat.count_succ]
  rw [show 4108 = 4107 + 1 by norm_num, Nat.count_succ]
  rw [show 4107 = 4106 + 1 by norm_num, Nat.count_succ]
  rw [show 4106 = 4105 + 1 by norm_num, Nat.count_succ]
  rw [show 4105 = 4104 + 1 by norm_num, Nat.count_succ]
  rw [show 4104 = 4103 + 1 by norm_num, Nat.count_succ]
  rw [show 4103 = 4102 + 1 by norm_num, Nat.count_succ]
  rw [show 4102 = 4101 + 1 by norm_num, Nat.count_succ]
  rw [show 4101 = 4100 + 1 by norm_num, Nat.count_succ]
  rw [show 4100 = 4099 + 1 by norm_num, Nat.count_succ]
  rw [count_4099]
  simp [prime_4099, not_prime_4100, not_prime_4101, not_prime_4102, not_prime_4103, not_prime_4104, not_prime_4105, not_prime_4106, not_prime_4107, not_prime_4108, not_prime_4109, not_prime_4110]

theorem prime_4111 : (4111 : Nat).Prime := by norm_num

theorem nth_565 : Nat.nth Nat.Prime 565 = 4111 := by
  rw [← count_4111]
  exact Nat.nth_count prime_4111

theorem not_prime_4112 : ¬Nat.Prime 4112 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2056) (n := 4112)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4113 : ¬Nat.Prime 4113 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1371) (n := 4113)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4114 : ¬Nat.Prime 4114 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2057) (n := 4114)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4115 : ¬Nat.Prime 4115 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 823) (n := 4115)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4116 : ¬Nat.Prime 4116 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2058) (n := 4116)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4117 : ¬Nat.Prime 4117 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 179) (n := 4117)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4118 : ¬Nat.Prime 4118 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2059) (n := 4118)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4119 : ¬Nat.Prime 4119 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1373) (n := 4119)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4120 : ¬Nat.Prime 4120 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2060) (n := 4120)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4121 : ¬Nat.Prime 4121 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 317) (n := 4121)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4122 : ¬Nat.Prime 4122 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2061) (n := 4122)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4123 : ¬Nat.Prime 4123 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 589) (n := 4123)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4124 : ¬Nat.Prime 4124 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2062) (n := 4124)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4125 : ¬Nat.Prime 4125 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1375) (n := 4125)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4126 : ¬Nat.Prime 4126 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2063) (n := 4126)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4127 : Nat.count Nat.Prime 4127 = 566 := by
  rw [show 4127 = 4126 + 1 by norm_num, Nat.count_succ]
  rw [show 4126 = 4125 + 1 by norm_num, Nat.count_succ]
  rw [show 4125 = 4124 + 1 by norm_num, Nat.count_succ]
  rw [show 4124 = 4123 + 1 by norm_num, Nat.count_succ]
  rw [show 4123 = 4122 + 1 by norm_num, Nat.count_succ]
  rw [show 4122 = 4121 + 1 by norm_num, Nat.count_succ]
  rw [show 4121 = 4120 + 1 by norm_num, Nat.count_succ]
  rw [show 4120 = 4119 + 1 by norm_num, Nat.count_succ]
  rw [show 4119 = 4118 + 1 by norm_num, Nat.count_succ]
  rw [show 4118 = 4117 + 1 by norm_num, Nat.count_succ]
  rw [show 4117 = 4116 + 1 by norm_num, Nat.count_succ]
  rw [show 4116 = 4115 + 1 by norm_num, Nat.count_succ]
  rw [show 4115 = 4114 + 1 by norm_num, Nat.count_succ]
  rw [show 4114 = 4113 + 1 by norm_num, Nat.count_succ]
  rw [show 4113 = 4112 + 1 by norm_num, Nat.count_succ]
  rw [show 4112 = 4111 + 1 by norm_num, Nat.count_succ]
  rw [count_4111]
  simp [prime_4111, not_prime_4112, not_prime_4113, not_prime_4114, not_prime_4115, not_prime_4116, not_prime_4117, not_prime_4118, not_prime_4119, not_prime_4120, not_prime_4121, not_prime_4122, not_prime_4123, not_prime_4124, not_prime_4125, not_prime_4126]

theorem prime_4127 : (4127 : Nat).Prime := by norm_num

theorem nth_566 : Nat.nth Nat.Prime 566 = 4127 := by
  rw [← count_4127]
  exact Nat.nth_count prime_4127

theorem not_prime_4128 : ¬Nat.Prime 4128 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2064) (n := 4128)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4129 : Nat.count Nat.Prime 4129 = 567 := by
  rw [show 4129 = 4128 + 1 by norm_num, Nat.count_succ]
  rw [show 4128 = 4127 + 1 by norm_num, Nat.count_succ]
  rw [count_4127]
  simp [prime_4127, not_prime_4128]

theorem prime_4129 : (4129 : Nat).Prime := by norm_num

theorem nth_567 : Nat.nth Nat.Prime 567 = 4129 := by
  rw [← count_4129]
  exact Nat.nth_count prime_4129

theorem not_prime_4130 : ¬Nat.Prime 4130 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2065) (n := 4130)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4131 : ¬Nat.Prime 4131 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1377) (n := 4131)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4132 : ¬Nat.Prime 4132 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2066) (n := 4132)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4133 : Nat.count Nat.Prime 4133 = 568 := by
  rw [show 4133 = 4132 + 1 by norm_num, Nat.count_succ]
  rw [show 4132 = 4131 + 1 by norm_num, Nat.count_succ]
  rw [show 4131 = 4130 + 1 by norm_num, Nat.count_succ]
  rw [show 4130 = 4129 + 1 by norm_num, Nat.count_succ]
  rw [count_4129]
  simp [prime_4129, not_prime_4130, not_prime_4131, not_prime_4132]

theorem prime_4133 : (4133 : Nat).Prime := by norm_num

theorem nth_568 : Nat.nth Nat.Prime 568 = 4133 := by
  rw [← count_4133]
  exact Nat.nth_count prime_4133

theorem not_prime_4134 : ¬Nat.Prime 4134 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2067) (n := 4134)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4135 : ¬Nat.Prime 4135 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 827) (n := 4135)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4136 : ¬Nat.Prime 4136 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2068) (n := 4136)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4137 : ¬Nat.Prime 4137 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1379) (n := 4137)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4138 : ¬Nat.Prime 4138 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2069) (n := 4138)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4139 : Nat.count Nat.Prime 4139 = 569 := by
  rw [show 4139 = 4138 + 1 by norm_num, Nat.count_succ]
  rw [show 4138 = 4137 + 1 by norm_num, Nat.count_succ]
  rw [show 4137 = 4136 + 1 by norm_num, Nat.count_succ]
  rw [show 4136 = 4135 + 1 by norm_num, Nat.count_succ]
  rw [show 4135 = 4134 + 1 by norm_num, Nat.count_succ]
  rw [show 4134 = 4133 + 1 by norm_num, Nat.count_succ]
  rw [count_4133]
  simp [prime_4133, not_prime_4134, not_prime_4135, not_prime_4136, not_prime_4137, not_prime_4138]

theorem prime_4139 : (4139 : Nat).Prime := by norm_num

theorem nth_569 : Nat.nth Nat.Prime 569 = 4139 := by
  rw [← count_4139]
  exact Nat.nth_count prime_4139

theorem not_prime_4140 : ¬Nat.Prime 4140 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2070) (n := 4140)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4141 : ¬Nat.Prime 4141 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 101) (n := 4141)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4142 : ¬Nat.Prime 4142 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2071) (n := 4142)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4143 : ¬Nat.Prime 4143 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1381) (n := 4143)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4144 : ¬Nat.Prime 4144 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2072) (n := 4144)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4145 : ¬Nat.Prime 4145 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 829) (n := 4145)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4146 : ¬Nat.Prime 4146 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2073) (n := 4146)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4147 : ¬Nat.Prime 4147 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 377) (n := 4147)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4148 : ¬Nat.Prime 4148 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2074) (n := 4148)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4149 : ¬Nat.Prime 4149 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1383) (n := 4149)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4150 : ¬Nat.Prime 4150 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2075) (n := 4150)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4151 : ¬Nat.Prime 4151 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 593) (n := 4151)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4152 : ¬Nat.Prime 4152 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2076) (n := 4152)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4153 : Nat.count Nat.Prime 4153 = 570 := by
  rw [show 4153 = 4152 + 1 by norm_num, Nat.count_succ]
  rw [show 4152 = 4151 + 1 by norm_num, Nat.count_succ]
  rw [show 4151 = 4150 + 1 by norm_num, Nat.count_succ]
  rw [show 4150 = 4149 + 1 by norm_num, Nat.count_succ]
  rw [show 4149 = 4148 + 1 by norm_num, Nat.count_succ]
  rw [show 4148 = 4147 + 1 by norm_num, Nat.count_succ]
  rw [show 4147 = 4146 + 1 by norm_num, Nat.count_succ]
  rw [show 4146 = 4145 + 1 by norm_num, Nat.count_succ]
  rw [show 4145 = 4144 + 1 by norm_num, Nat.count_succ]
  rw [show 4144 = 4143 + 1 by norm_num, Nat.count_succ]
  rw [show 4143 = 4142 + 1 by norm_num, Nat.count_succ]
  rw [show 4142 = 4141 + 1 by norm_num, Nat.count_succ]
  rw [show 4141 = 4140 + 1 by norm_num, Nat.count_succ]
  rw [show 4140 = 4139 + 1 by norm_num, Nat.count_succ]
  rw [count_4139]
  simp [prime_4139, not_prime_4140, not_prime_4141, not_prime_4142, not_prime_4143, not_prime_4144, not_prime_4145, not_prime_4146, not_prime_4147, not_prime_4148, not_prime_4149, not_prime_4150, not_prime_4151, not_prime_4152]

theorem prime_4153 : (4153 : Nat).Prime := by norm_num

theorem nth_570 : Nat.nth Nat.Prime 570 = 4153 := by
  rw [← count_4153]
  exact Nat.nth_count prime_4153

theorem not_prime_4154 : ¬Nat.Prime 4154 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2077) (n := 4154)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4155 : ¬Nat.Prime 4155 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1385) (n := 4155)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4156 : ¬Nat.Prime 4156 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2078) (n := 4156)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4157 : Nat.count Nat.Prime 4157 = 571 := by
  rw [show 4157 = 4156 + 1 by norm_num, Nat.count_succ]
  rw [show 4156 = 4155 + 1 by norm_num, Nat.count_succ]
  rw [show 4155 = 4154 + 1 by norm_num, Nat.count_succ]
  rw [show 4154 = 4153 + 1 by norm_num, Nat.count_succ]
  rw [count_4153]
  simp [prime_4153, not_prime_4154, not_prime_4155, not_prime_4156]

theorem prime_4157 : (4157 : Nat).Prime := by norm_num

theorem nth_571 : Nat.nth Nat.Prime 571 = 4157 := by
  rw [← count_4157]
  exact Nat.nth_count prime_4157

theorem not_prime_4158 : ¬Nat.Prime 4158 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2079) (n := 4158)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4159 : Nat.count Nat.Prime 4159 = 572 := by
  rw [show 4159 = 4158 + 1 by norm_num, Nat.count_succ]
  rw [show 4158 = 4157 + 1 by norm_num, Nat.count_succ]
  rw [count_4157]
  simp [prime_4157, not_prime_4158]

theorem prime_4159 : (4159 : Nat).Prime := by norm_num

theorem nth_572 : Nat.nth Nat.Prime 572 = 4159 := by
  rw [← count_4159]
  exact Nat.nth_count prime_4159

theorem not_prime_4160 : ¬Nat.Prime 4160 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2080) (n := 4160)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4161 : ¬Nat.Prime 4161 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1387) (n := 4161)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4162 : ¬Nat.Prime 4162 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2081) (n := 4162)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4163 : ¬Nat.Prime 4163 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 181) (n := 4163)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4164 : ¬Nat.Prime 4164 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2082) (n := 4164)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4165 : ¬Nat.Prime 4165 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 833) (n := 4165)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4166 : ¬Nat.Prime 4166 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2083) (n := 4166)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4167 : ¬Nat.Prime 4167 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1389) (n := 4167)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4168 : ¬Nat.Prime 4168 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2084) (n := 4168)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4169 : ¬Nat.Prime 4169 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 379) (n := 4169)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4170 : ¬Nat.Prime 4170 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2085) (n := 4170)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4171 : ¬Nat.Prime 4171 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 97) (n := 4171)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4172 : ¬Nat.Prime 4172 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2086) (n := 4172)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4173 : ¬Nat.Prime 4173 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1391) (n := 4173)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4174 : ¬Nat.Prime 4174 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2087) (n := 4174)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4175 : ¬Nat.Prime 4175 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 835) (n := 4175)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4176 : ¬Nat.Prime 4176 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2088) (n := 4176)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4177 : Nat.count Nat.Prime 4177 = 573 := by
  rw [show 4177 = 4176 + 1 by norm_num, Nat.count_succ]
  rw [show 4176 = 4175 + 1 by norm_num, Nat.count_succ]
  rw [show 4175 = 4174 + 1 by norm_num, Nat.count_succ]
  rw [show 4174 = 4173 + 1 by norm_num, Nat.count_succ]
  rw [show 4173 = 4172 + 1 by norm_num, Nat.count_succ]
  rw [show 4172 = 4171 + 1 by norm_num, Nat.count_succ]
  rw [show 4171 = 4170 + 1 by norm_num, Nat.count_succ]
  rw [show 4170 = 4169 + 1 by norm_num, Nat.count_succ]
  rw [show 4169 = 4168 + 1 by norm_num, Nat.count_succ]
  rw [show 4168 = 4167 + 1 by norm_num, Nat.count_succ]
  rw [show 4167 = 4166 + 1 by norm_num, Nat.count_succ]
  rw [show 4166 = 4165 + 1 by norm_num, Nat.count_succ]
  rw [show 4165 = 4164 + 1 by norm_num, Nat.count_succ]
  rw [show 4164 = 4163 + 1 by norm_num, Nat.count_succ]
  rw [show 4163 = 4162 + 1 by norm_num, Nat.count_succ]
  rw [show 4162 = 4161 + 1 by norm_num, Nat.count_succ]
  rw [show 4161 = 4160 + 1 by norm_num, Nat.count_succ]
  rw [show 4160 = 4159 + 1 by norm_num, Nat.count_succ]
  rw [count_4159]
  simp [prime_4159, not_prime_4160, not_prime_4161, not_prime_4162, not_prime_4163, not_prime_4164, not_prime_4165, not_prime_4166, not_prime_4167, not_prime_4168, not_prime_4169, not_prime_4170, not_prime_4171, not_prime_4172, not_prime_4173, not_prime_4174, not_prime_4175, not_prime_4176]

theorem prime_4177 : (4177 : Nat).Prime := by norm_num

theorem nth_573 : Nat.nth Nat.Prime 573 = 4177 := by
  rw [← count_4177]
  exact Nat.nth_count prime_4177

theorem not_prime_4178 : ¬Nat.Prime 4178 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2089) (n := 4178)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4179 : ¬Nat.Prime 4179 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1393) (n := 4179)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4180 : ¬Nat.Prime 4180 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2090) (n := 4180)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4181 : ¬Nat.Prime 4181 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 113) (n := 4181)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4182 : ¬Nat.Prime 4182 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2091) (n := 4182)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4183 : ¬Nat.Prime 4183 :=
  Nat.not_prime_of_mul_eq (a := 47) (b := 89) (n := 4183)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4184 : ¬Nat.Prime 4184 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2092) (n := 4184)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4185 : ¬Nat.Prime 4185 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1395) (n := 4185)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4186 : ¬Nat.Prime 4186 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2093) (n := 4186)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4187 : ¬Nat.Prime 4187 :=
  Nat.not_prime_of_mul_eq (a := 53) (b := 79) (n := 4187)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4188 : ¬Nat.Prime 4188 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2094) (n := 4188)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4189 : ¬Nat.Prime 4189 :=
  Nat.not_prime_of_mul_eq (a := 59) (b := 71) (n := 4189)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4190 : ¬Nat.Prime 4190 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2095) (n := 4190)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4191 : ¬Nat.Prime 4191 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1397) (n := 4191)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4192 : ¬Nat.Prime 4192 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2096) (n := 4192)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4193 : ¬Nat.Prime 4193 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 599) (n := 4193)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4194 : ¬Nat.Prime 4194 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2097) (n := 4194)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4195 : ¬Nat.Prime 4195 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 839) (n := 4195)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4196 : ¬Nat.Prime 4196 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2098) (n := 4196)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4197 : ¬Nat.Prime 4197 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1399) (n := 4197)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4198 : ¬Nat.Prime 4198 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2099) (n := 4198)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4199 : ¬Nat.Prime 4199 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 323) (n := 4199)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4200 : ¬Nat.Prime 4200 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2100) (n := 4200)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4201 : Nat.count Nat.Prime 4201 = 574 := by
  rw [show 4201 = 4200 + 1 by norm_num, Nat.count_succ]
  rw [show 4200 = 4199 + 1 by norm_num, Nat.count_succ]
  rw [show 4199 = 4198 + 1 by norm_num, Nat.count_succ]
  rw [show 4198 = 4197 + 1 by norm_num, Nat.count_succ]
  rw [show 4197 = 4196 + 1 by norm_num, Nat.count_succ]
  rw [show 4196 = 4195 + 1 by norm_num, Nat.count_succ]
  rw [show 4195 = 4194 + 1 by norm_num, Nat.count_succ]
  rw [show 4194 = 4193 + 1 by norm_num, Nat.count_succ]
  rw [show 4193 = 4192 + 1 by norm_num, Nat.count_succ]
  rw [show 4192 = 4191 + 1 by norm_num, Nat.count_succ]
  rw [show 4191 = 4190 + 1 by norm_num, Nat.count_succ]
  rw [show 4190 = 4189 + 1 by norm_num, Nat.count_succ]
  rw [show 4189 = 4188 + 1 by norm_num, Nat.count_succ]
  rw [show 4188 = 4187 + 1 by norm_num, Nat.count_succ]
  rw [show 4187 = 4186 + 1 by norm_num, Nat.count_succ]
  rw [show 4186 = 4185 + 1 by norm_num, Nat.count_succ]
  rw [show 4185 = 4184 + 1 by norm_num, Nat.count_succ]
  rw [show 4184 = 4183 + 1 by norm_num, Nat.count_succ]
  rw [show 4183 = 4182 + 1 by norm_num, Nat.count_succ]
  rw [show 4182 = 4181 + 1 by norm_num, Nat.count_succ]
  rw [show 4181 = 4180 + 1 by norm_num, Nat.count_succ]
  rw [show 4180 = 4179 + 1 by norm_num, Nat.count_succ]
  rw [show 4179 = 4178 + 1 by norm_num, Nat.count_succ]
  rw [show 4178 = 4177 + 1 by norm_num, Nat.count_succ]
  rw [count_4177]
  simp [prime_4177, not_prime_4178, not_prime_4179, not_prime_4180, not_prime_4181, not_prime_4182, not_prime_4183, not_prime_4184, not_prime_4185, not_prime_4186, not_prime_4187, not_prime_4188, not_prime_4189, not_prime_4190, not_prime_4191, not_prime_4192, not_prime_4193, not_prime_4194, not_prime_4195, not_prime_4196, not_prime_4197, not_prime_4198, not_prime_4199, not_prime_4200]

theorem prime_4201 : (4201 : Nat).Prime := by norm_num

theorem nth_574 : Nat.nth Nat.Prime 574 = 4201 := by
  rw [← count_4201]
  exact Nat.nth_count prime_4201

end OeisA100474.PrimeCertificate
