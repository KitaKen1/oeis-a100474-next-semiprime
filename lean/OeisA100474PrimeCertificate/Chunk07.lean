import OeisA100474PrimeCertificate.Chunk06

/-! Kernel prime/count certificate, chunk 07 (175–199). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_1040 : ¬Nat.Prime 1040 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 520) (n := 1040)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1041 : ¬Nat.Prime 1041 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 347) (n := 1041)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1042 : ¬Nat.Prime 1042 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 521) (n := 1042)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1043 : ¬Nat.Prime 1043 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 149) (n := 1043)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1044 : ¬Nat.Prime 1044 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 522) (n := 1044)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1045 : ¬Nat.Prime 1045 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 209) (n := 1045)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1046 : ¬Nat.Prime 1046 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 523) (n := 1046)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1047 : ¬Nat.Prime 1047 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 349) (n := 1047)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1048 : ¬Nat.Prime 1048 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 524) (n := 1048)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1049 : Nat.count Nat.Prime 1049 = 175 := by
  rw [show 1049 = 1048 + 1 by norm_num, Nat.count_succ]
  rw [show 1048 = 1047 + 1 by norm_num, Nat.count_succ]
  rw [show 1047 = 1046 + 1 by norm_num, Nat.count_succ]
  rw [show 1046 = 1045 + 1 by norm_num, Nat.count_succ]
  rw [show 1045 = 1044 + 1 by norm_num, Nat.count_succ]
  rw [show 1044 = 1043 + 1 by norm_num, Nat.count_succ]
  rw [show 1043 = 1042 + 1 by norm_num, Nat.count_succ]
  rw [show 1042 = 1041 + 1 by norm_num, Nat.count_succ]
  rw [show 1041 = 1040 + 1 by norm_num, Nat.count_succ]
  rw [show 1040 = 1039 + 1 by norm_num, Nat.count_succ]
  rw [count_1039]
  simp [prime_1039, not_prime_1040, not_prime_1041, not_prime_1042, not_prime_1043, not_prime_1044, not_prime_1045, not_prime_1046, not_prime_1047, not_prime_1048]

theorem prime_1049 : (1049 : Nat).Prime := by norm_num

theorem nth_175 : Nat.nth Nat.Prime 175 = 1049 := by
  rw [← count_1049]
  exact Nat.nth_count prime_1049

theorem not_prime_1050 : ¬Nat.Prime 1050 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 525) (n := 1050)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1051 : Nat.count Nat.Prime 1051 = 176 := by
  rw [show 1051 = 1050 + 1 by norm_num, Nat.count_succ]
  rw [show 1050 = 1049 + 1 by norm_num, Nat.count_succ]
  rw [count_1049]
  simp [prime_1049, not_prime_1050]

theorem prime_1051 : (1051 : Nat).Prime := by norm_num

theorem nth_176 : Nat.nth Nat.Prime 176 = 1051 := by
  rw [← count_1051]
  exact Nat.nth_count prime_1051

theorem not_prime_1052 : ¬Nat.Prime 1052 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 526) (n := 1052)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1053 : ¬Nat.Prime 1053 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 351) (n := 1053)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1054 : ¬Nat.Prime 1054 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 527) (n := 1054)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1055 : ¬Nat.Prime 1055 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 211) (n := 1055)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1056 : ¬Nat.Prime 1056 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 528) (n := 1056)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1057 : ¬Nat.Prime 1057 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 151) (n := 1057)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1058 : ¬Nat.Prime 1058 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 529) (n := 1058)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1059 : ¬Nat.Prime 1059 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 353) (n := 1059)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1060 : ¬Nat.Prime 1060 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 530) (n := 1060)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1061 : Nat.count Nat.Prime 1061 = 177 := by
  rw [show 1061 = 1060 + 1 by norm_num, Nat.count_succ]
  rw [show 1060 = 1059 + 1 by norm_num, Nat.count_succ]
  rw [show 1059 = 1058 + 1 by norm_num, Nat.count_succ]
  rw [show 1058 = 1057 + 1 by norm_num, Nat.count_succ]
  rw [show 1057 = 1056 + 1 by norm_num, Nat.count_succ]
  rw [show 1056 = 1055 + 1 by norm_num, Nat.count_succ]
  rw [show 1055 = 1054 + 1 by norm_num, Nat.count_succ]
  rw [show 1054 = 1053 + 1 by norm_num, Nat.count_succ]
  rw [show 1053 = 1052 + 1 by norm_num, Nat.count_succ]
  rw [show 1052 = 1051 + 1 by norm_num, Nat.count_succ]
  rw [count_1051]
  simp [prime_1051, not_prime_1052, not_prime_1053, not_prime_1054, not_prime_1055, not_prime_1056, not_prime_1057, not_prime_1058, not_prime_1059, not_prime_1060]

theorem prime_1061 : (1061 : Nat).Prime := by norm_num

theorem nth_177 : Nat.nth Nat.Prime 177 = 1061 := by
  rw [← count_1061]
  exact Nat.nth_count prime_1061

theorem not_prime_1062 : ¬Nat.Prime 1062 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 531) (n := 1062)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1063 : Nat.count Nat.Prime 1063 = 178 := by
  rw [show 1063 = 1062 + 1 by norm_num, Nat.count_succ]
  rw [show 1062 = 1061 + 1 by norm_num, Nat.count_succ]
  rw [count_1061]
  simp [prime_1061, not_prime_1062]

theorem prime_1063 : (1063 : Nat).Prime := by norm_num

theorem nth_178 : Nat.nth Nat.Prime 178 = 1063 := by
  rw [← count_1063]
  exact Nat.nth_count prime_1063

theorem not_prime_1064 : ¬Nat.Prime 1064 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 532) (n := 1064)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1065 : ¬Nat.Prime 1065 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 355) (n := 1065)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1066 : ¬Nat.Prime 1066 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 533) (n := 1066)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1067 : ¬Nat.Prime 1067 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 97) (n := 1067)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1068 : ¬Nat.Prime 1068 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 534) (n := 1068)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1069 : Nat.count Nat.Prime 1069 = 179 := by
  rw [show 1069 = 1068 + 1 by norm_num, Nat.count_succ]
  rw [show 1068 = 1067 + 1 by norm_num, Nat.count_succ]
  rw [show 1067 = 1066 + 1 by norm_num, Nat.count_succ]
  rw [show 1066 = 1065 + 1 by norm_num, Nat.count_succ]
  rw [show 1065 = 1064 + 1 by norm_num, Nat.count_succ]
  rw [show 1064 = 1063 + 1 by norm_num, Nat.count_succ]
  rw [count_1063]
  simp [prime_1063, not_prime_1064, not_prime_1065, not_prime_1066, not_prime_1067, not_prime_1068]

theorem prime_1069 : (1069 : Nat).Prime := by norm_num

theorem nth_179 : Nat.nth Nat.Prime 179 = 1069 := by
  rw [← count_1069]
  exact Nat.nth_count prime_1069

theorem not_prime_1070 : ¬Nat.Prime 1070 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 535) (n := 1070)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1071 : ¬Nat.Prime 1071 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 357) (n := 1071)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1072 : ¬Nat.Prime 1072 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 536) (n := 1072)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1073 : ¬Nat.Prime 1073 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 37) (n := 1073)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1074 : ¬Nat.Prime 1074 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 537) (n := 1074)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1075 : ¬Nat.Prime 1075 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 215) (n := 1075)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1076 : ¬Nat.Prime 1076 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 538) (n := 1076)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1077 : ¬Nat.Prime 1077 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 359) (n := 1077)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1078 : ¬Nat.Prime 1078 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 539) (n := 1078)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1079 : ¬Nat.Prime 1079 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 83) (n := 1079)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1080 : ¬Nat.Prime 1080 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 540) (n := 1080)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1081 : ¬Nat.Prime 1081 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 47) (n := 1081)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1082 : ¬Nat.Prime 1082 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 541) (n := 1082)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1083 : ¬Nat.Prime 1083 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 361) (n := 1083)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1084 : ¬Nat.Prime 1084 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 542) (n := 1084)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1085 : ¬Nat.Prime 1085 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 217) (n := 1085)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1086 : ¬Nat.Prime 1086 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 543) (n := 1086)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1087 : Nat.count Nat.Prime 1087 = 180 := by
  rw [show 1087 = 1086 + 1 by norm_num, Nat.count_succ]
  rw [show 1086 = 1085 + 1 by norm_num, Nat.count_succ]
  rw [show 1085 = 1084 + 1 by norm_num, Nat.count_succ]
  rw [show 1084 = 1083 + 1 by norm_num, Nat.count_succ]
  rw [show 1083 = 1082 + 1 by norm_num, Nat.count_succ]
  rw [show 1082 = 1081 + 1 by norm_num, Nat.count_succ]
  rw [show 1081 = 1080 + 1 by norm_num, Nat.count_succ]
  rw [show 1080 = 1079 + 1 by norm_num, Nat.count_succ]
  rw [show 1079 = 1078 + 1 by norm_num, Nat.count_succ]
  rw [show 1078 = 1077 + 1 by norm_num, Nat.count_succ]
  rw [show 1077 = 1076 + 1 by norm_num, Nat.count_succ]
  rw [show 1076 = 1075 + 1 by norm_num, Nat.count_succ]
  rw [show 1075 = 1074 + 1 by norm_num, Nat.count_succ]
  rw [show 1074 = 1073 + 1 by norm_num, Nat.count_succ]
  rw [show 1073 = 1072 + 1 by norm_num, Nat.count_succ]
  rw [show 1072 = 1071 + 1 by norm_num, Nat.count_succ]
  rw [show 1071 = 1070 + 1 by norm_num, Nat.count_succ]
  rw [show 1070 = 1069 + 1 by norm_num, Nat.count_succ]
  rw [count_1069]
  simp [prime_1069, not_prime_1070, not_prime_1071, not_prime_1072, not_prime_1073, not_prime_1074, not_prime_1075, not_prime_1076, not_prime_1077, not_prime_1078, not_prime_1079, not_prime_1080, not_prime_1081, not_prime_1082, not_prime_1083, not_prime_1084, not_prime_1085, not_prime_1086]

theorem prime_1087 : (1087 : Nat).Prime := by norm_num

theorem nth_180 : Nat.nth Nat.Prime 180 = 1087 := by
  rw [← count_1087]
  exact Nat.nth_count prime_1087

theorem not_prime_1088 : ¬Nat.Prime 1088 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 544) (n := 1088)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1089 : ¬Nat.Prime 1089 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 363) (n := 1089)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1090 : ¬Nat.Prime 1090 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 545) (n := 1090)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1091 : Nat.count Nat.Prime 1091 = 181 := by
  rw [show 1091 = 1090 + 1 by norm_num, Nat.count_succ]
  rw [show 1090 = 1089 + 1 by norm_num, Nat.count_succ]
  rw [show 1089 = 1088 + 1 by norm_num, Nat.count_succ]
  rw [show 1088 = 1087 + 1 by norm_num, Nat.count_succ]
  rw [count_1087]
  simp [prime_1087, not_prime_1088, not_prime_1089, not_prime_1090]

theorem prime_1091 : (1091 : Nat).Prime := by norm_num

theorem nth_181 : Nat.nth Nat.Prime 181 = 1091 := by
  rw [← count_1091]
  exact Nat.nth_count prime_1091

theorem not_prime_1092 : ¬Nat.Prime 1092 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 546) (n := 1092)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1093 : Nat.count Nat.Prime 1093 = 182 := by
  rw [show 1093 = 1092 + 1 by norm_num, Nat.count_succ]
  rw [show 1092 = 1091 + 1 by norm_num, Nat.count_succ]
  rw [count_1091]
  simp [prime_1091, not_prime_1092]

theorem prime_1093 : (1093 : Nat).Prime := by norm_num

theorem nth_182 : Nat.nth Nat.Prime 182 = 1093 := by
  rw [← count_1093]
  exact Nat.nth_count prime_1093

theorem not_prime_1094 : ¬Nat.Prime 1094 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 547) (n := 1094)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1095 : ¬Nat.Prime 1095 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 365) (n := 1095)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1096 : ¬Nat.Prime 1096 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 548) (n := 1096)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1097 : Nat.count Nat.Prime 1097 = 183 := by
  rw [show 1097 = 1096 + 1 by norm_num, Nat.count_succ]
  rw [show 1096 = 1095 + 1 by norm_num, Nat.count_succ]
  rw [show 1095 = 1094 + 1 by norm_num, Nat.count_succ]
  rw [show 1094 = 1093 + 1 by norm_num, Nat.count_succ]
  rw [count_1093]
  simp [prime_1093, not_prime_1094, not_prime_1095, not_prime_1096]

theorem prime_1097 : (1097 : Nat).Prime := by norm_num

theorem nth_183 : Nat.nth Nat.Prime 183 = 1097 := by
  rw [← count_1097]
  exact Nat.nth_count prime_1097

theorem not_prime_1098 : ¬Nat.Prime 1098 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 549) (n := 1098)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1099 : ¬Nat.Prime 1099 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 157) (n := 1099)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1100 : ¬Nat.Prime 1100 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 550) (n := 1100)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1101 : ¬Nat.Prime 1101 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 367) (n := 1101)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1102 : ¬Nat.Prime 1102 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 551) (n := 1102)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1103 : Nat.count Nat.Prime 1103 = 184 := by
  rw [show 1103 = 1102 + 1 by norm_num, Nat.count_succ]
  rw [show 1102 = 1101 + 1 by norm_num, Nat.count_succ]
  rw [show 1101 = 1100 + 1 by norm_num, Nat.count_succ]
  rw [show 1100 = 1099 + 1 by norm_num, Nat.count_succ]
  rw [show 1099 = 1098 + 1 by norm_num, Nat.count_succ]
  rw [show 1098 = 1097 + 1 by norm_num, Nat.count_succ]
  rw [count_1097]
  simp [prime_1097, not_prime_1098, not_prime_1099, not_prime_1100, not_prime_1101, not_prime_1102]

theorem prime_1103 : (1103 : Nat).Prime := by norm_num

theorem nth_184 : Nat.nth Nat.Prime 184 = 1103 := by
  rw [← count_1103]
  exact Nat.nth_count prime_1103

theorem not_prime_1104 : ¬Nat.Prime 1104 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 552) (n := 1104)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1105 : ¬Nat.Prime 1105 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 221) (n := 1105)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1106 : ¬Nat.Prime 1106 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 553) (n := 1106)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1107 : ¬Nat.Prime 1107 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 369) (n := 1107)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1108 : ¬Nat.Prime 1108 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 554) (n := 1108)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1109 : Nat.count Nat.Prime 1109 = 185 := by
  rw [show 1109 = 1108 + 1 by norm_num, Nat.count_succ]
  rw [show 1108 = 1107 + 1 by norm_num, Nat.count_succ]
  rw [show 1107 = 1106 + 1 by norm_num, Nat.count_succ]
  rw [show 1106 = 1105 + 1 by norm_num, Nat.count_succ]
  rw [show 1105 = 1104 + 1 by norm_num, Nat.count_succ]
  rw [show 1104 = 1103 + 1 by norm_num, Nat.count_succ]
  rw [count_1103]
  simp [prime_1103, not_prime_1104, not_prime_1105, not_prime_1106, not_prime_1107, not_prime_1108]

theorem prime_1109 : (1109 : Nat).Prime := by norm_num

theorem nth_185 : Nat.nth Nat.Prime 185 = 1109 := by
  rw [← count_1109]
  exact Nat.nth_count prime_1109

theorem not_prime_1110 : ¬Nat.Prime 1110 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 555) (n := 1110)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1111 : ¬Nat.Prime 1111 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 101) (n := 1111)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1112 : ¬Nat.Prime 1112 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 556) (n := 1112)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1113 : ¬Nat.Prime 1113 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 371) (n := 1113)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1114 : ¬Nat.Prime 1114 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 557) (n := 1114)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1115 : ¬Nat.Prime 1115 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 223) (n := 1115)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1116 : ¬Nat.Prime 1116 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 558) (n := 1116)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1117 : Nat.count Nat.Prime 1117 = 186 := by
  rw [show 1117 = 1116 + 1 by norm_num, Nat.count_succ]
  rw [show 1116 = 1115 + 1 by norm_num, Nat.count_succ]
  rw [show 1115 = 1114 + 1 by norm_num, Nat.count_succ]
  rw [show 1114 = 1113 + 1 by norm_num, Nat.count_succ]
  rw [show 1113 = 1112 + 1 by norm_num, Nat.count_succ]
  rw [show 1112 = 1111 + 1 by norm_num, Nat.count_succ]
  rw [show 1111 = 1110 + 1 by norm_num, Nat.count_succ]
  rw [show 1110 = 1109 + 1 by norm_num, Nat.count_succ]
  rw [count_1109]
  simp [prime_1109, not_prime_1110, not_prime_1111, not_prime_1112, not_prime_1113, not_prime_1114, not_prime_1115, not_prime_1116]

theorem prime_1117 : (1117 : Nat).Prime := by norm_num

theorem nth_186 : Nat.nth Nat.Prime 186 = 1117 := by
  rw [← count_1117]
  exact Nat.nth_count prime_1117

theorem not_prime_1118 : ¬Nat.Prime 1118 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 559) (n := 1118)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1119 : ¬Nat.Prime 1119 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 373) (n := 1119)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1120 : ¬Nat.Prime 1120 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 560) (n := 1120)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1121 : ¬Nat.Prime 1121 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 59) (n := 1121)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1122 : ¬Nat.Prime 1122 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 561) (n := 1122)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1123 : Nat.count Nat.Prime 1123 = 187 := by
  rw [show 1123 = 1122 + 1 by norm_num, Nat.count_succ]
  rw [show 1122 = 1121 + 1 by norm_num, Nat.count_succ]
  rw [show 1121 = 1120 + 1 by norm_num, Nat.count_succ]
  rw [show 1120 = 1119 + 1 by norm_num, Nat.count_succ]
  rw [show 1119 = 1118 + 1 by norm_num, Nat.count_succ]
  rw [show 1118 = 1117 + 1 by norm_num, Nat.count_succ]
  rw [count_1117]
  simp [prime_1117, not_prime_1118, not_prime_1119, not_prime_1120, not_prime_1121, not_prime_1122]

theorem prime_1123 : (1123 : Nat).Prime := by norm_num

theorem nth_187 : Nat.nth Nat.Prime 187 = 1123 := by
  rw [← count_1123]
  exact Nat.nth_count prime_1123

theorem not_prime_1124 : ¬Nat.Prime 1124 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 562) (n := 1124)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1125 : ¬Nat.Prime 1125 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 375) (n := 1125)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1126 : ¬Nat.Prime 1126 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 563) (n := 1126)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1127 : ¬Nat.Prime 1127 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 161) (n := 1127)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1128 : ¬Nat.Prime 1128 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 564) (n := 1128)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1129 : Nat.count Nat.Prime 1129 = 188 := by
  rw [show 1129 = 1128 + 1 by norm_num, Nat.count_succ]
  rw [show 1128 = 1127 + 1 by norm_num, Nat.count_succ]
  rw [show 1127 = 1126 + 1 by norm_num, Nat.count_succ]
  rw [show 1126 = 1125 + 1 by norm_num, Nat.count_succ]
  rw [show 1125 = 1124 + 1 by norm_num, Nat.count_succ]
  rw [show 1124 = 1123 + 1 by norm_num, Nat.count_succ]
  rw [count_1123]
  simp [prime_1123, not_prime_1124, not_prime_1125, not_prime_1126, not_prime_1127, not_prime_1128]

theorem prime_1129 : (1129 : Nat).Prime := by norm_num

theorem nth_188 : Nat.nth Nat.Prime 188 = 1129 := by
  rw [← count_1129]
  exact Nat.nth_count prime_1129

theorem not_prime_1130 : ¬Nat.Prime 1130 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 565) (n := 1130)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1131 : ¬Nat.Prime 1131 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 377) (n := 1131)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1132 : ¬Nat.Prime 1132 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 566) (n := 1132)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1133 : ¬Nat.Prime 1133 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 103) (n := 1133)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1134 : ¬Nat.Prime 1134 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 567) (n := 1134)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1135 : ¬Nat.Prime 1135 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 227) (n := 1135)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1136 : ¬Nat.Prime 1136 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 568) (n := 1136)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1137 : ¬Nat.Prime 1137 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 379) (n := 1137)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1138 : ¬Nat.Prime 1138 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 569) (n := 1138)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1139 : ¬Nat.Prime 1139 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 67) (n := 1139)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1140 : ¬Nat.Prime 1140 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 570) (n := 1140)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1141 : ¬Nat.Prime 1141 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 163) (n := 1141)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1142 : ¬Nat.Prime 1142 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 571) (n := 1142)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1143 : ¬Nat.Prime 1143 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 381) (n := 1143)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1144 : ¬Nat.Prime 1144 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 572) (n := 1144)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1145 : ¬Nat.Prime 1145 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 229) (n := 1145)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1146 : ¬Nat.Prime 1146 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 573) (n := 1146)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1147 : ¬Nat.Prime 1147 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 37) (n := 1147)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1148 : ¬Nat.Prime 1148 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 574) (n := 1148)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1149 : ¬Nat.Prime 1149 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 383) (n := 1149)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1150 : ¬Nat.Prime 1150 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 575) (n := 1150)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1151 : Nat.count Nat.Prime 1151 = 189 := by
  rw [show 1151 = 1150 + 1 by norm_num, Nat.count_succ]
  rw [show 1150 = 1149 + 1 by norm_num, Nat.count_succ]
  rw [show 1149 = 1148 + 1 by norm_num, Nat.count_succ]
  rw [show 1148 = 1147 + 1 by norm_num, Nat.count_succ]
  rw [show 1147 = 1146 + 1 by norm_num, Nat.count_succ]
  rw [show 1146 = 1145 + 1 by norm_num, Nat.count_succ]
  rw [show 1145 = 1144 + 1 by norm_num, Nat.count_succ]
  rw [show 1144 = 1143 + 1 by norm_num, Nat.count_succ]
  rw [show 1143 = 1142 + 1 by norm_num, Nat.count_succ]
  rw [show 1142 = 1141 + 1 by norm_num, Nat.count_succ]
  rw [show 1141 = 1140 + 1 by norm_num, Nat.count_succ]
  rw [show 1140 = 1139 + 1 by norm_num, Nat.count_succ]
  rw [show 1139 = 1138 + 1 by norm_num, Nat.count_succ]
  rw [show 1138 = 1137 + 1 by norm_num, Nat.count_succ]
  rw [show 1137 = 1136 + 1 by norm_num, Nat.count_succ]
  rw [show 1136 = 1135 + 1 by norm_num, Nat.count_succ]
  rw [show 1135 = 1134 + 1 by norm_num, Nat.count_succ]
  rw [show 1134 = 1133 + 1 by norm_num, Nat.count_succ]
  rw [show 1133 = 1132 + 1 by norm_num, Nat.count_succ]
  rw [show 1132 = 1131 + 1 by norm_num, Nat.count_succ]
  rw [show 1131 = 1130 + 1 by norm_num, Nat.count_succ]
  rw [show 1130 = 1129 + 1 by norm_num, Nat.count_succ]
  rw [count_1129]
  simp [prime_1129, not_prime_1130, not_prime_1131, not_prime_1132, not_prime_1133, not_prime_1134, not_prime_1135, not_prime_1136, not_prime_1137, not_prime_1138, not_prime_1139, not_prime_1140, not_prime_1141, not_prime_1142, not_prime_1143, not_prime_1144, not_prime_1145, not_prime_1146, not_prime_1147, not_prime_1148, not_prime_1149, not_prime_1150]

theorem prime_1151 : (1151 : Nat).Prime := by norm_num

theorem nth_189 : Nat.nth Nat.Prime 189 = 1151 := by
  rw [← count_1151]
  exact Nat.nth_count prime_1151

theorem not_prime_1152 : ¬Nat.Prime 1152 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 576) (n := 1152)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1153 : Nat.count Nat.Prime 1153 = 190 := by
  rw [show 1153 = 1152 + 1 by norm_num, Nat.count_succ]
  rw [show 1152 = 1151 + 1 by norm_num, Nat.count_succ]
  rw [count_1151]
  simp [prime_1151, not_prime_1152]

theorem prime_1153 : (1153 : Nat).Prime := by norm_num

theorem nth_190 : Nat.nth Nat.Prime 190 = 1153 := by
  rw [← count_1153]
  exact Nat.nth_count prime_1153

theorem not_prime_1154 : ¬Nat.Prime 1154 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 577) (n := 1154)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1155 : ¬Nat.Prime 1155 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 385) (n := 1155)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1156 : ¬Nat.Prime 1156 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 578) (n := 1156)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1157 : ¬Nat.Prime 1157 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 89) (n := 1157)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1158 : ¬Nat.Prime 1158 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 579) (n := 1158)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1159 : ¬Nat.Prime 1159 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 61) (n := 1159)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1160 : ¬Nat.Prime 1160 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 580) (n := 1160)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1161 : ¬Nat.Prime 1161 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 387) (n := 1161)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1162 : ¬Nat.Prime 1162 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 581) (n := 1162)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1163 : Nat.count Nat.Prime 1163 = 191 := by
  rw [show 1163 = 1162 + 1 by norm_num, Nat.count_succ]
  rw [show 1162 = 1161 + 1 by norm_num, Nat.count_succ]
  rw [show 1161 = 1160 + 1 by norm_num, Nat.count_succ]
  rw [show 1160 = 1159 + 1 by norm_num, Nat.count_succ]
  rw [show 1159 = 1158 + 1 by norm_num, Nat.count_succ]
  rw [show 1158 = 1157 + 1 by norm_num, Nat.count_succ]
  rw [show 1157 = 1156 + 1 by norm_num, Nat.count_succ]
  rw [show 1156 = 1155 + 1 by norm_num, Nat.count_succ]
  rw [show 1155 = 1154 + 1 by norm_num, Nat.count_succ]
  rw [show 1154 = 1153 + 1 by norm_num, Nat.count_succ]
  rw [count_1153]
  simp [prime_1153, not_prime_1154, not_prime_1155, not_prime_1156, not_prime_1157, not_prime_1158, not_prime_1159, not_prime_1160, not_prime_1161, not_prime_1162]

theorem prime_1163 : (1163 : Nat).Prime := by norm_num

theorem nth_191 : Nat.nth Nat.Prime 191 = 1163 := by
  rw [← count_1163]
  exact Nat.nth_count prime_1163

theorem not_prime_1164 : ¬Nat.Prime 1164 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 582) (n := 1164)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1165 : ¬Nat.Prime 1165 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 233) (n := 1165)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1166 : ¬Nat.Prime 1166 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 583) (n := 1166)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1167 : ¬Nat.Prime 1167 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 389) (n := 1167)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1168 : ¬Nat.Prime 1168 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 584) (n := 1168)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1169 : ¬Nat.Prime 1169 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 167) (n := 1169)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1170 : ¬Nat.Prime 1170 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 585) (n := 1170)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1171 : Nat.count Nat.Prime 1171 = 192 := by
  rw [show 1171 = 1170 + 1 by norm_num, Nat.count_succ]
  rw [show 1170 = 1169 + 1 by norm_num, Nat.count_succ]
  rw [show 1169 = 1168 + 1 by norm_num, Nat.count_succ]
  rw [show 1168 = 1167 + 1 by norm_num, Nat.count_succ]
  rw [show 1167 = 1166 + 1 by norm_num, Nat.count_succ]
  rw [show 1166 = 1165 + 1 by norm_num, Nat.count_succ]
  rw [show 1165 = 1164 + 1 by norm_num, Nat.count_succ]
  rw [show 1164 = 1163 + 1 by norm_num, Nat.count_succ]
  rw [count_1163]
  simp [prime_1163, not_prime_1164, not_prime_1165, not_prime_1166, not_prime_1167, not_prime_1168, not_prime_1169, not_prime_1170]

theorem prime_1171 : (1171 : Nat).Prime := by norm_num

theorem nth_192 : Nat.nth Nat.Prime 192 = 1171 := by
  rw [← count_1171]
  exact Nat.nth_count prime_1171

theorem not_prime_1172 : ¬Nat.Prime 1172 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 586) (n := 1172)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1173 : ¬Nat.Prime 1173 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 391) (n := 1173)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1174 : ¬Nat.Prime 1174 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 587) (n := 1174)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1175 : ¬Nat.Prime 1175 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 235) (n := 1175)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1176 : ¬Nat.Prime 1176 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 588) (n := 1176)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1177 : ¬Nat.Prime 1177 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 107) (n := 1177)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1178 : ¬Nat.Prime 1178 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 589) (n := 1178)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1179 : ¬Nat.Prime 1179 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 393) (n := 1179)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1180 : ¬Nat.Prime 1180 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 590) (n := 1180)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1181 : Nat.count Nat.Prime 1181 = 193 := by
  rw [show 1181 = 1180 + 1 by norm_num, Nat.count_succ]
  rw [show 1180 = 1179 + 1 by norm_num, Nat.count_succ]
  rw [show 1179 = 1178 + 1 by norm_num, Nat.count_succ]
  rw [show 1178 = 1177 + 1 by norm_num, Nat.count_succ]
  rw [show 1177 = 1176 + 1 by norm_num, Nat.count_succ]
  rw [show 1176 = 1175 + 1 by norm_num, Nat.count_succ]
  rw [show 1175 = 1174 + 1 by norm_num, Nat.count_succ]
  rw [show 1174 = 1173 + 1 by norm_num, Nat.count_succ]
  rw [show 1173 = 1172 + 1 by norm_num, Nat.count_succ]
  rw [show 1172 = 1171 + 1 by norm_num, Nat.count_succ]
  rw [count_1171]
  simp [prime_1171, not_prime_1172, not_prime_1173, not_prime_1174, not_prime_1175, not_prime_1176, not_prime_1177, not_prime_1178, not_prime_1179, not_prime_1180]

theorem prime_1181 : (1181 : Nat).Prime := by norm_num

theorem nth_193 : Nat.nth Nat.Prime 193 = 1181 := by
  rw [← count_1181]
  exact Nat.nth_count prime_1181

theorem not_prime_1182 : ¬Nat.Prime 1182 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 591) (n := 1182)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1183 : ¬Nat.Prime 1183 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 169) (n := 1183)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1184 : ¬Nat.Prime 1184 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 592) (n := 1184)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1185 : ¬Nat.Prime 1185 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 395) (n := 1185)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1186 : ¬Nat.Prime 1186 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 593) (n := 1186)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1187 : Nat.count Nat.Prime 1187 = 194 := by
  rw [show 1187 = 1186 + 1 by norm_num, Nat.count_succ]
  rw [show 1186 = 1185 + 1 by norm_num, Nat.count_succ]
  rw [show 1185 = 1184 + 1 by norm_num, Nat.count_succ]
  rw [show 1184 = 1183 + 1 by norm_num, Nat.count_succ]
  rw [show 1183 = 1182 + 1 by norm_num, Nat.count_succ]
  rw [show 1182 = 1181 + 1 by norm_num, Nat.count_succ]
  rw [count_1181]
  simp [prime_1181, not_prime_1182, not_prime_1183, not_prime_1184, not_prime_1185, not_prime_1186]

theorem prime_1187 : (1187 : Nat).Prime := by norm_num

theorem nth_194 : Nat.nth Nat.Prime 194 = 1187 := by
  rw [← count_1187]
  exact Nat.nth_count prime_1187

theorem not_prime_1188 : ¬Nat.Prime 1188 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 594) (n := 1188)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1189 : ¬Nat.Prime 1189 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 41) (n := 1189)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1190 : ¬Nat.Prime 1190 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 595) (n := 1190)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1191 : ¬Nat.Prime 1191 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 397) (n := 1191)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1192 : ¬Nat.Prime 1192 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 596) (n := 1192)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1193 : Nat.count Nat.Prime 1193 = 195 := by
  rw [show 1193 = 1192 + 1 by norm_num, Nat.count_succ]
  rw [show 1192 = 1191 + 1 by norm_num, Nat.count_succ]
  rw [show 1191 = 1190 + 1 by norm_num, Nat.count_succ]
  rw [show 1190 = 1189 + 1 by norm_num, Nat.count_succ]
  rw [show 1189 = 1188 + 1 by norm_num, Nat.count_succ]
  rw [show 1188 = 1187 + 1 by norm_num, Nat.count_succ]
  rw [count_1187]
  simp [prime_1187, not_prime_1188, not_prime_1189, not_prime_1190, not_prime_1191, not_prime_1192]

theorem prime_1193 : (1193 : Nat).Prime := by norm_num

theorem nth_195 : Nat.nth Nat.Prime 195 = 1193 := by
  rw [← count_1193]
  exact Nat.nth_count prime_1193

theorem not_prime_1194 : ¬Nat.Prime 1194 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 597) (n := 1194)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1195 : ¬Nat.Prime 1195 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 239) (n := 1195)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1196 : ¬Nat.Prime 1196 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 598) (n := 1196)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1197 : ¬Nat.Prime 1197 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 399) (n := 1197)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1198 : ¬Nat.Prime 1198 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 599) (n := 1198)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1199 : ¬Nat.Prime 1199 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 109) (n := 1199)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1200 : ¬Nat.Prime 1200 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 600) (n := 1200)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1201 : Nat.count Nat.Prime 1201 = 196 := by
  rw [show 1201 = 1200 + 1 by norm_num, Nat.count_succ]
  rw [show 1200 = 1199 + 1 by norm_num, Nat.count_succ]
  rw [show 1199 = 1198 + 1 by norm_num, Nat.count_succ]
  rw [show 1198 = 1197 + 1 by norm_num, Nat.count_succ]
  rw [show 1197 = 1196 + 1 by norm_num, Nat.count_succ]
  rw [show 1196 = 1195 + 1 by norm_num, Nat.count_succ]
  rw [show 1195 = 1194 + 1 by norm_num, Nat.count_succ]
  rw [show 1194 = 1193 + 1 by norm_num, Nat.count_succ]
  rw [count_1193]
  simp [prime_1193, not_prime_1194, not_prime_1195, not_prime_1196, not_prime_1197, not_prime_1198, not_prime_1199, not_prime_1200]

theorem prime_1201 : (1201 : Nat).Prime := by norm_num

theorem nth_196 : Nat.nth Nat.Prime 196 = 1201 := by
  rw [← count_1201]
  exact Nat.nth_count prime_1201

theorem not_prime_1202 : ¬Nat.Prime 1202 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 601) (n := 1202)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1203 : ¬Nat.Prime 1203 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 401) (n := 1203)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1204 : ¬Nat.Prime 1204 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 602) (n := 1204)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1205 : ¬Nat.Prime 1205 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 241) (n := 1205)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1206 : ¬Nat.Prime 1206 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 603) (n := 1206)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1207 : ¬Nat.Prime 1207 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 71) (n := 1207)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1208 : ¬Nat.Prime 1208 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 604) (n := 1208)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1209 : ¬Nat.Prime 1209 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 403) (n := 1209)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1210 : ¬Nat.Prime 1210 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 605) (n := 1210)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1211 : ¬Nat.Prime 1211 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 173) (n := 1211)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1212 : ¬Nat.Prime 1212 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 606) (n := 1212)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1213 : Nat.count Nat.Prime 1213 = 197 := by
  rw [show 1213 = 1212 + 1 by norm_num, Nat.count_succ]
  rw [show 1212 = 1211 + 1 by norm_num, Nat.count_succ]
  rw [show 1211 = 1210 + 1 by norm_num, Nat.count_succ]
  rw [show 1210 = 1209 + 1 by norm_num, Nat.count_succ]
  rw [show 1209 = 1208 + 1 by norm_num, Nat.count_succ]
  rw [show 1208 = 1207 + 1 by norm_num, Nat.count_succ]
  rw [show 1207 = 1206 + 1 by norm_num, Nat.count_succ]
  rw [show 1206 = 1205 + 1 by norm_num, Nat.count_succ]
  rw [show 1205 = 1204 + 1 by norm_num, Nat.count_succ]
  rw [show 1204 = 1203 + 1 by norm_num, Nat.count_succ]
  rw [show 1203 = 1202 + 1 by norm_num, Nat.count_succ]
  rw [show 1202 = 1201 + 1 by norm_num, Nat.count_succ]
  rw [count_1201]
  simp [prime_1201, not_prime_1202, not_prime_1203, not_prime_1204, not_prime_1205, not_prime_1206, not_prime_1207, not_prime_1208, not_prime_1209, not_prime_1210, not_prime_1211, not_prime_1212]

theorem prime_1213 : (1213 : Nat).Prime := by norm_num

theorem nth_197 : Nat.nth Nat.Prime 197 = 1213 := by
  rw [← count_1213]
  exact Nat.nth_count prime_1213

theorem not_prime_1214 : ¬Nat.Prime 1214 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 607) (n := 1214)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1215 : ¬Nat.Prime 1215 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 405) (n := 1215)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1216 : ¬Nat.Prime 1216 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 608) (n := 1216)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1217 : Nat.count Nat.Prime 1217 = 198 := by
  rw [show 1217 = 1216 + 1 by norm_num, Nat.count_succ]
  rw [show 1216 = 1215 + 1 by norm_num, Nat.count_succ]
  rw [show 1215 = 1214 + 1 by norm_num, Nat.count_succ]
  rw [show 1214 = 1213 + 1 by norm_num, Nat.count_succ]
  rw [count_1213]
  simp [prime_1213, not_prime_1214, not_prime_1215, not_prime_1216]

theorem prime_1217 : (1217 : Nat).Prime := by norm_num

theorem nth_198 : Nat.nth Nat.Prime 198 = 1217 := by
  rw [← count_1217]
  exact Nat.nth_count prime_1217

theorem not_prime_1218 : ¬Nat.Prime 1218 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 609) (n := 1218)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1219 : ¬Nat.Prime 1219 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 53) (n := 1219)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1220 : ¬Nat.Prime 1220 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 610) (n := 1220)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1221 : ¬Nat.Prime 1221 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 407) (n := 1221)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1222 : ¬Nat.Prime 1222 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 611) (n := 1222)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1223 : Nat.count Nat.Prime 1223 = 199 := by
  rw [show 1223 = 1222 + 1 by norm_num, Nat.count_succ]
  rw [show 1222 = 1221 + 1 by norm_num, Nat.count_succ]
  rw [show 1221 = 1220 + 1 by norm_num, Nat.count_succ]
  rw [show 1220 = 1219 + 1 by norm_num, Nat.count_succ]
  rw [show 1219 = 1218 + 1 by norm_num, Nat.count_succ]
  rw [show 1218 = 1217 + 1 by norm_num, Nat.count_succ]
  rw [count_1217]
  simp [prime_1217, not_prime_1218, not_prime_1219, not_prime_1220, not_prime_1221, not_prime_1222]

theorem prime_1223 : (1223 : Nat).Prime := by norm_num

theorem nth_199 : Nat.nth Nat.Prime 199 = 1223 := by
  rw [← count_1223]
  exact Nat.nth_count prime_1223

end OeisA100474.PrimeCertificate
