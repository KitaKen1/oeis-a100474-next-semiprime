import OeisA100474PrimeCertificate.Chunk17

/-! Kernel prime/count certificate, chunk 18 (450–474). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_3182 : ¬Nat.Prime 3182 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1591) (n := 3182)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3183 : ¬Nat.Prime 3183 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1061) (n := 3183)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3184 : ¬Nat.Prime 3184 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1592) (n := 3184)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3185 : ¬Nat.Prime 3185 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 637) (n := 3185)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3186 : ¬Nat.Prime 3186 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1593) (n := 3186)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3187 : Nat.count Nat.Prime 3187 = 450 := by
  rw [show 3187 = 3186 + 1 by norm_num, Nat.count_succ]
  rw [show 3186 = 3185 + 1 by norm_num, Nat.count_succ]
  rw [show 3185 = 3184 + 1 by norm_num, Nat.count_succ]
  rw [show 3184 = 3183 + 1 by norm_num, Nat.count_succ]
  rw [show 3183 = 3182 + 1 by norm_num, Nat.count_succ]
  rw [show 3182 = 3181 + 1 by norm_num, Nat.count_succ]
  rw [count_3181]
  simp [prime_3181, not_prime_3182, not_prime_3183, not_prime_3184, not_prime_3185, not_prime_3186]

theorem prime_3187 : (3187 : Nat).Prime := by norm_num

theorem nth_450 : Nat.nth Nat.Prime 450 = 3187 := by
  rw [← count_3187]
  exact Nat.nth_count prime_3187

theorem not_prime_3188 : ¬Nat.Prime 3188 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1594) (n := 3188)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3189 : ¬Nat.Prime 3189 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1063) (n := 3189)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3190 : ¬Nat.Prime 3190 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1595) (n := 3190)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3191 : Nat.count Nat.Prime 3191 = 451 := by
  rw [show 3191 = 3190 + 1 by norm_num, Nat.count_succ]
  rw [show 3190 = 3189 + 1 by norm_num, Nat.count_succ]
  rw [show 3189 = 3188 + 1 by norm_num, Nat.count_succ]
  rw [show 3188 = 3187 + 1 by norm_num, Nat.count_succ]
  rw [count_3187]
  simp [prime_3187, not_prime_3188, not_prime_3189, not_prime_3190]

theorem prime_3191 : (3191 : Nat).Prime := by norm_num

theorem nth_451 : Nat.nth Nat.Prime 451 = 3191 := by
  rw [← count_3191]
  exact Nat.nth_count prime_3191

theorem not_prime_3192 : ¬Nat.Prime 3192 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1596) (n := 3192)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3193 : ¬Nat.Prime 3193 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 103) (n := 3193)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3194 : ¬Nat.Prime 3194 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1597) (n := 3194)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3195 : ¬Nat.Prime 3195 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1065) (n := 3195)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3196 : ¬Nat.Prime 3196 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1598) (n := 3196)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3197 : ¬Nat.Prime 3197 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 139) (n := 3197)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3198 : ¬Nat.Prime 3198 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1599) (n := 3198)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3199 : ¬Nat.Prime 3199 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 457) (n := 3199)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3200 : ¬Nat.Prime 3200 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1600) (n := 3200)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3201 : ¬Nat.Prime 3201 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1067) (n := 3201)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3202 : ¬Nat.Prime 3202 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1601) (n := 3202)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3203 : Nat.count Nat.Prime 3203 = 452 := by
  rw [show 3203 = 3202 + 1 by norm_num, Nat.count_succ]
  rw [show 3202 = 3201 + 1 by norm_num, Nat.count_succ]
  rw [show 3201 = 3200 + 1 by norm_num, Nat.count_succ]
  rw [show 3200 = 3199 + 1 by norm_num, Nat.count_succ]
  rw [show 3199 = 3198 + 1 by norm_num, Nat.count_succ]
  rw [show 3198 = 3197 + 1 by norm_num, Nat.count_succ]
  rw [show 3197 = 3196 + 1 by norm_num, Nat.count_succ]
  rw [show 3196 = 3195 + 1 by norm_num, Nat.count_succ]
  rw [show 3195 = 3194 + 1 by norm_num, Nat.count_succ]
  rw [show 3194 = 3193 + 1 by norm_num, Nat.count_succ]
  rw [show 3193 = 3192 + 1 by norm_num, Nat.count_succ]
  rw [show 3192 = 3191 + 1 by norm_num, Nat.count_succ]
  rw [count_3191]
  simp [prime_3191, not_prime_3192, not_prime_3193, not_prime_3194, not_prime_3195, not_prime_3196, not_prime_3197, not_prime_3198, not_prime_3199, not_prime_3200, not_prime_3201, not_prime_3202]

theorem prime_3203 : (3203 : Nat).Prime := by norm_num

theorem nth_452 : Nat.nth Nat.Prime 452 = 3203 := by
  rw [← count_3203]
  exact Nat.nth_count prime_3203

theorem not_prime_3204 : ¬Nat.Prime 3204 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1602) (n := 3204)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3205 : ¬Nat.Prime 3205 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 641) (n := 3205)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3206 : ¬Nat.Prime 3206 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1603) (n := 3206)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3207 : ¬Nat.Prime 3207 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1069) (n := 3207)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3208 : ¬Nat.Prime 3208 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1604) (n := 3208)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3209 : Nat.count Nat.Prime 3209 = 453 := by
  rw [show 3209 = 3208 + 1 by norm_num, Nat.count_succ]
  rw [show 3208 = 3207 + 1 by norm_num, Nat.count_succ]
  rw [show 3207 = 3206 + 1 by norm_num, Nat.count_succ]
  rw [show 3206 = 3205 + 1 by norm_num, Nat.count_succ]
  rw [show 3205 = 3204 + 1 by norm_num, Nat.count_succ]
  rw [show 3204 = 3203 + 1 by norm_num, Nat.count_succ]
  rw [count_3203]
  simp [prime_3203, not_prime_3204, not_prime_3205, not_prime_3206, not_prime_3207, not_prime_3208]

theorem prime_3209 : (3209 : Nat).Prime := by norm_num

theorem nth_453 : Nat.nth Nat.Prime 453 = 3209 := by
  rw [← count_3209]
  exact Nat.nth_count prime_3209

theorem not_prime_3210 : ¬Nat.Prime 3210 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1605) (n := 3210)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3211 : ¬Nat.Prime 3211 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 247) (n := 3211)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3212 : ¬Nat.Prime 3212 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1606) (n := 3212)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3213 : ¬Nat.Prime 3213 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1071) (n := 3213)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3214 : ¬Nat.Prime 3214 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1607) (n := 3214)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3215 : ¬Nat.Prime 3215 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 643) (n := 3215)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3216 : ¬Nat.Prime 3216 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1608) (n := 3216)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3217 : Nat.count Nat.Prime 3217 = 454 := by
  rw [show 3217 = 3216 + 1 by norm_num, Nat.count_succ]
  rw [show 3216 = 3215 + 1 by norm_num, Nat.count_succ]
  rw [show 3215 = 3214 + 1 by norm_num, Nat.count_succ]
  rw [show 3214 = 3213 + 1 by norm_num, Nat.count_succ]
  rw [show 3213 = 3212 + 1 by norm_num, Nat.count_succ]
  rw [show 3212 = 3211 + 1 by norm_num, Nat.count_succ]
  rw [show 3211 = 3210 + 1 by norm_num, Nat.count_succ]
  rw [show 3210 = 3209 + 1 by norm_num, Nat.count_succ]
  rw [count_3209]
  simp [prime_3209, not_prime_3210, not_prime_3211, not_prime_3212, not_prime_3213, not_prime_3214, not_prime_3215, not_prime_3216]

theorem prime_3217 : (3217 : Nat).Prime := by norm_num

theorem nth_454 : Nat.nth Nat.Prime 454 = 3217 := by
  rw [← count_3217]
  exact Nat.nth_count prime_3217

theorem not_prime_3218 : ¬Nat.Prime 3218 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1609) (n := 3218)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3219 : ¬Nat.Prime 3219 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1073) (n := 3219)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3220 : ¬Nat.Prime 3220 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1610) (n := 3220)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3221 : Nat.count Nat.Prime 3221 = 455 := by
  rw [show 3221 = 3220 + 1 by norm_num, Nat.count_succ]
  rw [show 3220 = 3219 + 1 by norm_num, Nat.count_succ]
  rw [show 3219 = 3218 + 1 by norm_num, Nat.count_succ]
  rw [show 3218 = 3217 + 1 by norm_num, Nat.count_succ]
  rw [count_3217]
  simp [prime_3217, not_prime_3218, not_prime_3219, not_prime_3220]

theorem prime_3221 : (3221 : Nat).Prime := by norm_num

theorem nth_455 : Nat.nth Nat.Prime 455 = 3221 := by
  rw [← count_3221]
  exact Nat.nth_count prime_3221

theorem not_prime_3222 : ¬Nat.Prime 3222 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1611) (n := 3222)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3223 : ¬Nat.Prime 3223 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 293) (n := 3223)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3224 : ¬Nat.Prime 3224 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1612) (n := 3224)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3225 : ¬Nat.Prime 3225 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1075) (n := 3225)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3226 : ¬Nat.Prime 3226 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1613) (n := 3226)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3227 : ¬Nat.Prime 3227 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 461) (n := 3227)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3228 : ¬Nat.Prime 3228 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1614) (n := 3228)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3229 : Nat.count Nat.Prime 3229 = 456 := by
  rw [show 3229 = 3228 + 1 by norm_num, Nat.count_succ]
  rw [show 3228 = 3227 + 1 by norm_num, Nat.count_succ]
  rw [show 3227 = 3226 + 1 by norm_num, Nat.count_succ]
  rw [show 3226 = 3225 + 1 by norm_num, Nat.count_succ]
  rw [show 3225 = 3224 + 1 by norm_num, Nat.count_succ]
  rw [show 3224 = 3223 + 1 by norm_num, Nat.count_succ]
  rw [show 3223 = 3222 + 1 by norm_num, Nat.count_succ]
  rw [show 3222 = 3221 + 1 by norm_num, Nat.count_succ]
  rw [count_3221]
  simp [prime_3221, not_prime_3222, not_prime_3223, not_prime_3224, not_prime_3225, not_prime_3226, not_prime_3227, not_prime_3228]

theorem prime_3229 : (3229 : Nat).Prime := by norm_num

theorem nth_456 : Nat.nth Nat.Prime 456 = 3229 := by
  rw [← count_3229]
  exact Nat.nth_count prime_3229

theorem not_prime_3230 : ¬Nat.Prime 3230 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1615) (n := 3230)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3231 : ¬Nat.Prime 3231 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1077) (n := 3231)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3232 : ¬Nat.Prime 3232 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1616) (n := 3232)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3233 : ¬Nat.Prime 3233 :=
  Nat.not_prime_of_mul_eq (a := 53) (b := 61) (n := 3233)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3234 : ¬Nat.Prime 3234 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1617) (n := 3234)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3235 : ¬Nat.Prime 3235 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 647) (n := 3235)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3236 : ¬Nat.Prime 3236 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1618) (n := 3236)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3237 : ¬Nat.Prime 3237 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1079) (n := 3237)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3238 : ¬Nat.Prime 3238 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1619) (n := 3238)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3239 : ¬Nat.Prime 3239 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 79) (n := 3239)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3240 : ¬Nat.Prime 3240 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1620) (n := 3240)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3241 : ¬Nat.Prime 3241 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 463) (n := 3241)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3242 : ¬Nat.Prime 3242 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1621) (n := 3242)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3243 : ¬Nat.Prime 3243 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1081) (n := 3243)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3244 : ¬Nat.Prime 3244 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1622) (n := 3244)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3245 : ¬Nat.Prime 3245 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 649) (n := 3245)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3246 : ¬Nat.Prime 3246 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1623) (n := 3246)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3247 : ¬Nat.Prime 3247 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 191) (n := 3247)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3248 : ¬Nat.Prime 3248 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1624) (n := 3248)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3249 : ¬Nat.Prime 3249 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1083) (n := 3249)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3250 : ¬Nat.Prime 3250 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1625) (n := 3250)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3251 : Nat.count Nat.Prime 3251 = 457 := by
  rw [show 3251 = 3250 + 1 by norm_num, Nat.count_succ]
  rw [show 3250 = 3249 + 1 by norm_num, Nat.count_succ]
  rw [show 3249 = 3248 + 1 by norm_num, Nat.count_succ]
  rw [show 3248 = 3247 + 1 by norm_num, Nat.count_succ]
  rw [show 3247 = 3246 + 1 by norm_num, Nat.count_succ]
  rw [show 3246 = 3245 + 1 by norm_num, Nat.count_succ]
  rw [show 3245 = 3244 + 1 by norm_num, Nat.count_succ]
  rw [show 3244 = 3243 + 1 by norm_num, Nat.count_succ]
  rw [show 3243 = 3242 + 1 by norm_num, Nat.count_succ]
  rw [show 3242 = 3241 + 1 by norm_num, Nat.count_succ]
  rw [show 3241 = 3240 + 1 by norm_num, Nat.count_succ]
  rw [show 3240 = 3239 + 1 by norm_num, Nat.count_succ]
  rw [show 3239 = 3238 + 1 by norm_num, Nat.count_succ]
  rw [show 3238 = 3237 + 1 by norm_num, Nat.count_succ]
  rw [show 3237 = 3236 + 1 by norm_num, Nat.count_succ]
  rw [show 3236 = 3235 + 1 by norm_num, Nat.count_succ]
  rw [show 3235 = 3234 + 1 by norm_num, Nat.count_succ]
  rw [show 3234 = 3233 + 1 by norm_num, Nat.count_succ]
  rw [show 3233 = 3232 + 1 by norm_num, Nat.count_succ]
  rw [show 3232 = 3231 + 1 by norm_num, Nat.count_succ]
  rw [show 3231 = 3230 + 1 by norm_num, Nat.count_succ]
  rw [show 3230 = 3229 + 1 by norm_num, Nat.count_succ]
  rw [count_3229]
  simp [prime_3229, not_prime_3230, not_prime_3231, not_prime_3232, not_prime_3233, not_prime_3234, not_prime_3235, not_prime_3236, not_prime_3237, not_prime_3238, not_prime_3239, not_prime_3240, not_prime_3241, not_prime_3242, not_prime_3243, not_prime_3244, not_prime_3245, not_prime_3246, not_prime_3247, not_prime_3248, not_prime_3249, not_prime_3250]

theorem prime_3251 : (3251 : Nat).Prime := by norm_num

theorem nth_457 : Nat.nth Nat.Prime 457 = 3251 := by
  rw [← count_3251]
  exact Nat.nth_count prime_3251

theorem not_prime_3252 : ¬Nat.Prime 3252 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1626) (n := 3252)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3253 : Nat.count Nat.Prime 3253 = 458 := by
  rw [show 3253 = 3252 + 1 by norm_num, Nat.count_succ]
  rw [show 3252 = 3251 + 1 by norm_num, Nat.count_succ]
  rw [count_3251]
  simp [prime_3251, not_prime_3252]

theorem prime_3253 : (3253 : Nat).Prime := by norm_num

theorem nth_458 : Nat.nth Nat.Prime 458 = 3253 := by
  rw [← count_3253]
  exact Nat.nth_count prime_3253

theorem not_prime_3254 : ¬Nat.Prime 3254 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1627) (n := 3254)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3255 : ¬Nat.Prime 3255 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1085) (n := 3255)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3256 : ¬Nat.Prime 3256 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1628) (n := 3256)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3257 : Nat.count Nat.Prime 3257 = 459 := by
  rw [show 3257 = 3256 + 1 by norm_num, Nat.count_succ]
  rw [show 3256 = 3255 + 1 by norm_num, Nat.count_succ]
  rw [show 3255 = 3254 + 1 by norm_num, Nat.count_succ]
  rw [show 3254 = 3253 + 1 by norm_num, Nat.count_succ]
  rw [count_3253]
  simp [prime_3253, not_prime_3254, not_prime_3255, not_prime_3256]

theorem prime_3257 : (3257 : Nat).Prime := by norm_num

theorem nth_459 : Nat.nth Nat.Prime 459 = 3257 := by
  rw [← count_3257]
  exact Nat.nth_count prime_3257

theorem not_prime_3258 : ¬Nat.Prime 3258 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1629) (n := 3258)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3259 : Nat.count Nat.Prime 3259 = 460 := by
  rw [show 3259 = 3258 + 1 by norm_num, Nat.count_succ]
  rw [show 3258 = 3257 + 1 by norm_num, Nat.count_succ]
  rw [count_3257]
  simp [prime_3257, not_prime_3258]

theorem prime_3259 : (3259 : Nat).Prime := by norm_num

theorem nth_460 : Nat.nth Nat.Prime 460 = 3259 := by
  rw [← count_3259]
  exact Nat.nth_count prime_3259

theorem not_prime_3260 : ¬Nat.Prime 3260 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1630) (n := 3260)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3261 : ¬Nat.Prime 3261 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1087) (n := 3261)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3262 : ¬Nat.Prime 3262 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1631) (n := 3262)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3263 : ¬Nat.Prime 3263 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 251) (n := 3263)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3264 : ¬Nat.Prime 3264 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1632) (n := 3264)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3265 : ¬Nat.Prime 3265 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 653) (n := 3265)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3266 : ¬Nat.Prime 3266 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1633) (n := 3266)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3267 : ¬Nat.Prime 3267 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1089) (n := 3267)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3268 : ¬Nat.Prime 3268 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1634) (n := 3268)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3269 : ¬Nat.Prime 3269 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 467) (n := 3269)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3270 : ¬Nat.Prime 3270 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1635) (n := 3270)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3271 : Nat.count Nat.Prime 3271 = 461 := by
  rw [show 3271 = 3270 + 1 by norm_num, Nat.count_succ]
  rw [show 3270 = 3269 + 1 by norm_num, Nat.count_succ]
  rw [show 3269 = 3268 + 1 by norm_num, Nat.count_succ]
  rw [show 3268 = 3267 + 1 by norm_num, Nat.count_succ]
  rw [show 3267 = 3266 + 1 by norm_num, Nat.count_succ]
  rw [show 3266 = 3265 + 1 by norm_num, Nat.count_succ]
  rw [show 3265 = 3264 + 1 by norm_num, Nat.count_succ]
  rw [show 3264 = 3263 + 1 by norm_num, Nat.count_succ]
  rw [show 3263 = 3262 + 1 by norm_num, Nat.count_succ]
  rw [show 3262 = 3261 + 1 by norm_num, Nat.count_succ]
  rw [show 3261 = 3260 + 1 by norm_num, Nat.count_succ]
  rw [show 3260 = 3259 + 1 by norm_num, Nat.count_succ]
  rw [count_3259]
  simp [prime_3259, not_prime_3260, not_prime_3261, not_prime_3262, not_prime_3263, not_prime_3264, not_prime_3265, not_prime_3266, not_prime_3267, not_prime_3268, not_prime_3269, not_prime_3270]

theorem prime_3271 : (3271 : Nat).Prime := by norm_num

theorem nth_461 : Nat.nth Nat.Prime 461 = 3271 := by
  rw [← count_3271]
  exact Nat.nth_count prime_3271

theorem not_prime_3272 : ¬Nat.Prime 3272 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1636) (n := 3272)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3273 : ¬Nat.Prime 3273 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1091) (n := 3273)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3274 : ¬Nat.Prime 3274 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1637) (n := 3274)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3275 : ¬Nat.Prime 3275 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 655) (n := 3275)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3276 : ¬Nat.Prime 3276 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1638) (n := 3276)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3277 : ¬Nat.Prime 3277 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 113) (n := 3277)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3278 : ¬Nat.Prime 3278 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1639) (n := 3278)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3279 : ¬Nat.Prime 3279 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1093) (n := 3279)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3280 : ¬Nat.Prime 3280 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1640) (n := 3280)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3281 : ¬Nat.Prime 3281 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 193) (n := 3281)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3282 : ¬Nat.Prime 3282 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1641) (n := 3282)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3283 : ¬Nat.Prime 3283 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 469) (n := 3283)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3284 : ¬Nat.Prime 3284 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1642) (n := 3284)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3285 : ¬Nat.Prime 3285 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1095) (n := 3285)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3286 : ¬Nat.Prime 3286 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1643) (n := 3286)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3287 : ¬Nat.Prime 3287 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 173) (n := 3287)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3288 : ¬Nat.Prime 3288 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1644) (n := 3288)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3289 : ¬Nat.Prime 3289 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 299) (n := 3289)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3290 : ¬Nat.Prime 3290 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1645) (n := 3290)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3291 : ¬Nat.Prime 3291 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1097) (n := 3291)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3292 : ¬Nat.Prime 3292 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1646) (n := 3292)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3293 : ¬Nat.Prime 3293 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 89) (n := 3293)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3294 : ¬Nat.Prime 3294 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1647) (n := 3294)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3295 : ¬Nat.Prime 3295 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 659) (n := 3295)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3296 : ¬Nat.Prime 3296 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1648) (n := 3296)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3297 : ¬Nat.Prime 3297 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1099) (n := 3297)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3298 : ¬Nat.Prime 3298 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1649) (n := 3298)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3299 : Nat.count Nat.Prime 3299 = 462 := by
  rw [show 3299 = 3298 + 1 by norm_num, Nat.count_succ]
  rw [show 3298 = 3297 + 1 by norm_num, Nat.count_succ]
  rw [show 3297 = 3296 + 1 by norm_num, Nat.count_succ]
  rw [show 3296 = 3295 + 1 by norm_num, Nat.count_succ]
  rw [show 3295 = 3294 + 1 by norm_num, Nat.count_succ]
  rw [show 3294 = 3293 + 1 by norm_num, Nat.count_succ]
  rw [show 3293 = 3292 + 1 by norm_num, Nat.count_succ]
  rw [show 3292 = 3291 + 1 by norm_num, Nat.count_succ]
  rw [show 3291 = 3290 + 1 by norm_num, Nat.count_succ]
  rw [show 3290 = 3289 + 1 by norm_num, Nat.count_succ]
  rw [show 3289 = 3288 + 1 by norm_num, Nat.count_succ]
  rw [show 3288 = 3287 + 1 by norm_num, Nat.count_succ]
  rw [show 3287 = 3286 + 1 by norm_num, Nat.count_succ]
  rw [show 3286 = 3285 + 1 by norm_num, Nat.count_succ]
  rw [show 3285 = 3284 + 1 by norm_num, Nat.count_succ]
  rw [show 3284 = 3283 + 1 by norm_num, Nat.count_succ]
  rw [show 3283 = 3282 + 1 by norm_num, Nat.count_succ]
  rw [show 3282 = 3281 + 1 by norm_num, Nat.count_succ]
  rw [show 3281 = 3280 + 1 by norm_num, Nat.count_succ]
  rw [show 3280 = 3279 + 1 by norm_num, Nat.count_succ]
  rw [show 3279 = 3278 + 1 by norm_num, Nat.count_succ]
  rw [show 3278 = 3277 + 1 by norm_num, Nat.count_succ]
  rw [show 3277 = 3276 + 1 by norm_num, Nat.count_succ]
  rw [show 3276 = 3275 + 1 by norm_num, Nat.count_succ]
  rw [show 3275 = 3274 + 1 by norm_num, Nat.count_succ]
  rw [show 3274 = 3273 + 1 by norm_num, Nat.count_succ]
  rw [show 3273 = 3272 + 1 by norm_num, Nat.count_succ]
  rw [show 3272 = 3271 + 1 by norm_num, Nat.count_succ]
  rw [count_3271]
  simp [prime_3271, not_prime_3272, not_prime_3273, not_prime_3274, not_prime_3275, not_prime_3276, not_prime_3277, not_prime_3278, not_prime_3279, not_prime_3280, not_prime_3281, not_prime_3282, not_prime_3283, not_prime_3284, not_prime_3285, not_prime_3286, not_prime_3287, not_prime_3288, not_prime_3289, not_prime_3290, not_prime_3291, not_prime_3292, not_prime_3293, not_prime_3294, not_prime_3295, not_prime_3296, not_prime_3297, not_prime_3298]

theorem prime_3299 : (3299 : Nat).Prime := by norm_num

theorem nth_462 : Nat.nth Nat.Prime 462 = 3299 := by
  rw [← count_3299]
  exact Nat.nth_count prime_3299

theorem not_prime_3300 : ¬Nat.Prime 3300 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1650) (n := 3300)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3301 : Nat.count Nat.Prime 3301 = 463 := by
  rw [show 3301 = 3300 + 1 by norm_num, Nat.count_succ]
  rw [show 3300 = 3299 + 1 by norm_num, Nat.count_succ]
  rw [count_3299]
  simp [prime_3299, not_prime_3300]

theorem prime_3301 : (3301 : Nat).Prime := by norm_num

theorem nth_463 : Nat.nth Nat.Prime 463 = 3301 := by
  rw [← count_3301]
  exact Nat.nth_count prime_3301

theorem not_prime_3302 : ¬Nat.Prime 3302 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1651) (n := 3302)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3303 : ¬Nat.Prime 3303 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1101) (n := 3303)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3304 : ¬Nat.Prime 3304 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1652) (n := 3304)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3305 : ¬Nat.Prime 3305 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 661) (n := 3305)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3306 : ¬Nat.Prime 3306 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1653) (n := 3306)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3307 : Nat.count Nat.Prime 3307 = 464 := by
  rw [show 3307 = 3306 + 1 by norm_num, Nat.count_succ]
  rw [show 3306 = 3305 + 1 by norm_num, Nat.count_succ]
  rw [show 3305 = 3304 + 1 by norm_num, Nat.count_succ]
  rw [show 3304 = 3303 + 1 by norm_num, Nat.count_succ]
  rw [show 3303 = 3302 + 1 by norm_num, Nat.count_succ]
  rw [show 3302 = 3301 + 1 by norm_num, Nat.count_succ]
  rw [count_3301]
  simp [prime_3301, not_prime_3302, not_prime_3303, not_prime_3304, not_prime_3305, not_prime_3306]

theorem prime_3307 : (3307 : Nat).Prime := by norm_num

theorem nth_464 : Nat.nth Nat.Prime 464 = 3307 := by
  rw [← count_3307]
  exact Nat.nth_count prime_3307

theorem not_prime_3308 : ¬Nat.Prime 3308 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1654) (n := 3308)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3309 : ¬Nat.Prime 3309 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1103) (n := 3309)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3310 : ¬Nat.Prime 3310 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1655) (n := 3310)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3311 : ¬Nat.Prime 3311 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 473) (n := 3311)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3312 : ¬Nat.Prime 3312 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1656) (n := 3312)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3313 : Nat.count Nat.Prime 3313 = 465 := by
  rw [show 3313 = 3312 + 1 by norm_num, Nat.count_succ]
  rw [show 3312 = 3311 + 1 by norm_num, Nat.count_succ]
  rw [show 3311 = 3310 + 1 by norm_num, Nat.count_succ]
  rw [show 3310 = 3309 + 1 by norm_num, Nat.count_succ]
  rw [show 3309 = 3308 + 1 by norm_num, Nat.count_succ]
  rw [show 3308 = 3307 + 1 by norm_num, Nat.count_succ]
  rw [count_3307]
  simp [prime_3307, not_prime_3308, not_prime_3309, not_prime_3310, not_prime_3311, not_prime_3312]

theorem prime_3313 : (3313 : Nat).Prime := by norm_num

theorem nth_465 : Nat.nth Nat.Prime 465 = 3313 := by
  rw [← count_3313]
  exact Nat.nth_count prime_3313

theorem not_prime_3314 : ¬Nat.Prime 3314 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1657) (n := 3314)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3315 : ¬Nat.Prime 3315 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1105) (n := 3315)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3316 : ¬Nat.Prime 3316 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1658) (n := 3316)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3317 : ¬Nat.Prime 3317 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 107) (n := 3317)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3318 : ¬Nat.Prime 3318 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1659) (n := 3318)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3319 : Nat.count Nat.Prime 3319 = 466 := by
  rw [show 3319 = 3318 + 1 by norm_num, Nat.count_succ]
  rw [show 3318 = 3317 + 1 by norm_num, Nat.count_succ]
  rw [show 3317 = 3316 + 1 by norm_num, Nat.count_succ]
  rw [show 3316 = 3315 + 1 by norm_num, Nat.count_succ]
  rw [show 3315 = 3314 + 1 by norm_num, Nat.count_succ]
  rw [show 3314 = 3313 + 1 by norm_num, Nat.count_succ]
  rw [count_3313]
  simp [prime_3313, not_prime_3314, not_prime_3315, not_prime_3316, not_prime_3317, not_prime_3318]

theorem prime_3319 : (3319 : Nat).Prime := by norm_num

theorem nth_466 : Nat.nth Nat.Prime 466 = 3319 := by
  rw [← count_3319]
  exact Nat.nth_count prime_3319

theorem not_prime_3320 : ¬Nat.Prime 3320 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1660) (n := 3320)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3321 : ¬Nat.Prime 3321 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1107) (n := 3321)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3322 : ¬Nat.Prime 3322 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1661) (n := 3322)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3323 : Nat.count Nat.Prime 3323 = 467 := by
  rw [show 3323 = 3322 + 1 by norm_num, Nat.count_succ]
  rw [show 3322 = 3321 + 1 by norm_num, Nat.count_succ]
  rw [show 3321 = 3320 + 1 by norm_num, Nat.count_succ]
  rw [show 3320 = 3319 + 1 by norm_num, Nat.count_succ]
  rw [count_3319]
  simp [prime_3319, not_prime_3320, not_prime_3321, not_prime_3322]

theorem prime_3323 : (3323 : Nat).Prime := by norm_num

theorem nth_467 : Nat.nth Nat.Prime 467 = 3323 := by
  rw [← count_3323]
  exact Nat.nth_count prime_3323

theorem not_prime_3324 : ¬Nat.Prime 3324 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1662) (n := 3324)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3325 : ¬Nat.Prime 3325 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 665) (n := 3325)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3326 : ¬Nat.Prime 3326 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1663) (n := 3326)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3327 : ¬Nat.Prime 3327 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1109) (n := 3327)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3328 : ¬Nat.Prime 3328 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1664) (n := 3328)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3329 : Nat.count Nat.Prime 3329 = 468 := by
  rw [show 3329 = 3328 + 1 by norm_num, Nat.count_succ]
  rw [show 3328 = 3327 + 1 by norm_num, Nat.count_succ]
  rw [show 3327 = 3326 + 1 by norm_num, Nat.count_succ]
  rw [show 3326 = 3325 + 1 by norm_num, Nat.count_succ]
  rw [show 3325 = 3324 + 1 by norm_num, Nat.count_succ]
  rw [show 3324 = 3323 + 1 by norm_num, Nat.count_succ]
  rw [count_3323]
  simp [prime_3323, not_prime_3324, not_prime_3325, not_prime_3326, not_prime_3327, not_prime_3328]

theorem prime_3329 : (3329 : Nat).Prime := by norm_num

theorem nth_468 : Nat.nth Nat.Prime 468 = 3329 := by
  rw [← count_3329]
  exact Nat.nth_count prime_3329

theorem not_prime_3330 : ¬Nat.Prime 3330 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1665) (n := 3330)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3331 : Nat.count Nat.Prime 3331 = 469 := by
  rw [show 3331 = 3330 + 1 by norm_num, Nat.count_succ]
  rw [show 3330 = 3329 + 1 by norm_num, Nat.count_succ]
  rw [count_3329]
  simp [prime_3329, not_prime_3330]

theorem prime_3331 : (3331 : Nat).Prime := by norm_num

theorem nth_469 : Nat.nth Nat.Prime 469 = 3331 := by
  rw [← count_3331]
  exact Nat.nth_count prime_3331

theorem not_prime_3332 : ¬Nat.Prime 3332 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1666) (n := 3332)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3333 : ¬Nat.Prime 3333 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1111) (n := 3333)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3334 : ¬Nat.Prime 3334 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1667) (n := 3334)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3335 : ¬Nat.Prime 3335 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 667) (n := 3335)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3336 : ¬Nat.Prime 3336 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1668) (n := 3336)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3337 : ¬Nat.Prime 3337 :=
  Nat.not_prime_of_mul_eq (a := 47) (b := 71) (n := 3337)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3338 : ¬Nat.Prime 3338 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1669) (n := 3338)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3339 : ¬Nat.Prime 3339 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1113) (n := 3339)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3340 : ¬Nat.Prime 3340 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1670) (n := 3340)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3341 : ¬Nat.Prime 3341 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 257) (n := 3341)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3342 : ¬Nat.Prime 3342 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1671) (n := 3342)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3343 : Nat.count Nat.Prime 3343 = 470 := by
  rw [show 3343 = 3342 + 1 by norm_num, Nat.count_succ]
  rw [show 3342 = 3341 + 1 by norm_num, Nat.count_succ]
  rw [show 3341 = 3340 + 1 by norm_num, Nat.count_succ]
  rw [show 3340 = 3339 + 1 by norm_num, Nat.count_succ]
  rw [show 3339 = 3338 + 1 by norm_num, Nat.count_succ]
  rw [show 3338 = 3337 + 1 by norm_num, Nat.count_succ]
  rw [show 3337 = 3336 + 1 by norm_num, Nat.count_succ]
  rw [show 3336 = 3335 + 1 by norm_num, Nat.count_succ]
  rw [show 3335 = 3334 + 1 by norm_num, Nat.count_succ]
  rw [show 3334 = 3333 + 1 by norm_num, Nat.count_succ]
  rw [show 3333 = 3332 + 1 by norm_num, Nat.count_succ]
  rw [show 3332 = 3331 + 1 by norm_num, Nat.count_succ]
  rw [count_3331]
  simp [prime_3331, not_prime_3332, not_prime_3333, not_prime_3334, not_prime_3335, not_prime_3336, not_prime_3337, not_prime_3338, not_prime_3339, not_prime_3340, not_prime_3341, not_prime_3342]

theorem prime_3343 : (3343 : Nat).Prime := by norm_num

theorem nth_470 : Nat.nth Nat.Prime 470 = 3343 := by
  rw [← count_3343]
  exact Nat.nth_count prime_3343

theorem not_prime_3344 : ¬Nat.Prime 3344 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1672) (n := 3344)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3345 : ¬Nat.Prime 3345 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1115) (n := 3345)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3346 : ¬Nat.Prime 3346 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1673) (n := 3346)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3347 : Nat.count Nat.Prime 3347 = 471 := by
  rw [show 3347 = 3346 + 1 by norm_num, Nat.count_succ]
  rw [show 3346 = 3345 + 1 by norm_num, Nat.count_succ]
  rw [show 3345 = 3344 + 1 by norm_num, Nat.count_succ]
  rw [show 3344 = 3343 + 1 by norm_num, Nat.count_succ]
  rw [count_3343]
  simp [prime_3343, not_prime_3344, not_prime_3345, not_prime_3346]

theorem prime_3347 : (3347 : Nat).Prime := by norm_num

theorem nth_471 : Nat.nth Nat.Prime 471 = 3347 := by
  rw [← count_3347]
  exact Nat.nth_count prime_3347

theorem not_prime_3348 : ¬Nat.Prime 3348 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1674) (n := 3348)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3349 : ¬Nat.Prime 3349 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 197) (n := 3349)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3350 : ¬Nat.Prime 3350 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1675) (n := 3350)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3351 : ¬Nat.Prime 3351 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1117) (n := 3351)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3352 : ¬Nat.Prime 3352 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1676) (n := 3352)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3353 : ¬Nat.Prime 3353 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 479) (n := 3353)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3354 : ¬Nat.Prime 3354 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1677) (n := 3354)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3355 : ¬Nat.Prime 3355 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 671) (n := 3355)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3356 : ¬Nat.Prime 3356 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1678) (n := 3356)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3357 : ¬Nat.Prime 3357 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1119) (n := 3357)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3358 : ¬Nat.Prime 3358 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1679) (n := 3358)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3359 : Nat.count Nat.Prime 3359 = 472 := by
  rw [show 3359 = 3358 + 1 by norm_num, Nat.count_succ]
  rw [show 3358 = 3357 + 1 by norm_num, Nat.count_succ]
  rw [show 3357 = 3356 + 1 by norm_num, Nat.count_succ]
  rw [show 3356 = 3355 + 1 by norm_num, Nat.count_succ]
  rw [show 3355 = 3354 + 1 by norm_num, Nat.count_succ]
  rw [show 3354 = 3353 + 1 by norm_num, Nat.count_succ]
  rw [show 3353 = 3352 + 1 by norm_num, Nat.count_succ]
  rw [show 3352 = 3351 + 1 by norm_num, Nat.count_succ]
  rw [show 3351 = 3350 + 1 by norm_num, Nat.count_succ]
  rw [show 3350 = 3349 + 1 by norm_num, Nat.count_succ]
  rw [show 3349 = 3348 + 1 by norm_num, Nat.count_succ]
  rw [show 3348 = 3347 + 1 by norm_num, Nat.count_succ]
  rw [count_3347]
  simp [prime_3347, not_prime_3348, not_prime_3349, not_prime_3350, not_prime_3351, not_prime_3352, not_prime_3353, not_prime_3354, not_prime_3355, not_prime_3356, not_prime_3357, not_prime_3358]

theorem prime_3359 : (3359 : Nat).Prime := by norm_num

theorem nth_472 : Nat.nth Nat.Prime 472 = 3359 := by
  rw [← count_3359]
  exact Nat.nth_count prime_3359

theorem not_prime_3360 : ¬Nat.Prime 3360 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1680) (n := 3360)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3361 : Nat.count Nat.Prime 3361 = 473 := by
  rw [show 3361 = 3360 + 1 by norm_num, Nat.count_succ]
  rw [show 3360 = 3359 + 1 by norm_num, Nat.count_succ]
  rw [count_3359]
  simp [prime_3359, not_prime_3360]

theorem prime_3361 : (3361 : Nat).Prime := by norm_num

theorem nth_473 : Nat.nth Nat.Prime 473 = 3361 := by
  rw [← count_3361]
  exact Nat.nth_count prime_3361

theorem not_prime_3362 : ¬Nat.Prime 3362 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1681) (n := 3362)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3363 : ¬Nat.Prime 3363 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1121) (n := 3363)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3364 : ¬Nat.Prime 3364 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1682) (n := 3364)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3365 : ¬Nat.Prime 3365 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 673) (n := 3365)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3366 : ¬Nat.Prime 3366 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1683) (n := 3366)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3367 : ¬Nat.Prime 3367 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 481) (n := 3367)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3368 : ¬Nat.Prime 3368 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1684) (n := 3368)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3369 : ¬Nat.Prime 3369 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1123) (n := 3369)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3370 : ¬Nat.Prime 3370 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1685) (n := 3370)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3371 : Nat.count Nat.Prime 3371 = 474 := by
  rw [show 3371 = 3370 + 1 by norm_num, Nat.count_succ]
  rw [show 3370 = 3369 + 1 by norm_num, Nat.count_succ]
  rw [show 3369 = 3368 + 1 by norm_num, Nat.count_succ]
  rw [show 3368 = 3367 + 1 by norm_num, Nat.count_succ]
  rw [show 3367 = 3366 + 1 by norm_num, Nat.count_succ]
  rw [show 3366 = 3365 + 1 by norm_num, Nat.count_succ]
  rw [show 3365 = 3364 + 1 by norm_num, Nat.count_succ]
  rw [show 3364 = 3363 + 1 by norm_num, Nat.count_succ]
  rw [show 3363 = 3362 + 1 by norm_num, Nat.count_succ]
  rw [show 3362 = 3361 + 1 by norm_num, Nat.count_succ]
  rw [count_3361]
  simp [prime_3361, not_prime_3362, not_prime_3363, not_prime_3364, not_prime_3365, not_prime_3366, not_prime_3367, not_prime_3368, not_prime_3369, not_prime_3370]

theorem prime_3371 : (3371 : Nat).Prime := by norm_num

theorem nth_474 : Nat.nth Nat.Prime 474 = 3371 := by
  rw [← count_3371]
  exact Nat.nth_count prime_3371

end OeisA100474.PrimeCertificate
