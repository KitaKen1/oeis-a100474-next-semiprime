import OeisA100474PrimeCertificate.Chunk22

/-! Kernel prime/count certificate, chunk 23 (575–599). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_4202 : ¬Nat.Prime 4202 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2101) (n := 4202)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4203 : ¬Nat.Prime 4203 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1401) (n := 4203)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4204 : ¬Nat.Prime 4204 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2102) (n := 4204)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4205 : ¬Nat.Prime 4205 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 841) (n := 4205)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4206 : ¬Nat.Prime 4206 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2103) (n := 4206)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4207 : ¬Nat.Prime 4207 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 601) (n := 4207)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4208 : ¬Nat.Prime 4208 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2104) (n := 4208)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4209 : ¬Nat.Prime 4209 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1403) (n := 4209)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4210 : ¬Nat.Prime 4210 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2105) (n := 4210)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4211 : Nat.count Nat.Prime 4211 = 575 := by
  rw [show 4211 = 4210 + 1 by norm_num, Nat.count_succ]
  rw [show 4210 = 4209 + 1 by norm_num, Nat.count_succ]
  rw [show 4209 = 4208 + 1 by norm_num, Nat.count_succ]
  rw [show 4208 = 4207 + 1 by norm_num, Nat.count_succ]
  rw [show 4207 = 4206 + 1 by norm_num, Nat.count_succ]
  rw [show 4206 = 4205 + 1 by norm_num, Nat.count_succ]
  rw [show 4205 = 4204 + 1 by norm_num, Nat.count_succ]
  rw [show 4204 = 4203 + 1 by norm_num, Nat.count_succ]
  rw [show 4203 = 4202 + 1 by norm_num, Nat.count_succ]
  rw [show 4202 = 4201 + 1 by norm_num, Nat.count_succ]
  rw [count_4201]
  simp [prime_4201, not_prime_4202, not_prime_4203, not_prime_4204, not_prime_4205, not_prime_4206, not_prime_4207, not_prime_4208, not_prime_4209, not_prime_4210]

theorem prime_4211 : (4211 : Nat).Prime := by norm_num

theorem nth_575 : Nat.nth Nat.Prime 575 = 4211 := by
  rw [← count_4211]
  exact Nat.nth_count prime_4211

theorem not_prime_4212 : ¬Nat.Prime 4212 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2106) (n := 4212)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4213 : ¬Nat.Prime 4213 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 383) (n := 4213)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4214 : ¬Nat.Prime 4214 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2107) (n := 4214)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4215 : ¬Nat.Prime 4215 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1405) (n := 4215)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4216 : ¬Nat.Prime 4216 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2108) (n := 4216)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4217 : Nat.count Nat.Prime 4217 = 576 := by
  rw [show 4217 = 4216 + 1 by norm_num, Nat.count_succ]
  rw [show 4216 = 4215 + 1 by norm_num, Nat.count_succ]
  rw [show 4215 = 4214 + 1 by norm_num, Nat.count_succ]
  rw [show 4214 = 4213 + 1 by norm_num, Nat.count_succ]
  rw [show 4213 = 4212 + 1 by norm_num, Nat.count_succ]
  rw [show 4212 = 4211 + 1 by norm_num, Nat.count_succ]
  rw [count_4211]
  simp [prime_4211, not_prime_4212, not_prime_4213, not_prime_4214, not_prime_4215, not_prime_4216]

theorem prime_4217 : (4217 : Nat).Prime := by norm_num

theorem nth_576 : Nat.nth Nat.Prime 576 = 4217 := by
  rw [← count_4217]
  exact Nat.nth_count prime_4217

theorem not_prime_4218 : ¬Nat.Prime 4218 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2109) (n := 4218)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4219 : Nat.count Nat.Prime 4219 = 577 := by
  rw [show 4219 = 4218 + 1 by norm_num, Nat.count_succ]
  rw [show 4218 = 4217 + 1 by norm_num, Nat.count_succ]
  rw [count_4217]
  simp [prime_4217, not_prime_4218]

theorem prime_4219 : (4219 : Nat).Prime := by norm_num

theorem nth_577 : Nat.nth Nat.Prime 577 = 4219 := by
  rw [← count_4219]
  exact Nat.nth_count prime_4219

theorem not_prime_4220 : ¬Nat.Prime 4220 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2110) (n := 4220)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4221 : ¬Nat.Prime 4221 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1407) (n := 4221)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4222 : ¬Nat.Prime 4222 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2111) (n := 4222)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4223 : ¬Nat.Prime 4223 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 103) (n := 4223)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4224 : ¬Nat.Prime 4224 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2112) (n := 4224)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4225 : ¬Nat.Prime 4225 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 845) (n := 4225)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4226 : ¬Nat.Prime 4226 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2113) (n := 4226)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4227 : ¬Nat.Prime 4227 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1409) (n := 4227)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4228 : ¬Nat.Prime 4228 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2114) (n := 4228)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4229 : Nat.count Nat.Prime 4229 = 578 := by
  rw [show 4229 = 4228 + 1 by norm_num, Nat.count_succ]
  rw [show 4228 = 4227 + 1 by norm_num, Nat.count_succ]
  rw [show 4227 = 4226 + 1 by norm_num, Nat.count_succ]
  rw [show 4226 = 4225 + 1 by norm_num, Nat.count_succ]
  rw [show 4225 = 4224 + 1 by norm_num, Nat.count_succ]
  rw [show 4224 = 4223 + 1 by norm_num, Nat.count_succ]
  rw [show 4223 = 4222 + 1 by norm_num, Nat.count_succ]
  rw [show 4222 = 4221 + 1 by norm_num, Nat.count_succ]
  rw [show 4221 = 4220 + 1 by norm_num, Nat.count_succ]
  rw [show 4220 = 4219 + 1 by norm_num, Nat.count_succ]
  rw [count_4219]
  simp [prime_4219, not_prime_4220, not_prime_4221, not_prime_4222, not_prime_4223, not_prime_4224, not_prime_4225, not_prime_4226, not_prime_4227, not_prime_4228]

theorem prime_4229 : (4229 : Nat).Prime := by norm_num

theorem nth_578 : Nat.nth Nat.Prime 578 = 4229 := by
  rw [← count_4229]
  exact Nat.nth_count prime_4229

theorem not_prime_4230 : ¬Nat.Prime 4230 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2115) (n := 4230)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4231 : Nat.count Nat.Prime 4231 = 579 := by
  rw [show 4231 = 4230 + 1 by norm_num, Nat.count_succ]
  rw [show 4230 = 4229 + 1 by norm_num, Nat.count_succ]
  rw [count_4229]
  simp [prime_4229, not_prime_4230]

theorem prime_4231 : (4231 : Nat).Prime := by norm_num

theorem nth_579 : Nat.nth Nat.Prime 579 = 4231 := by
  rw [← count_4231]
  exact Nat.nth_count prime_4231

theorem not_prime_4232 : ¬Nat.Prime 4232 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2116) (n := 4232)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4233 : ¬Nat.Prime 4233 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1411) (n := 4233)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4234 : ¬Nat.Prime 4234 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2117) (n := 4234)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4235 : ¬Nat.Prime 4235 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 847) (n := 4235)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4236 : ¬Nat.Prime 4236 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2118) (n := 4236)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4237 : ¬Nat.Prime 4237 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 223) (n := 4237)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4238 : ¬Nat.Prime 4238 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2119) (n := 4238)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4239 : ¬Nat.Prime 4239 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1413) (n := 4239)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4240 : ¬Nat.Prime 4240 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2120) (n := 4240)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4241 : Nat.count Nat.Prime 4241 = 580 := by
  rw [show 4241 = 4240 + 1 by norm_num, Nat.count_succ]
  rw [show 4240 = 4239 + 1 by norm_num, Nat.count_succ]
  rw [show 4239 = 4238 + 1 by norm_num, Nat.count_succ]
  rw [show 4238 = 4237 + 1 by norm_num, Nat.count_succ]
  rw [show 4237 = 4236 + 1 by norm_num, Nat.count_succ]
  rw [show 4236 = 4235 + 1 by norm_num, Nat.count_succ]
  rw [show 4235 = 4234 + 1 by norm_num, Nat.count_succ]
  rw [show 4234 = 4233 + 1 by norm_num, Nat.count_succ]
  rw [show 4233 = 4232 + 1 by norm_num, Nat.count_succ]
  rw [show 4232 = 4231 + 1 by norm_num, Nat.count_succ]
  rw [count_4231]
  simp [prime_4231, not_prime_4232, not_prime_4233, not_prime_4234, not_prime_4235, not_prime_4236, not_prime_4237, not_prime_4238, not_prime_4239, not_prime_4240]

theorem prime_4241 : (4241 : Nat).Prime := by norm_num

theorem nth_580 : Nat.nth Nat.Prime 580 = 4241 := by
  rw [← count_4241]
  exact Nat.nth_count prime_4241

theorem not_prime_4242 : ¬Nat.Prime 4242 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2121) (n := 4242)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4243 : Nat.count Nat.Prime 4243 = 581 := by
  rw [show 4243 = 4242 + 1 by norm_num, Nat.count_succ]
  rw [show 4242 = 4241 + 1 by norm_num, Nat.count_succ]
  rw [count_4241]
  simp [prime_4241, not_prime_4242]

theorem prime_4243 : (4243 : Nat).Prime := by norm_num

theorem nth_581 : Nat.nth Nat.Prime 581 = 4243 := by
  rw [← count_4243]
  exact Nat.nth_count prime_4243

theorem not_prime_4244 : ¬Nat.Prime 4244 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2122) (n := 4244)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4245 : ¬Nat.Prime 4245 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1415) (n := 4245)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4246 : ¬Nat.Prime 4246 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2123) (n := 4246)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4247 : ¬Nat.Prime 4247 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 137) (n := 4247)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4248 : ¬Nat.Prime 4248 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2124) (n := 4248)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4249 : ¬Nat.Prime 4249 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 607) (n := 4249)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4250 : ¬Nat.Prime 4250 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2125) (n := 4250)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4251 : ¬Nat.Prime 4251 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1417) (n := 4251)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4252 : ¬Nat.Prime 4252 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2126) (n := 4252)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4253 : Nat.count Nat.Prime 4253 = 582 := by
  rw [show 4253 = 4252 + 1 by norm_num, Nat.count_succ]
  rw [show 4252 = 4251 + 1 by norm_num, Nat.count_succ]
  rw [show 4251 = 4250 + 1 by norm_num, Nat.count_succ]
  rw [show 4250 = 4249 + 1 by norm_num, Nat.count_succ]
  rw [show 4249 = 4248 + 1 by norm_num, Nat.count_succ]
  rw [show 4248 = 4247 + 1 by norm_num, Nat.count_succ]
  rw [show 4247 = 4246 + 1 by norm_num, Nat.count_succ]
  rw [show 4246 = 4245 + 1 by norm_num, Nat.count_succ]
  rw [show 4245 = 4244 + 1 by norm_num, Nat.count_succ]
  rw [show 4244 = 4243 + 1 by norm_num, Nat.count_succ]
  rw [count_4243]
  simp [prime_4243, not_prime_4244, not_prime_4245, not_prime_4246, not_prime_4247, not_prime_4248, not_prime_4249, not_prime_4250, not_prime_4251, not_prime_4252]

theorem prime_4253 : (4253 : Nat).Prime := by norm_num

theorem nth_582 : Nat.nth Nat.Prime 582 = 4253 := by
  rw [← count_4253]
  exact Nat.nth_count prime_4253

theorem not_prime_4254 : ¬Nat.Prime 4254 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2127) (n := 4254)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4255 : ¬Nat.Prime 4255 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 851) (n := 4255)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4256 : ¬Nat.Prime 4256 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2128) (n := 4256)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4257 : ¬Nat.Prime 4257 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1419) (n := 4257)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4258 : ¬Nat.Prime 4258 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2129) (n := 4258)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4259 : Nat.count Nat.Prime 4259 = 583 := by
  rw [show 4259 = 4258 + 1 by norm_num, Nat.count_succ]
  rw [show 4258 = 4257 + 1 by norm_num, Nat.count_succ]
  rw [show 4257 = 4256 + 1 by norm_num, Nat.count_succ]
  rw [show 4256 = 4255 + 1 by norm_num, Nat.count_succ]
  rw [show 4255 = 4254 + 1 by norm_num, Nat.count_succ]
  rw [show 4254 = 4253 + 1 by norm_num, Nat.count_succ]
  rw [count_4253]
  simp [prime_4253, not_prime_4254, not_prime_4255, not_prime_4256, not_prime_4257, not_prime_4258]

theorem prime_4259 : (4259 : Nat).Prime := by norm_num

theorem nth_583 : Nat.nth Nat.Prime 583 = 4259 := by
  rw [← count_4259]
  exact Nat.nth_count prime_4259

theorem not_prime_4260 : ¬Nat.Prime 4260 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2130) (n := 4260)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4261 : Nat.count Nat.Prime 4261 = 584 := by
  rw [show 4261 = 4260 + 1 by norm_num, Nat.count_succ]
  rw [show 4260 = 4259 + 1 by norm_num, Nat.count_succ]
  rw [count_4259]
  simp [prime_4259, not_prime_4260]

theorem prime_4261 : (4261 : Nat).Prime := by norm_num

theorem nth_584 : Nat.nth Nat.Prime 584 = 4261 := by
  rw [← count_4261]
  exact Nat.nth_count prime_4261

theorem not_prime_4262 : ¬Nat.Prime 4262 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2131) (n := 4262)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4263 : ¬Nat.Prime 4263 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1421) (n := 4263)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4264 : ¬Nat.Prime 4264 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2132) (n := 4264)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4265 : ¬Nat.Prime 4265 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 853) (n := 4265)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4266 : ¬Nat.Prime 4266 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2133) (n := 4266)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4267 : ¬Nat.Prime 4267 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 251) (n := 4267)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4268 : ¬Nat.Prime 4268 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2134) (n := 4268)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4269 : ¬Nat.Prime 4269 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1423) (n := 4269)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4270 : ¬Nat.Prime 4270 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2135) (n := 4270)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4271 : Nat.count Nat.Prime 4271 = 585 := by
  rw [show 4271 = 4270 + 1 by norm_num, Nat.count_succ]
  rw [show 4270 = 4269 + 1 by norm_num, Nat.count_succ]
  rw [show 4269 = 4268 + 1 by norm_num, Nat.count_succ]
  rw [show 4268 = 4267 + 1 by norm_num, Nat.count_succ]
  rw [show 4267 = 4266 + 1 by norm_num, Nat.count_succ]
  rw [show 4266 = 4265 + 1 by norm_num, Nat.count_succ]
  rw [show 4265 = 4264 + 1 by norm_num, Nat.count_succ]
  rw [show 4264 = 4263 + 1 by norm_num, Nat.count_succ]
  rw [show 4263 = 4262 + 1 by norm_num, Nat.count_succ]
  rw [show 4262 = 4261 + 1 by norm_num, Nat.count_succ]
  rw [count_4261]
  simp [prime_4261, not_prime_4262, not_prime_4263, not_prime_4264, not_prime_4265, not_prime_4266, not_prime_4267, not_prime_4268, not_prime_4269, not_prime_4270]

theorem prime_4271 : (4271 : Nat).Prime := by norm_num

theorem nth_585 : Nat.nth Nat.Prime 585 = 4271 := by
  rw [← count_4271]
  exact Nat.nth_count prime_4271

theorem not_prime_4272 : ¬Nat.Prime 4272 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2136) (n := 4272)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4273 : Nat.count Nat.Prime 4273 = 586 := by
  rw [show 4273 = 4272 + 1 by norm_num, Nat.count_succ]
  rw [show 4272 = 4271 + 1 by norm_num, Nat.count_succ]
  rw [count_4271]
  simp [prime_4271, not_prime_4272]

theorem prime_4273 : (4273 : Nat).Prime := by norm_num

theorem nth_586 : Nat.nth Nat.Prime 586 = 4273 := by
  rw [← count_4273]
  exact Nat.nth_count prime_4273

theorem not_prime_4274 : ¬Nat.Prime 4274 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2137) (n := 4274)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4275 : ¬Nat.Prime 4275 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1425) (n := 4275)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4276 : ¬Nat.Prime 4276 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2138) (n := 4276)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4277 : ¬Nat.Prime 4277 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 611) (n := 4277)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4278 : ¬Nat.Prime 4278 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2139) (n := 4278)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4279 : ¬Nat.Prime 4279 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 389) (n := 4279)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4280 : ¬Nat.Prime 4280 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2140) (n := 4280)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4281 : ¬Nat.Prime 4281 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1427) (n := 4281)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4282 : ¬Nat.Prime 4282 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2141) (n := 4282)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4283 : Nat.count Nat.Prime 4283 = 587 := by
  rw [show 4283 = 4282 + 1 by norm_num, Nat.count_succ]
  rw [show 4282 = 4281 + 1 by norm_num, Nat.count_succ]
  rw [show 4281 = 4280 + 1 by norm_num, Nat.count_succ]
  rw [show 4280 = 4279 + 1 by norm_num, Nat.count_succ]
  rw [show 4279 = 4278 + 1 by norm_num, Nat.count_succ]
  rw [show 4278 = 4277 + 1 by norm_num, Nat.count_succ]
  rw [show 4277 = 4276 + 1 by norm_num, Nat.count_succ]
  rw [show 4276 = 4275 + 1 by norm_num, Nat.count_succ]
  rw [show 4275 = 4274 + 1 by norm_num, Nat.count_succ]
  rw [show 4274 = 4273 + 1 by norm_num, Nat.count_succ]
  rw [count_4273]
  simp [prime_4273, not_prime_4274, not_prime_4275, not_prime_4276, not_prime_4277, not_prime_4278, not_prime_4279, not_prime_4280, not_prime_4281, not_prime_4282]

theorem prime_4283 : (4283 : Nat).Prime := by norm_num

theorem nth_587 : Nat.nth Nat.Prime 587 = 4283 := by
  rw [← count_4283]
  exact Nat.nth_count prime_4283

theorem not_prime_4284 : ¬Nat.Prime 4284 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2142) (n := 4284)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4285 : ¬Nat.Prime 4285 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 857) (n := 4285)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4286 : ¬Nat.Prime 4286 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2143) (n := 4286)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4287 : ¬Nat.Prime 4287 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1429) (n := 4287)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4288 : ¬Nat.Prime 4288 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2144) (n := 4288)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4289 : Nat.count Nat.Prime 4289 = 588 := by
  rw [show 4289 = 4288 + 1 by norm_num, Nat.count_succ]
  rw [show 4288 = 4287 + 1 by norm_num, Nat.count_succ]
  rw [show 4287 = 4286 + 1 by norm_num, Nat.count_succ]
  rw [show 4286 = 4285 + 1 by norm_num, Nat.count_succ]
  rw [show 4285 = 4284 + 1 by norm_num, Nat.count_succ]
  rw [show 4284 = 4283 + 1 by norm_num, Nat.count_succ]
  rw [count_4283]
  simp [prime_4283, not_prime_4284, not_prime_4285, not_prime_4286, not_prime_4287, not_prime_4288]

theorem prime_4289 : (4289 : Nat).Prime := by norm_num

theorem nth_588 : Nat.nth Nat.Prime 588 = 4289 := by
  rw [← count_4289]
  exact Nat.nth_count prime_4289

theorem not_prime_4290 : ¬Nat.Prime 4290 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2145) (n := 4290)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4291 : ¬Nat.Prime 4291 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 613) (n := 4291)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4292 : ¬Nat.Prime 4292 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2146) (n := 4292)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4293 : ¬Nat.Prime 4293 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1431) (n := 4293)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4294 : ¬Nat.Prime 4294 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2147) (n := 4294)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4295 : ¬Nat.Prime 4295 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 859) (n := 4295)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4296 : ¬Nat.Prime 4296 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2148) (n := 4296)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4297 : Nat.count Nat.Prime 4297 = 589 := by
  rw [show 4297 = 4296 + 1 by norm_num, Nat.count_succ]
  rw [show 4296 = 4295 + 1 by norm_num, Nat.count_succ]
  rw [show 4295 = 4294 + 1 by norm_num, Nat.count_succ]
  rw [show 4294 = 4293 + 1 by norm_num, Nat.count_succ]
  rw [show 4293 = 4292 + 1 by norm_num, Nat.count_succ]
  rw [show 4292 = 4291 + 1 by norm_num, Nat.count_succ]
  rw [show 4291 = 4290 + 1 by norm_num, Nat.count_succ]
  rw [show 4290 = 4289 + 1 by norm_num, Nat.count_succ]
  rw [count_4289]
  simp [prime_4289, not_prime_4290, not_prime_4291, not_prime_4292, not_prime_4293, not_prime_4294, not_prime_4295, not_prime_4296]

theorem prime_4297 : (4297 : Nat).Prime := by norm_num

theorem nth_589 : Nat.nth Nat.Prime 589 = 4297 := by
  rw [← count_4297]
  exact Nat.nth_count prime_4297

theorem not_prime_4298 : ¬Nat.Prime 4298 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2149) (n := 4298)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4299 : ¬Nat.Prime 4299 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1433) (n := 4299)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4300 : ¬Nat.Prime 4300 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2150) (n := 4300)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4301 : ¬Nat.Prime 4301 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 391) (n := 4301)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4302 : ¬Nat.Prime 4302 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2151) (n := 4302)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4303 : ¬Nat.Prime 4303 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 331) (n := 4303)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4304 : ¬Nat.Prime 4304 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2152) (n := 4304)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4305 : ¬Nat.Prime 4305 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1435) (n := 4305)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4306 : ¬Nat.Prime 4306 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2153) (n := 4306)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4307 : ¬Nat.Prime 4307 :=
  Nat.not_prime_of_mul_eq (a := 59) (b := 73) (n := 4307)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4308 : ¬Nat.Prime 4308 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2154) (n := 4308)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4309 : ¬Nat.Prime 4309 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 139) (n := 4309)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4310 : ¬Nat.Prime 4310 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2155) (n := 4310)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4311 : ¬Nat.Prime 4311 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1437) (n := 4311)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4312 : ¬Nat.Prime 4312 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2156) (n := 4312)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4313 : ¬Nat.Prime 4313 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 227) (n := 4313)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4314 : ¬Nat.Prime 4314 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2157) (n := 4314)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4315 : ¬Nat.Prime 4315 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 863) (n := 4315)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4316 : ¬Nat.Prime 4316 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2158) (n := 4316)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4317 : ¬Nat.Prime 4317 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1439) (n := 4317)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4318 : ¬Nat.Prime 4318 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2159) (n := 4318)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4319 : ¬Nat.Prime 4319 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 617) (n := 4319)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4320 : ¬Nat.Prime 4320 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2160) (n := 4320)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4321 : ¬Nat.Prime 4321 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 149) (n := 4321)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4322 : ¬Nat.Prime 4322 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2161) (n := 4322)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4323 : ¬Nat.Prime 4323 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1441) (n := 4323)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4324 : ¬Nat.Prime 4324 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2162) (n := 4324)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4325 : ¬Nat.Prime 4325 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 865) (n := 4325)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4326 : ¬Nat.Prime 4326 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2163) (n := 4326)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4327 : Nat.count Nat.Prime 4327 = 590 := by
  rw [show 4327 = 4326 + 1 by norm_num, Nat.count_succ]
  rw [show 4326 = 4325 + 1 by norm_num, Nat.count_succ]
  rw [show 4325 = 4324 + 1 by norm_num, Nat.count_succ]
  rw [show 4324 = 4323 + 1 by norm_num, Nat.count_succ]
  rw [show 4323 = 4322 + 1 by norm_num, Nat.count_succ]
  rw [show 4322 = 4321 + 1 by norm_num, Nat.count_succ]
  rw [show 4321 = 4320 + 1 by norm_num, Nat.count_succ]
  rw [show 4320 = 4319 + 1 by norm_num, Nat.count_succ]
  rw [show 4319 = 4318 + 1 by norm_num, Nat.count_succ]
  rw [show 4318 = 4317 + 1 by norm_num, Nat.count_succ]
  rw [show 4317 = 4316 + 1 by norm_num, Nat.count_succ]
  rw [show 4316 = 4315 + 1 by norm_num, Nat.count_succ]
  rw [show 4315 = 4314 + 1 by norm_num, Nat.count_succ]
  rw [show 4314 = 4313 + 1 by norm_num, Nat.count_succ]
  rw [show 4313 = 4312 + 1 by norm_num, Nat.count_succ]
  rw [show 4312 = 4311 + 1 by norm_num, Nat.count_succ]
  rw [show 4311 = 4310 + 1 by norm_num, Nat.count_succ]
  rw [show 4310 = 4309 + 1 by norm_num, Nat.count_succ]
  rw [show 4309 = 4308 + 1 by norm_num, Nat.count_succ]
  rw [show 4308 = 4307 + 1 by norm_num, Nat.count_succ]
  rw [show 4307 = 4306 + 1 by norm_num, Nat.count_succ]
  rw [show 4306 = 4305 + 1 by norm_num, Nat.count_succ]
  rw [show 4305 = 4304 + 1 by norm_num, Nat.count_succ]
  rw [show 4304 = 4303 + 1 by norm_num, Nat.count_succ]
  rw [show 4303 = 4302 + 1 by norm_num, Nat.count_succ]
  rw [show 4302 = 4301 + 1 by norm_num, Nat.count_succ]
  rw [show 4301 = 4300 + 1 by norm_num, Nat.count_succ]
  rw [show 4300 = 4299 + 1 by norm_num, Nat.count_succ]
  rw [show 4299 = 4298 + 1 by norm_num, Nat.count_succ]
  rw [show 4298 = 4297 + 1 by norm_num, Nat.count_succ]
  rw [count_4297]
  simp [prime_4297, not_prime_4298, not_prime_4299, not_prime_4300, not_prime_4301, not_prime_4302, not_prime_4303, not_prime_4304, not_prime_4305, not_prime_4306, not_prime_4307, not_prime_4308, not_prime_4309, not_prime_4310, not_prime_4311, not_prime_4312, not_prime_4313, not_prime_4314, not_prime_4315, not_prime_4316, not_prime_4317, not_prime_4318, not_prime_4319, not_prime_4320, not_prime_4321, not_prime_4322, not_prime_4323, not_prime_4324, not_prime_4325, not_prime_4326]

theorem prime_4327 : (4327 : Nat).Prime := by norm_num

theorem nth_590 : Nat.nth Nat.Prime 590 = 4327 := by
  rw [← count_4327]
  exact Nat.nth_count prime_4327

theorem not_prime_4328 : ¬Nat.Prime 4328 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2164) (n := 4328)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4329 : ¬Nat.Prime 4329 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1443) (n := 4329)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4330 : ¬Nat.Prime 4330 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2165) (n := 4330)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4331 : ¬Nat.Prime 4331 :=
  Nat.not_prime_of_mul_eq (a := 61) (b := 71) (n := 4331)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4332 : ¬Nat.Prime 4332 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2166) (n := 4332)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4333 : ¬Nat.Prime 4333 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 619) (n := 4333)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4334 : ¬Nat.Prime 4334 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2167) (n := 4334)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4335 : ¬Nat.Prime 4335 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1445) (n := 4335)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4336 : ¬Nat.Prime 4336 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2168) (n := 4336)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4337 : Nat.count Nat.Prime 4337 = 591 := by
  rw [show 4337 = 4336 + 1 by norm_num, Nat.count_succ]
  rw [show 4336 = 4335 + 1 by norm_num, Nat.count_succ]
  rw [show 4335 = 4334 + 1 by norm_num, Nat.count_succ]
  rw [show 4334 = 4333 + 1 by norm_num, Nat.count_succ]
  rw [show 4333 = 4332 + 1 by norm_num, Nat.count_succ]
  rw [show 4332 = 4331 + 1 by norm_num, Nat.count_succ]
  rw [show 4331 = 4330 + 1 by norm_num, Nat.count_succ]
  rw [show 4330 = 4329 + 1 by norm_num, Nat.count_succ]
  rw [show 4329 = 4328 + 1 by norm_num, Nat.count_succ]
  rw [show 4328 = 4327 + 1 by norm_num, Nat.count_succ]
  rw [count_4327]
  simp [prime_4327, not_prime_4328, not_prime_4329, not_prime_4330, not_prime_4331, not_prime_4332, not_prime_4333, not_prime_4334, not_prime_4335, not_prime_4336]

theorem prime_4337 : (4337 : Nat).Prime := by norm_num

theorem nth_591 : Nat.nth Nat.Prime 591 = 4337 := by
  rw [← count_4337]
  exact Nat.nth_count prime_4337

theorem not_prime_4338 : ¬Nat.Prime 4338 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2169) (n := 4338)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4339 : Nat.count Nat.Prime 4339 = 592 := by
  rw [show 4339 = 4338 + 1 by norm_num, Nat.count_succ]
  rw [show 4338 = 4337 + 1 by norm_num, Nat.count_succ]
  rw [count_4337]
  simp [prime_4337, not_prime_4338]

theorem prime_4339 : (4339 : Nat).Prime := by norm_num

theorem nth_592 : Nat.nth Nat.Prime 592 = 4339 := by
  rw [← count_4339]
  exact Nat.nth_count prime_4339

theorem not_prime_4340 : ¬Nat.Prime 4340 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2170) (n := 4340)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4341 : ¬Nat.Prime 4341 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1447) (n := 4341)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4342 : ¬Nat.Prime 4342 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2171) (n := 4342)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4343 : ¬Nat.Prime 4343 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 101) (n := 4343)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4344 : ¬Nat.Prime 4344 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2172) (n := 4344)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4345 : ¬Nat.Prime 4345 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 869) (n := 4345)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4346 : ¬Nat.Prime 4346 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2173) (n := 4346)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4347 : ¬Nat.Prime 4347 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1449) (n := 4347)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4348 : ¬Nat.Prime 4348 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2174) (n := 4348)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4349 : Nat.count Nat.Prime 4349 = 593 := by
  rw [show 4349 = 4348 + 1 by norm_num, Nat.count_succ]
  rw [show 4348 = 4347 + 1 by norm_num, Nat.count_succ]
  rw [show 4347 = 4346 + 1 by norm_num, Nat.count_succ]
  rw [show 4346 = 4345 + 1 by norm_num, Nat.count_succ]
  rw [show 4345 = 4344 + 1 by norm_num, Nat.count_succ]
  rw [show 4344 = 4343 + 1 by norm_num, Nat.count_succ]
  rw [show 4343 = 4342 + 1 by norm_num, Nat.count_succ]
  rw [show 4342 = 4341 + 1 by norm_num, Nat.count_succ]
  rw [show 4341 = 4340 + 1 by norm_num, Nat.count_succ]
  rw [show 4340 = 4339 + 1 by norm_num, Nat.count_succ]
  rw [count_4339]
  simp [prime_4339, not_prime_4340, not_prime_4341, not_prime_4342, not_prime_4343, not_prime_4344, not_prime_4345, not_prime_4346, not_prime_4347, not_prime_4348]

theorem prime_4349 : (4349 : Nat).Prime := by norm_num

theorem nth_593 : Nat.nth Nat.Prime 593 = 4349 := by
  rw [← count_4349]
  exact Nat.nth_count prime_4349

theorem not_prime_4350 : ¬Nat.Prime 4350 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2175) (n := 4350)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4351 : ¬Nat.Prime 4351 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 229) (n := 4351)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4352 : ¬Nat.Prime 4352 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2176) (n := 4352)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4353 : ¬Nat.Prime 4353 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1451) (n := 4353)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4354 : ¬Nat.Prime 4354 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2177) (n := 4354)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4355 : ¬Nat.Prime 4355 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 871) (n := 4355)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4356 : ¬Nat.Prime 4356 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2178) (n := 4356)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4357 : Nat.count Nat.Prime 4357 = 594 := by
  rw [show 4357 = 4356 + 1 by norm_num, Nat.count_succ]
  rw [show 4356 = 4355 + 1 by norm_num, Nat.count_succ]
  rw [show 4355 = 4354 + 1 by norm_num, Nat.count_succ]
  rw [show 4354 = 4353 + 1 by norm_num, Nat.count_succ]
  rw [show 4353 = 4352 + 1 by norm_num, Nat.count_succ]
  rw [show 4352 = 4351 + 1 by norm_num, Nat.count_succ]
  rw [show 4351 = 4350 + 1 by norm_num, Nat.count_succ]
  rw [show 4350 = 4349 + 1 by norm_num, Nat.count_succ]
  rw [count_4349]
  simp [prime_4349, not_prime_4350, not_prime_4351, not_prime_4352, not_prime_4353, not_prime_4354, not_prime_4355, not_prime_4356]

theorem prime_4357 : (4357 : Nat).Prime := by norm_num

theorem nth_594 : Nat.nth Nat.Prime 594 = 4357 := by
  rw [← count_4357]
  exact Nat.nth_count prime_4357

theorem not_prime_4358 : ¬Nat.Prime 4358 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2179) (n := 4358)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4359 : ¬Nat.Prime 4359 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1453) (n := 4359)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4360 : ¬Nat.Prime 4360 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2180) (n := 4360)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4361 : ¬Nat.Prime 4361 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 623) (n := 4361)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4362 : ¬Nat.Prime 4362 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2181) (n := 4362)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4363 : Nat.count Nat.Prime 4363 = 595 := by
  rw [show 4363 = 4362 + 1 by norm_num, Nat.count_succ]
  rw [show 4362 = 4361 + 1 by norm_num, Nat.count_succ]
  rw [show 4361 = 4360 + 1 by norm_num, Nat.count_succ]
  rw [show 4360 = 4359 + 1 by norm_num, Nat.count_succ]
  rw [show 4359 = 4358 + 1 by norm_num, Nat.count_succ]
  rw [show 4358 = 4357 + 1 by norm_num, Nat.count_succ]
  rw [count_4357]
  simp [prime_4357, not_prime_4358, not_prime_4359, not_prime_4360, not_prime_4361, not_prime_4362]

theorem prime_4363 : (4363 : Nat).Prime := by norm_num

theorem nth_595 : Nat.nth Nat.Prime 595 = 4363 := by
  rw [← count_4363]
  exact Nat.nth_count prime_4363

theorem not_prime_4364 : ¬Nat.Prime 4364 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2182) (n := 4364)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4365 : ¬Nat.Prime 4365 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1455) (n := 4365)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4366 : ¬Nat.Prime 4366 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2183) (n := 4366)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4367 : ¬Nat.Prime 4367 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 397) (n := 4367)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4368 : ¬Nat.Prime 4368 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2184) (n := 4368)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4369 : ¬Nat.Prime 4369 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 257) (n := 4369)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4370 : ¬Nat.Prime 4370 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2185) (n := 4370)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4371 : ¬Nat.Prime 4371 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1457) (n := 4371)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4372 : ¬Nat.Prime 4372 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2186) (n := 4372)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4373 : Nat.count Nat.Prime 4373 = 596 := by
  rw [show 4373 = 4372 + 1 by norm_num, Nat.count_succ]
  rw [show 4372 = 4371 + 1 by norm_num, Nat.count_succ]
  rw [show 4371 = 4370 + 1 by norm_num, Nat.count_succ]
  rw [show 4370 = 4369 + 1 by norm_num, Nat.count_succ]
  rw [show 4369 = 4368 + 1 by norm_num, Nat.count_succ]
  rw [show 4368 = 4367 + 1 by norm_num, Nat.count_succ]
  rw [show 4367 = 4366 + 1 by norm_num, Nat.count_succ]
  rw [show 4366 = 4365 + 1 by norm_num, Nat.count_succ]
  rw [show 4365 = 4364 + 1 by norm_num, Nat.count_succ]
  rw [show 4364 = 4363 + 1 by norm_num, Nat.count_succ]
  rw [count_4363]
  simp [prime_4363, not_prime_4364, not_prime_4365, not_prime_4366, not_prime_4367, not_prime_4368, not_prime_4369, not_prime_4370, not_prime_4371, not_prime_4372]

theorem prime_4373 : (4373 : Nat).Prime := by norm_num

theorem nth_596 : Nat.nth Nat.Prime 596 = 4373 := by
  rw [← count_4373]
  exact Nat.nth_count prime_4373

theorem not_prime_4374 : ¬Nat.Prime 4374 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2187) (n := 4374)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4375 : ¬Nat.Prime 4375 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 875) (n := 4375)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4376 : ¬Nat.Prime 4376 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2188) (n := 4376)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4377 : ¬Nat.Prime 4377 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1459) (n := 4377)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4378 : ¬Nat.Prime 4378 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2189) (n := 4378)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4379 : ¬Nat.Prime 4379 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 151) (n := 4379)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4380 : ¬Nat.Prime 4380 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2190) (n := 4380)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4381 : ¬Nat.Prime 4381 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 337) (n := 4381)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4382 : ¬Nat.Prime 4382 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2191) (n := 4382)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4383 : ¬Nat.Prime 4383 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1461) (n := 4383)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4384 : ¬Nat.Prime 4384 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2192) (n := 4384)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4385 : ¬Nat.Prime 4385 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 877) (n := 4385)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4386 : ¬Nat.Prime 4386 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2193) (n := 4386)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4387 : ¬Nat.Prime 4387 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 107) (n := 4387)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4388 : ¬Nat.Prime 4388 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2194) (n := 4388)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4389 : ¬Nat.Prime 4389 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1463) (n := 4389)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4390 : ¬Nat.Prime 4390 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2195) (n := 4390)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4391 : Nat.count Nat.Prime 4391 = 597 := by
  rw [show 4391 = 4390 + 1 by norm_num, Nat.count_succ]
  rw [show 4390 = 4389 + 1 by norm_num, Nat.count_succ]
  rw [show 4389 = 4388 + 1 by norm_num, Nat.count_succ]
  rw [show 4388 = 4387 + 1 by norm_num, Nat.count_succ]
  rw [show 4387 = 4386 + 1 by norm_num, Nat.count_succ]
  rw [show 4386 = 4385 + 1 by norm_num, Nat.count_succ]
  rw [show 4385 = 4384 + 1 by norm_num, Nat.count_succ]
  rw [show 4384 = 4383 + 1 by norm_num, Nat.count_succ]
  rw [show 4383 = 4382 + 1 by norm_num, Nat.count_succ]
  rw [show 4382 = 4381 + 1 by norm_num, Nat.count_succ]
  rw [show 4381 = 4380 + 1 by norm_num, Nat.count_succ]
  rw [show 4380 = 4379 + 1 by norm_num, Nat.count_succ]
  rw [show 4379 = 4378 + 1 by norm_num, Nat.count_succ]
  rw [show 4378 = 4377 + 1 by norm_num, Nat.count_succ]
  rw [show 4377 = 4376 + 1 by norm_num, Nat.count_succ]
  rw [show 4376 = 4375 + 1 by norm_num, Nat.count_succ]
  rw [show 4375 = 4374 + 1 by norm_num, Nat.count_succ]
  rw [show 4374 = 4373 + 1 by norm_num, Nat.count_succ]
  rw [count_4373]
  simp [prime_4373, not_prime_4374, not_prime_4375, not_prime_4376, not_prime_4377, not_prime_4378, not_prime_4379, not_prime_4380, not_prime_4381, not_prime_4382, not_prime_4383, not_prime_4384, not_prime_4385, not_prime_4386, not_prime_4387, not_prime_4388, not_prime_4389, not_prime_4390]

theorem prime_4391 : (4391 : Nat).Prime := by norm_num

theorem nth_597 : Nat.nth Nat.Prime 597 = 4391 := by
  rw [← count_4391]
  exact Nat.nth_count prime_4391

theorem not_prime_4392 : ¬Nat.Prime 4392 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2196) (n := 4392)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4393 : ¬Nat.Prime 4393 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 191) (n := 4393)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4394 : ¬Nat.Prime 4394 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2197) (n := 4394)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4395 : ¬Nat.Prime 4395 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1465) (n := 4395)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4396 : ¬Nat.Prime 4396 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2198) (n := 4396)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4397 : Nat.count Nat.Prime 4397 = 598 := by
  rw [show 4397 = 4396 + 1 by norm_num, Nat.count_succ]
  rw [show 4396 = 4395 + 1 by norm_num, Nat.count_succ]
  rw [show 4395 = 4394 + 1 by norm_num, Nat.count_succ]
  rw [show 4394 = 4393 + 1 by norm_num, Nat.count_succ]
  rw [show 4393 = 4392 + 1 by norm_num, Nat.count_succ]
  rw [show 4392 = 4391 + 1 by norm_num, Nat.count_succ]
  rw [count_4391]
  simp [prime_4391, not_prime_4392, not_prime_4393, not_prime_4394, not_prime_4395, not_prime_4396]

theorem prime_4397 : (4397 : Nat).Prime := by norm_num

theorem nth_598 : Nat.nth Nat.Prime 598 = 4397 := by
  rw [← count_4397]
  exact Nat.nth_count prime_4397

theorem not_prime_4398 : ¬Nat.Prime 4398 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2199) (n := 4398)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4399 : ¬Nat.Prime 4399 :=
  Nat.not_prime_of_mul_eq (a := 53) (b := 83) (n := 4399)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4400 : ¬Nat.Prime 4400 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2200) (n := 4400)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4401 : ¬Nat.Prime 4401 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1467) (n := 4401)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4402 : ¬Nat.Prime 4402 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2201) (n := 4402)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4403 : ¬Nat.Prime 4403 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 629) (n := 4403)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4404 : ¬Nat.Prime 4404 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2202) (n := 4404)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4405 : ¬Nat.Prime 4405 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 881) (n := 4405)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4406 : ¬Nat.Prime 4406 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2203) (n := 4406)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4407 : ¬Nat.Prime 4407 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1469) (n := 4407)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4408 : ¬Nat.Prime 4408 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2204) (n := 4408)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4409 : Nat.count Nat.Prime 4409 = 599 := by
  rw [show 4409 = 4408 + 1 by norm_num, Nat.count_succ]
  rw [show 4408 = 4407 + 1 by norm_num, Nat.count_succ]
  rw [show 4407 = 4406 + 1 by norm_num, Nat.count_succ]
  rw [show 4406 = 4405 + 1 by norm_num, Nat.count_succ]
  rw [show 4405 = 4404 + 1 by norm_num, Nat.count_succ]
  rw [show 4404 = 4403 + 1 by norm_num, Nat.count_succ]
  rw [show 4403 = 4402 + 1 by norm_num, Nat.count_succ]
  rw [show 4402 = 4401 + 1 by norm_num, Nat.count_succ]
  rw [show 4401 = 4400 + 1 by norm_num, Nat.count_succ]
  rw [show 4400 = 4399 + 1 by norm_num, Nat.count_succ]
  rw [show 4399 = 4398 + 1 by norm_num, Nat.count_succ]
  rw [show 4398 = 4397 + 1 by norm_num, Nat.count_succ]
  rw [count_4397]
  simp [prime_4397, not_prime_4398, not_prime_4399, not_prime_4400, not_prime_4401, not_prime_4402, not_prime_4403, not_prime_4404, not_prime_4405, not_prime_4406, not_prime_4407, not_prime_4408]

theorem prime_4409 : (4409 : Nat).Prime := by norm_num

theorem nth_599 : Nat.nth Nat.Prime 599 = 4409 := by
  rw [← count_4409]
  exact Nat.nth_count prime_4409

end OeisA100474.PrimeCertificate
