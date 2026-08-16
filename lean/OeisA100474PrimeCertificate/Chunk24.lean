import OeisA100474PrimeCertificate.Chunk23

/-! Kernel prime/count certificate, chunk 24 (600–624). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_4410 : ¬Nat.Prime 4410 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2205) (n := 4410)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4411 : ¬Nat.Prime 4411 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 401) (n := 4411)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4412 : ¬Nat.Prime 4412 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2206) (n := 4412)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4413 : ¬Nat.Prime 4413 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1471) (n := 4413)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4414 : ¬Nat.Prime 4414 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2207) (n := 4414)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4415 : ¬Nat.Prime 4415 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 883) (n := 4415)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4416 : ¬Nat.Prime 4416 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2208) (n := 4416)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4417 : ¬Nat.Prime 4417 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 631) (n := 4417)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4418 : ¬Nat.Prime 4418 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2209) (n := 4418)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4419 : ¬Nat.Prime 4419 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1473) (n := 4419)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4420 : ¬Nat.Prime 4420 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2210) (n := 4420)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4421 : Nat.count Nat.Prime 4421 = 600 := by
  rw [show 4421 = 4420 + 1 by norm_num, Nat.count_succ]
  rw [show 4420 = 4419 + 1 by norm_num, Nat.count_succ]
  rw [show 4419 = 4418 + 1 by norm_num, Nat.count_succ]
  rw [show 4418 = 4417 + 1 by norm_num, Nat.count_succ]
  rw [show 4417 = 4416 + 1 by norm_num, Nat.count_succ]
  rw [show 4416 = 4415 + 1 by norm_num, Nat.count_succ]
  rw [show 4415 = 4414 + 1 by norm_num, Nat.count_succ]
  rw [show 4414 = 4413 + 1 by norm_num, Nat.count_succ]
  rw [show 4413 = 4412 + 1 by norm_num, Nat.count_succ]
  rw [show 4412 = 4411 + 1 by norm_num, Nat.count_succ]
  rw [show 4411 = 4410 + 1 by norm_num, Nat.count_succ]
  rw [show 4410 = 4409 + 1 by norm_num, Nat.count_succ]
  rw [count_4409]
  simp [prime_4409, not_prime_4410, not_prime_4411, not_prime_4412, not_prime_4413, not_prime_4414, not_prime_4415, not_prime_4416, not_prime_4417, not_prime_4418, not_prime_4419, not_prime_4420]

theorem prime_4421 : (4421 : Nat).Prime := by norm_num

theorem nth_600 : Nat.nth Nat.Prime 600 = 4421 := by
  rw [← count_4421]
  exact Nat.nth_count prime_4421

theorem not_prime_4422 : ¬Nat.Prime 4422 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2211) (n := 4422)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4423 : Nat.count Nat.Prime 4423 = 601 := by
  rw [show 4423 = 4422 + 1 by norm_num, Nat.count_succ]
  rw [show 4422 = 4421 + 1 by norm_num, Nat.count_succ]
  rw [count_4421]
  simp [prime_4421, not_prime_4422]

theorem prime_4423 : (4423 : Nat).Prime := by norm_num

theorem nth_601 : Nat.nth Nat.Prime 601 = 4423 := by
  rw [← count_4423]
  exact Nat.nth_count prime_4423

theorem not_prime_4424 : ¬Nat.Prime 4424 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2212) (n := 4424)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4425 : ¬Nat.Prime 4425 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1475) (n := 4425)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4426 : ¬Nat.Prime 4426 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2213) (n := 4426)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4427 : ¬Nat.Prime 4427 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 233) (n := 4427)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4428 : ¬Nat.Prime 4428 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2214) (n := 4428)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4429 : ¬Nat.Prime 4429 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 103) (n := 4429)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4430 : ¬Nat.Prime 4430 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2215) (n := 4430)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4431 : ¬Nat.Prime 4431 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1477) (n := 4431)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4432 : ¬Nat.Prime 4432 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2216) (n := 4432)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4433 : ¬Nat.Prime 4433 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 403) (n := 4433)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4434 : ¬Nat.Prime 4434 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2217) (n := 4434)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4435 : ¬Nat.Prime 4435 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 887) (n := 4435)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4436 : ¬Nat.Prime 4436 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2218) (n := 4436)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4437 : ¬Nat.Prime 4437 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1479) (n := 4437)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4438 : ¬Nat.Prime 4438 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2219) (n := 4438)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4439 : ¬Nat.Prime 4439 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 193) (n := 4439)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4440 : ¬Nat.Prime 4440 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2220) (n := 4440)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4441 : Nat.count Nat.Prime 4441 = 602 := by
  rw [show 4441 = 4440 + 1 by norm_num, Nat.count_succ]
  rw [show 4440 = 4439 + 1 by norm_num, Nat.count_succ]
  rw [show 4439 = 4438 + 1 by norm_num, Nat.count_succ]
  rw [show 4438 = 4437 + 1 by norm_num, Nat.count_succ]
  rw [show 4437 = 4436 + 1 by norm_num, Nat.count_succ]
  rw [show 4436 = 4435 + 1 by norm_num, Nat.count_succ]
  rw [show 4435 = 4434 + 1 by norm_num, Nat.count_succ]
  rw [show 4434 = 4433 + 1 by norm_num, Nat.count_succ]
  rw [show 4433 = 4432 + 1 by norm_num, Nat.count_succ]
  rw [show 4432 = 4431 + 1 by norm_num, Nat.count_succ]
  rw [show 4431 = 4430 + 1 by norm_num, Nat.count_succ]
  rw [show 4430 = 4429 + 1 by norm_num, Nat.count_succ]
  rw [show 4429 = 4428 + 1 by norm_num, Nat.count_succ]
  rw [show 4428 = 4427 + 1 by norm_num, Nat.count_succ]
  rw [show 4427 = 4426 + 1 by norm_num, Nat.count_succ]
  rw [show 4426 = 4425 + 1 by norm_num, Nat.count_succ]
  rw [show 4425 = 4424 + 1 by norm_num, Nat.count_succ]
  rw [show 4424 = 4423 + 1 by norm_num, Nat.count_succ]
  rw [count_4423]
  simp [prime_4423, not_prime_4424, not_prime_4425, not_prime_4426, not_prime_4427, not_prime_4428, not_prime_4429, not_prime_4430, not_prime_4431, not_prime_4432, not_prime_4433, not_prime_4434, not_prime_4435, not_prime_4436, not_prime_4437, not_prime_4438, not_prime_4439, not_prime_4440]

theorem prime_4441 : (4441 : Nat).Prime := by norm_num

theorem nth_602 : Nat.nth Nat.Prime 602 = 4441 := by
  rw [← count_4441]
  exact Nat.nth_count prime_4441

theorem not_prime_4442 : ¬Nat.Prime 4442 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2221) (n := 4442)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4443 : ¬Nat.Prime 4443 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1481) (n := 4443)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4444 : ¬Nat.Prime 4444 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2222) (n := 4444)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4445 : ¬Nat.Prime 4445 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 889) (n := 4445)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4446 : ¬Nat.Prime 4446 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2223) (n := 4446)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4447 : Nat.count Nat.Prime 4447 = 603 := by
  rw [show 4447 = 4446 + 1 by norm_num, Nat.count_succ]
  rw [show 4446 = 4445 + 1 by norm_num, Nat.count_succ]
  rw [show 4445 = 4444 + 1 by norm_num, Nat.count_succ]
  rw [show 4444 = 4443 + 1 by norm_num, Nat.count_succ]
  rw [show 4443 = 4442 + 1 by norm_num, Nat.count_succ]
  rw [show 4442 = 4441 + 1 by norm_num, Nat.count_succ]
  rw [count_4441]
  simp [prime_4441, not_prime_4442, not_prime_4443, not_prime_4444, not_prime_4445, not_prime_4446]

theorem prime_4447 : (4447 : Nat).Prime := by norm_num

theorem nth_603 : Nat.nth Nat.Prime 603 = 4447 := by
  rw [← count_4447]
  exact Nat.nth_count prime_4447

theorem not_prime_4448 : ¬Nat.Prime 4448 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2224) (n := 4448)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4449 : ¬Nat.Prime 4449 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1483) (n := 4449)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4450 : ¬Nat.Prime 4450 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2225) (n := 4450)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4451 : Nat.count Nat.Prime 4451 = 604 := by
  rw [show 4451 = 4450 + 1 by norm_num, Nat.count_succ]
  rw [show 4450 = 4449 + 1 by norm_num, Nat.count_succ]
  rw [show 4449 = 4448 + 1 by norm_num, Nat.count_succ]
  rw [show 4448 = 4447 + 1 by norm_num, Nat.count_succ]
  rw [count_4447]
  simp [prime_4447, not_prime_4448, not_prime_4449, not_prime_4450]

theorem prime_4451 : (4451 : Nat).Prime := by norm_num

theorem nth_604 : Nat.nth Nat.Prime 604 = 4451 := by
  rw [← count_4451]
  exact Nat.nth_count prime_4451

theorem not_prime_4452 : ¬Nat.Prime 4452 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2226) (n := 4452)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4453 : ¬Nat.Prime 4453 :=
  Nat.not_prime_of_mul_eq (a := 61) (b := 73) (n := 4453)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4454 : ¬Nat.Prime 4454 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2227) (n := 4454)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4455 : ¬Nat.Prime 4455 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1485) (n := 4455)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4456 : ¬Nat.Prime 4456 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2228) (n := 4456)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4457 : Nat.count Nat.Prime 4457 = 605 := by
  rw [show 4457 = 4456 + 1 by norm_num, Nat.count_succ]
  rw [show 4456 = 4455 + 1 by norm_num, Nat.count_succ]
  rw [show 4455 = 4454 + 1 by norm_num, Nat.count_succ]
  rw [show 4454 = 4453 + 1 by norm_num, Nat.count_succ]
  rw [show 4453 = 4452 + 1 by norm_num, Nat.count_succ]
  rw [show 4452 = 4451 + 1 by norm_num, Nat.count_succ]
  rw [count_4451]
  simp [prime_4451, not_prime_4452, not_prime_4453, not_prime_4454, not_prime_4455, not_prime_4456]

theorem prime_4457 : (4457 : Nat).Prime := by norm_num

theorem nth_605 : Nat.nth Nat.Prime 605 = 4457 := by
  rw [← count_4457]
  exact Nat.nth_count prime_4457

theorem not_prime_4458 : ¬Nat.Prime 4458 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2229) (n := 4458)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4459 : ¬Nat.Prime 4459 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 637) (n := 4459)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4460 : ¬Nat.Prime 4460 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2230) (n := 4460)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4461 : ¬Nat.Prime 4461 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1487) (n := 4461)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4462 : ¬Nat.Prime 4462 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2231) (n := 4462)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4463 : Nat.count Nat.Prime 4463 = 606 := by
  rw [show 4463 = 4462 + 1 by norm_num, Nat.count_succ]
  rw [show 4462 = 4461 + 1 by norm_num, Nat.count_succ]
  rw [show 4461 = 4460 + 1 by norm_num, Nat.count_succ]
  rw [show 4460 = 4459 + 1 by norm_num, Nat.count_succ]
  rw [show 4459 = 4458 + 1 by norm_num, Nat.count_succ]
  rw [show 4458 = 4457 + 1 by norm_num, Nat.count_succ]
  rw [count_4457]
  simp [prime_4457, not_prime_4458, not_prime_4459, not_prime_4460, not_prime_4461, not_prime_4462]

theorem prime_4463 : (4463 : Nat).Prime := by norm_num

theorem nth_606 : Nat.nth Nat.Prime 606 = 4463 := by
  rw [← count_4463]
  exact Nat.nth_count prime_4463

theorem not_prime_4464 : ¬Nat.Prime 4464 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2232) (n := 4464)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4465 : ¬Nat.Prime 4465 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 893) (n := 4465)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4466 : ¬Nat.Prime 4466 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2233) (n := 4466)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4467 : ¬Nat.Prime 4467 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1489) (n := 4467)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4468 : ¬Nat.Prime 4468 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2234) (n := 4468)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4469 : ¬Nat.Prime 4469 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 109) (n := 4469)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4470 : ¬Nat.Prime 4470 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2235) (n := 4470)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4471 : ¬Nat.Prime 4471 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 263) (n := 4471)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4472 : ¬Nat.Prime 4472 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2236) (n := 4472)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4473 : ¬Nat.Prime 4473 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1491) (n := 4473)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4474 : ¬Nat.Prime 4474 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2237) (n := 4474)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4475 : ¬Nat.Prime 4475 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 895) (n := 4475)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4476 : ¬Nat.Prime 4476 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2238) (n := 4476)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4477 : ¬Nat.Prime 4477 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 407) (n := 4477)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4478 : ¬Nat.Prime 4478 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2239) (n := 4478)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4479 : ¬Nat.Prime 4479 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1493) (n := 4479)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4480 : ¬Nat.Prime 4480 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2240) (n := 4480)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4481 : Nat.count Nat.Prime 4481 = 607 := by
  rw [show 4481 = 4480 + 1 by norm_num, Nat.count_succ]
  rw [show 4480 = 4479 + 1 by norm_num, Nat.count_succ]
  rw [show 4479 = 4478 + 1 by norm_num, Nat.count_succ]
  rw [show 4478 = 4477 + 1 by norm_num, Nat.count_succ]
  rw [show 4477 = 4476 + 1 by norm_num, Nat.count_succ]
  rw [show 4476 = 4475 + 1 by norm_num, Nat.count_succ]
  rw [show 4475 = 4474 + 1 by norm_num, Nat.count_succ]
  rw [show 4474 = 4473 + 1 by norm_num, Nat.count_succ]
  rw [show 4473 = 4472 + 1 by norm_num, Nat.count_succ]
  rw [show 4472 = 4471 + 1 by norm_num, Nat.count_succ]
  rw [show 4471 = 4470 + 1 by norm_num, Nat.count_succ]
  rw [show 4470 = 4469 + 1 by norm_num, Nat.count_succ]
  rw [show 4469 = 4468 + 1 by norm_num, Nat.count_succ]
  rw [show 4468 = 4467 + 1 by norm_num, Nat.count_succ]
  rw [show 4467 = 4466 + 1 by norm_num, Nat.count_succ]
  rw [show 4466 = 4465 + 1 by norm_num, Nat.count_succ]
  rw [show 4465 = 4464 + 1 by norm_num, Nat.count_succ]
  rw [show 4464 = 4463 + 1 by norm_num, Nat.count_succ]
  rw [count_4463]
  simp [prime_4463, not_prime_4464, not_prime_4465, not_prime_4466, not_prime_4467, not_prime_4468, not_prime_4469, not_prime_4470, not_prime_4471, not_prime_4472, not_prime_4473, not_prime_4474, not_prime_4475, not_prime_4476, not_prime_4477, not_prime_4478, not_prime_4479, not_prime_4480]

theorem prime_4481 : (4481 : Nat).Prime := by norm_num

theorem nth_607 : Nat.nth Nat.Prime 607 = 4481 := by
  rw [← count_4481]
  exact Nat.nth_count prime_4481

theorem not_prime_4482 : ¬Nat.Prime 4482 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2241) (n := 4482)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4483 : Nat.count Nat.Prime 4483 = 608 := by
  rw [show 4483 = 4482 + 1 by norm_num, Nat.count_succ]
  rw [show 4482 = 4481 + 1 by norm_num, Nat.count_succ]
  rw [count_4481]
  simp [prime_4481, not_prime_4482]

theorem prime_4483 : (4483 : Nat).Prime := by norm_num

theorem nth_608 : Nat.nth Nat.Prime 608 = 4483 := by
  rw [← count_4483]
  exact Nat.nth_count prime_4483

theorem not_prime_4484 : ¬Nat.Prime 4484 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2242) (n := 4484)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4485 : ¬Nat.Prime 4485 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1495) (n := 4485)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4486 : ¬Nat.Prime 4486 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2243) (n := 4486)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4487 : ¬Nat.Prime 4487 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 641) (n := 4487)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4488 : ¬Nat.Prime 4488 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2244) (n := 4488)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4489 : ¬Nat.Prime 4489 :=
  Nat.not_prime_of_mul_eq (a := 67) (b := 67) (n := 4489)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4490 : ¬Nat.Prime 4490 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2245) (n := 4490)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4491 : ¬Nat.Prime 4491 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1497) (n := 4491)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4492 : ¬Nat.Prime 4492 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2246) (n := 4492)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4493 : Nat.count Nat.Prime 4493 = 609 := by
  rw [show 4493 = 4492 + 1 by norm_num, Nat.count_succ]
  rw [show 4492 = 4491 + 1 by norm_num, Nat.count_succ]
  rw [show 4491 = 4490 + 1 by norm_num, Nat.count_succ]
  rw [show 4490 = 4489 + 1 by norm_num, Nat.count_succ]
  rw [show 4489 = 4488 + 1 by norm_num, Nat.count_succ]
  rw [show 4488 = 4487 + 1 by norm_num, Nat.count_succ]
  rw [show 4487 = 4486 + 1 by norm_num, Nat.count_succ]
  rw [show 4486 = 4485 + 1 by norm_num, Nat.count_succ]
  rw [show 4485 = 4484 + 1 by norm_num, Nat.count_succ]
  rw [show 4484 = 4483 + 1 by norm_num, Nat.count_succ]
  rw [count_4483]
  simp [prime_4483, not_prime_4484, not_prime_4485, not_prime_4486, not_prime_4487, not_prime_4488, not_prime_4489, not_prime_4490, not_prime_4491, not_prime_4492]

theorem prime_4493 : (4493 : Nat).Prime := by norm_num

theorem nth_609 : Nat.nth Nat.Prime 609 = 4493 := by
  rw [← count_4493]
  exact Nat.nth_count prime_4493

theorem not_prime_4494 : ¬Nat.Prime 4494 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2247) (n := 4494)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4495 : ¬Nat.Prime 4495 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 899) (n := 4495)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4496 : ¬Nat.Prime 4496 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2248) (n := 4496)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4497 : ¬Nat.Prime 4497 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1499) (n := 4497)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4498 : ¬Nat.Prime 4498 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2249) (n := 4498)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4499 : ¬Nat.Prime 4499 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 409) (n := 4499)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4500 : ¬Nat.Prime 4500 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2250) (n := 4500)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4501 : ¬Nat.Prime 4501 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 643) (n := 4501)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4502 : ¬Nat.Prime 4502 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2251) (n := 4502)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4503 : ¬Nat.Prime 4503 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1501) (n := 4503)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4504 : ¬Nat.Prime 4504 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2252) (n := 4504)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4505 : ¬Nat.Prime 4505 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 901) (n := 4505)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4506 : ¬Nat.Prime 4506 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2253) (n := 4506)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4507 : Nat.count Nat.Prime 4507 = 610 := by
  rw [show 4507 = 4506 + 1 by norm_num, Nat.count_succ]
  rw [show 4506 = 4505 + 1 by norm_num, Nat.count_succ]
  rw [show 4505 = 4504 + 1 by norm_num, Nat.count_succ]
  rw [show 4504 = 4503 + 1 by norm_num, Nat.count_succ]
  rw [show 4503 = 4502 + 1 by norm_num, Nat.count_succ]
  rw [show 4502 = 4501 + 1 by norm_num, Nat.count_succ]
  rw [show 4501 = 4500 + 1 by norm_num, Nat.count_succ]
  rw [show 4500 = 4499 + 1 by norm_num, Nat.count_succ]
  rw [show 4499 = 4498 + 1 by norm_num, Nat.count_succ]
  rw [show 4498 = 4497 + 1 by norm_num, Nat.count_succ]
  rw [show 4497 = 4496 + 1 by norm_num, Nat.count_succ]
  rw [show 4496 = 4495 + 1 by norm_num, Nat.count_succ]
  rw [show 4495 = 4494 + 1 by norm_num, Nat.count_succ]
  rw [show 4494 = 4493 + 1 by norm_num, Nat.count_succ]
  rw [count_4493]
  simp [prime_4493, not_prime_4494, not_prime_4495, not_prime_4496, not_prime_4497, not_prime_4498, not_prime_4499, not_prime_4500, not_prime_4501, not_prime_4502, not_prime_4503, not_prime_4504, not_prime_4505, not_prime_4506]

theorem prime_4507 : (4507 : Nat).Prime := by norm_num

theorem nth_610 : Nat.nth Nat.Prime 610 = 4507 := by
  rw [← count_4507]
  exact Nat.nth_count prime_4507

theorem not_prime_4508 : ¬Nat.Prime 4508 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2254) (n := 4508)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4509 : ¬Nat.Prime 4509 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1503) (n := 4509)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4510 : ¬Nat.Prime 4510 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2255) (n := 4510)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4511 : ¬Nat.Prime 4511 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 347) (n := 4511)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4512 : ¬Nat.Prime 4512 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2256) (n := 4512)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4513 : Nat.count Nat.Prime 4513 = 611 := by
  rw [show 4513 = 4512 + 1 by norm_num, Nat.count_succ]
  rw [show 4512 = 4511 + 1 by norm_num, Nat.count_succ]
  rw [show 4511 = 4510 + 1 by norm_num, Nat.count_succ]
  rw [show 4510 = 4509 + 1 by norm_num, Nat.count_succ]
  rw [show 4509 = 4508 + 1 by norm_num, Nat.count_succ]
  rw [show 4508 = 4507 + 1 by norm_num, Nat.count_succ]
  rw [count_4507]
  simp [prime_4507, not_prime_4508, not_prime_4509, not_prime_4510, not_prime_4511, not_prime_4512]

theorem prime_4513 : (4513 : Nat).Prime := by norm_num

theorem nth_611 : Nat.nth Nat.Prime 611 = 4513 := by
  rw [← count_4513]
  exact Nat.nth_count prime_4513

theorem not_prime_4514 : ¬Nat.Prime 4514 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2257) (n := 4514)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4515 : ¬Nat.Prime 4515 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1505) (n := 4515)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4516 : ¬Nat.Prime 4516 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2258) (n := 4516)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4517 : Nat.count Nat.Prime 4517 = 612 := by
  rw [show 4517 = 4516 + 1 by norm_num, Nat.count_succ]
  rw [show 4516 = 4515 + 1 by norm_num, Nat.count_succ]
  rw [show 4515 = 4514 + 1 by norm_num, Nat.count_succ]
  rw [show 4514 = 4513 + 1 by norm_num, Nat.count_succ]
  rw [count_4513]
  simp [prime_4513, not_prime_4514, not_prime_4515, not_prime_4516]

theorem prime_4517 : (4517 : Nat).Prime := by norm_num

theorem nth_612 : Nat.nth Nat.Prime 612 = 4517 := by
  rw [← count_4517]
  exact Nat.nth_count prime_4517

theorem not_prime_4518 : ¬Nat.Prime 4518 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2259) (n := 4518)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4519 : Nat.count Nat.Prime 4519 = 613 := by
  rw [show 4519 = 4518 + 1 by norm_num, Nat.count_succ]
  rw [show 4518 = 4517 + 1 by norm_num, Nat.count_succ]
  rw [count_4517]
  simp [prime_4517, not_prime_4518]

theorem prime_4519 : (4519 : Nat).Prime := by norm_num

theorem nth_613 : Nat.nth Nat.Prime 613 = 4519 := by
  rw [← count_4519]
  exact Nat.nth_count prime_4519

theorem not_prime_4520 : ¬Nat.Prime 4520 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2260) (n := 4520)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4521 : ¬Nat.Prime 4521 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1507) (n := 4521)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4522 : ¬Nat.Prime 4522 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2261) (n := 4522)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4523 : Nat.count Nat.Prime 4523 = 614 := by
  rw [show 4523 = 4522 + 1 by norm_num, Nat.count_succ]
  rw [show 4522 = 4521 + 1 by norm_num, Nat.count_succ]
  rw [show 4521 = 4520 + 1 by norm_num, Nat.count_succ]
  rw [show 4520 = 4519 + 1 by norm_num, Nat.count_succ]
  rw [count_4519]
  simp [prime_4519, not_prime_4520, not_prime_4521, not_prime_4522]

theorem prime_4523 : (4523 : Nat).Prime := by norm_num

theorem nth_614 : Nat.nth Nat.Prime 614 = 4523 := by
  rw [← count_4523]
  exact Nat.nth_count prime_4523

theorem not_prime_4524 : ¬Nat.Prime 4524 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2262) (n := 4524)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4525 : ¬Nat.Prime 4525 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 905) (n := 4525)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4526 : ¬Nat.Prime 4526 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2263) (n := 4526)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4527 : ¬Nat.Prime 4527 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1509) (n := 4527)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4528 : ¬Nat.Prime 4528 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2264) (n := 4528)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4529 : ¬Nat.Prime 4529 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 647) (n := 4529)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4530 : ¬Nat.Prime 4530 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2265) (n := 4530)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4531 : ¬Nat.Prime 4531 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 197) (n := 4531)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4532 : ¬Nat.Prime 4532 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2266) (n := 4532)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4533 : ¬Nat.Prime 4533 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1511) (n := 4533)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4534 : ¬Nat.Prime 4534 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2267) (n := 4534)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4535 : ¬Nat.Prime 4535 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 907) (n := 4535)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4536 : ¬Nat.Prime 4536 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2268) (n := 4536)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4537 : ¬Nat.Prime 4537 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 349) (n := 4537)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4538 : ¬Nat.Prime 4538 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2269) (n := 4538)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4539 : ¬Nat.Prime 4539 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1513) (n := 4539)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4540 : ¬Nat.Prime 4540 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2270) (n := 4540)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4541 : ¬Nat.Prime 4541 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 239) (n := 4541)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4542 : ¬Nat.Prime 4542 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2271) (n := 4542)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4543 : ¬Nat.Prime 4543 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 649) (n := 4543)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4544 : ¬Nat.Prime 4544 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2272) (n := 4544)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4545 : ¬Nat.Prime 4545 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1515) (n := 4545)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4546 : ¬Nat.Prime 4546 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2273) (n := 4546)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4547 : Nat.count Nat.Prime 4547 = 615 := by
  rw [show 4547 = 4546 + 1 by norm_num, Nat.count_succ]
  rw [show 4546 = 4545 + 1 by norm_num, Nat.count_succ]
  rw [show 4545 = 4544 + 1 by norm_num, Nat.count_succ]
  rw [show 4544 = 4543 + 1 by norm_num, Nat.count_succ]
  rw [show 4543 = 4542 + 1 by norm_num, Nat.count_succ]
  rw [show 4542 = 4541 + 1 by norm_num, Nat.count_succ]
  rw [show 4541 = 4540 + 1 by norm_num, Nat.count_succ]
  rw [show 4540 = 4539 + 1 by norm_num, Nat.count_succ]
  rw [show 4539 = 4538 + 1 by norm_num, Nat.count_succ]
  rw [show 4538 = 4537 + 1 by norm_num, Nat.count_succ]
  rw [show 4537 = 4536 + 1 by norm_num, Nat.count_succ]
  rw [show 4536 = 4535 + 1 by norm_num, Nat.count_succ]
  rw [show 4535 = 4534 + 1 by norm_num, Nat.count_succ]
  rw [show 4534 = 4533 + 1 by norm_num, Nat.count_succ]
  rw [show 4533 = 4532 + 1 by norm_num, Nat.count_succ]
  rw [show 4532 = 4531 + 1 by norm_num, Nat.count_succ]
  rw [show 4531 = 4530 + 1 by norm_num, Nat.count_succ]
  rw [show 4530 = 4529 + 1 by norm_num, Nat.count_succ]
  rw [show 4529 = 4528 + 1 by norm_num, Nat.count_succ]
  rw [show 4528 = 4527 + 1 by norm_num, Nat.count_succ]
  rw [show 4527 = 4526 + 1 by norm_num, Nat.count_succ]
  rw [show 4526 = 4525 + 1 by norm_num, Nat.count_succ]
  rw [show 4525 = 4524 + 1 by norm_num, Nat.count_succ]
  rw [show 4524 = 4523 + 1 by norm_num, Nat.count_succ]
  rw [count_4523]
  simp [prime_4523, not_prime_4524, not_prime_4525, not_prime_4526, not_prime_4527, not_prime_4528, not_prime_4529, not_prime_4530, not_prime_4531, not_prime_4532, not_prime_4533, not_prime_4534, not_prime_4535, not_prime_4536, not_prime_4537, not_prime_4538, not_prime_4539, not_prime_4540, not_prime_4541, not_prime_4542, not_prime_4543, not_prime_4544, not_prime_4545, not_prime_4546]

theorem prime_4547 : (4547 : Nat).Prime := by norm_num

theorem nth_615 : Nat.nth Nat.Prime 615 = 4547 := by
  rw [← count_4547]
  exact Nat.nth_count prime_4547

theorem not_prime_4548 : ¬Nat.Prime 4548 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2274) (n := 4548)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4549 : Nat.count Nat.Prime 4549 = 616 := by
  rw [show 4549 = 4548 + 1 by norm_num, Nat.count_succ]
  rw [show 4548 = 4547 + 1 by norm_num, Nat.count_succ]
  rw [count_4547]
  simp [prime_4547, not_prime_4548]

theorem prime_4549 : (4549 : Nat).Prime := by norm_num

theorem nth_616 : Nat.nth Nat.Prime 616 = 4549 := by
  rw [← count_4549]
  exact Nat.nth_count prime_4549

theorem not_prime_4550 : ¬Nat.Prime 4550 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2275) (n := 4550)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4551 : ¬Nat.Prime 4551 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1517) (n := 4551)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4552 : ¬Nat.Prime 4552 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2276) (n := 4552)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4553 : ¬Nat.Prime 4553 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 157) (n := 4553)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4554 : ¬Nat.Prime 4554 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2277) (n := 4554)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4555 : ¬Nat.Prime 4555 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 911) (n := 4555)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4556 : ¬Nat.Prime 4556 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2278) (n := 4556)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4557 : ¬Nat.Prime 4557 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1519) (n := 4557)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4558 : ¬Nat.Prime 4558 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2279) (n := 4558)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4559 : ¬Nat.Prime 4559 :=
  Nat.not_prime_of_mul_eq (a := 47) (b := 97) (n := 4559)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4560 : ¬Nat.Prime 4560 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2280) (n := 4560)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4561 : Nat.count Nat.Prime 4561 = 617 := by
  rw [show 4561 = 4560 + 1 by norm_num, Nat.count_succ]
  rw [show 4560 = 4559 + 1 by norm_num, Nat.count_succ]
  rw [show 4559 = 4558 + 1 by norm_num, Nat.count_succ]
  rw [show 4558 = 4557 + 1 by norm_num, Nat.count_succ]
  rw [show 4557 = 4556 + 1 by norm_num, Nat.count_succ]
  rw [show 4556 = 4555 + 1 by norm_num, Nat.count_succ]
  rw [show 4555 = 4554 + 1 by norm_num, Nat.count_succ]
  rw [show 4554 = 4553 + 1 by norm_num, Nat.count_succ]
  rw [show 4553 = 4552 + 1 by norm_num, Nat.count_succ]
  rw [show 4552 = 4551 + 1 by norm_num, Nat.count_succ]
  rw [show 4551 = 4550 + 1 by norm_num, Nat.count_succ]
  rw [show 4550 = 4549 + 1 by norm_num, Nat.count_succ]
  rw [count_4549]
  simp [prime_4549, not_prime_4550, not_prime_4551, not_prime_4552, not_prime_4553, not_prime_4554, not_prime_4555, not_prime_4556, not_prime_4557, not_prime_4558, not_prime_4559, not_prime_4560]

theorem prime_4561 : (4561 : Nat).Prime := by norm_num

theorem nth_617 : Nat.nth Nat.Prime 617 = 4561 := by
  rw [← count_4561]
  exact Nat.nth_count prime_4561

theorem not_prime_4562 : ¬Nat.Prime 4562 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2281) (n := 4562)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4563 : ¬Nat.Prime 4563 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1521) (n := 4563)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4564 : ¬Nat.Prime 4564 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2282) (n := 4564)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4565 : ¬Nat.Prime 4565 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 913) (n := 4565)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4566 : ¬Nat.Prime 4566 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2283) (n := 4566)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4567 : Nat.count Nat.Prime 4567 = 618 := by
  rw [show 4567 = 4566 + 1 by norm_num, Nat.count_succ]
  rw [show 4566 = 4565 + 1 by norm_num, Nat.count_succ]
  rw [show 4565 = 4564 + 1 by norm_num, Nat.count_succ]
  rw [show 4564 = 4563 + 1 by norm_num, Nat.count_succ]
  rw [show 4563 = 4562 + 1 by norm_num, Nat.count_succ]
  rw [show 4562 = 4561 + 1 by norm_num, Nat.count_succ]
  rw [count_4561]
  simp [prime_4561, not_prime_4562, not_prime_4563, not_prime_4564, not_prime_4565, not_prime_4566]

theorem prime_4567 : (4567 : Nat).Prime := by norm_num

theorem nth_618 : Nat.nth Nat.Prime 618 = 4567 := by
  rw [← count_4567]
  exact Nat.nth_count prime_4567

theorem not_prime_4568 : ¬Nat.Prime 4568 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2284) (n := 4568)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4569 : ¬Nat.Prime 4569 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1523) (n := 4569)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4570 : ¬Nat.Prime 4570 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2285) (n := 4570)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4571 : ¬Nat.Prime 4571 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 653) (n := 4571)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4572 : ¬Nat.Prime 4572 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2286) (n := 4572)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4573 : ¬Nat.Prime 4573 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 269) (n := 4573)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4574 : ¬Nat.Prime 4574 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2287) (n := 4574)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4575 : ¬Nat.Prime 4575 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1525) (n := 4575)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4576 : ¬Nat.Prime 4576 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2288) (n := 4576)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4577 : ¬Nat.Prime 4577 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 199) (n := 4577)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4578 : ¬Nat.Prime 4578 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2289) (n := 4578)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4579 : ¬Nat.Prime 4579 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 241) (n := 4579)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4580 : ¬Nat.Prime 4580 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2290) (n := 4580)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4581 : ¬Nat.Prime 4581 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1527) (n := 4581)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4582 : ¬Nat.Prime 4582 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2291) (n := 4582)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4583 : Nat.count Nat.Prime 4583 = 619 := by
  rw [show 4583 = 4582 + 1 by norm_num, Nat.count_succ]
  rw [show 4582 = 4581 + 1 by norm_num, Nat.count_succ]
  rw [show 4581 = 4580 + 1 by norm_num, Nat.count_succ]
  rw [show 4580 = 4579 + 1 by norm_num, Nat.count_succ]
  rw [show 4579 = 4578 + 1 by norm_num, Nat.count_succ]
  rw [show 4578 = 4577 + 1 by norm_num, Nat.count_succ]
  rw [show 4577 = 4576 + 1 by norm_num, Nat.count_succ]
  rw [show 4576 = 4575 + 1 by norm_num, Nat.count_succ]
  rw [show 4575 = 4574 + 1 by norm_num, Nat.count_succ]
  rw [show 4574 = 4573 + 1 by norm_num, Nat.count_succ]
  rw [show 4573 = 4572 + 1 by norm_num, Nat.count_succ]
  rw [show 4572 = 4571 + 1 by norm_num, Nat.count_succ]
  rw [show 4571 = 4570 + 1 by norm_num, Nat.count_succ]
  rw [show 4570 = 4569 + 1 by norm_num, Nat.count_succ]
  rw [show 4569 = 4568 + 1 by norm_num, Nat.count_succ]
  rw [show 4568 = 4567 + 1 by norm_num, Nat.count_succ]
  rw [count_4567]
  simp [prime_4567, not_prime_4568, not_prime_4569, not_prime_4570, not_prime_4571, not_prime_4572, not_prime_4573, not_prime_4574, not_prime_4575, not_prime_4576, not_prime_4577, not_prime_4578, not_prime_4579, not_prime_4580, not_prime_4581, not_prime_4582]

theorem prime_4583 : (4583 : Nat).Prime := by norm_num

theorem nth_619 : Nat.nth Nat.Prime 619 = 4583 := by
  rw [← count_4583]
  exact Nat.nth_count prime_4583

theorem not_prime_4584 : ¬Nat.Prime 4584 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2292) (n := 4584)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4585 : ¬Nat.Prime 4585 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 917) (n := 4585)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4586 : ¬Nat.Prime 4586 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2293) (n := 4586)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4587 : ¬Nat.Prime 4587 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1529) (n := 4587)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4588 : ¬Nat.Prime 4588 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2294) (n := 4588)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4589 : ¬Nat.Prime 4589 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 353) (n := 4589)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4590 : ¬Nat.Prime 4590 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2295) (n := 4590)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4591 : Nat.count Nat.Prime 4591 = 620 := by
  rw [show 4591 = 4590 + 1 by norm_num, Nat.count_succ]
  rw [show 4590 = 4589 + 1 by norm_num, Nat.count_succ]
  rw [show 4589 = 4588 + 1 by norm_num, Nat.count_succ]
  rw [show 4588 = 4587 + 1 by norm_num, Nat.count_succ]
  rw [show 4587 = 4586 + 1 by norm_num, Nat.count_succ]
  rw [show 4586 = 4585 + 1 by norm_num, Nat.count_succ]
  rw [show 4585 = 4584 + 1 by norm_num, Nat.count_succ]
  rw [show 4584 = 4583 + 1 by norm_num, Nat.count_succ]
  rw [count_4583]
  simp [prime_4583, not_prime_4584, not_prime_4585, not_prime_4586, not_prime_4587, not_prime_4588, not_prime_4589, not_prime_4590]

theorem prime_4591 : (4591 : Nat).Prime := by norm_num

theorem nth_620 : Nat.nth Nat.Prime 620 = 4591 := by
  rw [← count_4591]
  exact Nat.nth_count prime_4591

theorem not_prime_4592 : ¬Nat.Prime 4592 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2296) (n := 4592)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4593 : ¬Nat.Prime 4593 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1531) (n := 4593)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4594 : ¬Nat.Prime 4594 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2297) (n := 4594)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4595 : ¬Nat.Prime 4595 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 919) (n := 4595)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4596 : ¬Nat.Prime 4596 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2298) (n := 4596)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4597 : Nat.count Nat.Prime 4597 = 621 := by
  rw [show 4597 = 4596 + 1 by norm_num, Nat.count_succ]
  rw [show 4596 = 4595 + 1 by norm_num, Nat.count_succ]
  rw [show 4595 = 4594 + 1 by norm_num, Nat.count_succ]
  rw [show 4594 = 4593 + 1 by norm_num, Nat.count_succ]
  rw [show 4593 = 4592 + 1 by norm_num, Nat.count_succ]
  rw [show 4592 = 4591 + 1 by norm_num, Nat.count_succ]
  rw [count_4591]
  simp [prime_4591, not_prime_4592, not_prime_4593, not_prime_4594, not_prime_4595, not_prime_4596]

theorem prime_4597 : (4597 : Nat).Prime := by norm_num

theorem nth_621 : Nat.nth Nat.Prime 621 = 4597 := by
  rw [← count_4597]
  exact Nat.nth_count prime_4597

theorem not_prime_4598 : ¬Nat.Prime 4598 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2299) (n := 4598)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4599 : ¬Nat.Prime 4599 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1533) (n := 4599)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4600 : ¬Nat.Prime 4600 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2300) (n := 4600)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4601 : ¬Nat.Prime 4601 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 107) (n := 4601)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4602 : ¬Nat.Prime 4602 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2301) (n := 4602)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4603 : Nat.count Nat.Prime 4603 = 622 := by
  rw [show 4603 = 4602 + 1 by norm_num, Nat.count_succ]
  rw [show 4602 = 4601 + 1 by norm_num, Nat.count_succ]
  rw [show 4601 = 4600 + 1 by norm_num, Nat.count_succ]
  rw [show 4600 = 4599 + 1 by norm_num, Nat.count_succ]
  rw [show 4599 = 4598 + 1 by norm_num, Nat.count_succ]
  rw [show 4598 = 4597 + 1 by norm_num, Nat.count_succ]
  rw [count_4597]
  simp [prime_4597, not_prime_4598, not_prime_4599, not_prime_4600, not_prime_4601, not_prime_4602]

theorem prime_4603 : (4603 : Nat).Prime := by norm_num

theorem nth_622 : Nat.nth Nat.Prime 622 = 4603 := by
  rw [← count_4603]
  exact Nat.nth_count prime_4603

theorem not_prime_4604 : ¬Nat.Prime 4604 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2302) (n := 4604)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4605 : ¬Nat.Prime 4605 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1535) (n := 4605)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4606 : ¬Nat.Prime 4606 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2303) (n := 4606)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4607 : ¬Nat.Prime 4607 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 271) (n := 4607)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4608 : ¬Nat.Prime 4608 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2304) (n := 4608)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4609 : ¬Nat.Prime 4609 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 419) (n := 4609)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4610 : ¬Nat.Prime 4610 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2305) (n := 4610)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4611 : ¬Nat.Prime 4611 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1537) (n := 4611)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4612 : ¬Nat.Prime 4612 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2306) (n := 4612)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4613 : ¬Nat.Prime 4613 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 659) (n := 4613)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4614 : ¬Nat.Prime 4614 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2307) (n := 4614)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4615 : ¬Nat.Prime 4615 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 923) (n := 4615)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4616 : ¬Nat.Prime 4616 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2308) (n := 4616)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4617 : ¬Nat.Prime 4617 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1539) (n := 4617)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4618 : ¬Nat.Prime 4618 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2309) (n := 4618)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4619 : ¬Nat.Prime 4619 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 149) (n := 4619)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4620 : ¬Nat.Prime 4620 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2310) (n := 4620)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4621 : Nat.count Nat.Prime 4621 = 623 := by
  rw [show 4621 = 4620 + 1 by norm_num, Nat.count_succ]
  rw [show 4620 = 4619 + 1 by norm_num, Nat.count_succ]
  rw [show 4619 = 4618 + 1 by norm_num, Nat.count_succ]
  rw [show 4618 = 4617 + 1 by norm_num, Nat.count_succ]
  rw [show 4617 = 4616 + 1 by norm_num, Nat.count_succ]
  rw [show 4616 = 4615 + 1 by norm_num, Nat.count_succ]
  rw [show 4615 = 4614 + 1 by norm_num, Nat.count_succ]
  rw [show 4614 = 4613 + 1 by norm_num, Nat.count_succ]
  rw [show 4613 = 4612 + 1 by norm_num, Nat.count_succ]
  rw [show 4612 = 4611 + 1 by norm_num, Nat.count_succ]
  rw [show 4611 = 4610 + 1 by norm_num, Nat.count_succ]
  rw [show 4610 = 4609 + 1 by norm_num, Nat.count_succ]
  rw [show 4609 = 4608 + 1 by norm_num, Nat.count_succ]
  rw [show 4608 = 4607 + 1 by norm_num, Nat.count_succ]
  rw [show 4607 = 4606 + 1 by norm_num, Nat.count_succ]
  rw [show 4606 = 4605 + 1 by norm_num, Nat.count_succ]
  rw [show 4605 = 4604 + 1 by norm_num, Nat.count_succ]
  rw [show 4604 = 4603 + 1 by norm_num, Nat.count_succ]
  rw [count_4603]
  simp [prime_4603, not_prime_4604, not_prime_4605, not_prime_4606, not_prime_4607, not_prime_4608, not_prime_4609, not_prime_4610, not_prime_4611, not_prime_4612, not_prime_4613, not_prime_4614, not_prime_4615, not_prime_4616, not_prime_4617, not_prime_4618, not_prime_4619, not_prime_4620]

theorem prime_4621 : (4621 : Nat).Prime := by norm_num

theorem nth_623 : Nat.nth Nat.Prime 623 = 4621 := by
  rw [← count_4621]
  exact Nat.nth_count prime_4621

theorem not_prime_4622 : ¬Nat.Prime 4622 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2311) (n := 4622)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4623 : ¬Nat.Prime 4623 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1541) (n := 4623)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4624 : ¬Nat.Prime 4624 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2312) (n := 4624)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4625 : ¬Nat.Prime 4625 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 925) (n := 4625)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4626 : ¬Nat.Prime 4626 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2313) (n := 4626)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4627 : ¬Nat.Prime 4627 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 661) (n := 4627)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4628 : ¬Nat.Prime 4628 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2314) (n := 4628)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4629 : ¬Nat.Prime 4629 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1543) (n := 4629)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4630 : ¬Nat.Prime 4630 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2315) (n := 4630)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4631 : ¬Nat.Prime 4631 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 421) (n := 4631)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4632 : ¬Nat.Prime 4632 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2316) (n := 4632)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4633 : ¬Nat.Prime 4633 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 113) (n := 4633)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4634 : ¬Nat.Prime 4634 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2317) (n := 4634)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4635 : ¬Nat.Prime 4635 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1545) (n := 4635)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4636 : ¬Nat.Prime 4636 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2318) (n := 4636)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4637 : Nat.count Nat.Prime 4637 = 624 := by
  rw [show 4637 = 4636 + 1 by norm_num, Nat.count_succ]
  rw [show 4636 = 4635 + 1 by norm_num, Nat.count_succ]
  rw [show 4635 = 4634 + 1 by norm_num, Nat.count_succ]
  rw [show 4634 = 4633 + 1 by norm_num, Nat.count_succ]
  rw [show 4633 = 4632 + 1 by norm_num, Nat.count_succ]
  rw [show 4632 = 4631 + 1 by norm_num, Nat.count_succ]
  rw [show 4631 = 4630 + 1 by norm_num, Nat.count_succ]
  rw [show 4630 = 4629 + 1 by norm_num, Nat.count_succ]
  rw [show 4629 = 4628 + 1 by norm_num, Nat.count_succ]
  rw [show 4628 = 4627 + 1 by norm_num, Nat.count_succ]
  rw [show 4627 = 4626 + 1 by norm_num, Nat.count_succ]
  rw [show 4626 = 4625 + 1 by norm_num, Nat.count_succ]
  rw [show 4625 = 4624 + 1 by norm_num, Nat.count_succ]
  rw [show 4624 = 4623 + 1 by norm_num, Nat.count_succ]
  rw [show 4623 = 4622 + 1 by norm_num, Nat.count_succ]
  rw [show 4622 = 4621 + 1 by norm_num, Nat.count_succ]
  rw [count_4621]
  simp [prime_4621, not_prime_4622, not_prime_4623, not_prime_4624, not_prime_4625, not_prime_4626, not_prime_4627, not_prime_4628, not_prime_4629, not_prime_4630, not_prime_4631, not_prime_4632, not_prime_4633, not_prime_4634, not_prime_4635, not_prime_4636]

theorem prime_4637 : (4637 : Nat).Prime := by norm_num

theorem nth_624 : Nat.nth Nat.Prime 624 = 4637 := by
  rw [← count_4637]
  exact Nat.nth_count prime_4637

end OeisA100474.PrimeCertificate
