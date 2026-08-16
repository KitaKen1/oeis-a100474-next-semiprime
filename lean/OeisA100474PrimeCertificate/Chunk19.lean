import OeisA100474PrimeCertificate.Chunk18

/-! Kernel prime/count certificate, chunk 19 (475–499). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_3372 : ¬Nat.Prime 3372 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1686) (n := 3372)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3373 : Nat.count Nat.Prime 3373 = 475 := by
  rw [show 3373 = 3372 + 1 by norm_num, Nat.count_succ]
  rw [show 3372 = 3371 + 1 by norm_num, Nat.count_succ]
  rw [count_3371]
  simp [prime_3371, not_prime_3372]

theorem prime_3373 : (3373 : Nat).Prime := by norm_num

theorem nth_475 : Nat.nth Nat.Prime 475 = 3373 := by
  rw [← count_3373]
  exact Nat.nth_count prime_3373

theorem not_prime_3374 : ¬Nat.Prime 3374 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1687) (n := 3374)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3375 : ¬Nat.Prime 3375 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1125) (n := 3375)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3376 : ¬Nat.Prime 3376 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1688) (n := 3376)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3377 : ¬Nat.Prime 3377 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 307) (n := 3377)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3378 : ¬Nat.Prime 3378 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1689) (n := 3378)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3379 : ¬Nat.Prime 3379 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 109) (n := 3379)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3380 : ¬Nat.Prime 3380 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1690) (n := 3380)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3381 : ¬Nat.Prime 3381 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1127) (n := 3381)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3382 : ¬Nat.Prime 3382 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1691) (n := 3382)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3383 : ¬Nat.Prime 3383 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 199) (n := 3383)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3384 : ¬Nat.Prime 3384 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1692) (n := 3384)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3385 : ¬Nat.Prime 3385 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 677) (n := 3385)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3386 : ¬Nat.Prime 3386 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1693) (n := 3386)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3387 : ¬Nat.Prime 3387 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1129) (n := 3387)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3388 : ¬Nat.Prime 3388 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1694) (n := 3388)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3389 : Nat.count Nat.Prime 3389 = 476 := by
  rw [show 3389 = 3388 + 1 by norm_num, Nat.count_succ]
  rw [show 3388 = 3387 + 1 by norm_num, Nat.count_succ]
  rw [show 3387 = 3386 + 1 by norm_num, Nat.count_succ]
  rw [show 3386 = 3385 + 1 by norm_num, Nat.count_succ]
  rw [show 3385 = 3384 + 1 by norm_num, Nat.count_succ]
  rw [show 3384 = 3383 + 1 by norm_num, Nat.count_succ]
  rw [show 3383 = 3382 + 1 by norm_num, Nat.count_succ]
  rw [show 3382 = 3381 + 1 by norm_num, Nat.count_succ]
  rw [show 3381 = 3380 + 1 by norm_num, Nat.count_succ]
  rw [show 3380 = 3379 + 1 by norm_num, Nat.count_succ]
  rw [show 3379 = 3378 + 1 by norm_num, Nat.count_succ]
  rw [show 3378 = 3377 + 1 by norm_num, Nat.count_succ]
  rw [show 3377 = 3376 + 1 by norm_num, Nat.count_succ]
  rw [show 3376 = 3375 + 1 by norm_num, Nat.count_succ]
  rw [show 3375 = 3374 + 1 by norm_num, Nat.count_succ]
  rw [show 3374 = 3373 + 1 by norm_num, Nat.count_succ]
  rw [count_3373]
  simp [prime_3373, not_prime_3374, not_prime_3375, not_prime_3376, not_prime_3377, not_prime_3378, not_prime_3379, not_prime_3380, not_prime_3381, not_prime_3382, not_prime_3383, not_prime_3384, not_prime_3385, not_prime_3386, not_prime_3387, not_prime_3388]

theorem prime_3389 : (3389 : Nat).Prime := by norm_num

theorem nth_476 : Nat.nth Nat.Prime 476 = 3389 := by
  rw [← count_3389]
  exact Nat.nth_count prime_3389

theorem not_prime_3390 : ¬Nat.Prime 3390 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1695) (n := 3390)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3391 : Nat.count Nat.Prime 3391 = 477 := by
  rw [show 3391 = 3390 + 1 by norm_num, Nat.count_succ]
  rw [show 3390 = 3389 + 1 by norm_num, Nat.count_succ]
  rw [count_3389]
  simp [prime_3389, not_prime_3390]

theorem prime_3391 : (3391 : Nat).Prime := by norm_num

theorem nth_477 : Nat.nth Nat.Prime 477 = 3391 := by
  rw [← count_3391]
  exact Nat.nth_count prime_3391

theorem not_prime_3392 : ¬Nat.Prime 3392 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1696) (n := 3392)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3393 : ¬Nat.Prime 3393 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1131) (n := 3393)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3394 : ¬Nat.Prime 3394 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1697) (n := 3394)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3395 : ¬Nat.Prime 3395 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 679) (n := 3395)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3396 : ¬Nat.Prime 3396 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1698) (n := 3396)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3397 : ¬Nat.Prime 3397 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 79) (n := 3397)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3398 : ¬Nat.Prime 3398 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1699) (n := 3398)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3399 : ¬Nat.Prime 3399 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1133) (n := 3399)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3400 : ¬Nat.Prime 3400 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1700) (n := 3400)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3401 : ¬Nat.Prime 3401 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 179) (n := 3401)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3402 : ¬Nat.Prime 3402 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1701) (n := 3402)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3403 : ¬Nat.Prime 3403 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 83) (n := 3403)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3404 : ¬Nat.Prime 3404 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1702) (n := 3404)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3405 : ¬Nat.Prime 3405 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1135) (n := 3405)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3406 : ¬Nat.Prime 3406 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1703) (n := 3406)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3407 : Nat.count Nat.Prime 3407 = 478 := by
  rw [show 3407 = 3406 + 1 by norm_num, Nat.count_succ]
  rw [show 3406 = 3405 + 1 by norm_num, Nat.count_succ]
  rw [show 3405 = 3404 + 1 by norm_num, Nat.count_succ]
  rw [show 3404 = 3403 + 1 by norm_num, Nat.count_succ]
  rw [show 3403 = 3402 + 1 by norm_num, Nat.count_succ]
  rw [show 3402 = 3401 + 1 by norm_num, Nat.count_succ]
  rw [show 3401 = 3400 + 1 by norm_num, Nat.count_succ]
  rw [show 3400 = 3399 + 1 by norm_num, Nat.count_succ]
  rw [show 3399 = 3398 + 1 by norm_num, Nat.count_succ]
  rw [show 3398 = 3397 + 1 by norm_num, Nat.count_succ]
  rw [show 3397 = 3396 + 1 by norm_num, Nat.count_succ]
  rw [show 3396 = 3395 + 1 by norm_num, Nat.count_succ]
  rw [show 3395 = 3394 + 1 by norm_num, Nat.count_succ]
  rw [show 3394 = 3393 + 1 by norm_num, Nat.count_succ]
  rw [show 3393 = 3392 + 1 by norm_num, Nat.count_succ]
  rw [show 3392 = 3391 + 1 by norm_num, Nat.count_succ]
  rw [count_3391]
  simp [prime_3391, not_prime_3392, not_prime_3393, not_prime_3394, not_prime_3395, not_prime_3396, not_prime_3397, not_prime_3398, not_prime_3399, not_prime_3400, not_prime_3401, not_prime_3402, not_prime_3403, not_prime_3404, not_prime_3405, not_prime_3406]

theorem prime_3407 : (3407 : Nat).Prime := by norm_num

theorem nth_478 : Nat.nth Nat.Prime 478 = 3407 := by
  rw [← count_3407]
  exact Nat.nth_count prime_3407

theorem not_prime_3408 : ¬Nat.Prime 3408 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1704) (n := 3408)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3409 : ¬Nat.Prime 3409 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 487) (n := 3409)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3410 : ¬Nat.Prime 3410 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1705) (n := 3410)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3411 : ¬Nat.Prime 3411 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1137) (n := 3411)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3412 : ¬Nat.Prime 3412 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1706) (n := 3412)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3413 : Nat.count Nat.Prime 3413 = 479 := by
  rw [show 3413 = 3412 + 1 by norm_num, Nat.count_succ]
  rw [show 3412 = 3411 + 1 by norm_num, Nat.count_succ]
  rw [show 3411 = 3410 + 1 by norm_num, Nat.count_succ]
  rw [show 3410 = 3409 + 1 by norm_num, Nat.count_succ]
  rw [show 3409 = 3408 + 1 by norm_num, Nat.count_succ]
  rw [show 3408 = 3407 + 1 by norm_num, Nat.count_succ]
  rw [count_3407]
  simp [prime_3407, not_prime_3408, not_prime_3409, not_prime_3410, not_prime_3411, not_prime_3412]

theorem prime_3413 : (3413 : Nat).Prime := by norm_num

theorem nth_479 : Nat.nth Nat.Prime 479 = 3413 := by
  rw [← count_3413]
  exact Nat.nth_count prime_3413

theorem not_prime_3414 : ¬Nat.Prime 3414 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1707) (n := 3414)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3415 : ¬Nat.Prime 3415 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 683) (n := 3415)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3416 : ¬Nat.Prime 3416 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1708) (n := 3416)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3417 : ¬Nat.Prime 3417 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1139) (n := 3417)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3418 : ¬Nat.Prime 3418 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1709) (n := 3418)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3419 : ¬Nat.Prime 3419 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 263) (n := 3419)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3420 : ¬Nat.Prime 3420 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1710) (n := 3420)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3421 : ¬Nat.Prime 3421 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 311) (n := 3421)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3422 : ¬Nat.Prime 3422 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1711) (n := 3422)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3423 : ¬Nat.Prime 3423 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1141) (n := 3423)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3424 : ¬Nat.Prime 3424 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1712) (n := 3424)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3425 : ¬Nat.Prime 3425 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 685) (n := 3425)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3426 : ¬Nat.Prime 3426 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1713) (n := 3426)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3427 : ¬Nat.Prime 3427 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 149) (n := 3427)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3428 : ¬Nat.Prime 3428 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1714) (n := 3428)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3429 : ¬Nat.Prime 3429 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1143) (n := 3429)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3430 : ¬Nat.Prime 3430 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1715) (n := 3430)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3431 : ¬Nat.Prime 3431 :=
  Nat.not_prime_of_mul_eq (a := 47) (b := 73) (n := 3431)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3432 : ¬Nat.Prime 3432 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1716) (n := 3432)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3433 : Nat.count Nat.Prime 3433 = 480 := by
  rw [show 3433 = 3432 + 1 by norm_num, Nat.count_succ]
  rw [show 3432 = 3431 + 1 by norm_num, Nat.count_succ]
  rw [show 3431 = 3430 + 1 by norm_num, Nat.count_succ]
  rw [show 3430 = 3429 + 1 by norm_num, Nat.count_succ]
  rw [show 3429 = 3428 + 1 by norm_num, Nat.count_succ]
  rw [show 3428 = 3427 + 1 by norm_num, Nat.count_succ]
  rw [show 3427 = 3426 + 1 by norm_num, Nat.count_succ]
  rw [show 3426 = 3425 + 1 by norm_num, Nat.count_succ]
  rw [show 3425 = 3424 + 1 by norm_num, Nat.count_succ]
  rw [show 3424 = 3423 + 1 by norm_num, Nat.count_succ]
  rw [show 3423 = 3422 + 1 by norm_num, Nat.count_succ]
  rw [show 3422 = 3421 + 1 by norm_num, Nat.count_succ]
  rw [show 3421 = 3420 + 1 by norm_num, Nat.count_succ]
  rw [show 3420 = 3419 + 1 by norm_num, Nat.count_succ]
  rw [show 3419 = 3418 + 1 by norm_num, Nat.count_succ]
  rw [show 3418 = 3417 + 1 by norm_num, Nat.count_succ]
  rw [show 3417 = 3416 + 1 by norm_num, Nat.count_succ]
  rw [show 3416 = 3415 + 1 by norm_num, Nat.count_succ]
  rw [show 3415 = 3414 + 1 by norm_num, Nat.count_succ]
  rw [show 3414 = 3413 + 1 by norm_num, Nat.count_succ]
  rw [count_3413]
  simp [prime_3413, not_prime_3414, not_prime_3415, not_prime_3416, not_prime_3417, not_prime_3418, not_prime_3419, not_prime_3420, not_prime_3421, not_prime_3422, not_prime_3423, not_prime_3424, not_prime_3425, not_prime_3426, not_prime_3427, not_prime_3428, not_prime_3429, not_prime_3430, not_prime_3431, not_prime_3432]

theorem prime_3433 : (3433 : Nat).Prime := by norm_num

theorem nth_480 : Nat.nth Nat.Prime 480 = 3433 := by
  rw [← count_3433]
  exact Nat.nth_count prime_3433

theorem not_prime_3434 : ¬Nat.Prime 3434 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1717) (n := 3434)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3435 : ¬Nat.Prime 3435 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1145) (n := 3435)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3436 : ¬Nat.Prime 3436 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1718) (n := 3436)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3437 : ¬Nat.Prime 3437 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 491) (n := 3437)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3438 : ¬Nat.Prime 3438 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1719) (n := 3438)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3439 : ¬Nat.Prime 3439 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 181) (n := 3439)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3440 : ¬Nat.Prime 3440 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1720) (n := 3440)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3441 : ¬Nat.Prime 3441 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1147) (n := 3441)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3442 : ¬Nat.Prime 3442 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1721) (n := 3442)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3443 : ¬Nat.Prime 3443 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 313) (n := 3443)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3444 : ¬Nat.Prime 3444 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1722) (n := 3444)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3445 : ¬Nat.Prime 3445 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 689) (n := 3445)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3446 : ¬Nat.Prime 3446 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1723) (n := 3446)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3447 : ¬Nat.Prime 3447 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1149) (n := 3447)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3448 : ¬Nat.Prime 3448 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1724) (n := 3448)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3449 : Nat.count Nat.Prime 3449 = 481 := by
  rw [show 3449 = 3448 + 1 by norm_num, Nat.count_succ]
  rw [show 3448 = 3447 + 1 by norm_num, Nat.count_succ]
  rw [show 3447 = 3446 + 1 by norm_num, Nat.count_succ]
  rw [show 3446 = 3445 + 1 by norm_num, Nat.count_succ]
  rw [show 3445 = 3444 + 1 by norm_num, Nat.count_succ]
  rw [show 3444 = 3443 + 1 by norm_num, Nat.count_succ]
  rw [show 3443 = 3442 + 1 by norm_num, Nat.count_succ]
  rw [show 3442 = 3441 + 1 by norm_num, Nat.count_succ]
  rw [show 3441 = 3440 + 1 by norm_num, Nat.count_succ]
  rw [show 3440 = 3439 + 1 by norm_num, Nat.count_succ]
  rw [show 3439 = 3438 + 1 by norm_num, Nat.count_succ]
  rw [show 3438 = 3437 + 1 by norm_num, Nat.count_succ]
  rw [show 3437 = 3436 + 1 by norm_num, Nat.count_succ]
  rw [show 3436 = 3435 + 1 by norm_num, Nat.count_succ]
  rw [show 3435 = 3434 + 1 by norm_num, Nat.count_succ]
  rw [show 3434 = 3433 + 1 by norm_num, Nat.count_succ]
  rw [count_3433]
  simp [prime_3433, not_prime_3434, not_prime_3435, not_prime_3436, not_prime_3437, not_prime_3438, not_prime_3439, not_prime_3440, not_prime_3441, not_prime_3442, not_prime_3443, not_prime_3444, not_prime_3445, not_prime_3446, not_prime_3447, not_prime_3448]

theorem prime_3449 : (3449 : Nat).Prime := by norm_num

theorem nth_481 : Nat.nth Nat.Prime 481 = 3449 := by
  rw [← count_3449]
  exact Nat.nth_count prime_3449

theorem not_prime_3450 : ¬Nat.Prime 3450 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1725) (n := 3450)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3451 : ¬Nat.Prime 3451 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 493) (n := 3451)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3452 : ¬Nat.Prime 3452 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1726) (n := 3452)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3453 : ¬Nat.Prime 3453 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1151) (n := 3453)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3454 : ¬Nat.Prime 3454 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1727) (n := 3454)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3455 : ¬Nat.Prime 3455 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 691) (n := 3455)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3456 : ¬Nat.Prime 3456 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1728) (n := 3456)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3457 : Nat.count Nat.Prime 3457 = 482 := by
  rw [show 3457 = 3456 + 1 by norm_num, Nat.count_succ]
  rw [show 3456 = 3455 + 1 by norm_num, Nat.count_succ]
  rw [show 3455 = 3454 + 1 by norm_num, Nat.count_succ]
  rw [show 3454 = 3453 + 1 by norm_num, Nat.count_succ]
  rw [show 3453 = 3452 + 1 by norm_num, Nat.count_succ]
  rw [show 3452 = 3451 + 1 by norm_num, Nat.count_succ]
  rw [show 3451 = 3450 + 1 by norm_num, Nat.count_succ]
  rw [show 3450 = 3449 + 1 by norm_num, Nat.count_succ]
  rw [count_3449]
  simp [prime_3449, not_prime_3450, not_prime_3451, not_prime_3452, not_prime_3453, not_prime_3454, not_prime_3455, not_prime_3456]

theorem prime_3457 : (3457 : Nat).Prime := by norm_num

theorem nth_482 : Nat.nth Nat.Prime 482 = 3457 := by
  rw [← count_3457]
  exact Nat.nth_count prime_3457

theorem not_prime_3458 : ¬Nat.Prime 3458 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1729) (n := 3458)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3459 : ¬Nat.Prime 3459 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1153) (n := 3459)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3460 : ¬Nat.Prime 3460 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1730) (n := 3460)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3461 : Nat.count Nat.Prime 3461 = 483 := by
  rw [show 3461 = 3460 + 1 by norm_num, Nat.count_succ]
  rw [show 3460 = 3459 + 1 by norm_num, Nat.count_succ]
  rw [show 3459 = 3458 + 1 by norm_num, Nat.count_succ]
  rw [show 3458 = 3457 + 1 by norm_num, Nat.count_succ]
  rw [count_3457]
  simp [prime_3457, not_prime_3458, not_prime_3459, not_prime_3460]

theorem prime_3461 : (3461 : Nat).Prime := by norm_num

theorem nth_483 : Nat.nth Nat.Prime 483 = 3461 := by
  rw [← count_3461]
  exact Nat.nth_count prime_3461

theorem not_prime_3462 : ¬Nat.Prime 3462 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1731) (n := 3462)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3463 : Nat.count Nat.Prime 3463 = 484 := by
  rw [show 3463 = 3462 + 1 by norm_num, Nat.count_succ]
  rw [show 3462 = 3461 + 1 by norm_num, Nat.count_succ]
  rw [count_3461]
  simp [prime_3461, not_prime_3462]

theorem prime_3463 : (3463 : Nat).Prime := by norm_num

theorem nth_484 : Nat.nth Nat.Prime 484 = 3463 := by
  rw [← count_3463]
  exact Nat.nth_count prime_3463

theorem not_prime_3464 : ¬Nat.Prime 3464 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1732) (n := 3464)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3465 : ¬Nat.Prime 3465 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1155) (n := 3465)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3466 : ¬Nat.Prime 3466 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1733) (n := 3466)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3467 : Nat.count Nat.Prime 3467 = 485 := by
  rw [show 3467 = 3466 + 1 by norm_num, Nat.count_succ]
  rw [show 3466 = 3465 + 1 by norm_num, Nat.count_succ]
  rw [show 3465 = 3464 + 1 by norm_num, Nat.count_succ]
  rw [show 3464 = 3463 + 1 by norm_num, Nat.count_succ]
  rw [count_3463]
  simp [prime_3463, not_prime_3464, not_prime_3465, not_prime_3466]

theorem prime_3467 : (3467 : Nat).Prime := by norm_num

theorem nth_485 : Nat.nth Nat.Prime 485 = 3467 := by
  rw [← count_3467]
  exact Nat.nth_count prime_3467

theorem not_prime_3468 : ¬Nat.Prime 3468 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1734) (n := 3468)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3469 : Nat.count Nat.Prime 3469 = 486 := by
  rw [show 3469 = 3468 + 1 by norm_num, Nat.count_succ]
  rw [show 3468 = 3467 + 1 by norm_num, Nat.count_succ]
  rw [count_3467]
  simp [prime_3467, not_prime_3468]

theorem prime_3469 : (3469 : Nat).Prime := by norm_num

theorem nth_486 : Nat.nth Nat.Prime 486 = 3469 := by
  rw [← count_3469]
  exact Nat.nth_count prime_3469

theorem not_prime_3470 : ¬Nat.Prime 3470 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1735) (n := 3470)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3471 : ¬Nat.Prime 3471 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1157) (n := 3471)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3472 : ¬Nat.Prime 3472 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1736) (n := 3472)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3473 : ¬Nat.Prime 3473 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 151) (n := 3473)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3474 : ¬Nat.Prime 3474 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1737) (n := 3474)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3475 : ¬Nat.Prime 3475 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 695) (n := 3475)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3476 : ¬Nat.Prime 3476 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1738) (n := 3476)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3477 : ¬Nat.Prime 3477 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1159) (n := 3477)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3478 : ¬Nat.Prime 3478 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1739) (n := 3478)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3479 : ¬Nat.Prime 3479 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 497) (n := 3479)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3480 : ¬Nat.Prime 3480 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1740) (n := 3480)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3481 : ¬Nat.Prime 3481 :=
  Nat.not_prime_of_mul_eq (a := 59) (b := 59) (n := 3481)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3482 : ¬Nat.Prime 3482 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1741) (n := 3482)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3483 : ¬Nat.Prime 3483 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1161) (n := 3483)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3484 : ¬Nat.Prime 3484 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1742) (n := 3484)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3485 : ¬Nat.Prime 3485 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 697) (n := 3485)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3486 : ¬Nat.Prime 3486 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1743) (n := 3486)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3487 : ¬Nat.Prime 3487 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 317) (n := 3487)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3488 : ¬Nat.Prime 3488 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1744) (n := 3488)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3489 : ¬Nat.Prime 3489 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1163) (n := 3489)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3490 : ¬Nat.Prime 3490 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1745) (n := 3490)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3491 : Nat.count Nat.Prime 3491 = 487 := by
  rw [show 3491 = 3490 + 1 by norm_num, Nat.count_succ]
  rw [show 3490 = 3489 + 1 by norm_num, Nat.count_succ]
  rw [show 3489 = 3488 + 1 by norm_num, Nat.count_succ]
  rw [show 3488 = 3487 + 1 by norm_num, Nat.count_succ]
  rw [show 3487 = 3486 + 1 by norm_num, Nat.count_succ]
  rw [show 3486 = 3485 + 1 by norm_num, Nat.count_succ]
  rw [show 3485 = 3484 + 1 by norm_num, Nat.count_succ]
  rw [show 3484 = 3483 + 1 by norm_num, Nat.count_succ]
  rw [show 3483 = 3482 + 1 by norm_num, Nat.count_succ]
  rw [show 3482 = 3481 + 1 by norm_num, Nat.count_succ]
  rw [show 3481 = 3480 + 1 by norm_num, Nat.count_succ]
  rw [show 3480 = 3479 + 1 by norm_num, Nat.count_succ]
  rw [show 3479 = 3478 + 1 by norm_num, Nat.count_succ]
  rw [show 3478 = 3477 + 1 by norm_num, Nat.count_succ]
  rw [show 3477 = 3476 + 1 by norm_num, Nat.count_succ]
  rw [show 3476 = 3475 + 1 by norm_num, Nat.count_succ]
  rw [show 3475 = 3474 + 1 by norm_num, Nat.count_succ]
  rw [show 3474 = 3473 + 1 by norm_num, Nat.count_succ]
  rw [show 3473 = 3472 + 1 by norm_num, Nat.count_succ]
  rw [show 3472 = 3471 + 1 by norm_num, Nat.count_succ]
  rw [show 3471 = 3470 + 1 by norm_num, Nat.count_succ]
  rw [show 3470 = 3469 + 1 by norm_num, Nat.count_succ]
  rw [count_3469]
  simp [prime_3469, not_prime_3470, not_prime_3471, not_prime_3472, not_prime_3473, not_prime_3474, not_prime_3475, not_prime_3476, not_prime_3477, not_prime_3478, not_prime_3479, not_prime_3480, not_prime_3481, not_prime_3482, not_prime_3483, not_prime_3484, not_prime_3485, not_prime_3486, not_prime_3487, not_prime_3488, not_prime_3489, not_prime_3490]

theorem prime_3491 : (3491 : Nat).Prime := by norm_num

theorem nth_487 : Nat.nth Nat.Prime 487 = 3491 := by
  rw [← count_3491]
  exact Nat.nth_count prime_3491

theorem not_prime_3492 : ¬Nat.Prime 3492 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1746) (n := 3492)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3493 : ¬Nat.Prime 3493 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 499) (n := 3493)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3494 : ¬Nat.Prime 3494 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1747) (n := 3494)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3495 : ¬Nat.Prime 3495 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1165) (n := 3495)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3496 : ¬Nat.Prime 3496 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1748) (n := 3496)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3497 : ¬Nat.Prime 3497 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 269) (n := 3497)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3498 : ¬Nat.Prime 3498 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1749) (n := 3498)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3499 : Nat.count Nat.Prime 3499 = 488 := by
  rw [show 3499 = 3498 + 1 by norm_num, Nat.count_succ]
  rw [show 3498 = 3497 + 1 by norm_num, Nat.count_succ]
  rw [show 3497 = 3496 + 1 by norm_num, Nat.count_succ]
  rw [show 3496 = 3495 + 1 by norm_num, Nat.count_succ]
  rw [show 3495 = 3494 + 1 by norm_num, Nat.count_succ]
  rw [show 3494 = 3493 + 1 by norm_num, Nat.count_succ]
  rw [show 3493 = 3492 + 1 by norm_num, Nat.count_succ]
  rw [show 3492 = 3491 + 1 by norm_num, Nat.count_succ]
  rw [count_3491]
  simp [prime_3491, not_prime_3492, not_prime_3493, not_prime_3494, not_prime_3495, not_prime_3496, not_prime_3497, not_prime_3498]

theorem prime_3499 : (3499 : Nat).Prime := by norm_num

theorem nth_488 : Nat.nth Nat.Prime 488 = 3499 := by
  rw [← count_3499]
  exact Nat.nth_count prime_3499

theorem not_prime_3500 : ¬Nat.Prime 3500 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1750) (n := 3500)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3501 : ¬Nat.Prime 3501 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1167) (n := 3501)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3502 : ¬Nat.Prime 3502 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1751) (n := 3502)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3503 : ¬Nat.Prime 3503 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 113) (n := 3503)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3504 : ¬Nat.Prime 3504 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1752) (n := 3504)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3505 : ¬Nat.Prime 3505 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 701) (n := 3505)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3506 : ¬Nat.Prime 3506 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1753) (n := 3506)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3507 : ¬Nat.Prime 3507 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1169) (n := 3507)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3508 : ¬Nat.Prime 3508 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1754) (n := 3508)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3509 : ¬Nat.Prime 3509 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 319) (n := 3509)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3510 : ¬Nat.Prime 3510 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1755) (n := 3510)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3511 : Nat.count Nat.Prime 3511 = 489 := by
  rw [show 3511 = 3510 + 1 by norm_num, Nat.count_succ]
  rw [show 3510 = 3509 + 1 by norm_num, Nat.count_succ]
  rw [show 3509 = 3508 + 1 by norm_num, Nat.count_succ]
  rw [show 3508 = 3507 + 1 by norm_num, Nat.count_succ]
  rw [show 3507 = 3506 + 1 by norm_num, Nat.count_succ]
  rw [show 3506 = 3505 + 1 by norm_num, Nat.count_succ]
  rw [show 3505 = 3504 + 1 by norm_num, Nat.count_succ]
  rw [show 3504 = 3503 + 1 by norm_num, Nat.count_succ]
  rw [show 3503 = 3502 + 1 by norm_num, Nat.count_succ]
  rw [show 3502 = 3501 + 1 by norm_num, Nat.count_succ]
  rw [show 3501 = 3500 + 1 by norm_num, Nat.count_succ]
  rw [show 3500 = 3499 + 1 by norm_num, Nat.count_succ]
  rw [count_3499]
  simp [prime_3499, not_prime_3500, not_prime_3501, not_prime_3502, not_prime_3503, not_prime_3504, not_prime_3505, not_prime_3506, not_prime_3507, not_prime_3508, not_prime_3509, not_prime_3510]

theorem prime_3511 : (3511 : Nat).Prime := by norm_num

theorem nth_489 : Nat.nth Nat.Prime 489 = 3511 := by
  rw [← count_3511]
  exact Nat.nth_count prime_3511

theorem not_prime_3512 : ¬Nat.Prime 3512 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1756) (n := 3512)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3513 : ¬Nat.Prime 3513 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1171) (n := 3513)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3514 : ¬Nat.Prime 3514 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1757) (n := 3514)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3515 : ¬Nat.Prime 3515 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 703) (n := 3515)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3516 : ¬Nat.Prime 3516 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1758) (n := 3516)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3517 : Nat.count Nat.Prime 3517 = 490 := by
  rw [show 3517 = 3516 + 1 by norm_num, Nat.count_succ]
  rw [show 3516 = 3515 + 1 by norm_num, Nat.count_succ]
  rw [show 3515 = 3514 + 1 by norm_num, Nat.count_succ]
  rw [show 3514 = 3513 + 1 by norm_num, Nat.count_succ]
  rw [show 3513 = 3512 + 1 by norm_num, Nat.count_succ]
  rw [show 3512 = 3511 + 1 by norm_num, Nat.count_succ]
  rw [count_3511]
  simp [prime_3511, not_prime_3512, not_prime_3513, not_prime_3514, not_prime_3515, not_prime_3516]

theorem prime_3517 : (3517 : Nat).Prime := by norm_num

theorem nth_490 : Nat.nth Nat.Prime 490 = 3517 := by
  rw [← count_3517]
  exact Nat.nth_count prime_3517

theorem not_prime_3518 : ¬Nat.Prime 3518 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1759) (n := 3518)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3519 : ¬Nat.Prime 3519 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1173) (n := 3519)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3520 : ¬Nat.Prime 3520 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1760) (n := 3520)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3521 : ¬Nat.Prime 3521 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 503) (n := 3521)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3522 : ¬Nat.Prime 3522 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1761) (n := 3522)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3523 : ¬Nat.Prime 3523 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 271) (n := 3523)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3524 : ¬Nat.Prime 3524 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1762) (n := 3524)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3525 : ¬Nat.Prime 3525 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1175) (n := 3525)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3526 : ¬Nat.Prime 3526 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1763) (n := 3526)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3527 : Nat.count Nat.Prime 3527 = 491 := by
  rw [show 3527 = 3526 + 1 by norm_num, Nat.count_succ]
  rw [show 3526 = 3525 + 1 by norm_num, Nat.count_succ]
  rw [show 3525 = 3524 + 1 by norm_num, Nat.count_succ]
  rw [show 3524 = 3523 + 1 by norm_num, Nat.count_succ]
  rw [show 3523 = 3522 + 1 by norm_num, Nat.count_succ]
  rw [show 3522 = 3521 + 1 by norm_num, Nat.count_succ]
  rw [show 3521 = 3520 + 1 by norm_num, Nat.count_succ]
  rw [show 3520 = 3519 + 1 by norm_num, Nat.count_succ]
  rw [show 3519 = 3518 + 1 by norm_num, Nat.count_succ]
  rw [show 3518 = 3517 + 1 by norm_num, Nat.count_succ]
  rw [count_3517]
  simp [prime_3517, not_prime_3518, not_prime_3519, not_prime_3520, not_prime_3521, not_prime_3522, not_prime_3523, not_prime_3524, not_prime_3525, not_prime_3526]

theorem prime_3527 : (3527 : Nat).Prime := by norm_num

theorem nth_491 : Nat.nth Nat.Prime 491 = 3527 := by
  rw [← count_3527]
  exact Nat.nth_count prime_3527

theorem not_prime_3528 : ¬Nat.Prime 3528 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1764) (n := 3528)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3529 : Nat.count Nat.Prime 3529 = 492 := by
  rw [show 3529 = 3528 + 1 by norm_num, Nat.count_succ]
  rw [show 3528 = 3527 + 1 by norm_num, Nat.count_succ]
  rw [count_3527]
  simp [prime_3527, not_prime_3528]

theorem prime_3529 : (3529 : Nat).Prime := by norm_num

theorem nth_492 : Nat.nth Nat.Prime 492 = 3529 := by
  rw [← count_3529]
  exact Nat.nth_count prime_3529

theorem not_prime_3530 : ¬Nat.Prime 3530 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1765) (n := 3530)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3531 : ¬Nat.Prime 3531 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1177) (n := 3531)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3532 : ¬Nat.Prime 3532 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1766) (n := 3532)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3533 : Nat.count Nat.Prime 3533 = 493 := by
  rw [show 3533 = 3532 + 1 by norm_num, Nat.count_succ]
  rw [show 3532 = 3531 + 1 by norm_num, Nat.count_succ]
  rw [show 3531 = 3530 + 1 by norm_num, Nat.count_succ]
  rw [show 3530 = 3529 + 1 by norm_num, Nat.count_succ]
  rw [count_3529]
  simp [prime_3529, not_prime_3530, not_prime_3531, not_prime_3532]

theorem prime_3533 : (3533 : Nat).Prime := by norm_num

theorem nth_493 : Nat.nth Nat.Prime 493 = 3533 := by
  rw [← count_3533]
  exact Nat.nth_count prime_3533

theorem not_prime_3534 : ¬Nat.Prime 3534 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1767) (n := 3534)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3535 : ¬Nat.Prime 3535 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 707) (n := 3535)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3536 : ¬Nat.Prime 3536 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1768) (n := 3536)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3537 : ¬Nat.Prime 3537 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1179) (n := 3537)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3538 : ¬Nat.Prime 3538 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1769) (n := 3538)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3539 : Nat.count Nat.Prime 3539 = 494 := by
  rw [show 3539 = 3538 + 1 by norm_num, Nat.count_succ]
  rw [show 3538 = 3537 + 1 by norm_num, Nat.count_succ]
  rw [show 3537 = 3536 + 1 by norm_num, Nat.count_succ]
  rw [show 3536 = 3535 + 1 by norm_num, Nat.count_succ]
  rw [show 3535 = 3534 + 1 by norm_num, Nat.count_succ]
  rw [show 3534 = 3533 + 1 by norm_num, Nat.count_succ]
  rw [count_3533]
  simp [prime_3533, not_prime_3534, not_prime_3535, not_prime_3536, not_prime_3537, not_prime_3538]

theorem prime_3539 : (3539 : Nat).Prime := by norm_num

theorem nth_494 : Nat.nth Nat.Prime 494 = 3539 := by
  rw [← count_3539]
  exact Nat.nth_count prime_3539

theorem not_prime_3540 : ¬Nat.Prime 3540 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1770) (n := 3540)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3541 : Nat.count Nat.Prime 3541 = 495 := by
  rw [show 3541 = 3540 + 1 by norm_num, Nat.count_succ]
  rw [show 3540 = 3539 + 1 by norm_num, Nat.count_succ]
  rw [count_3539]
  simp [prime_3539, not_prime_3540]

theorem prime_3541 : (3541 : Nat).Prime := by norm_num

theorem nth_495 : Nat.nth Nat.Prime 495 = 3541 := by
  rw [← count_3541]
  exact Nat.nth_count prime_3541

theorem not_prime_3542 : ¬Nat.Prime 3542 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1771) (n := 3542)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3543 : ¬Nat.Prime 3543 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1181) (n := 3543)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3544 : ¬Nat.Prime 3544 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1772) (n := 3544)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3545 : ¬Nat.Prime 3545 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 709) (n := 3545)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3546 : ¬Nat.Prime 3546 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1773) (n := 3546)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3547 : Nat.count Nat.Prime 3547 = 496 := by
  rw [show 3547 = 3546 + 1 by norm_num, Nat.count_succ]
  rw [show 3546 = 3545 + 1 by norm_num, Nat.count_succ]
  rw [show 3545 = 3544 + 1 by norm_num, Nat.count_succ]
  rw [show 3544 = 3543 + 1 by norm_num, Nat.count_succ]
  rw [show 3543 = 3542 + 1 by norm_num, Nat.count_succ]
  rw [show 3542 = 3541 + 1 by norm_num, Nat.count_succ]
  rw [count_3541]
  simp [prime_3541, not_prime_3542, not_prime_3543, not_prime_3544, not_prime_3545, not_prime_3546]

theorem prime_3547 : (3547 : Nat).Prime := by norm_num

theorem nth_496 : Nat.nth Nat.Prime 496 = 3547 := by
  rw [← count_3547]
  exact Nat.nth_count prime_3547

theorem not_prime_3548 : ¬Nat.Prime 3548 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1774) (n := 3548)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3549 : ¬Nat.Prime 3549 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1183) (n := 3549)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3550 : ¬Nat.Prime 3550 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1775) (n := 3550)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3551 : ¬Nat.Prime 3551 :=
  Nat.not_prime_of_mul_eq (a := 53) (b := 67) (n := 3551)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3552 : ¬Nat.Prime 3552 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1776) (n := 3552)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3553 : ¬Nat.Prime 3553 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 323) (n := 3553)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3554 : ¬Nat.Prime 3554 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1777) (n := 3554)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3555 : ¬Nat.Prime 3555 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1185) (n := 3555)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3556 : ¬Nat.Prime 3556 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1778) (n := 3556)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3557 : Nat.count Nat.Prime 3557 = 497 := by
  rw [show 3557 = 3556 + 1 by norm_num, Nat.count_succ]
  rw [show 3556 = 3555 + 1 by norm_num, Nat.count_succ]
  rw [show 3555 = 3554 + 1 by norm_num, Nat.count_succ]
  rw [show 3554 = 3553 + 1 by norm_num, Nat.count_succ]
  rw [show 3553 = 3552 + 1 by norm_num, Nat.count_succ]
  rw [show 3552 = 3551 + 1 by norm_num, Nat.count_succ]
  rw [show 3551 = 3550 + 1 by norm_num, Nat.count_succ]
  rw [show 3550 = 3549 + 1 by norm_num, Nat.count_succ]
  rw [show 3549 = 3548 + 1 by norm_num, Nat.count_succ]
  rw [show 3548 = 3547 + 1 by norm_num, Nat.count_succ]
  rw [count_3547]
  simp [prime_3547, not_prime_3548, not_prime_3549, not_prime_3550, not_prime_3551, not_prime_3552, not_prime_3553, not_prime_3554, not_prime_3555, not_prime_3556]

theorem prime_3557 : (3557 : Nat).Prime := by norm_num

theorem nth_497 : Nat.nth Nat.Prime 497 = 3557 := by
  rw [← count_3557]
  exact Nat.nth_count prime_3557

theorem not_prime_3558 : ¬Nat.Prime 3558 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1779) (n := 3558)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3559 : Nat.count Nat.Prime 3559 = 498 := by
  rw [show 3559 = 3558 + 1 by norm_num, Nat.count_succ]
  rw [show 3558 = 3557 + 1 by norm_num, Nat.count_succ]
  rw [count_3557]
  simp [prime_3557, not_prime_3558]

theorem prime_3559 : (3559 : Nat).Prime := by norm_num

theorem nth_498 : Nat.nth Nat.Prime 498 = 3559 := by
  rw [← count_3559]
  exact Nat.nth_count prime_3559

theorem not_prime_3560 : ¬Nat.Prime 3560 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1780) (n := 3560)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3561 : ¬Nat.Prime 3561 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1187) (n := 3561)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3562 : ¬Nat.Prime 3562 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1781) (n := 3562)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3563 : ¬Nat.Prime 3563 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 509) (n := 3563)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3564 : ¬Nat.Prime 3564 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1782) (n := 3564)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3565 : ¬Nat.Prime 3565 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 713) (n := 3565)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3566 : ¬Nat.Prime 3566 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1783) (n := 3566)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3567 : ¬Nat.Prime 3567 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1189) (n := 3567)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3568 : ¬Nat.Prime 3568 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1784) (n := 3568)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3569 : ¬Nat.Prime 3569 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 83) (n := 3569)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3570 : ¬Nat.Prime 3570 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1785) (n := 3570)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3571 : Nat.count Nat.Prime 3571 = 499 := by
  rw [show 3571 = 3570 + 1 by norm_num, Nat.count_succ]
  rw [show 3570 = 3569 + 1 by norm_num, Nat.count_succ]
  rw [show 3569 = 3568 + 1 by norm_num, Nat.count_succ]
  rw [show 3568 = 3567 + 1 by norm_num, Nat.count_succ]
  rw [show 3567 = 3566 + 1 by norm_num, Nat.count_succ]
  rw [show 3566 = 3565 + 1 by norm_num, Nat.count_succ]
  rw [show 3565 = 3564 + 1 by norm_num, Nat.count_succ]
  rw [show 3564 = 3563 + 1 by norm_num, Nat.count_succ]
  rw [show 3563 = 3562 + 1 by norm_num, Nat.count_succ]
  rw [show 3562 = 3561 + 1 by norm_num, Nat.count_succ]
  rw [show 3561 = 3560 + 1 by norm_num, Nat.count_succ]
  rw [show 3560 = 3559 + 1 by norm_num, Nat.count_succ]
  rw [count_3559]
  simp [prime_3559, not_prime_3560, not_prime_3561, not_prime_3562, not_prime_3563, not_prime_3564, not_prime_3565, not_prime_3566, not_prime_3567, not_prime_3568, not_prime_3569, not_prime_3570]

theorem prime_3571 : (3571 : Nat).Prime := by norm_num

theorem nth_499 : Nat.nth Nat.Prime 499 = 3571 := by
  rw [← count_3571]
  exact Nat.nth_count prime_3571

end OeisA100474.PrimeCertificate
