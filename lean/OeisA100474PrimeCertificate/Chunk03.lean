import OeisA100474PrimeCertificate.Chunk02

/-! Kernel prime/count certificate, chunk 03 (75–99). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_380 : ¬Nat.Prime 380 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 190) (n := 380)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_381 : ¬Nat.Prime 381 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 127) (n := 381)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_382 : ¬Nat.Prime 382 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 191) (n := 382)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_383 : Nat.count Nat.Prime 383 = 75 := by
  rw [show 383 = 382 + 1 by norm_num, Nat.count_succ]
  rw [show 382 = 381 + 1 by norm_num, Nat.count_succ]
  rw [show 381 = 380 + 1 by norm_num, Nat.count_succ]
  rw [show 380 = 379 + 1 by norm_num, Nat.count_succ]
  rw [count_379]
  simp [prime_379, not_prime_380, not_prime_381, not_prime_382]

theorem prime_383 : (383 : Nat).Prime := by norm_num

theorem nth_75 : Nat.nth Nat.Prime 75 = 383 := by
  rw [← count_383]
  exact Nat.nth_count prime_383

theorem not_prime_384 : ¬Nat.Prime 384 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 192) (n := 384)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_385 : ¬Nat.Prime 385 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 77) (n := 385)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_386 : ¬Nat.Prime 386 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 193) (n := 386)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_387 : ¬Nat.Prime 387 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 129) (n := 387)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_388 : ¬Nat.Prime 388 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 194) (n := 388)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_389 : Nat.count Nat.Prime 389 = 76 := by
  rw [show 389 = 388 + 1 by norm_num, Nat.count_succ]
  rw [show 388 = 387 + 1 by norm_num, Nat.count_succ]
  rw [show 387 = 386 + 1 by norm_num, Nat.count_succ]
  rw [show 386 = 385 + 1 by norm_num, Nat.count_succ]
  rw [show 385 = 384 + 1 by norm_num, Nat.count_succ]
  rw [show 384 = 383 + 1 by norm_num, Nat.count_succ]
  rw [count_383]
  simp [prime_383, not_prime_384, not_prime_385, not_prime_386, not_prime_387, not_prime_388]

theorem prime_389 : (389 : Nat).Prime := by norm_num

theorem nth_76 : Nat.nth Nat.Prime 76 = 389 := by
  rw [← count_389]
  exact Nat.nth_count prime_389

theorem not_prime_390 : ¬Nat.Prime 390 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 195) (n := 390)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_391 : ¬Nat.Prime 391 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 23) (n := 391)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_392 : ¬Nat.Prime 392 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 196) (n := 392)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_393 : ¬Nat.Prime 393 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 131) (n := 393)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_394 : ¬Nat.Prime 394 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 197) (n := 394)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_395 : ¬Nat.Prime 395 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 79) (n := 395)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_396 : ¬Nat.Prime 396 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 198) (n := 396)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_397 : Nat.count Nat.Prime 397 = 77 := by
  rw [show 397 = 396 + 1 by norm_num, Nat.count_succ]
  rw [show 396 = 395 + 1 by norm_num, Nat.count_succ]
  rw [show 395 = 394 + 1 by norm_num, Nat.count_succ]
  rw [show 394 = 393 + 1 by norm_num, Nat.count_succ]
  rw [show 393 = 392 + 1 by norm_num, Nat.count_succ]
  rw [show 392 = 391 + 1 by norm_num, Nat.count_succ]
  rw [show 391 = 390 + 1 by norm_num, Nat.count_succ]
  rw [show 390 = 389 + 1 by norm_num, Nat.count_succ]
  rw [count_389]
  simp [prime_389, not_prime_390, not_prime_391, not_prime_392, not_prime_393, not_prime_394, not_prime_395, not_prime_396]

theorem prime_397 : (397 : Nat).Prime := by norm_num

theorem nth_77 : Nat.nth Nat.Prime 77 = 397 := by
  rw [← count_397]
  exact Nat.nth_count prime_397

theorem not_prime_398 : ¬Nat.Prime 398 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 199) (n := 398)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_399 : ¬Nat.Prime 399 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 133) (n := 399)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_400 : ¬Nat.Prime 400 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 200) (n := 400)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_401 : Nat.count Nat.Prime 401 = 78 := by
  rw [show 401 = 400 + 1 by norm_num, Nat.count_succ]
  rw [show 400 = 399 + 1 by norm_num, Nat.count_succ]
  rw [show 399 = 398 + 1 by norm_num, Nat.count_succ]
  rw [show 398 = 397 + 1 by norm_num, Nat.count_succ]
  rw [count_397]
  simp [prime_397, not_prime_398, not_prime_399, not_prime_400]

theorem prime_401 : (401 : Nat).Prime := by norm_num

theorem nth_78 : Nat.nth Nat.Prime 78 = 401 := by
  rw [← count_401]
  exact Nat.nth_count prime_401

theorem not_prime_402 : ¬Nat.Prime 402 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 201) (n := 402)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_403 : ¬Nat.Prime 403 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 31) (n := 403)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_404 : ¬Nat.Prime 404 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 202) (n := 404)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_405 : ¬Nat.Prime 405 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 135) (n := 405)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_406 : ¬Nat.Prime 406 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 203) (n := 406)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_407 : ¬Nat.Prime 407 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 37) (n := 407)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_408 : ¬Nat.Prime 408 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 204) (n := 408)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_409 : Nat.count Nat.Prime 409 = 79 := by
  rw [show 409 = 408 + 1 by norm_num, Nat.count_succ]
  rw [show 408 = 407 + 1 by norm_num, Nat.count_succ]
  rw [show 407 = 406 + 1 by norm_num, Nat.count_succ]
  rw [show 406 = 405 + 1 by norm_num, Nat.count_succ]
  rw [show 405 = 404 + 1 by norm_num, Nat.count_succ]
  rw [show 404 = 403 + 1 by norm_num, Nat.count_succ]
  rw [show 403 = 402 + 1 by norm_num, Nat.count_succ]
  rw [show 402 = 401 + 1 by norm_num, Nat.count_succ]
  rw [count_401]
  simp [prime_401, not_prime_402, not_prime_403, not_prime_404, not_prime_405, not_prime_406, not_prime_407, not_prime_408]

theorem prime_409 : (409 : Nat).Prime := by norm_num

theorem nth_79 : Nat.nth Nat.Prime 79 = 409 := by
  rw [← count_409]
  exact Nat.nth_count prime_409

theorem not_prime_410 : ¬Nat.Prime 410 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 205) (n := 410)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_411 : ¬Nat.Prime 411 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 137) (n := 411)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_412 : ¬Nat.Prime 412 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 206) (n := 412)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_413 : ¬Nat.Prime 413 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 59) (n := 413)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_414 : ¬Nat.Prime 414 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 207) (n := 414)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_415 : ¬Nat.Prime 415 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 83) (n := 415)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_416 : ¬Nat.Prime 416 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 208) (n := 416)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_417 : ¬Nat.Prime 417 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 139) (n := 417)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_418 : ¬Nat.Prime 418 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 209) (n := 418)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_419 : Nat.count Nat.Prime 419 = 80 := by
  rw [show 419 = 418 + 1 by norm_num, Nat.count_succ]
  rw [show 418 = 417 + 1 by norm_num, Nat.count_succ]
  rw [show 417 = 416 + 1 by norm_num, Nat.count_succ]
  rw [show 416 = 415 + 1 by norm_num, Nat.count_succ]
  rw [show 415 = 414 + 1 by norm_num, Nat.count_succ]
  rw [show 414 = 413 + 1 by norm_num, Nat.count_succ]
  rw [show 413 = 412 + 1 by norm_num, Nat.count_succ]
  rw [show 412 = 411 + 1 by norm_num, Nat.count_succ]
  rw [show 411 = 410 + 1 by norm_num, Nat.count_succ]
  rw [show 410 = 409 + 1 by norm_num, Nat.count_succ]
  rw [count_409]
  simp [prime_409, not_prime_410, not_prime_411, not_prime_412, not_prime_413, not_prime_414, not_prime_415, not_prime_416, not_prime_417, not_prime_418]

theorem prime_419 : (419 : Nat).Prime := by norm_num

theorem nth_80 : Nat.nth Nat.Prime 80 = 419 := by
  rw [← count_419]
  exact Nat.nth_count prime_419

theorem not_prime_420 : ¬Nat.Prime 420 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 210) (n := 420)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_421 : Nat.count Nat.Prime 421 = 81 := by
  rw [show 421 = 420 + 1 by norm_num, Nat.count_succ]
  rw [show 420 = 419 + 1 by norm_num, Nat.count_succ]
  rw [count_419]
  simp [prime_419, not_prime_420]

theorem prime_421 : (421 : Nat).Prime := by norm_num

theorem nth_81 : Nat.nth Nat.Prime 81 = 421 := by
  rw [← count_421]
  exact Nat.nth_count prime_421

theorem not_prime_422 : ¬Nat.Prime 422 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 211) (n := 422)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_423 : ¬Nat.Prime 423 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 141) (n := 423)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_424 : ¬Nat.Prime 424 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 212) (n := 424)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_425 : ¬Nat.Prime 425 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 85) (n := 425)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_426 : ¬Nat.Prime 426 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 213) (n := 426)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_427 : ¬Nat.Prime 427 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 61) (n := 427)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_428 : ¬Nat.Prime 428 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 214) (n := 428)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_429 : ¬Nat.Prime 429 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 143) (n := 429)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_430 : ¬Nat.Prime 430 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 215) (n := 430)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_431 : Nat.count Nat.Prime 431 = 82 := by
  rw [show 431 = 430 + 1 by norm_num, Nat.count_succ]
  rw [show 430 = 429 + 1 by norm_num, Nat.count_succ]
  rw [show 429 = 428 + 1 by norm_num, Nat.count_succ]
  rw [show 428 = 427 + 1 by norm_num, Nat.count_succ]
  rw [show 427 = 426 + 1 by norm_num, Nat.count_succ]
  rw [show 426 = 425 + 1 by norm_num, Nat.count_succ]
  rw [show 425 = 424 + 1 by norm_num, Nat.count_succ]
  rw [show 424 = 423 + 1 by norm_num, Nat.count_succ]
  rw [show 423 = 422 + 1 by norm_num, Nat.count_succ]
  rw [show 422 = 421 + 1 by norm_num, Nat.count_succ]
  rw [count_421]
  simp [prime_421, not_prime_422, not_prime_423, not_prime_424, not_prime_425, not_prime_426, not_prime_427, not_prime_428, not_prime_429, not_prime_430]

theorem prime_431 : (431 : Nat).Prime := by norm_num

theorem nth_82 : Nat.nth Nat.Prime 82 = 431 := by
  rw [← count_431]
  exact Nat.nth_count prime_431

theorem not_prime_432 : ¬Nat.Prime 432 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 216) (n := 432)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_433 : Nat.count Nat.Prime 433 = 83 := by
  rw [show 433 = 432 + 1 by norm_num, Nat.count_succ]
  rw [show 432 = 431 + 1 by norm_num, Nat.count_succ]
  rw [count_431]
  simp [prime_431, not_prime_432]

theorem prime_433 : (433 : Nat).Prime := by norm_num

theorem nth_83 : Nat.nth Nat.Prime 83 = 433 := by
  rw [← count_433]
  exact Nat.nth_count prime_433

theorem not_prime_434 : ¬Nat.Prime 434 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 217) (n := 434)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_435 : ¬Nat.Prime 435 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 145) (n := 435)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_436 : ¬Nat.Prime 436 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 218) (n := 436)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_437 : ¬Nat.Prime 437 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 23) (n := 437)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_438 : ¬Nat.Prime 438 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 219) (n := 438)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_439 : Nat.count Nat.Prime 439 = 84 := by
  rw [show 439 = 438 + 1 by norm_num, Nat.count_succ]
  rw [show 438 = 437 + 1 by norm_num, Nat.count_succ]
  rw [show 437 = 436 + 1 by norm_num, Nat.count_succ]
  rw [show 436 = 435 + 1 by norm_num, Nat.count_succ]
  rw [show 435 = 434 + 1 by norm_num, Nat.count_succ]
  rw [show 434 = 433 + 1 by norm_num, Nat.count_succ]
  rw [count_433]
  simp [prime_433, not_prime_434, not_prime_435, not_prime_436, not_prime_437, not_prime_438]

theorem prime_439 : (439 : Nat).Prime := by norm_num

theorem nth_84 : Nat.nth Nat.Prime 84 = 439 := by
  rw [← count_439]
  exact Nat.nth_count prime_439

theorem not_prime_440 : ¬Nat.Prime 440 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 220) (n := 440)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_441 : ¬Nat.Prime 441 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 147) (n := 441)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_442 : ¬Nat.Prime 442 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 221) (n := 442)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_443 : Nat.count Nat.Prime 443 = 85 := by
  rw [show 443 = 442 + 1 by norm_num, Nat.count_succ]
  rw [show 442 = 441 + 1 by norm_num, Nat.count_succ]
  rw [show 441 = 440 + 1 by norm_num, Nat.count_succ]
  rw [show 440 = 439 + 1 by norm_num, Nat.count_succ]
  rw [count_439]
  simp [prime_439, not_prime_440, not_prime_441, not_prime_442]

theorem prime_443 : (443 : Nat).Prime := by norm_num

theorem nth_85 : Nat.nth Nat.Prime 85 = 443 := by
  rw [← count_443]
  exact Nat.nth_count prime_443

theorem not_prime_444 : ¬Nat.Prime 444 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 222) (n := 444)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_445 : ¬Nat.Prime 445 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 89) (n := 445)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_446 : ¬Nat.Prime 446 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 223) (n := 446)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_447 : ¬Nat.Prime 447 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 149) (n := 447)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_448 : ¬Nat.Prime 448 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 224) (n := 448)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_449 : Nat.count Nat.Prime 449 = 86 := by
  rw [show 449 = 448 + 1 by norm_num, Nat.count_succ]
  rw [show 448 = 447 + 1 by norm_num, Nat.count_succ]
  rw [show 447 = 446 + 1 by norm_num, Nat.count_succ]
  rw [show 446 = 445 + 1 by norm_num, Nat.count_succ]
  rw [show 445 = 444 + 1 by norm_num, Nat.count_succ]
  rw [show 444 = 443 + 1 by norm_num, Nat.count_succ]
  rw [count_443]
  simp [prime_443, not_prime_444, not_prime_445, not_prime_446, not_prime_447, not_prime_448]

theorem prime_449 : (449 : Nat).Prime := by norm_num

theorem nth_86 : Nat.nth Nat.Prime 86 = 449 := by
  rw [← count_449]
  exact Nat.nth_count prime_449

theorem not_prime_450 : ¬Nat.Prime 450 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 225) (n := 450)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_451 : ¬Nat.Prime 451 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 41) (n := 451)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_452 : ¬Nat.Prime 452 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 226) (n := 452)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_453 : ¬Nat.Prime 453 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 151) (n := 453)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_454 : ¬Nat.Prime 454 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 227) (n := 454)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_455 : ¬Nat.Prime 455 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 91) (n := 455)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_456 : ¬Nat.Prime 456 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 228) (n := 456)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_457 : Nat.count Nat.Prime 457 = 87 := by
  rw [show 457 = 456 + 1 by norm_num, Nat.count_succ]
  rw [show 456 = 455 + 1 by norm_num, Nat.count_succ]
  rw [show 455 = 454 + 1 by norm_num, Nat.count_succ]
  rw [show 454 = 453 + 1 by norm_num, Nat.count_succ]
  rw [show 453 = 452 + 1 by norm_num, Nat.count_succ]
  rw [show 452 = 451 + 1 by norm_num, Nat.count_succ]
  rw [show 451 = 450 + 1 by norm_num, Nat.count_succ]
  rw [show 450 = 449 + 1 by norm_num, Nat.count_succ]
  rw [count_449]
  simp [prime_449, not_prime_450, not_prime_451, not_prime_452, not_prime_453, not_prime_454, not_prime_455, not_prime_456]

theorem prime_457 : (457 : Nat).Prime := by norm_num

theorem nth_87 : Nat.nth Nat.Prime 87 = 457 := by
  rw [← count_457]
  exact Nat.nth_count prime_457

theorem not_prime_458 : ¬Nat.Prime 458 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 229) (n := 458)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_459 : ¬Nat.Prime 459 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 153) (n := 459)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_460 : ¬Nat.Prime 460 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 230) (n := 460)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_461 : Nat.count Nat.Prime 461 = 88 := by
  rw [show 461 = 460 + 1 by norm_num, Nat.count_succ]
  rw [show 460 = 459 + 1 by norm_num, Nat.count_succ]
  rw [show 459 = 458 + 1 by norm_num, Nat.count_succ]
  rw [show 458 = 457 + 1 by norm_num, Nat.count_succ]
  rw [count_457]
  simp [prime_457, not_prime_458, not_prime_459, not_prime_460]

theorem prime_461 : (461 : Nat).Prime := by norm_num

theorem nth_88 : Nat.nth Nat.Prime 88 = 461 := by
  rw [← count_461]
  exact Nat.nth_count prime_461

theorem not_prime_462 : ¬Nat.Prime 462 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 231) (n := 462)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_463 : Nat.count Nat.Prime 463 = 89 := by
  rw [show 463 = 462 + 1 by norm_num, Nat.count_succ]
  rw [show 462 = 461 + 1 by norm_num, Nat.count_succ]
  rw [count_461]
  simp [prime_461, not_prime_462]

theorem prime_463 : (463 : Nat).Prime := by norm_num

theorem nth_89 : Nat.nth Nat.Prime 89 = 463 := by
  rw [← count_463]
  exact Nat.nth_count prime_463

theorem not_prime_464 : ¬Nat.Prime 464 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 232) (n := 464)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_465 : ¬Nat.Prime 465 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 155) (n := 465)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_466 : ¬Nat.Prime 466 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 233) (n := 466)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_467 : Nat.count Nat.Prime 467 = 90 := by
  rw [show 467 = 466 + 1 by norm_num, Nat.count_succ]
  rw [show 466 = 465 + 1 by norm_num, Nat.count_succ]
  rw [show 465 = 464 + 1 by norm_num, Nat.count_succ]
  rw [show 464 = 463 + 1 by norm_num, Nat.count_succ]
  rw [count_463]
  simp [prime_463, not_prime_464, not_prime_465, not_prime_466]

theorem prime_467 : (467 : Nat).Prime := by norm_num

theorem nth_90 : Nat.nth Nat.Prime 90 = 467 := by
  rw [← count_467]
  exact Nat.nth_count prime_467

theorem not_prime_468 : ¬Nat.Prime 468 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 234) (n := 468)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_469 : ¬Nat.Prime 469 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 67) (n := 469)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_470 : ¬Nat.Prime 470 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 235) (n := 470)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_471 : ¬Nat.Prime 471 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 157) (n := 471)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_472 : ¬Nat.Prime 472 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 236) (n := 472)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_473 : ¬Nat.Prime 473 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 43) (n := 473)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_474 : ¬Nat.Prime 474 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 237) (n := 474)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_475 : ¬Nat.Prime 475 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 95) (n := 475)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_476 : ¬Nat.Prime 476 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 238) (n := 476)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_477 : ¬Nat.Prime 477 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 159) (n := 477)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_478 : ¬Nat.Prime 478 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 239) (n := 478)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_479 : Nat.count Nat.Prime 479 = 91 := by
  rw [show 479 = 478 + 1 by norm_num, Nat.count_succ]
  rw [show 478 = 477 + 1 by norm_num, Nat.count_succ]
  rw [show 477 = 476 + 1 by norm_num, Nat.count_succ]
  rw [show 476 = 475 + 1 by norm_num, Nat.count_succ]
  rw [show 475 = 474 + 1 by norm_num, Nat.count_succ]
  rw [show 474 = 473 + 1 by norm_num, Nat.count_succ]
  rw [show 473 = 472 + 1 by norm_num, Nat.count_succ]
  rw [show 472 = 471 + 1 by norm_num, Nat.count_succ]
  rw [show 471 = 470 + 1 by norm_num, Nat.count_succ]
  rw [show 470 = 469 + 1 by norm_num, Nat.count_succ]
  rw [show 469 = 468 + 1 by norm_num, Nat.count_succ]
  rw [show 468 = 467 + 1 by norm_num, Nat.count_succ]
  rw [count_467]
  simp [prime_467, not_prime_468, not_prime_469, not_prime_470, not_prime_471, not_prime_472, not_prime_473, not_prime_474, not_prime_475, not_prime_476, not_prime_477, not_prime_478]

theorem prime_479 : (479 : Nat).Prime := by norm_num

theorem nth_91 : Nat.nth Nat.Prime 91 = 479 := by
  rw [← count_479]
  exact Nat.nth_count prime_479

theorem not_prime_480 : ¬Nat.Prime 480 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 240) (n := 480)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_481 : ¬Nat.Prime 481 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 37) (n := 481)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_482 : ¬Nat.Prime 482 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 241) (n := 482)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_483 : ¬Nat.Prime 483 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 161) (n := 483)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_484 : ¬Nat.Prime 484 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 242) (n := 484)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_485 : ¬Nat.Prime 485 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 97) (n := 485)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_486 : ¬Nat.Prime 486 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 243) (n := 486)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_487 : Nat.count Nat.Prime 487 = 92 := by
  rw [show 487 = 486 + 1 by norm_num, Nat.count_succ]
  rw [show 486 = 485 + 1 by norm_num, Nat.count_succ]
  rw [show 485 = 484 + 1 by norm_num, Nat.count_succ]
  rw [show 484 = 483 + 1 by norm_num, Nat.count_succ]
  rw [show 483 = 482 + 1 by norm_num, Nat.count_succ]
  rw [show 482 = 481 + 1 by norm_num, Nat.count_succ]
  rw [show 481 = 480 + 1 by norm_num, Nat.count_succ]
  rw [show 480 = 479 + 1 by norm_num, Nat.count_succ]
  rw [count_479]
  simp [prime_479, not_prime_480, not_prime_481, not_prime_482, not_prime_483, not_prime_484, not_prime_485, not_prime_486]

theorem prime_487 : (487 : Nat).Prime := by norm_num

theorem nth_92 : Nat.nth Nat.Prime 92 = 487 := by
  rw [← count_487]
  exact Nat.nth_count prime_487

theorem not_prime_488 : ¬Nat.Prime 488 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 244) (n := 488)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_489 : ¬Nat.Prime 489 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 163) (n := 489)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_490 : ¬Nat.Prime 490 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 245) (n := 490)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_491 : Nat.count Nat.Prime 491 = 93 := by
  rw [show 491 = 490 + 1 by norm_num, Nat.count_succ]
  rw [show 490 = 489 + 1 by norm_num, Nat.count_succ]
  rw [show 489 = 488 + 1 by norm_num, Nat.count_succ]
  rw [show 488 = 487 + 1 by norm_num, Nat.count_succ]
  rw [count_487]
  simp [prime_487, not_prime_488, not_prime_489, not_prime_490]

theorem prime_491 : (491 : Nat).Prime := by norm_num

theorem nth_93 : Nat.nth Nat.Prime 93 = 491 := by
  rw [← count_491]
  exact Nat.nth_count prime_491

theorem not_prime_492 : ¬Nat.Prime 492 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 246) (n := 492)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_493 : ¬Nat.Prime 493 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 29) (n := 493)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_494 : ¬Nat.Prime 494 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 247) (n := 494)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_495 : ¬Nat.Prime 495 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 165) (n := 495)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_496 : ¬Nat.Prime 496 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 248) (n := 496)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_497 : ¬Nat.Prime 497 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 71) (n := 497)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_498 : ¬Nat.Prime 498 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 249) (n := 498)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_499 : Nat.count Nat.Prime 499 = 94 := by
  rw [show 499 = 498 + 1 by norm_num, Nat.count_succ]
  rw [show 498 = 497 + 1 by norm_num, Nat.count_succ]
  rw [show 497 = 496 + 1 by norm_num, Nat.count_succ]
  rw [show 496 = 495 + 1 by norm_num, Nat.count_succ]
  rw [show 495 = 494 + 1 by norm_num, Nat.count_succ]
  rw [show 494 = 493 + 1 by norm_num, Nat.count_succ]
  rw [show 493 = 492 + 1 by norm_num, Nat.count_succ]
  rw [show 492 = 491 + 1 by norm_num, Nat.count_succ]
  rw [count_491]
  simp [prime_491, not_prime_492, not_prime_493, not_prime_494, not_prime_495, not_prime_496, not_prime_497, not_prime_498]

theorem prime_499 : (499 : Nat).Prime := by norm_num

theorem nth_94 : Nat.nth Nat.Prime 94 = 499 := by
  rw [← count_499]
  exact Nat.nth_count prime_499

theorem not_prime_500 : ¬Nat.Prime 500 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 250) (n := 500)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_501 : ¬Nat.Prime 501 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 167) (n := 501)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_502 : ¬Nat.Prime 502 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 251) (n := 502)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_503 : Nat.count Nat.Prime 503 = 95 := by
  rw [show 503 = 502 + 1 by norm_num, Nat.count_succ]
  rw [show 502 = 501 + 1 by norm_num, Nat.count_succ]
  rw [show 501 = 500 + 1 by norm_num, Nat.count_succ]
  rw [show 500 = 499 + 1 by norm_num, Nat.count_succ]
  rw [count_499]
  simp [prime_499, not_prime_500, not_prime_501, not_prime_502]

theorem prime_503 : (503 : Nat).Prime := by norm_num

theorem nth_95 : Nat.nth Nat.Prime 95 = 503 := by
  rw [← count_503]
  exact Nat.nth_count prime_503

theorem not_prime_504 : ¬Nat.Prime 504 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 252) (n := 504)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_505 : ¬Nat.Prime 505 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 101) (n := 505)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_506 : ¬Nat.Prime 506 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 253) (n := 506)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_507 : ¬Nat.Prime 507 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 169) (n := 507)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_508 : ¬Nat.Prime 508 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 254) (n := 508)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_509 : Nat.count Nat.Prime 509 = 96 := by
  rw [show 509 = 508 + 1 by norm_num, Nat.count_succ]
  rw [show 508 = 507 + 1 by norm_num, Nat.count_succ]
  rw [show 507 = 506 + 1 by norm_num, Nat.count_succ]
  rw [show 506 = 505 + 1 by norm_num, Nat.count_succ]
  rw [show 505 = 504 + 1 by norm_num, Nat.count_succ]
  rw [show 504 = 503 + 1 by norm_num, Nat.count_succ]
  rw [count_503]
  simp [prime_503, not_prime_504, not_prime_505, not_prime_506, not_prime_507, not_prime_508]

theorem prime_509 : (509 : Nat).Prime := by norm_num

theorem nth_96 : Nat.nth Nat.Prime 96 = 509 := by
  rw [← count_509]
  exact Nat.nth_count prime_509

theorem not_prime_510 : ¬Nat.Prime 510 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 255) (n := 510)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_511 : ¬Nat.Prime 511 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 73) (n := 511)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_512 : ¬Nat.Prime 512 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 256) (n := 512)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_513 : ¬Nat.Prime 513 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 171) (n := 513)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_514 : ¬Nat.Prime 514 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 257) (n := 514)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_515 : ¬Nat.Prime 515 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 103) (n := 515)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_516 : ¬Nat.Prime 516 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 258) (n := 516)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_517 : ¬Nat.Prime 517 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 47) (n := 517)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_518 : ¬Nat.Prime 518 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 259) (n := 518)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_519 : ¬Nat.Prime 519 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 173) (n := 519)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_520 : ¬Nat.Prime 520 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 260) (n := 520)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_521 : Nat.count Nat.Prime 521 = 97 := by
  rw [show 521 = 520 + 1 by norm_num, Nat.count_succ]
  rw [show 520 = 519 + 1 by norm_num, Nat.count_succ]
  rw [show 519 = 518 + 1 by norm_num, Nat.count_succ]
  rw [show 518 = 517 + 1 by norm_num, Nat.count_succ]
  rw [show 517 = 516 + 1 by norm_num, Nat.count_succ]
  rw [show 516 = 515 + 1 by norm_num, Nat.count_succ]
  rw [show 515 = 514 + 1 by norm_num, Nat.count_succ]
  rw [show 514 = 513 + 1 by norm_num, Nat.count_succ]
  rw [show 513 = 512 + 1 by norm_num, Nat.count_succ]
  rw [show 512 = 511 + 1 by norm_num, Nat.count_succ]
  rw [show 511 = 510 + 1 by norm_num, Nat.count_succ]
  rw [show 510 = 509 + 1 by norm_num, Nat.count_succ]
  rw [count_509]
  simp [prime_509, not_prime_510, not_prime_511, not_prime_512, not_prime_513, not_prime_514, not_prime_515, not_prime_516, not_prime_517, not_prime_518, not_prime_519, not_prime_520]

theorem prime_521 : (521 : Nat).Prime := by norm_num

theorem nth_97 : Nat.nth Nat.Prime 97 = 521 := by
  rw [← count_521]
  exact Nat.nth_count prime_521

theorem not_prime_522 : ¬Nat.Prime 522 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 261) (n := 522)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_523 : Nat.count Nat.Prime 523 = 98 := by
  rw [show 523 = 522 + 1 by norm_num, Nat.count_succ]
  rw [show 522 = 521 + 1 by norm_num, Nat.count_succ]
  rw [count_521]
  simp [prime_521, not_prime_522]

theorem prime_523 : (523 : Nat).Prime := by norm_num

theorem nth_98 : Nat.nth Nat.Prime 98 = 523 := by
  rw [← count_523]
  exact Nat.nth_count prime_523

theorem not_prime_524 : ¬Nat.Prime 524 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 262) (n := 524)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_525 : ¬Nat.Prime 525 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 175) (n := 525)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_526 : ¬Nat.Prime 526 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 263) (n := 526)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_527 : ¬Nat.Prime 527 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 31) (n := 527)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_528 : ¬Nat.Prime 528 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 264) (n := 528)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_529 : ¬Nat.Prime 529 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 23) (n := 529)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_530 : ¬Nat.Prime 530 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 265) (n := 530)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_531 : ¬Nat.Prime 531 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 177) (n := 531)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_532 : ¬Nat.Prime 532 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 266) (n := 532)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_533 : ¬Nat.Prime 533 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 41) (n := 533)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_534 : ¬Nat.Prime 534 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 267) (n := 534)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_535 : ¬Nat.Prime 535 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 107) (n := 535)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_536 : ¬Nat.Prime 536 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 268) (n := 536)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_537 : ¬Nat.Prime 537 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 179) (n := 537)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_538 : ¬Nat.Prime 538 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 269) (n := 538)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_539 : ¬Nat.Prime 539 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 77) (n := 539)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_540 : ¬Nat.Prime 540 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 270) (n := 540)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_541 : Nat.count Nat.Prime 541 = 99 := by
  rw [show 541 = 540 + 1 by norm_num, Nat.count_succ]
  rw [show 540 = 539 + 1 by norm_num, Nat.count_succ]
  rw [show 539 = 538 + 1 by norm_num, Nat.count_succ]
  rw [show 538 = 537 + 1 by norm_num, Nat.count_succ]
  rw [show 537 = 536 + 1 by norm_num, Nat.count_succ]
  rw [show 536 = 535 + 1 by norm_num, Nat.count_succ]
  rw [show 535 = 534 + 1 by norm_num, Nat.count_succ]
  rw [show 534 = 533 + 1 by norm_num, Nat.count_succ]
  rw [show 533 = 532 + 1 by norm_num, Nat.count_succ]
  rw [show 532 = 531 + 1 by norm_num, Nat.count_succ]
  rw [show 531 = 530 + 1 by norm_num, Nat.count_succ]
  rw [show 530 = 529 + 1 by norm_num, Nat.count_succ]
  rw [show 529 = 528 + 1 by norm_num, Nat.count_succ]
  rw [show 528 = 527 + 1 by norm_num, Nat.count_succ]
  rw [show 527 = 526 + 1 by norm_num, Nat.count_succ]
  rw [show 526 = 525 + 1 by norm_num, Nat.count_succ]
  rw [show 525 = 524 + 1 by norm_num, Nat.count_succ]
  rw [show 524 = 523 + 1 by norm_num, Nat.count_succ]
  rw [count_523]
  simp [prime_523, not_prime_524, not_prime_525, not_prime_526, not_prime_527, not_prime_528, not_prime_529, not_prime_530, not_prime_531, not_prime_532, not_prime_533, not_prime_534, not_prime_535, not_prime_536, not_prime_537, not_prime_538, not_prime_539, not_prime_540]

theorem prime_541 : (541 : Nat).Prime := by norm_num

theorem nth_99 : Nat.nth Nat.Prime 99 = 541 := by
  rw [← count_541]
  exact Nat.nth_count prime_541

end OeisA100474.PrimeCertificate
