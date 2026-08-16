import OeisA100474PrimeCertificate.Chunk08

/-! Kernel prime/count certificate, chunk 09 (225–249). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_1428 : ¬Nat.Prime 1428 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 714) (n := 1428)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1429 : Nat.count Nat.Prime 1429 = 225 := by
  rw [show 1429 = 1428 + 1 by norm_num, Nat.count_succ]
  rw [show 1428 = 1427 + 1 by norm_num, Nat.count_succ]
  rw [count_1427]
  simp [prime_1427, not_prime_1428]

theorem prime_1429 : (1429 : Nat).Prime := by norm_num

theorem nth_225 : Nat.nth Nat.Prime 225 = 1429 := by
  rw [← count_1429]
  exact Nat.nth_count prime_1429

theorem not_prime_1430 : ¬Nat.Prime 1430 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 715) (n := 1430)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1431 : ¬Nat.Prime 1431 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 477) (n := 1431)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1432 : ¬Nat.Prime 1432 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 716) (n := 1432)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1433 : Nat.count Nat.Prime 1433 = 226 := by
  rw [show 1433 = 1432 + 1 by norm_num, Nat.count_succ]
  rw [show 1432 = 1431 + 1 by norm_num, Nat.count_succ]
  rw [show 1431 = 1430 + 1 by norm_num, Nat.count_succ]
  rw [show 1430 = 1429 + 1 by norm_num, Nat.count_succ]
  rw [count_1429]
  simp [prime_1429, not_prime_1430, not_prime_1431, not_prime_1432]

theorem prime_1433 : (1433 : Nat).Prime := by norm_num

theorem nth_226 : Nat.nth Nat.Prime 226 = 1433 := by
  rw [← count_1433]
  exact Nat.nth_count prime_1433

theorem not_prime_1434 : ¬Nat.Prime 1434 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 717) (n := 1434)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1435 : ¬Nat.Prime 1435 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 287) (n := 1435)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1436 : ¬Nat.Prime 1436 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 718) (n := 1436)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1437 : ¬Nat.Prime 1437 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 479) (n := 1437)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1438 : ¬Nat.Prime 1438 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 719) (n := 1438)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1439 : Nat.count Nat.Prime 1439 = 227 := by
  rw [show 1439 = 1438 + 1 by norm_num, Nat.count_succ]
  rw [show 1438 = 1437 + 1 by norm_num, Nat.count_succ]
  rw [show 1437 = 1436 + 1 by norm_num, Nat.count_succ]
  rw [show 1436 = 1435 + 1 by norm_num, Nat.count_succ]
  rw [show 1435 = 1434 + 1 by norm_num, Nat.count_succ]
  rw [show 1434 = 1433 + 1 by norm_num, Nat.count_succ]
  rw [count_1433]
  simp [prime_1433, not_prime_1434, not_prime_1435, not_prime_1436, not_prime_1437, not_prime_1438]

theorem prime_1439 : (1439 : Nat).Prime := by norm_num

theorem nth_227 : Nat.nth Nat.Prime 227 = 1439 := by
  rw [← count_1439]
  exact Nat.nth_count prime_1439

theorem not_prime_1440 : ¬Nat.Prime 1440 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 720) (n := 1440)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1441 : ¬Nat.Prime 1441 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 131) (n := 1441)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1442 : ¬Nat.Prime 1442 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 721) (n := 1442)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1443 : ¬Nat.Prime 1443 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 481) (n := 1443)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1444 : ¬Nat.Prime 1444 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 722) (n := 1444)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1445 : ¬Nat.Prime 1445 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 289) (n := 1445)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1446 : ¬Nat.Prime 1446 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 723) (n := 1446)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1447 : Nat.count Nat.Prime 1447 = 228 := by
  rw [show 1447 = 1446 + 1 by norm_num, Nat.count_succ]
  rw [show 1446 = 1445 + 1 by norm_num, Nat.count_succ]
  rw [show 1445 = 1444 + 1 by norm_num, Nat.count_succ]
  rw [show 1444 = 1443 + 1 by norm_num, Nat.count_succ]
  rw [show 1443 = 1442 + 1 by norm_num, Nat.count_succ]
  rw [show 1442 = 1441 + 1 by norm_num, Nat.count_succ]
  rw [show 1441 = 1440 + 1 by norm_num, Nat.count_succ]
  rw [show 1440 = 1439 + 1 by norm_num, Nat.count_succ]
  rw [count_1439]
  simp [prime_1439, not_prime_1440, not_prime_1441, not_prime_1442, not_prime_1443, not_prime_1444, not_prime_1445, not_prime_1446]

theorem prime_1447 : (1447 : Nat).Prime := by norm_num

theorem nth_228 : Nat.nth Nat.Prime 228 = 1447 := by
  rw [← count_1447]
  exact Nat.nth_count prime_1447

theorem not_prime_1448 : ¬Nat.Prime 1448 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 724) (n := 1448)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1449 : ¬Nat.Prime 1449 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 483) (n := 1449)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1450 : ¬Nat.Prime 1450 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 725) (n := 1450)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1451 : Nat.count Nat.Prime 1451 = 229 := by
  rw [show 1451 = 1450 + 1 by norm_num, Nat.count_succ]
  rw [show 1450 = 1449 + 1 by norm_num, Nat.count_succ]
  rw [show 1449 = 1448 + 1 by norm_num, Nat.count_succ]
  rw [show 1448 = 1447 + 1 by norm_num, Nat.count_succ]
  rw [count_1447]
  simp [prime_1447, not_prime_1448, not_prime_1449, not_prime_1450]

theorem prime_1451 : (1451 : Nat).Prime := by norm_num

theorem nth_229 : Nat.nth Nat.Prime 229 = 1451 := by
  rw [← count_1451]
  exact Nat.nth_count prime_1451

theorem not_prime_1452 : ¬Nat.Prime 1452 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 726) (n := 1452)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1453 : Nat.count Nat.Prime 1453 = 230 := by
  rw [show 1453 = 1452 + 1 by norm_num, Nat.count_succ]
  rw [show 1452 = 1451 + 1 by norm_num, Nat.count_succ]
  rw [count_1451]
  simp [prime_1451, not_prime_1452]

theorem prime_1453 : (1453 : Nat).Prime := by norm_num

theorem nth_230 : Nat.nth Nat.Prime 230 = 1453 := by
  rw [← count_1453]
  exact Nat.nth_count prime_1453

theorem not_prime_1454 : ¬Nat.Prime 1454 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 727) (n := 1454)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1455 : ¬Nat.Prime 1455 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 485) (n := 1455)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1456 : ¬Nat.Prime 1456 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 728) (n := 1456)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1457 : ¬Nat.Prime 1457 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 47) (n := 1457)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1458 : ¬Nat.Prime 1458 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 729) (n := 1458)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1459 : Nat.count Nat.Prime 1459 = 231 := by
  rw [show 1459 = 1458 + 1 by norm_num, Nat.count_succ]
  rw [show 1458 = 1457 + 1 by norm_num, Nat.count_succ]
  rw [show 1457 = 1456 + 1 by norm_num, Nat.count_succ]
  rw [show 1456 = 1455 + 1 by norm_num, Nat.count_succ]
  rw [show 1455 = 1454 + 1 by norm_num, Nat.count_succ]
  rw [show 1454 = 1453 + 1 by norm_num, Nat.count_succ]
  rw [count_1453]
  simp [prime_1453, not_prime_1454, not_prime_1455, not_prime_1456, not_prime_1457, not_prime_1458]

theorem prime_1459 : (1459 : Nat).Prime := by norm_num

theorem nth_231 : Nat.nth Nat.Prime 231 = 1459 := by
  rw [← count_1459]
  exact Nat.nth_count prime_1459

theorem not_prime_1460 : ¬Nat.Prime 1460 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 730) (n := 1460)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1461 : ¬Nat.Prime 1461 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 487) (n := 1461)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1462 : ¬Nat.Prime 1462 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 731) (n := 1462)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1463 : ¬Nat.Prime 1463 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 209) (n := 1463)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1464 : ¬Nat.Prime 1464 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 732) (n := 1464)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1465 : ¬Nat.Prime 1465 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 293) (n := 1465)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1466 : ¬Nat.Prime 1466 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 733) (n := 1466)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1467 : ¬Nat.Prime 1467 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 489) (n := 1467)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1468 : ¬Nat.Prime 1468 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 734) (n := 1468)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1469 : ¬Nat.Prime 1469 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 113) (n := 1469)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1470 : ¬Nat.Prime 1470 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 735) (n := 1470)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1471 : Nat.count Nat.Prime 1471 = 232 := by
  rw [show 1471 = 1470 + 1 by norm_num, Nat.count_succ]
  rw [show 1470 = 1469 + 1 by norm_num, Nat.count_succ]
  rw [show 1469 = 1468 + 1 by norm_num, Nat.count_succ]
  rw [show 1468 = 1467 + 1 by norm_num, Nat.count_succ]
  rw [show 1467 = 1466 + 1 by norm_num, Nat.count_succ]
  rw [show 1466 = 1465 + 1 by norm_num, Nat.count_succ]
  rw [show 1465 = 1464 + 1 by norm_num, Nat.count_succ]
  rw [show 1464 = 1463 + 1 by norm_num, Nat.count_succ]
  rw [show 1463 = 1462 + 1 by norm_num, Nat.count_succ]
  rw [show 1462 = 1461 + 1 by norm_num, Nat.count_succ]
  rw [show 1461 = 1460 + 1 by norm_num, Nat.count_succ]
  rw [show 1460 = 1459 + 1 by norm_num, Nat.count_succ]
  rw [count_1459]
  simp [prime_1459, not_prime_1460, not_prime_1461, not_prime_1462, not_prime_1463, not_prime_1464, not_prime_1465, not_prime_1466, not_prime_1467, not_prime_1468, not_prime_1469, not_prime_1470]

theorem prime_1471 : (1471 : Nat).Prime := by norm_num

theorem nth_232 : Nat.nth Nat.Prime 232 = 1471 := by
  rw [← count_1471]
  exact Nat.nth_count prime_1471

theorem not_prime_1472 : ¬Nat.Prime 1472 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 736) (n := 1472)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1473 : ¬Nat.Prime 1473 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 491) (n := 1473)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1474 : ¬Nat.Prime 1474 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 737) (n := 1474)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1475 : ¬Nat.Prime 1475 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 295) (n := 1475)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1476 : ¬Nat.Prime 1476 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 738) (n := 1476)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1477 : ¬Nat.Prime 1477 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 211) (n := 1477)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1478 : ¬Nat.Prime 1478 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 739) (n := 1478)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1479 : ¬Nat.Prime 1479 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 493) (n := 1479)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1480 : ¬Nat.Prime 1480 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 740) (n := 1480)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1481 : Nat.count Nat.Prime 1481 = 233 := by
  rw [show 1481 = 1480 + 1 by norm_num, Nat.count_succ]
  rw [show 1480 = 1479 + 1 by norm_num, Nat.count_succ]
  rw [show 1479 = 1478 + 1 by norm_num, Nat.count_succ]
  rw [show 1478 = 1477 + 1 by norm_num, Nat.count_succ]
  rw [show 1477 = 1476 + 1 by norm_num, Nat.count_succ]
  rw [show 1476 = 1475 + 1 by norm_num, Nat.count_succ]
  rw [show 1475 = 1474 + 1 by norm_num, Nat.count_succ]
  rw [show 1474 = 1473 + 1 by norm_num, Nat.count_succ]
  rw [show 1473 = 1472 + 1 by norm_num, Nat.count_succ]
  rw [show 1472 = 1471 + 1 by norm_num, Nat.count_succ]
  rw [count_1471]
  simp [prime_1471, not_prime_1472, not_prime_1473, not_prime_1474, not_prime_1475, not_prime_1476, not_prime_1477, not_prime_1478, not_prime_1479, not_prime_1480]

theorem prime_1481 : (1481 : Nat).Prime := by norm_num

theorem nth_233 : Nat.nth Nat.Prime 233 = 1481 := by
  rw [← count_1481]
  exact Nat.nth_count prime_1481

theorem not_prime_1482 : ¬Nat.Prime 1482 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 741) (n := 1482)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1483 : Nat.count Nat.Prime 1483 = 234 := by
  rw [show 1483 = 1482 + 1 by norm_num, Nat.count_succ]
  rw [show 1482 = 1481 + 1 by norm_num, Nat.count_succ]
  rw [count_1481]
  simp [prime_1481, not_prime_1482]

theorem prime_1483 : (1483 : Nat).Prime := by norm_num

theorem nth_234 : Nat.nth Nat.Prime 234 = 1483 := by
  rw [← count_1483]
  exact Nat.nth_count prime_1483

theorem not_prime_1484 : ¬Nat.Prime 1484 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 742) (n := 1484)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1485 : ¬Nat.Prime 1485 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 495) (n := 1485)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1486 : ¬Nat.Prime 1486 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 743) (n := 1486)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1487 : Nat.count Nat.Prime 1487 = 235 := by
  rw [show 1487 = 1486 + 1 by norm_num, Nat.count_succ]
  rw [show 1486 = 1485 + 1 by norm_num, Nat.count_succ]
  rw [show 1485 = 1484 + 1 by norm_num, Nat.count_succ]
  rw [show 1484 = 1483 + 1 by norm_num, Nat.count_succ]
  rw [count_1483]
  simp [prime_1483, not_prime_1484, not_prime_1485, not_prime_1486]

theorem prime_1487 : (1487 : Nat).Prime := by norm_num

theorem nth_235 : Nat.nth Nat.Prime 235 = 1487 := by
  rw [← count_1487]
  exact Nat.nth_count prime_1487

theorem not_prime_1488 : ¬Nat.Prime 1488 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 744) (n := 1488)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1489 : Nat.count Nat.Prime 1489 = 236 := by
  rw [show 1489 = 1488 + 1 by norm_num, Nat.count_succ]
  rw [show 1488 = 1487 + 1 by norm_num, Nat.count_succ]
  rw [count_1487]
  simp [prime_1487, not_prime_1488]

theorem prime_1489 : (1489 : Nat).Prime := by norm_num

theorem nth_236 : Nat.nth Nat.Prime 236 = 1489 := by
  rw [← count_1489]
  exact Nat.nth_count prime_1489

theorem not_prime_1490 : ¬Nat.Prime 1490 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 745) (n := 1490)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1491 : ¬Nat.Prime 1491 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 497) (n := 1491)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1492 : ¬Nat.Prime 1492 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 746) (n := 1492)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1493 : Nat.count Nat.Prime 1493 = 237 := by
  rw [show 1493 = 1492 + 1 by norm_num, Nat.count_succ]
  rw [show 1492 = 1491 + 1 by norm_num, Nat.count_succ]
  rw [show 1491 = 1490 + 1 by norm_num, Nat.count_succ]
  rw [show 1490 = 1489 + 1 by norm_num, Nat.count_succ]
  rw [count_1489]
  simp [prime_1489, not_prime_1490, not_prime_1491, not_prime_1492]

theorem prime_1493 : (1493 : Nat).Prime := by norm_num

theorem nth_237 : Nat.nth Nat.Prime 237 = 1493 := by
  rw [← count_1493]
  exact Nat.nth_count prime_1493

theorem not_prime_1494 : ¬Nat.Prime 1494 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 747) (n := 1494)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1495 : ¬Nat.Prime 1495 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 299) (n := 1495)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1496 : ¬Nat.Prime 1496 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 748) (n := 1496)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1497 : ¬Nat.Prime 1497 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 499) (n := 1497)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1498 : ¬Nat.Prime 1498 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 749) (n := 1498)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1499 : Nat.count Nat.Prime 1499 = 238 := by
  rw [show 1499 = 1498 + 1 by norm_num, Nat.count_succ]
  rw [show 1498 = 1497 + 1 by norm_num, Nat.count_succ]
  rw [show 1497 = 1496 + 1 by norm_num, Nat.count_succ]
  rw [show 1496 = 1495 + 1 by norm_num, Nat.count_succ]
  rw [show 1495 = 1494 + 1 by norm_num, Nat.count_succ]
  rw [show 1494 = 1493 + 1 by norm_num, Nat.count_succ]
  rw [count_1493]
  simp [prime_1493, not_prime_1494, not_prime_1495, not_prime_1496, not_prime_1497, not_prime_1498]

theorem prime_1499 : (1499 : Nat).Prime := by norm_num

theorem nth_238 : Nat.nth Nat.Prime 238 = 1499 := by
  rw [← count_1499]
  exact Nat.nth_count prime_1499

theorem not_prime_1500 : ¬Nat.Prime 1500 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 750) (n := 1500)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1501 : ¬Nat.Prime 1501 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 79) (n := 1501)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1502 : ¬Nat.Prime 1502 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 751) (n := 1502)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1503 : ¬Nat.Prime 1503 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 501) (n := 1503)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1504 : ¬Nat.Prime 1504 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 752) (n := 1504)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1505 : ¬Nat.Prime 1505 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 301) (n := 1505)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1506 : ¬Nat.Prime 1506 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 753) (n := 1506)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1507 : ¬Nat.Prime 1507 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 137) (n := 1507)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1508 : ¬Nat.Prime 1508 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 754) (n := 1508)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1509 : ¬Nat.Prime 1509 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 503) (n := 1509)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1510 : ¬Nat.Prime 1510 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 755) (n := 1510)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1511 : Nat.count Nat.Prime 1511 = 239 := by
  rw [show 1511 = 1510 + 1 by norm_num, Nat.count_succ]
  rw [show 1510 = 1509 + 1 by norm_num, Nat.count_succ]
  rw [show 1509 = 1508 + 1 by norm_num, Nat.count_succ]
  rw [show 1508 = 1507 + 1 by norm_num, Nat.count_succ]
  rw [show 1507 = 1506 + 1 by norm_num, Nat.count_succ]
  rw [show 1506 = 1505 + 1 by norm_num, Nat.count_succ]
  rw [show 1505 = 1504 + 1 by norm_num, Nat.count_succ]
  rw [show 1504 = 1503 + 1 by norm_num, Nat.count_succ]
  rw [show 1503 = 1502 + 1 by norm_num, Nat.count_succ]
  rw [show 1502 = 1501 + 1 by norm_num, Nat.count_succ]
  rw [show 1501 = 1500 + 1 by norm_num, Nat.count_succ]
  rw [show 1500 = 1499 + 1 by norm_num, Nat.count_succ]
  rw [count_1499]
  simp [prime_1499, not_prime_1500, not_prime_1501, not_prime_1502, not_prime_1503, not_prime_1504, not_prime_1505, not_prime_1506, not_prime_1507, not_prime_1508, not_prime_1509, not_prime_1510]

theorem prime_1511 : (1511 : Nat).Prime := by norm_num

theorem nth_239 : Nat.nth Nat.Prime 239 = 1511 := by
  rw [← count_1511]
  exact Nat.nth_count prime_1511

theorem not_prime_1512 : ¬Nat.Prime 1512 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 756) (n := 1512)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1513 : ¬Nat.Prime 1513 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 89) (n := 1513)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1514 : ¬Nat.Prime 1514 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 757) (n := 1514)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1515 : ¬Nat.Prime 1515 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 505) (n := 1515)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1516 : ¬Nat.Prime 1516 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 758) (n := 1516)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1517 : ¬Nat.Prime 1517 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 41) (n := 1517)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1518 : ¬Nat.Prime 1518 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 759) (n := 1518)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1519 : ¬Nat.Prime 1519 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 217) (n := 1519)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1520 : ¬Nat.Prime 1520 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 760) (n := 1520)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1521 : ¬Nat.Prime 1521 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 507) (n := 1521)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1522 : ¬Nat.Prime 1522 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 761) (n := 1522)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1523 : Nat.count Nat.Prime 1523 = 240 := by
  rw [show 1523 = 1522 + 1 by norm_num, Nat.count_succ]
  rw [show 1522 = 1521 + 1 by norm_num, Nat.count_succ]
  rw [show 1521 = 1520 + 1 by norm_num, Nat.count_succ]
  rw [show 1520 = 1519 + 1 by norm_num, Nat.count_succ]
  rw [show 1519 = 1518 + 1 by norm_num, Nat.count_succ]
  rw [show 1518 = 1517 + 1 by norm_num, Nat.count_succ]
  rw [show 1517 = 1516 + 1 by norm_num, Nat.count_succ]
  rw [show 1516 = 1515 + 1 by norm_num, Nat.count_succ]
  rw [show 1515 = 1514 + 1 by norm_num, Nat.count_succ]
  rw [show 1514 = 1513 + 1 by norm_num, Nat.count_succ]
  rw [show 1513 = 1512 + 1 by norm_num, Nat.count_succ]
  rw [show 1512 = 1511 + 1 by norm_num, Nat.count_succ]
  rw [count_1511]
  simp [prime_1511, not_prime_1512, not_prime_1513, not_prime_1514, not_prime_1515, not_prime_1516, not_prime_1517, not_prime_1518, not_prime_1519, not_prime_1520, not_prime_1521, not_prime_1522]

theorem prime_1523 : (1523 : Nat).Prime := by norm_num

theorem nth_240 : Nat.nth Nat.Prime 240 = 1523 := by
  rw [← count_1523]
  exact Nat.nth_count prime_1523

theorem not_prime_1524 : ¬Nat.Prime 1524 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 762) (n := 1524)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1525 : ¬Nat.Prime 1525 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 305) (n := 1525)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1526 : ¬Nat.Prime 1526 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 763) (n := 1526)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1527 : ¬Nat.Prime 1527 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 509) (n := 1527)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1528 : ¬Nat.Prime 1528 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 764) (n := 1528)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1529 : ¬Nat.Prime 1529 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 139) (n := 1529)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1530 : ¬Nat.Prime 1530 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 765) (n := 1530)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1531 : Nat.count Nat.Prime 1531 = 241 := by
  rw [show 1531 = 1530 + 1 by norm_num, Nat.count_succ]
  rw [show 1530 = 1529 + 1 by norm_num, Nat.count_succ]
  rw [show 1529 = 1528 + 1 by norm_num, Nat.count_succ]
  rw [show 1528 = 1527 + 1 by norm_num, Nat.count_succ]
  rw [show 1527 = 1526 + 1 by norm_num, Nat.count_succ]
  rw [show 1526 = 1525 + 1 by norm_num, Nat.count_succ]
  rw [show 1525 = 1524 + 1 by norm_num, Nat.count_succ]
  rw [show 1524 = 1523 + 1 by norm_num, Nat.count_succ]
  rw [count_1523]
  simp [prime_1523, not_prime_1524, not_prime_1525, not_prime_1526, not_prime_1527, not_prime_1528, not_prime_1529, not_prime_1530]

theorem prime_1531 : (1531 : Nat).Prime := by norm_num

theorem nth_241 : Nat.nth Nat.Prime 241 = 1531 := by
  rw [← count_1531]
  exact Nat.nth_count prime_1531

theorem not_prime_1532 : ¬Nat.Prime 1532 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 766) (n := 1532)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1533 : ¬Nat.Prime 1533 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 511) (n := 1533)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1534 : ¬Nat.Prime 1534 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 767) (n := 1534)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1535 : ¬Nat.Prime 1535 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 307) (n := 1535)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1536 : ¬Nat.Prime 1536 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 768) (n := 1536)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1537 : ¬Nat.Prime 1537 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 53) (n := 1537)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1538 : ¬Nat.Prime 1538 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 769) (n := 1538)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1539 : ¬Nat.Prime 1539 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 513) (n := 1539)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1540 : ¬Nat.Prime 1540 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 770) (n := 1540)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1541 : ¬Nat.Prime 1541 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 67) (n := 1541)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1542 : ¬Nat.Prime 1542 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 771) (n := 1542)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1543 : Nat.count Nat.Prime 1543 = 242 := by
  rw [show 1543 = 1542 + 1 by norm_num, Nat.count_succ]
  rw [show 1542 = 1541 + 1 by norm_num, Nat.count_succ]
  rw [show 1541 = 1540 + 1 by norm_num, Nat.count_succ]
  rw [show 1540 = 1539 + 1 by norm_num, Nat.count_succ]
  rw [show 1539 = 1538 + 1 by norm_num, Nat.count_succ]
  rw [show 1538 = 1537 + 1 by norm_num, Nat.count_succ]
  rw [show 1537 = 1536 + 1 by norm_num, Nat.count_succ]
  rw [show 1536 = 1535 + 1 by norm_num, Nat.count_succ]
  rw [show 1535 = 1534 + 1 by norm_num, Nat.count_succ]
  rw [show 1534 = 1533 + 1 by norm_num, Nat.count_succ]
  rw [show 1533 = 1532 + 1 by norm_num, Nat.count_succ]
  rw [show 1532 = 1531 + 1 by norm_num, Nat.count_succ]
  rw [count_1531]
  simp [prime_1531, not_prime_1532, not_prime_1533, not_prime_1534, not_prime_1535, not_prime_1536, not_prime_1537, not_prime_1538, not_prime_1539, not_prime_1540, not_prime_1541, not_prime_1542]

theorem prime_1543 : (1543 : Nat).Prime := by norm_num

theorem nth_242 : Nat.nth Nat.Prime 242 = 1543 := by
  rw [← count_1543]
  exact Nat.nth_count prime_1543

theorem not_prime_1544 : ¬Nat.Prime 1544 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 772) (n := 1544)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1545 : ¬Nat.Prime 1545 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 515) (n := 1545)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1546 : ¬Nat.Prime 1546 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 773) (n := 1546)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1547 : ¬Nat.Prime 1547 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 221) (n := 1547)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1548 : ¬Nat.Prime 1548 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 774) (n := 1548)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1549 : Nat.count Nat.Prime 1549 = 243 := by
  rw [show 1549 = 1548 + 1 by norm_num, Nat.count_succ]
  rw [show 1548 = 1547 + 1 by norm_num, Nat.count_succ]
  rw [show 1547 = 1546 + 1 by norm_num, Nat.count_succ]
  rw [show 1546 = 1545 + 1 by norm_num, Nat.count_succ]
  rw [show 1545 = 1544 + 1 by norm_num, Nat.count_succ]
  rw [show 1544 = 1543 + 1 by norm_num, Nat.count_succ]
  rw [count_1543]
  simp [prime_1543, not_prime_1544, not_prime_1545, not_prime_1546, not_prime_1547, not_prime_1548]

theorem prime_1549 : (1549 : Nat).Prime := by norm_num

theorem nth_243 : Nat.nth Nat.Prime 243 = 1549 := by
  rw [← count_1549]
  exact Nat.nth_count prime_1549

theorem not_prime_1550 : ¬Nat.Prime 1550 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 775) (n := 1550)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1551 : ¬Nat.Prime 1551 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 517) (n := 1551)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1552 : ¬Nat.Prime 1552 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 776) (n := 1552)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1553 : Nat.count Nat.Prime 1553 = 244 := by
  rw [show 1553 = 1552 + 1 by norm_num, Nat.count_succ]
  rw [show 1552 = 1551 + 1 by norm_num, Nat.count_succ]
  rw [show 1551 = 1550 + 1 by norm_num, Nat.count_succ]
  rw [show 1550 = 1549 + 1 by norm_num, Nat.count_succ]
  rw [count_1549]
  simp [prime_1549, not_prime_1550, not_prime_1551, not_prime_1552]

theorem prime_1553 : (1553 : Nat).Prime := by norm_num

theorem nth_244 : Nat.nth Nat.Prime 244 = 1553 := by
  rw [← count_1553]
  exact Nat.nth_count prime_1553

theorem not_prime_1554 : ¬Nat.Prime 1554 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 777) (n := 1554)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1555 : ¬Nat.Prime 1555 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 311) (n := 1555)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1556 : ¬Nat.Prime 1556 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 778) (n := 1556)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1557 : ¬Nat.Prime 1557 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 519) (n := 1557)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1558 : ¬Nat.Prime 1558 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 779) (n := 1558)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1559 : Nat.count Nat.Prime 1559 = 245 := by
  rw [show 1559 = 1558 + 1 by norm_num, Nat.count_succ]
  rw [show 1558 = 1557 + 1 by norm_num, Nat.count_succ]
  rw [show 1557 = 1556 + 1 by norm_num, Nat.count_succ]
  rw [show 1556 = 1555 + 1 by norm_num, Nat.count_succ]
  rw [show 1555 = 1554 + 1 by norm_num, Nat.count_succ]
  rw [show 1554 = 1553 + 1 by norm_num, Nat.count_succ]
  rw [count_1553]
  simp [prime_1553, not_prime_1554, not_prime_1555, not_prime_1556, not_prime_1557, not_prime_1558]

theorem prime_1559 : (1559 : Nat).Prime := by norm_num

theorem nth_245 : Nat.nth Nat.Prime 245 = 1559 := by
  rw [← count_1559]
  exact Nat.nth_count prime_1559

theorem not_prime_1560 : ¬Nat.Prime 1560 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 780) (n := 1560)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1561 : ¬Nat.Prime 1561 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 223) (n := 1561)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1562 : ¬Nat.Prime 1562 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 781) (n := 1562)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1563 : ¬Nat.Prime 1563 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 521) (n := 1563)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1564 : ¬Nat.Prime 1564 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 782) (n := 1564)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1565 : ¬Nat.Prime 1565 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 313) (n := 1565)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1566 : ¬Nat.Prime 1566 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 783) (n := 1566)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1567 : Nat.count Nat.Prime 1567 = 246 := by
  rw [show 1567 = 1566 + 1 by norm_num, Nat.count_succ]
  rw [show 1566 = 1565 + 1 by norm_num, Nat.count_succ]
  rw [show 1565 = 1564 + 1 by norm_num, Nat.count_succ]
  rw [show 1564 = 1563 + 1 by norm_num, Nat.count_succ]
  rw [show 1563 = 1562 + 1 by norm_num, Nat.count_succ]
  rw [show 1562 = 1561 + 1 by norm_num, Nat.count_succ]
  rw [show 1561 = 1560 + 1 by norm_num, Nat.count_succ]
  rw [show 1560 = 1559 + 1 by norm_num, Nat.count_succ]
  rw [count_1559]
  simp [prime_1559, not_prime_1560, not_prime_1561, not_prime_1562, not_prime_1563, not_prime_1564, not_prime_1565, not_prime_1566]

theorem prime_1567 : (1567 : Nat).Prime := by norm_num

theorem nth_246 : Nat.nth Nat.Prime 246 = 1567 := by
  rw [← count_1567]
  exact Nat.nth_count prime_1567

theorem not_prime_1568 : ¬Nat.Prime 1568 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 784) (n := 1568)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1569 : ¬Nat.Prime 1569 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 523) (n := 1569)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1570 : ¬Nat.Prime 1570 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 785) (n := 1570)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1571 : Nat.count Nat.Prime 1571 = 247 := by
  rw [show 1571 = 1570 + 1 by norm_num, Nat.count_succ]
  rw [show 1570 = 1569 + 1 by norm_num, Nat.count_succ]
  rw [show 1569 = 1568 + 1 by norm_num, Nat.count_succ]
  rw [show 1568 = 1567 + 1 by norm_num, Nat.count_succ]
  rw [count_1567]
  simp [prime_1567, not_prime_1568, not_prime_1569, not_prime_1570]

theorem prime_1571 : (1571 : Nat).Prime := by norm_num

theorem nth_247 : Nat.nth Nat.Prime 247 = 1571 := by
  rw [← count_1571]
  exact Nat.nth_count prime_1571

theorem not_prime_1572 : ¬Nat.Prime 1572 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 786) (n := 1572)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1573 : ¬Nat.Prime 1573 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 143) (n := 1573)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1574 : ¬Nat.Prime 1574 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 787) (n := 1574)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1575 : ¬Nat.Prime 1575 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 525) (n := 1575)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1576 : ¬Nat.Prime 1576 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 788) (n := 1576)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1577 : ¬Nat.Prime 1577 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 83) (n := 1577)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1578 : ¬Nat.Prime 1578 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 789) (n := 1578)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1579 : Nat.count Nat.Prime 1579 = 248 := by
  rw [show 1579 = 1578 + 1 by norm_num, Nat.count_succ]
  rw [show 1578 = 1577 + 1 by norm_num, Nat.count_succ]
  rw [show 1577 = 1576 + 1 by norm_num, Nat.count_succ]
  rw [show 1576 = 1575 + 1 by norm_num, Nat.count_succ]
  rw [show 1575 = 1574 + 1 by norm_num, Nat.count_succ]
  rw [show 1574 = 1573 + 1 by norm_num, Nat.count_succ]
  rw [show 1573 = 1572 + 1 by norm_num, Nat.count_succ]
  rw [show 1572 = 1571 + 1 by norm_num, Nat.count_succ]
  rw [count_1571]
  simp [prime_1571, not_prime_1572, not_prime_1573, not_prime_1574, not_prime_1575, not_prime_1576, not_prime_1577, not_prime_1578]

theorem prime_1579 : (1579 : Nat).Prime := by norm_num

theorem nth_248 : Nat.nth Nat.Prime 248 = 1579 := by
  rw [← count_1579]
  exact Nat.nth_count prime_1579

theorem not_prime_1580 : ¬Nat.Prime 1580 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 790) (n := 1580)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1581 : ¬Nat.Prime 1581 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 527) (n := 1581)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1582 : ¬Nat.Prime 1582 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 791) (n := 1582)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1583 : Nat.count Nat.Prime 1583 = 249 := by
  rw [show 1583 = 1582 + 1 by norm_num, Nat.count_succ]
  rw [show 1582 = 1581 + 1 by norm_num, Nat.count_succ]
  rw [show 1581 = 1580 + 1 by norm_num, Nat.count_succ]
  rw [show 1580 = 1579 + 1 by norm_num, Nat.count_succ]
  rw [count_1579]
  simp [prime_1579, not_prime_1580, not_prime_1581, not_prime_1582]

theorem prime_1583 : (1583 : Nat).Prime := by norm_num

theorem nth_249 : Nat.nth Nat.Prime 249 = 1583 := by
  rw [← count_1583]
  exact Nat.nth_count prime_1583

end OeisA100474.PrimeCertificate
