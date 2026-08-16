import OeisA100474PrimeCertificate.Chunk14

/-! Kernel prime/count certificate, chunk 15 (375–399). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_2558 : ¬Nat.Prime 2558 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1279) (n := 2558)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2559 : ¬Nat.Prime 2559 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 853) (n := 2559)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2560 : ¬Nat.Prime 2560 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1280) (n := 2560)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2561 : ¬Nat.Prime 2561 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 197) (n := 2561)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2562 : ¬Nat.Prime 2562 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1281) (n := 2562)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2563 : ¬Nat.Prime 2563 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 233) (n := 2563)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2564 : ¬Nat.Prime 2564 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1282) (n := 2564)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2565 : ¬Nat.Prime 2565 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 855) (n := 2565)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2566 : ¬Nat.Prime 2566 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1283) (n := 2566)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2567 : ¬Nat.Prime 2567 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 151) (n := 2567)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2568 : ¬Nat.Prime 2568 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1284) (n := 2568)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2569 : ¬Nat.Prime 2569 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 367) (n := 2569)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2570 : ¬Nat.Prime 2570 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1285) (n := 2570)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2571 : ¬Nat.Prime 2571 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 857) (n := 2571)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2572 : ¬Nat.Prime 2572 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1286) (n := 2572)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2573 : ¬Nat.Prime 2573 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 83) (n := 2573)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2574 : ¬Nat.Prime 2574 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1287) (n := 2574)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2575 : ¬Nat.Prime 2575 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 515) (n := 2575)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2576 : ¬Nat.Prime 2576 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1288) (n := 2576)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2577 : ¬Nat.Prime 2577 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 859) (n := 2577)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2578 : ¬Nat.Prime 2578 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1289) (n := 2578)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2579 : Nat.count Nat.Prime 2579 = 375 := by
  rw [show 2579 = 2578 + 1 by norm_num, Nat.count_succ]
  rw [show 2578 = 2577 + 1 by norm_num, Nat.count_succ]
  rw [show 2577 = 2576 + 1 by norm_num, Nat.count_succ]
  rw [show 2576 = 2575 + 1 by norm_num, Nat.count_succ]
  rw [show 2575 = 2574 + 1 by norm_num, Nat.count_succ]
  rw [show 2574 = 2573 + 1 by norm_num, Nat.count_succ]
  rw [show 2573 = 2572 + 1 by norm_num, Nat.count_succ]
  rw [show 2572 = 2571 + 1 by norm_num, Nat.count_succ]
  rw [show 2571 = 2570 + 1 by norm_num, Nat.count_succ]
  rw [show 2570 = 2569 + 1 by norm_num, Nat.count_succ]
  rw [show 2569 = 2568 + 1 by norm_num, Nat.count_succ]
  rw [show 2568 = 2567 + 1 by norm_num, Nat.count_succ]
  rw [show 2567 = 2566 + 1 by norm_num, Nat.count_succ]
  rw [show 2566 = 2565 + 1 by norm_num, Nat.count_succ]
  rw [show 2565 = 2564 + 1 by norm_num, Nat.count_succ]
  rw [show 2564 = 2563 + 1 by norm_num, Nat.count_succ]
  rw [show 2563 = 2562 + 1 by norm_num, Nat.count_succ]
  rw [show 2562 = 2561 + 1 by norm_num, Nat.count_succ]
  rw [show 2561 = 2560 + 1 by norm_num, Nat.count_succ]
  rw [show 2560 = 2559 + 1 by norm_num, Nat.count_succ]
  rw [show 2559 = 2558 + 1 by norm_num, Nat.count_succ]
  rw [show 2558 = 2557 + 1 by norm_num, Nat.count_succ]
  rw [count_2557]
  simp [prime_2557, not_prime_2558, not_prime_2559, not_prime_2560, not_prime_2561, not_prime_2562, not_prime_2563, not_prime_2564, not_prime_2565, not_prime_2566, not_prime_2567, not_prime_2568, not_prime_2569, not_prime_2570, not_prime_2571, not_prime_2572, not_prime_2573, not_prime_2574, not_prime_2575, not_prime_2576, not_prime_2577, not_prime_2578]

theorem prime_2579 : (2579 : Nat).Prime := by norm_num

theorem nth_375 : Nat.nth Nat.Prime 375 = 2579 := by
  rw [← count_2579]
  exact Nat.nth_count prime_2579

theorem not_prime_2580 : ¬Nat.Prime 2580 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1290) (n := 2580)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2581 : ¬Nat.Prime 2581 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 89) (n := 2581)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2582 : ¬Nat.Prime 2582 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1291) (n := 2582)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2583 : ¬Nat.Prime 2583 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 861) (n := 2583)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2584 : ¬Nat.Prime 2584 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1292) (n := 2584)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2585 : ¬Nat.Prime 2585 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 517) (n := 2585)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2586 : ¬Nat.Prime 2586 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1293) (n := 2586)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2587 : ¬Nat.Prime 2587 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 199) (n := 2587)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2588 : ¬Nat.Prime 2588 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1294) (n := 2588)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2589 : ¬Nat.Prime 2589 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 863) (n := 2589)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2590 : ¬Nat.Prime 2590 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1295) (n := 2590)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2591 : Nat.count Nat.Prime 2591 = 376 := by
  rw [show 2591 = 2590 + 1 by norm_num, Nat.count_succ]
  rw [show 2590 = 2589 + 1 by norm_num, Nat.count_succ]
  rw [show 2589 = 2588 + 1 by norm_num, Nat.count_succ]
  rw [show 2588 = 2587 + 1 by norm_num, Nat.count_succ]
  rw [show 2587 = 2586 + 1 by norm_num, Nat.count_succ]
  rw [show 2586 = 2585 + 1 by norm_num, Nat.count_succ]
  rw [show 2585 = 2584 + 1 by norm_num, Nat.count_succ]
  rw [show 2584 = 2583 + 1 by norm_num, Nat.count_succ]
  rw [show 2583 = 2582 + 1 by norm_num, Nat.count_succ]
  rw [show 2582 = 2581 + 1 by norm_num, Nat.count_succ]
  rw [show 2581 = 2580 + 1 by norm_num, Nat.count_succ]
  rw [show 2580 = 2579 + 1 by norm_num, Nat.count_succ]
  rw [count_2579]
  simp [prime_2579, not_prime_2580, not_prime_2581, not_prime_2582, not_prime_2583, not_prime_2584, not_prime_2585, not_prime_2586, not_prime_2587, not_prime_2588, not_prime_2589, not_prime_2590]

theorem prime_2591 : (2591 : Nat).Prime := by norm_num

theorem nth_376 : Nat.nth Nat.Prime 376 = 2591 := by
  rw [← count_2591]
  exact Nat.nth_count prime_2591

theorem not_prime_2592 : ¬Nat.Prime 2592 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1296) (n := 2592)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2593 : Nat.count Nat.Prime 2593 = 377 := by
  rw [show 2593 = 2592 + 1 by norm_num, Nat.count_succ]
  rw [show 2592 = 2591 + 1 by norm_num, Nat.count_succ]
  rw [count_2591]
  simp [prime_2591, not_prime_2592]

theorem prime_2593 : (2593 : Nat).Prime := by norm_num

theorem nth_377 : Nat.nth Nat.Prime 377 = 2593 := by
  rw [← count_2593]
  exact Nat.nth_count prime_2593

theorem not_prime_2594 : ¬Nat.Prime 2594 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1297) (n := 2594)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2595 : ¬Nat.Prime 2595 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 865) (n := 2595)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2596 : ¬Nat.Prime 2596 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1298) (n := 2596)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2597 : ¬Nat.Prime 2597 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 371) (n := 2597)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2598 : ¬Nat.Prime 2598 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1299) (n := 2598)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2599 : ¬Nat.Prime 2599 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 113) (n := 2599)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2600 : ¬Nat.Prime 2600 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1300) (n := 2600)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2601 : ¬Nat.Prime 2601 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 867) (n := 2601)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2602 : ¬Nat.Prime 2602 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1301) (n := 2602)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2603 : ¬Nat.Prime 2603 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 137) (n := 2603)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2604 : ¬Nat.Prime 2604 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1302) (n := 2604)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2605 : ¬Nat.Prime 2605 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 521) (n := 2605)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2606 : ¬Nat.Prime 2606 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1303) (n := 2606)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2607 : ¬Nat.Prime 2607 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 869) (n := 2607)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2608 : ¬Nat.Prime 2608 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1304) (n := 2608)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2609 : Nat.count Nat.Prime 2609 = 378 := by
  rw [show 2609 = 2608 + 1 by norm_num, Nat.count_succ]
  rw [show 2608 = 2607 + 1 by norm_num, Nat.count_succ]
  rw [show 2607 = 2606 + 1 by norm_num, Nat.count_succ]
  rw [show 2606 = 2605 + 1 by norm_num, Nat.count_succ]
  rw [show 2605 = 2604 + 1 by norm_num, Nat.count_succ]
  rw [show 2604 = 2603 + 1 by norm_num, Nat.count_succ]
  rw [show 2603 = 2602 + 1 by norm_num, Nat.count_succ]
  rw [show 2602 = 2601 + 1 by norm_num, Nat.count_succ]
  rw [show 2601 = 2600 + 1 by norm_num, Nat.count_succ]
  rw [show 2600 = 2599 + 1 by norm_num, Nat.count_succ]
  rw [show 2599 = 2598 + 1 by norm_num, Nat.count_succ]
  rw [show 2598 = 2597 + 1 by norm_num, Nat.count_succ]
  rw [show 2597 = 2596 + 1 by norm_num, Nat.count_succ]
  rw [show 2596 = 2595 + 1 by norm_num, Nat.count_succ]
  rw [show 2595 = 2594 + 1 by norm_num, Nat.count_succ]
  rw [show 2594 = 2593 + 1 by norm_num, Nat.count_succ]
  rw [count_2593]
  simp [prime_2593, not_prime_2594, not_prime_2595, not_prime_2596, not_prime_2597, not_prime_2598, not_prime_2599, not_prime_2600, not_prime_2601, not_prime_2602, not_prime_2603, not_prime_2604, not_prime_2605, not_prime_2606, not_prime_2607, not_prime_2608]

theorem prime_2609 : (2609 : Nat).Prime := by norm_num

theorem nth_378 : Nat.nth Nat.Prime 378 = 2609 := by
  rw [← count_2609]
  exact Nat.nth_count prime_2609

theorem not_prime_2610 : ¬Nat.Prime 2610 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1305) (n := 2610)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2611 : ¬Nat.Prime 2611 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 373) (n := 2611)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2612 : ¬Nat.Prime 2612 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1306) (n := 2612)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2613 : ¬Nat.Prime 2613 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 871) (n := 2613)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2614 : ¬Nat.Prime 2614 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1307) (n := 2614)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2615 : ¬Nat.Prime 2615 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 523) (n := 2615)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2616 : ¬Nat.Prime 2616 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1308) (n := 2616)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2617 : Nat.count Nat.Prime 2617 = 379 := by
  rw [show 2617 = 2616 + 1 by norm_num, Nat.count_succ]
  rw [show 2616 = 2615 + 1 by norm_num, Nat.count_succ]
  rw [show 2615 = 2614 + 1 by norm_num, Nat.count_succ]
  rw [show 2614 = 2613 + 1 by norm_num, Nat.count_succ]
  rw [show 2613 = 2612 + 1 by norm_num, Nat.count_succ]
  rw [show 2612 = 2611 + 1 by norm_num, Nat.count_succ]
  rw [show 2611 = 2610 + 1 by norm_num, Nat.count_succ]
  rw [show 2610 = 2609 + 1 by norm_num, Nat.count_succ]
  rw [count_2609]
  simp [prime_2609, not_prime_2610, not_prime_2611, not_prime_2612, not_prime_2613, not_prime_2614, not_prime_2615, not_prime_2616]

theorem prime_2617 : (2617 : Nat).Prime := by norm_num

theorem nth_379 : Nat.nth Nat.Prime 379 = 2617 := by
  rw [← count_2617]
  exact Nat.nth_count prime_2617

theorem not_prime_2618 : ¬Nat.Prime 2618 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1309) (n := 2618)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2619 : ¬Nat.Prime 2619 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 873) (n := 2619)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2620 : ¬Nat.Prime 2620 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1310) (n := 2620)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2621 : Nat.count Nat.Prime 2621 = 380 := by
  rw [show 2621 = 2620 + 1 by norm_num, Nat.count_succ]
  rw [show 2620 = 2619 + 1 by norm_num, Nat.count_succ]
  rw [show 2619 = 2618 + 1 by norm_num, Nat.count_succ]
  rw [show 2618 = 2617 + 1 by norm_num, Nat.count_succ]
  rw [count_2617]
  simp [prime_2617, not_prime_2618, not_prime_2619, not_prime_2620]

theorem prime_2621 : (2621 : Nat).Prime := by norm_num

theorem nth_380 : Nat.nth Nat.Prime 380 = 2621 := by
  rw [← count_2621]
  exact Nat.nth_count prime_2621

theorem not_prime_2622 : ¬Nat.Prime 2622 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1311) (n := 2622)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2623 : ¬Nat.Prime 2623 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 61) (n := 2623)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2624 : ¬Nat.Prime 2624 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1312) (n := 2624)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2625 : ¬Nat.Prime 2625 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 875) (n := 2625)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2626 : ¬Nat.Prime 2626 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1313) (n := 2626)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2627 : ¬Nat.Prime 2627 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 71) (n := 2627)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2628 : ¬Nat.Prime 2628 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1314) (n := 2628)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2629 : ¬Nat.Prime 2629 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 239) (n := 2629)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2630 : ¬Nat.Prime 2630 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1315) (n := 2630)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2631 : ¬Nat.Prime 2631 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 877) (n := 2631)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2632 : ¬Nat.Prime 2632 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1316) (n := 2632)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2633 : Nat.count Nat.Prime 2633 = 381 := by
  rw [show 2633 = 2632 + 1 by norm_num, Nat.count_succ]
  rw [show 2632 = 2631 + 1 by norm_num, Nat.count_succ]
  rw [show 2631 = 2630 + 1 by norm_num, Nat.count_succ]
  rw [show 2630 = 2629 + 1 by norm_num, Nat.count_succ]
  rw [show 2629 = 2628 + 1 by norm_num, Nat.count_succ]
  rw [show 2628 = 2627 + 1 by norm_num, Nat.count_succ]
  rw [show 2627 = 2626 + 1 by norm_num, Nat.count_succ]
  rw [show 2626 = 2625 + 1 by norm_num, Nat.count_succ]
  rw [show 2625 = 2624 + 1 by norm_num, Nat.count_succ]
  rw [show 2624 = 2623 + 1 by norm_num, Nat.count_succ]
  rw [show 2623 = 2622 + 1 by norm_num, Nat.count_succ]
  rw [show 2622 = 2621 + 1 by norm_num, Nat.count_succ]
  rw [count_2621]
  simp [prime_2621, not_prime_2622, not_prime_2623, not_prime_2624, not_prime_2625, not_prime_2626, not_prime_2627, not_prime_2628, not_prime_2629, not_prime_2630, not_prime_2631, not_prime_2632]

theorem prime_2633 : (2633 : Nat).Prime := by norm_num

theorem nth_381 : Nat.nth Nat.Prime 381 = 2633 := by
  rw [← count_2633]
  exact Nat.nth_count prime_2633

theorem not_prime_2634 : ¬Nat.Prime 2634 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1317) (n := 2634)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2635 : ¬Nat.Prime 2635 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 527) (n := 2635)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2636 : ¬Nat.Prime 2636 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1318) (n := 2636)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2637 : ¬Nat.Prime 2637 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 879) (n := 2637)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2638 : ¬Nat.Prime 2638 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1319) (n := 2638)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2639 : ¬Nat.Prime 2639 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 377) (n := 2639)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2640 : ¬Nat.Prime 2640 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1320) (n := 2640)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2641 : ¬Nat.Prime 2641 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 139) (n := 2641)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2642 : ¬Nat.Prime 2642 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1321) (n := 2642)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2643 : ¬Nat.Prime 2643 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 881) (n := 2643)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2644 : ¬Nat.Prime 2644 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1322) (n := 2644)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2645 : ¬Nat.Prime 2645 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 529) (n := 2645)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2646 : ¬Nat.Prime 2646 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1323) (n := 2646)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2647 : Nat.count Nat.Prime 2647 = 382 := by
  rw [show 2647 = 2646 + 1 by norm_num, Nat.count_succ]
  rw [show 2646 = 2645 + 1 by norm_num, Nat.count_succ]
  rw [show 2645 = 2644 + 1 by norm_num, Nat.count_succ]
  rw [show 2644 = 2643 + 1 by norm_num, Nat.count_succ]
  rw [show 2643 = 2642 + 1 by norm_num, Nat.count_succ]
  rw [show 2642 = 2641 + 1 by norm_num, Nat.count_succ]
  rw [show 2641 = 2640 + 1 by norm_num, Nat.count_succ]
  rw [show 2640 = 2639 + 1 by norm_num, Nat.count_succ]
  rw [show 2639 = 2638 + 1 by norm_num, Nat.count_succ]
  rw [show 2638 = 2637 + 1 by norm_num, Nat.count_succ]
  rw [show 2637 = 2636 + 1 by norm_num, Nat.count_succ]
  rw [show 2636 = 2635 + 1 by norm_num, Nat.count_succ]
  rw [show 2635 = 2634 + 1 by norm_num, Nat.count_succ]
  rw [show 2634 = 2633 + 1 by norm_num, Nat.count_succ]
  rw [count_2633]
  simp [prime_2633, not_prime_2634, not_prime_2635, not_prime_2636, not_prime_2637, not_prime_2638, not_prime_2639, not_prime_2640, not_prime_2641, not_prime_2642, not_prime_2643, not_prime_2644, not_prime_2645, not_prime_2646]

theorem prime_2647 : (2647 : Nat).Prime := by norm_num

theorem nth_382 : Nat.nth Nat.Prime 382 = 2647 := by
  rw [← count_2647]
  exact Nat.nth_count prime_2647

theorem not_prime_2648 : ¬Nat.Prime 2648 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1324) (n := 2648)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2649 : ¬Nat.Prime 2649 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 883) (n := 2649)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2650 : ¬Nat.Prime 2650 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1325) (n := 2650)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2651 : ¬Nat.Prime 2651 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 241) (n := 2651)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2652 : ¬Nat.Prime 2652 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1326) (n := 2652)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2653 : ¬Nat.Prime 2653 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 379) (n := 2653)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2654 : ¬Nat.Prime 2654 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1327) (n := 2654)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2655 : ¬Nat.Prime 2655 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 885) (n := 2655)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2656 : ¬Nat.Prime 2656 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1328) (n := 2656)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2657 : Nat.count Nat.Prime 2657 = 383 := by
  rw [show 2657 = 2656 + 1 by norm_num, Nat.count_succ]
  rw [show 2656 = 2655 + 1 by norm_num, Nat.count_succ]
  rw [show 2655 = 2654 + 1 by norm_num, Nat.count_succ]
  rw [show 2654 = 2653 + 1 by norm_num, Nat.count_succ]
  rw [show 2653 = 2652 + 1 by norm_num, Nat.count_succ]
  rw [show 2652 = 2651 + 1 by norm_num, Nat.count_succ]
  rw [show 2651 = 2650 + 1 by norm_num, Nat.count_succ]
  rw [show 2650 = 2649 + 1 by norm_num, Nat.count_succ]
  rw [show 2649 = 2648 + 1 by norm_num, Nat.count_succ]
  rw [show 2648 = 2647 + 1 by norm_num, Nat.count_succ]
  rw [count_2647]
  simp [prime_2647, not_prime_2648, not_prime_2649, not_prime_2650, not_prime_2651, not_prime_2652, not_prime_2653, not_prime_2654, not_prime_2655, not_prime_2656]

theorem prime_2657 : (2657 : Nat).Prime := by norm_num

theorem nth_383 : Nat.nth Nat.Prime 383 = 2657 := by
  rw [← count_2657]
  exact Nat.nth_count prime_2657

theorem not_prime_2658 : ¬Nat.Prime 2658 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1329) (n := 2658)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2659 : Nat.count Nat.Prime 2659 = 384 := by
  rw [show 2659 = 2658 + 1 by norm_num, Nat.count_succ]
  rw [show 2658 = 2657 + 1 by norm_num, Nat.count_succ]
  rw [count_2657]
  simp [prime_2657, not_prime_2658]

theorem prime_2659 : (2659 : Nat).Prime := by norm_num

theorem nth_384 : Nat.nth Nat.Prime 384 = 2659 := by
  rw [← count_2659]
  exact Nat.nth_count prime_2659

theorem not_prime_2660 : ¬Nat.Prime 2660 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1330) (n := 2660)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2661 : ¬Nat.Prime 2661 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 887) (n := 2661)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2662 : ¬Nat.Prime 2662 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1331) (n := 2662)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2663 : Nat.count Nat.Prime 2663 = 385 := by
  rw [show 2663 = 2662 + 1 by norm_num, Nat.count_succ]
  rw [show 2662 = 2661 + 1 by norm_num, Nat.count_succ]
  rw [show 2661 = 2660 + 1 by norm_num, Nat.count_succ]
  rw [show 2660 = 2659 + 1 by norm_num, Nat.count_succ]
  rw [count_2659]
  simp [prime_2659, not_prime_2660, not_prime_2661, not_prime_2662]

theorem prime_2663 : (2663 : Nat).Prime := by norm_num

theorem nth_385 : Nat.nth Nat.Prime 385 = 2663 := by
  rw [← count_2663]
  exact Nat.nth_count prime_2663

theorem not_prime_2664 : ¬Nat.Prime 2664 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1332) (n := 2664)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2665 : ¬Nat.Prime 2665 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 533) (n := 2665)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2666 : ¬Nat.Prime 2666 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1333) (n := 2666)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2667 : ¬Nat.Prime 2667 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 889) (n := 2667)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2668 : ¬Nat.Prime 2668 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1334) (n := 2668)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2669 : ¬Nat.Prime 2669 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 157) (n := 2669)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2670 : ¬Nat.Prime 2670 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1335) (n := 2670)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2671 : Nat.count Nat.Prime 2671 = 386 := by
  rw [show 2671 = 2670 + 1 by norm_num, Nat.count_succ]
  rw [show 2670 = 2669 + 1 by norm_num, Nat.count_succ]
  rw [show 2669 = 2668 + 1 by norm_num, Nat.count_succ]
  rw [show 2668 = 2667 + 1 by norm_num, Nat.count_succ]
  rw [show 2667 = 2666 + 1 by norm_num, Nat.count_succ]
  rw [show 2666 = 2665 + 1 by norm_num, Nat.count_succ]
  rw [show 2665 = 2664 + 1 by norm_num, Nat.count_succ]
  rw [show 2664 = 2663 + 1 by norm_num, Nat.count_succ]
  rw [count_2663]
  simp [prime_2663, not_prime_2664, not_prime_2665, not_prime_2666, not_prime_2667, not_prime_2668, not_prime_2669, not_prime_2670]

theorem prime_2671 : (2671 : Nat).Prime := by norm_num

theorem nth_386 : Nat.nth Nat.Prime 386 = 2671 := by
  rw [← count_2671]
  exact Nat.nth_count prime_2671

theorem not_prime_2672 : ¬Nat.Prime 2672 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1336) (n := 2672)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2673 : ¬Nat.Prime 2673 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 891) (n := 2673)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2674 : ¬Nat.Prime 2674 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1337) (n := 2674)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2675 : ¬Nat.Prime 2675 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 535) (n := 2675)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2676 : ¬Nat.Prime 2676 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1338) (n := 2676)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2677 : Nat.count Nat.Prime 2677 = 387 := by
  rw [show 2677 = 2676 + 1 by norm_num, Nat.count_succ]
  rw [show 2676 = 2675 + 1 by norm_num, Nat.count_succ]
  rw [show 2675 = 2674 + 1 by norm_num, Nat.count_succ]
  rw [show 2674 = 2673 + 1 by norm_num, Nat.count_succ]
  rw [show 2673 = 2672 + 1 by norm_num, Nat.count_succ]
  rw [show 2672 = 2671 + 1 by norm_num, Nat.count_succ]
  rw [count_2671]
  simp [prime_2671, not_prime_2672, not_prime_2673, not_prime_2674, not_prime_2675, not_prime_2676]

theorem prime_2677 : (2677 : Nat).Prime := by norm_num

theorem nth_387 : Nat.nth Nat.Prime 387 = 2677 := by
  rw [← count_2677]
  exact Nat.nth_count prime_2677

theorem not_prime_2678 : ¬Nat.Prime 2678 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1339) (n := 2678)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2679 : ¬Nat.Prime 2679 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 893) (n := 2679)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2680 : ¬Nat.Prime 2680 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1340) (n := 2680)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2681 : ¬Nat.Prime 2681 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 383) (n := 2681)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2682 : ¬Nat.Prime 2682 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1341) (n := 2682)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2683 : Nat.count Nat.Prime 2683 = 388 := by
  rw [show 2683 = 2682 + 1 by norm_num, Nat.count_succ]
  rw [show 2682 = 2681 + 1 by norm_num, Nat.count_succ]
  rw [show 2681 = 2680 + 1 by norm_num, Nat.count_succ]
  rw [show 2680 = 2679 + 1 by norm_num, Nat.count_succ]
  rw [show 2679 = 2678 + 1 by norm_num, Nat.count_succ]
  rw [show 2678 = 2677 + 1 by norm_num, Nat.count_succ]
  rw [count_2677]
  simp [prime_2677, not_prime_2678, not_prime_2679, not_prime_2680, not_prime_2681, not_prime_2682]

theorem prime_2683 : (2683 : Nat).Prime := by norm_num

theorem nth_388 : Nat.nth Nat.Prime 388 = 2683 := by
  rw [← count_2683]
  exact Nat.nth_count prime_2683

theorem not_prime_2684 : ¬Nat.Prime 2684 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1342) (n := 2684)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2685 : ¬Nat.Prime 2685 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 895) (n := 2685)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2686 : ¬Nat.Prime 2686 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1343) (n := 2686)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2687 : Nat.count Nat.Prime 2687 = 389 := by
  rw [show 2687 = 2686 + 1 by norm_num, Nat.count_succ]
  rw [show 2686 = 2685 + 1 by norm_num, Nat.count_succ]
  rw [show 2685 = 2684 + 1 by norm_num, Nat.count_succ]
  rw [show 2684 = 2683 + 1 by norm_num, Nat.count_succ]
  rw [count_2683]
  simp [prime_2683, not_prime_2684, not_prime_2685, not_prime_2686]

theorem prime_2687 : (2687 : Nat).Prime := by norm_num

theorem nth_389 : Nat.nth Nat.Prime 389 = 2687 := by
  rw [← count_2687]
  exact Nat.nth_count prime_2687

theorem not_prime_2688 : ¬Nat.Prime 2688 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1344) (n := 2688)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2689 : Nat.count Nat.Prime 2689 = 390 := by
  rw [show 2689 = 2688 + 1 by norm_num, Nat.count_succ]
  rw [show 2688 = 2687 + 1 by norm_num, Nat.count_succ]
  rw [count_2687]
  simp [prime_2687, not_prime_2688]

theorem prime_2689 : (2689 : Nat).Prime := by norm_num

theorem nth_390 : Nat.nth Nat.Prime 390 = 2689 := by
  rw [← count_2689]
  exact Nat.nth_count prime_2689

theorem not_prime_2690 : ¬Nat.Prime 2690 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1345) (n := 2690)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2691 : ¬Nat.Prime 2691 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 897) (n := 2691)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2692 : ¬Nat.Prime 2692 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1346) (n := 2692)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2693 : Nat.count Nat.Prime 2693 = 391 := by
  rw [show 2693 = 2692 + 1 by norm_num, Nat.count_succ]
  rw [show 2692 = 2691 + 1 by norm_num, Nat.count_succ]
  rw [show 2691 = 2690 + 1 by norm_num, Nat.count_succ]
  rw [show 2690 = 2689 + 1 by norm_num, Nat.count_succ]
  rw [count_2689]
  simp [prime_2689, not_prime_2690, not_prime_2691, not_prime_2692]

theorem prime_2693 : (2693 : Nat).Prime := by norm_num

theorem nth_391 : Nat.nth Nat.Prime 391 = 2693 := by
  rw [← count_2693]
  exact Nat.nth_count prime_2693

theorem not_prime_2694 : ¬Nat.Prime 2694 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1347) (n := 2694)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2695 : ¬Nat.Prime 2695 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 539) (n := 2695)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2696 : ¬Nat.Prime 2696 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1348) (n := 2696)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2697 : ¬Nat.Prime 2697 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 899) (n := 2697)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2698 : ¬Nat.Prime 2698 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1349) (n := 2698)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2699 : Nat.count Nat.Prime 2699 = 392 := by
  rw [show 2699 = 2698 + 1 by norm_num, Nat.count_succ]
  rw [show 2698 = 2697 + 1 by norm_num, Nat.count_succ]
  rw [show 2697 = 2696 + 1 by norm_num, Nat.count_succ]
  rw [show 2696 = 2695 + 1 by norm_num, Nat.count_succ]
  rw [show 2695 = 2694 + 1 by norm_num, Nat.count_succ]
  rw [show 2694 = 2693 + 1 by norm_num, Nat.count_succ]
  rw [count_2693]
  simp [prime_2693, not_prime_2694, not_prime_2695, not_prime_2696, not_prime_2697, not_prime_2698]

theorem prime_2699 : (2699 : Nat).Prime := by norm_num

theorem nth_392 : Nat.nth Nat.Prime 392 = 2699 := by
  rw [← count_2699]
  exact Nat.nth_count prime_2699

theorem not_prime_2700 : ¬Nat.Prime 2700 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1350) (n := 2700)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2701 : ¬Nat.Prime 2701 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 73) (n := 2701)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2702 : ¬Nat.Prime 2702 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1351) (n := 2702)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2703 : ¬Nat.Prime 2703 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 901) (n := 2703)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2704 : ¬Nat.Prime 2704 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1352) (n := 2704)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2705 : ¬Nat.Prime 2705 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 541) (n := 2705)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2706 : ¬Nat.Prime 2706 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1353) (n := 2706)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2707 : Nat.count Nat.Prime 2707 = 393 := by
  rw [show 2707 = 2706 + 1 by norm_num, Nat.count_succ]
  rw [show 2706 = 2705 + 1 by norm_num, Nat.count_succ]
  rw [show 2705 = 2704 + 1 by norm_num, Nat.count_succ]
  rw [show 2704 = 2703 + 1 by norm_num, Nat.count_succ]
  rw [show 2703 = 2702 + 1 by norm_num, Nat.count_succ]
  rw [show 2702 = 2701 + 1 by norm_num, Nat.count_succ]
  rw [show 2701 = 2700 + 1 by norm_num, Nat.count_succ]
  rw [show 2700 = 2699 + 1 by norm_num, Nat.count_succ]
  rw [count_2699]
  simp [prime_2699, not_prime_2700, not_prime_2701, not_prime_2702, not_prime_2703, not_prime_2704, not_prime_2705, not_prime_2706]

theorem prime_2707 : (2707 : Nat).Prime := by norm_num

theorem nth_393 : Nat.nth Nat.Prime 393 = 2707 := by
  rw [← count_2707]
  exact Nat.nth_count prime_2707

theorem not_prime_2708 : ¬Nat.Prime 2708 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1354) (n := 2708)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2709 : ¬Nat.Prime 2709 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 903) (n := 2709)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2710 : ¬Nat.Prime 2710 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1355) (n := 2710)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2711 : Nat.count Nat.Prime 2711 = 394 := by
  rw [show 2711 = 2710 + 1 by norm_num, Nat.count_succ]
  rw [show 2710 = 2709 + 1 by norm_num, Nat.count_succ]
  rw [show 2709 = 2708 + 1 by norm_num, Nat.count_succ]
  rw [show 2708 = 2707 + 1 by norm_num, Nat.count_succ]
  rw [count_2707]
  simp [prime_2707, not_prime_2708, not_prime_2709, not_prime_2710]

theorem prime_2711 : (2711 : Nat).Prime := by norm_num

theorem nth_394 : Nat.nth Nat.Prime 394 = 2711 := by
  rw [← count_2711]
  exact Nat.nth_count prime_2711

theorem not_prime_2712 : ¬Nat.Prime 2712 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1356) (n := 2712)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2713 : Nat.count Nat.Prime 2713 = 395 := by
  rw [show 2713 = 2712 + 1 by norm_num, Nat.count_succ]
  rw [show 2712 = 2711 + 1 by norm_num, Nat.count_succ]
  rw [count_2711]
  simp [prime_2711, not_prime_2712]

theorem prime_2713 : (2713 : Nat).Prime := by norm_num

theorem nth_395 : Nat.nth Nat.Prime 395 = 2713 := by
  rw [← count_2713]
  exact Nat.nth_count prime_2713

theorem not_prime_2714 : ¬Nat.Prime 2714 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1357) (n := 2714)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2715 : ¬Nat.Prime 2715 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 905) (n := 2715)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2716 : ¬Nat.Prime 2716 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1358) (n := 2716)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2717 : ¬Nat.Prime 2717 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 247) (n := 2717)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2718 : ¬Nat.Prime 2718 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1359) (n := 2718)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2719 : Nat.count Nat.Prime 2719 = 396 := by
  rw [show 2719 = 2718 + 1 by norm_num, Nat.count_succ]
  rw [show 2718 = 2717 + 1 by norm_num, Nat.count_succ]
  rw [show 2717 = 2716 + 1 by norm_num, Nat.count_succ]
  rw [show 2716 = 2715 + 1 by norm_num, Nat.count_succ]
  rw [show 2715 = 2714 + 1 by norm_num, Nat.count_succ]
  rw [show 2714 = 2713 + 1 by norm_num, Nat.count_succ]
  rw [count_2713]
  simp [prime_2713, not_prime_2714, not_prime_2715, not_prime_2716, not_prime_2717, not_prime_2718]

theorem prime_2719 : (2719 : Nat).Prime := by norm_num

theorem nth_396 : Nat.nth Nat.Prime 396 = 2719 := by
  rw [← count_2719]
  exact Nat.nth_count prime_2719

theorem not_prime_2720 : ¬Nat.Prime 2720 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1360) (n := 2720)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2721 : ¬Nat.Prime 2721 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 907) (n := 2721)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2722 : ¬Nat.Prime 2722 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1361) (n := 2722)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2723 : ¬Nat.Prime 2723 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 389) (n := 2723)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2724 : ¬Nat.Prime 2724 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1362) (n := 2724)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2725 : ¬Nat.Prime 2725 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 545) (n := 2725)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2726 : ¬Nat.Prime 2726 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1363) (n := 2726)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2727 : ¬Nat.Prime 2727 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 909) (n := 2727)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2728 : ¬Nat.Prime 2728 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1364) (n := 2728)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2729 : Nat.count Nat.Prime 2729 = 397 := by
  rw [show 2729 = 2728 + 1 by norm_num, Nat.count_succ]
  rw [show 2728 = 2727 + 1 by norm_num, Nat.count_succ]
  rw [show 2727 = 2726 + 1 by norm_num, Nat.count_succ]
  rw [show 2726 = 2725 + 1 by norm_num, Nat.count_succ]
  rw [show 2725 = 2724 + 1 by norm_num, Nat.count_succ]
  rw [show 2724 = 2723 + 1 by norm_num, Nat.count_succ]
  rw [show 2723 = 2722 + 1 by norm_num, Nat.count_succ]
  rw [show 2722 = 2721 + 1 by norm_num, Nat.count_succ]
  rw [show 2721 = 2720 + 1 by norm_num, Nat.count_succ]
  rw [show 2720 = 2719 + 1 by norm_num, Nat.count_succ]
  rw [count_2719]
  simp [prime_2719, not_prime_2720, not_prime_2721, not_prime_2722, not_prime_2723, not_prime_2724, not_prime_2725, not_prime_2726, not_prime_2727, not_prime_2728]

theorem prime_2729 : (2729 : Nat).Prime := by norm_num

theorem nth_397 : Nat.nth Nat.Prime 397 = 2729 := by
  rw [← count_2729]
  exact Nat.nth_count prime_2729

theorem not_prime_2730 : ¬Nat.Prime 2730 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1365) (n := 2730)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2731 : Nat.count Nat.Prime 2731 = 398 := by
  rw [show 2731 = 2730 + 1 by norm_num, Nat.count_succ]
  rw [show 2730 = 2729 + 1 by norm_num, Nat.count_succ]
  rw [count_2729]
  simp [prime_2729, not_prime_2730]

theorem prime_2731 : (2731 : Nat).Prime := by norm_num

theorem nth_398 : Nat.nth Nat.Prime 398 = 2731 := by
  rw [← count_2731]
  exact Nat.nth_count prime_2731

theorem not_prime_2732 : ¬Nat.Prime 2732 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1366) (n := 2732)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2733 : ¬Nat.Prime 2733 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 911) (n := 2733)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2734 : ¬Nat.Prime 2734 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1367) (n := 2734)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2735 : ¬Nat.Prime 2735 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 547) (n := 2735)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2736 : ¬Nat.Prime 2736 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1368) (n := 2736)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2737 : ¬Nat.Prime 2737 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 391) (n := 2737)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2738 : ¬Nat.Prime 2738 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1369) (n := 2738)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2739 : ¬Nat.Prime 2739 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 913) (n := 2739)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2740 : ¬Nat.Prime 2740 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1370) (n := 2740)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2741 : Nat.count Nat.Prime 2741 = 399 := by
  rw [show 2741 = 2740 + 1 by norm_num, Nat.count_succ]
  rw [show 2740 = 2739 + 1 by norm_num, Nat.count_succ]
  rw [show 2739 = 2738 + 1 by norm_num, Nat.count_succ]
  rw [show 2738 = 2737 + 1 by norm_num, Nat.count_succ]
  rw [show 2737 = 2736 + 1 by norm_num, Nat.count_succ]
  rw [show 2736 = 2735 + 1 by norm_num, Nat.count_succ]
  rw [show 2735 = 2734 + 1 by norm_num, Nat.count_succ]
  rw [show 2734 = 2733 + 1 by norm_num, Nat.count_succ]
  rw [show 2733 = 2732 + 1 by norm_num, Nat.count_succ]
  rw [show 2732 = 2731 + 1 by norm_num, Nat.count_succ]
  rw [count_2731]
  simp [prime_2731, not_prime_2732, not_prime_2733, not_prime_2734, not_prime_2735, not_prime_2736, not_prime_2737, not_prime_2738, not_prime_2739, not_prime_2740]

theorem prime_2741 : (2741 : Nat).Prime := by norm_num

theorem nth_399 : Nat.nth Nat.Prime 399 = 2741 := by
  rw [← count_2741]
  exact Nat.nth_count prime_2741

end OeisA100474.PrimeCertificate
