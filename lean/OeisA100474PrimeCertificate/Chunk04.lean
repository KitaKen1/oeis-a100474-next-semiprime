import OeisA100474PrimeCertificate.Chunk03

/-! Kernel prime/count certificate, chunk 04 (100–124). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_542 : ¬Nat.Prime 542 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 271) (n := 542)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_543 : ¬Nat.Prime 543 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 181) (n := 543)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_544 : ¬Nat.Prime 544 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 272) (n := 544)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_545 : ¬Nat.Prime 545 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 109) (n := 545)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_546 : ¬Nat.Prime 546 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 273) (n := 546)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_547 : Nat.count Nat.Prime 547 = 100 := by
  rw [show 547 = 546 + 1 by norm_num, Nat.count_succ]
  rw [show 546 = 545 + 1 by norm_num, Nat.count_succ]
  rw [show 545 = 544 + 1 by norm_num, Nat.count_succ]
  rw [show 544 = 543 + 1 by norm_num, Nat.count_succ]
  rw [show 543 = 542 + 1 by norm_num, Nat.count_succ]
  rw [show 542 = 541 + 1 by norm_num, Nat.count_succ]
  rw [count_541]
  simp [prime_541, not_prime_542, not_prime_543, not_prime_544, not_prime_545, not_prime_546]

theorem prime_547 : (547 : Nat).Prime := by norm_num

theorem nth_100 : Nat.nth Nat.Prime 100 = 547 := by
  rw [← count_547]
  exact Nat.nth_count prime_547

theorem not_prime_548 : ¬Nat.Prime 548 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 274) (n := 548)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_549 : ¬Nat.Prime 549 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 183) (n := 549)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_550 : ¬Nat.Prime 550 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 275) (n := 550)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_551 : ¬Nat.Prime 551 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 29) (n := 551)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_552 : ¬Nat.Prime 552 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 276) (n := 552)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_553 : ¬Nat.Prime 553 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 79) (n := 553)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_554 : ¬Nat.Prime 554 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 277) (n := 554)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_555 : ¬Nat.Prime 555 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 185) (n := 555)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_556 : ¬Nat.Prime 556 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 278) (n := 556)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_557 : Nat.count Nat.Prime 557 = 101 := by
  rw [show 557 = 556 + 1 by norm_num, Nat.count_succ]
  rw [show 556 = 555 + 1 by norm_num, Nat.count_succ]
  rw [show 555 = 554 + 1 by norm_num, Nat.count_succ]
  rw [show 554 = 553 + 1 by norm_num, Nat.count_succ]
  rw [show 553 = 552 + 1 by norm_num, Nat.count_succ]
  rw [show 552 = 551 + 1 by norm_num, Nat.count_succ]
  rw [show 551 = 550 + 1 by norm_num, Nat.count_succ]
  rw [show 550 = 549 + 1 by norm_num, Nat.count_succ]
  rw [show 549 = 548 + 1 by norm_num, Nat.count_succ]
  rw [show 548 = 547 + 1 by norm_num, Nat.count_succ]
  rw [count_547]
  simp [prime_547, not_prime_548, not_prime_549, not_prime_550, not_prime_551, not_prime_552, not_prime_553, not_prime_554, not_prime_555, not_prime_556]

theorem prime_557 : (557 : Nat).Prime := by norm_num

theorem nth_101 : Nat.nth Nat.Prime 101 = 557 := by
  rw [← count_557]
  exact Nat.nth_count prime_557

theorem not_prime_558 : ¬Nat.Prime 558 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 279) (n := 558)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_559 : ¬Nat.Prime 559 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 43) (n := 559)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_560 : ¬Nat.Prime 560 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 280) (n := 560)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_561 : ¬Nat.Prime 561 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 187) (n := 561)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_562 : ¬Nat.Prime 562 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 281) (n := 562)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_563 : Nat.count Nat.Prime 563 = 102 := by
  rw [show 563 = 562 + 1 by norm_num, Nat.count_succ]
  rw [show 562 = 561 + 1 by norm_num, Nat.count_succ]
  rw [show 561 = 560 + 1 by norm_num, Nat.count_succ]
  rw [show 560 = 559 + 1 by norm_num, Nat.count_succ]
  rw [show 559 = 558 + 1 by norm_num, Nat.count_succ]
  rw [show 558 = 557 + 1 by norm_num, Nat.count_succ]
  rw [count_557]
  simp [prime_557, not_prime_558, not_prime_559, not_prime_560, not_prime_561, not_prime_562]

theorem prime_563 : (563 : Nat).Prime := by norm_num

theorem nth_102 : Nat.nth Nat.Prime 102 = 563 := by
  rw [← count_563]
  exact Nat.nth_count prime_563

theorem not_prime_564 : ¬Nat.Prime 564 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 282) (n := 564)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_565 : ¬Nat.Prime 565 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 113) (n := 565)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_566 : ¬Nat.Prime 566 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 283) (n := 566)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_567 : ¬Nat.Prime 567 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 189) (n := 567)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_568 : ¬Nat.Prime 568 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 284) (n := 568)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_569 : Nat.count Nat.Prime 569 = 103 := by
  rw [show 569 = 568 + 1 by norm_num, Nat.count_succ]
  rw [show 568 = 567 + 1 by norm_num, Nat.count_succ]
  rw [show 567 = 566 + 1 by norm_num, Nat.count_succ]
  rw [show 566 = 565 + 1 by norm_num, Nat.count_succ]
  rw [show 565 = 564 + 1 by norm_num, Nat.count_succ]
  rw [show 564 = 563 + 1 by norm_num, Nat.count_succ]
  rw [count_563]
  simp [prime_563, not_prime_564, not_prime_565, not_prime_566, not_prime_567, not_prime_568]

theorem prime_569 : (569 : Nat).Prime := by norm_num

theorem nth_103 : Nat.nth Nat.Prime 103 = 569 := by
  rw [← count_569]
  exact Nat.nth_count prime_569

theorem not_prime_570 : ¬Nat.Prime 570 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 285) (n := 570)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_571 : Nat.count Nat.Prime 571 = 104 := by
  rw [show 571 = 570 + 1 by norm_num, Nat.count_succ]
  rw [show 570 = 569 + 1 by norm_num, Nat.count_succ]
  rw [count_569]
  simp [prime_569, not_prime_570]

theorem prime_571 : (571 : Nat).Prime := by norm_num

theorem nth_104 : Nat.nth Nat.Prime 104 = 571 := by
  rw [← count_571]
  exact Nat.nth_count prime_571

theorem not_prime_572 : ¬Nat.Prime 572 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 286) (n := 572)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_573 : ¬Nat.Prime 573 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 191) (n := 573)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_574 : ¬Nat.Prime 574 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 287) (n := 574)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_575 : ¬Nat.Prime 575 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 115) (n := 575)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_576 : ¬Nat.Prime 576 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 288) (n := 576)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_577 : Nat.count Nat.Prime 577 = 105 := by
  rw [show 577 = 576 + 1 by norm_num, Nat.count_succ]
  rw [show 576 = 575 + 1 by norm_num, Nat.count_succ]
  rw [show 575 = 574 + 1 by norm_num, Nat.count_succ]
  rw [show 574 = 573 + 1 by norm_num, Nat.count_succ]
  rw [show 573 = 572 + 1 by norm_num, Nat.count_succ]
  rw [show 572 = 571 + 1 by norm_num, Nat.count_succ]
  rw [count_571]
  simp [prime_571, not_prime_572, not_prime_573, not_prime_574, not_prime_575, not_prime_576]

theorem prime_577 : (577 : Nat).Prime := by norm_num

theorem nth_105 : Nat.nth Nat.Prime 105 = 577 := by
  rw [← count_577]
  exact Nat.nth_count prime_577

theorem not_prime_578 : ¬Nat.Prime 578 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 289) (n := 578)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_579 : ¬Nat.Prime 579 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 193) (n := 579)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_580 : ¬Nat.Prime 580 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 290) (n := 580)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_581 : ¬Nat.Prime 581 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 83) (n := 581)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_582 : ¬Nat.Prime 582 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 291) (n := 582)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_583 : ¬Nat.Prime 583 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 53) (n := 583)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_584 : ¬Nat.Prime 584 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 292) (n := 584)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_585 : ¬Nat.Prime 585 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 195) (n := 585)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_586 : ¬Nat.Prime 586 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 293) (n := 586)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_587 : Nat.count Nat.Prime 587 = 106 := by
  rw [show 587 = 586 + 1 by norm_num, Nat.count_succ]
  rw [show 586 = 585 + 1 by norm_num, Nat.count_succ]
  rw [show 585 = 584 + 1 by norm_num, Nat.count_succ]
  rw [show 584 = 583 + 1 by norm_num, Nat.count_succ]
  rw [show 583 = 582 + 1 by norm_num, Nat.count_succ]
  rw [show 582 = 581 + 1 by norm_num, Nat.count_succ]
  rw [show 581 = 580 + 1 by norm_num, Nat.count_succ]
  rw [show 580 = 579 + 1 by norm_num, Nat.count_succ]
  rw [show 579 = 578 + 1 by norm_num, Nat.count_succ]
  rw [show 578 = 577 + 1 by norm_num, Nat.count_succ]
  rw [count_577]
  simp [prime_577, not_prime_578, not_prime_579, not_prime_580, not_prime_581, not_prime_582, not_prime_583, not_prime_584, not_prime_585, not_prime_586]

theorem prime_587 : (587 : Nat).Prime := by norm_num

theorem nth_106 : Nat.nth Nat.Prime 106 = 587 := by
  rw [← count_587]
  exact Nat.nth_count prime_587

theorem not_prime_588 : ¬Nat.Prime 588 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 294) (n := 588)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_589 : ¬Nat.Prime 589 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 31) (n := 589)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_590 : ¬Nat.Prime 590 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 295) (n := 590)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_591 : ¬Nat.Prime 591 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 197) (n := 591)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_592 : ¬Nat.Prime 592 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 296) (n := 592)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_593 : Nat.count Nat.Prime 593 = 107 := by
  rw [show 593 = 592 + 1 by norm_num, Nat.count_succ]
  rw [show 592 = 591 + 1 by norm_num, Nat.count_succ]
  rw [show 591 = 590 + 1 by norm_num, Nat.count_succ]
  rw [show 590 = 589 + 1 by norm_num, Nat.count_succ]
  rw [show 589 = 588 + 1 by norm_num, Nat.count_succ]
  rw [show 588 = 587 + 1 by norm_num, Nat.count_succ]
  rw [count_587]
  simp [prime_587, not_prime_588, not_prime_589, not_prime_590, not_prime_591, not_prime_592]

theorem prime_593 : (593 : Nat).Prime := by norm_num

theorem nth_107 : Nat.nth Nat.Prime 107 = 593 := by
  rw [← count_593]
  exact Nat.nth_count prime_593

theorem not_prime_594 : ¬Nat.Prime 594 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 297) (n := 594)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_595 : ¬Nat.Prime 595 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 119) (n := 595)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_596 : ¬Nat.Prime 596 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 298) (n := 596)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_597 : ¬Nat.Prime 597 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 199) (n := 597)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_598 : ¬Nat.Prime 598 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 299) (n := 598)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_599 : Nat.count Nat.Prime 599 = 108 := by
  rw [show 599 = 598 + 1 by norm_num, Nat.count_succ]
  rw [show 598 = 597 + 1 by norm_num, Nat.count_succ]
  rw [show 597 = 596 + 1 by norm_num, Nat.count_succ]
  rw [show 596 = 595 + 1 by norm_num, Nat.count_succ]
  rw [show 595 = 594 + 1 by norm_num, Nat.count_succ]
  rw [show 594 = 593 + 1 by norm_num, Nat.count_succ]
  rw [count_593]
  simp [prime_593, not_prime_594, not_prime_595, not_prime_596, not_prime_597, not_prime_598]

theorem prime_599 : (599 : Nat).Prime := by norm_num

theorem nth_108 : Nat.nth Nat.Prime 108 = 599 := by
  rw [← count_599]
  exact Nat.nth_count prime_599

theorem not_prime_600 : ¬Nat.Prime 600 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 300) (n := 600)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_601 : Nat.count Nat.Prime 601 = 109 := by
  rw [show 601 = 600 + 1 by norm_num, Nat.count_succ]
  rw [show 600 = 599 + 1 by norm_num, Nat.count_succ]
  rw [count_599]
  simp [prime_599, not_prime_600]

theorem prime_601 : (601 : Nat).Prime := by norm_num

theorem nth_109 : Nat.nth Nat.Prime 109 = 601 := by
  rw [← count_601]
  exact Nat.nth_count prime_601

theorem not_prime_602 : ¬Nat.Prime 602 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 301) (n := 602)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_603 : ¬Nat.Prime 603 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 201) (n := 603)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_604 : ¬Nat.Prime 604 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 302) (n := 604)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_605 : ¬Nat.Prime 605 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 121) (n := 605)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_606 : ¬Nat.Prime 606 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 303) (n := 606)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_607 : Nat.count Nat.Prime 607 = 110 := by
  rw [show 607 = 606 + 1 by norm_num, Nat.count_succ]
  rw [show 606 = 605 + 1 by norm_num, Nat.count_succ]
  rw [show 605 = 604 + 1 by norm_num, Nat.count_succ]
  rw [show 604 = 603 + 1 by norm_num, Nat.count_succ]
  rw [show 603 = 602 + 1 by norm_num, Nat.count_succ]
  rw [show 602 = 601 + 1 by norm_num, Nat.count_succ]
  rw [count_601]
  simp [prime_601, not_prime_602, not_prime_603, not_prime_604, not_prime_605, not_prime_606]

theorem prime_607 : (607 : Nat).Prime := by norm_num

theorem nth_110 : Nat.nth Nat.Prime 110 = 607 := by
  rw [← count_607]
  exact Nat.nth_count prime_607

theorem not_prime_608 : ¬Nat.Prime 608 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 304) (n := 608)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_609 : ¬Nat.Prime 609 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 203) (n := 609)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_610 : ¬Nat.Prime 610 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 305) (n := 610)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_611 : ¬Nat.Prime 611 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 47) (n := 611)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_612 : ¬Nat.Prime 612 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 306) (n := 612)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_613 : Nat.count Nat.Prime 613 = 111 := by
  rw [show 613 = 612 + 1 by norm_num, Nat.count_succ]
  rw [show 612 = 611 + 1 by norm_num, Nat.count_succ]
  rw [show 611 = 610 + 1 by norm_num, Nat.count_succ]
  rw [show 610 = 609 + 1 by norm_num, Nat.count_succ]
  rw [show 609 = 608 + 1 by norm_num, Nat.count_succ]
  rw [show 608 = 607 + 1 by norm_num, Nat.count_succ]
  rw [count_607]
  simp [prime_607, not_prime_608, not_prime_609, not_prime_610, not_prime_611, not_prime_612]

theorem prime_613 : (613 : Nat).Prime := by norm_num

theorem nth_111 : Nat.nth Nat.Prime 111 = 613 := by
  rw [← count_613]
  exact Nat.nth_count prime_613

theorem not_prime_614 : ¬Nat.Prime 614 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 307) (n := 614)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_615 : ¬Nat.Prime 615 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 205) (n := 615)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_616 : ¬Nat.Prime 616 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 308) (n := 616)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_617 : Nat.count Nat.Prime 617 = 112 := by
  rw [show 617 = 616 + 1 by norm_num, Nat.count_succ]
  rw [show 616 = 615 + 1 by norm_num, Nat.count_succ]
  rw [show 615 = 614 + 1 by norm_num, Nat.count_succ]
  rw [show 614 = 613 + 1 by norm_num, Nat.count_succ]
  rw [count_613]
  simp [prime_613, not_prime_614, not_prime_615, not_prime_616]

theorem prime_617 : (617 : Nat).Prime := by norm_num

theorem nth_112 : Nat.nth Nat.Prime 112 = 617 := by
  rw [← count_617]
  exact Nat.nth_count prime_617

theorem not_prime_618 : ¬Nat.Prime 618 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 309) (n := 618)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_619 : Nat.count Nat.Prime 619 = 113 := by
  rw [show 619 = 618 + 1 by norm_num, Nat.count_succ]
  rw [show 618 = 617 + 1 by norm_num, Nat.count_succ]
  rw [count_617]
  simp [prime_617, not_prime_618]

theorem prime_619 : (619 : Nat).Prime := by norm_num

theorem nth_113 : Nat.nth Nat.Prime 113 = 619 := by
  rw [← count_619]
  exact Nat.nth_count prime_619

theorem not_prime_620 : ¬Nat.Prime 620 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 310) (n := 620)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_621 : ¬Nat.Prime 621 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 207) (n := 621)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_622 : ¬Nat.Prime 622 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 311) (n := 622)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_623 : ¬Nat.Prime 623 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 89) (n := 623)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_624 : ¬Nat.Prime 624 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 312) (n := 624)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_625 : ¬Nat.Prime 625 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 125) (n := 625)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_626 : ¬Nat.Prime 626 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 313) (n := 626)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_627 : ¬Nat.Prime 627 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 209) (n := 627)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_628 : ¬Nat.Prime 628 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 314) (n := 628)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_629 : ¬Nat.Prime 629 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 37) (n := 629)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_630 : ¬Nat.Prime 630 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 315) (n := 630)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_631 : Nat.count Nat.Prime 631 = 114 := by
  rw [show 631 = 630 + 1 by norm_num, Nat.count_succ]
  rw [show 630 = 629 + 1 by norm_num, Nat.count_succ]
  rw [show 629 = 628 + 1 by norm_num, Nat.count_succ]
  rw [show 628 = 627 + 1 by norm_num, Nat.count_succ]
  rw [show 627 = 626 + 1 by norm_num, Nat.count_succ]
  rw [show 626 = 625 + 1 by norm_num, Nat.count_succ]
  rw [show 625 = 624 + 1 by norm_num, Nat.count_succ]
  rw [show 624 = 623 + 1 by norm_num, Nat.count_succ]
  rw [show 623 = 622 + 1 by norm_num, Nat.count_succ]
  rw [show 622 = 621 + 1 by norm_num, Nat.count_succ]
  rw [show 621 = 620 + 1 by norm_num, Nat.count_succ]
  rw [show 620 = 619 + 1 by norm_num, Nat.count_succ]
  rw [count_619]
  simp [prime_619, not_prime_620, not_prime_621, not_prime_622, not_prime_623, not_prime_624, not_prime_625, not_prime_626, not_prime_627, not_prime_628, not_prime_629, not_prime_630]

theorem prime_631 : (631 : Nat).Prime := by norm_num

theorem nth_114 : Nat.nth Nat.Prime 114 = 631 := by
  rw [← count_631]
  exact Nat.nth_count prime_631

theorem not_prime_632 : ¬Nat.Prime 632 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 316) (n := 632)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_633 : ¬Nat.Prime 633 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 211) (n := 633)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_634 : ¬Nat.Prime 634 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 317) (n := 634)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_635 : ¬Nat.Prime 635 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 127) (n := 635)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_636 : ¬Nat.Prime 636 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 318) (n := 636)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_637 : ¬Nat.Prime 637 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 91) (n := 637)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_638 : ¬Nat.Prime 638 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 319) (n := 638)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_639 : ¬Nat.Prime 639 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 213) (n := 639)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_640 : ¬Nat.Prime 640 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 320) (n := 640)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_641 : Nat.count Nat.Prime 641 = 115 := by
  rw [show 641 = 640 + 1 by norm_num, Nat.count_succ]
  rw [show 640 = 639 + 1 by norm_num, Nat.count_succ]
  rw [show 639 = 638 + 1 by norm_num, Nat.count_succ]
  rw [show 638 = 637 + 1 by norm_num, Nat.count_succ]
  rw [show 637 = 636 + 1 by norm_num, Nat.count_succ]
  rw [show 636 = 635 + 1 by norm_num, Nat.count_succ]
  rw [show 635 = 634 + 1 by norm_num, Nat.count_succ]
  rw [show 634 = 633 + 1 by norm_num, Nat.count_succ]
  rw [show 633 = 632 + 1 by norm_num, Nat.count_succ]
  rw [show 632 = 631 + 1 by norm_num, Nat.count_succ]
  rw [count_631]
  simp [prime_631, not_prime_632, not_prime_633, not_prime_634, not_prime_635, not_prime_636, not_prime_637, not_prime_638, not_prime_639, not_prime_640]

theorem prime_641 : (641 : Nat).Prime := by norm_num

theorem nth_115 : Nat.nth Nat.Prime 115 = 641 := by
  rw [← count_641]
  exact Nat.nth_count prime_641

theorem not_prime_642 : ¬Nat.Prime 642 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 321) (n := 642)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_643 : Nat.count Nat.Prime 643 = 116 := by
  rw [show 643 = 642 + 1 by norm_num, Nat.count_succ]
  rw [show 642 = 641 + 1 by norm_num, Nat.count_succ]
  rw [count_641]
  simp [prime_641, not_prime_642]

theorem prime_643 : (643 : Nat).Prime := by norm_num

theorem nth_116 : Nat.nth Nat.Prime 116 = 643 := by
  rw [← count_643]
  exact Nat.nth_count prime_643

theorem not_prime_644 : ¬Nat.Prime 644 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 322) (n := 644)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_645 : ¬Nat.Prime 645 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 215) (n := 645)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_646 : ¬Nat.Prime 646 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 323) (n := 646)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_647 : Nat.count Nat.Prime 647 = 117 := by
  rw [show 647 = 646 + 1 by norm_num, Nat.count_succ]
  rw [show 646 = 645 + 1 by norm_num, Nat.count_succ]
  rw [show 645 = 644 + 1 by norm_num, Nat.count_succ]
  rw [show 644 = 643 + 1 by norm_num, Nat.count_succ]
  rw [count_643]
  simp [prime_643, not_prime_644, not_prime_645, not_prime_646]

theorem prime_647 : (647 : Nat).Prime := by norm_num

theorem nth_117 : Nat.nth Nat.Prime 117 = 647 := by
  rw [← count_647]
  exact Nat.nth_count prime_647

theorem not_prime_648 : ¬Nat.Prime 648 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 324) (n := 648)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_649 : ¬Nat.Prime 649 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 59) (n := 649)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_650 : ¬Nat.Prime 650 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 325) (n := 650)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_651 : ¬Nat.Prime 651 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 217) (n := 651)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_652 : ¬Nat.Prime 652 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 326) (n := 652)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_653 : Nat.count Nat.Prime 653 = 118 := by
  rw [show 653 = 652 + 1 by norm_num, Nat.count_succ]
  rw [show 652 = 651 + 1 by norm_num, Nat.count_succ]
  rw [show 651 = 650 + 1 by norm_num, Nat.count_succ]
  rw [show 650 = 649 + 1 by norm_num, Nat.count_succ]
  rw [show 649 = 648 + 1 by norm_num, Nat.count_succ]
  rw [show 648 = 647 + 1 by norm_num, Nat.count_succ]
  rw [count_647]
  simp [prime_647, not_prime_648, not_prime_649, not_prime_650, not_prime_651, not_prime_652]

theorem prime_653 : (653 : Nat).Prime := by norm_num

theorem nth_118 : Nat.nth Nat.Prime 118 = 653 := by
  rw [← count_653]
  exact Nat.nth_count prime_653

theorem not_prime_654 : ¬Nat.Prime 654 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 327) (n := 654)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_655 : ¬Nat.Prime 655 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 131) (n := 655)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_656 : ¬Nat.Prime 656 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 328) (n := 656)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_657 : ¬Nat.Prime 657 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 219) (n := 657)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_658 : ¬Nat.Prime 658 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 329) (n := 658)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_659 : Nat.count Nat.Prime 659 = 119 := by
  rw [show 659 = 658 + 1 by norm_num, Nat.count_succ]
  rw [show 658 = 657 + 1 by norm_num, Nat.count_succ]
  rw [show 657 = 656 + 1 by norm_num, Nat.count_succ]
  rw [show 656 = 655 + 1 by norm_num, Nat.count_succ]
  rw [show 655 = 654 + 1 by norm_num, Nat.count_succ]
  rw [show 654 = 653 + 1 by norm_num, Nat.count_succ]
  rw [count_653]
  simp [prime_653, not_prime_654, not_prime_655, not_prime_656, not_prime_657, not_prime_658]

theorem prime_659 : (659 : Nat).Prime := by norm_num

theorem nth_119 : Nat.nth Nat.Prime 119 = 659 := by
  rw [← count_659]
  exact Nat.nth_count prime_659

theorem not_prime_660 : ¬Nat.Prime 660 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 330) (n := 660)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_661 : Nat.count Nat.Prime 661 = 120 := by
  rw [show 661 = 660 + 1 by norm_num, Nat.count_succ]
  rw [show 660 = 659 + 1 by norm_num, Nat.count_succ]
  rw [count_659]
  simp [prime_659, not_prime_660]

theorem prime_661 : (661 : Nat).Prime := by norm_num

theorem nth_120 : Nat.nth Nat.Prime 120 = 661 := by
  rw [← count_661]
  exact Nat.nth_count prime_661

theorem not_prime_662 : ¬Nat.Prime 662 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 331) (n := 662)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_663 : ¬Nat.Prime 663 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 221) (n := 663)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_664 : ¬Nat.Prime 664 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 332) (n := 664)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_665 : ¬Nat.Prime 665 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 133) (n := 665)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_666 : ¬Nat.Prime 666 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 333) (n := 666)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_667 : ¬Nat.Prime 667 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 29) (n := 667)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_668 : ¬Nat.Prime 668 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 334) (n := 668)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_669 : ¬Nat.Prime 669 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 223) (n := 669)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_670 : ¬Nat.Prime 670 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 335) (n := 670)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_671 : ¬Nat.Prime 671 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 61) (n := 671)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_672 : ¬Nat.Prime 672 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 336) (n := 672)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_673 : Nat.count Nat.Prime 673 = 121 := by
  rw [show 673 = 672 + 1 by norm_num, Nat.count_succ]
  rw [show 672 = 671 + 1 by norm_num, Nat.count_succ]
  rw [show 671 = 670 + 1 by norm_num, Nat.count_succ]
  rw [show 670 = 669 + 1 by norm_num, Nat.count_succ]
  rw [show 669 = 668 + 1 by norm_num, Nat.count_succ]
  rw [show 668 = 667 + 1 by norm_num, Nat.count_succ]
  rw [show 667 = 666 + 1 by norm_num, Nat.count_succ]
  rw [show 666 = 665 + 1 by norm_num, Nat.count_succ]
  rw [show 665 = 664 + 1 by norm_num, Nat.count_succ]
  rw [show 664 = 663 + 1 by norm_num, Nat.count_succ]
  rw [show 663 = 662 + 1 by norm_num, Nat.count_succ]
  rw [show 662 = 661 + 1 by norm_num, Nat.count_succ]
  rw [count_661]
  simp [prime_661, not_prime_662, not_prime_663, not_prime_664, not_prime_665, not_prime_666, not_prime_667, not_prime_668, not_prime_669, not_prime_670, not_prime_671, not_prime_672]

theorem prime_673 : (673 : Nat).Prime := by norm_num

theorem nth_121 : Nat.nth Nat.Prime 121 = 673 := by
  rw [← count_673]
  exact Nat.nth_count prime_673

theorem not_prime_674 : ¬Nat.Prime 674 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 337) (n := 674)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_675 : ¬Nat.Prime 675 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 225) (n := 675)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_676 : ¬Nat.Prime 676 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 338) (n := 676)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_677 : Nat.count Nat.Prime 677 = 122 := by
  rw [show 677 = 676 + 1 by norm_num, Nat.count_succ]
  rw [show 676 = 675 + 1 by norm_num, Nat.count_succ]
  rw [show 675 = 674 + 1 by norm_num, Nat.count_succ]
  rw [show 674 = 673 + 1 by norm_num, Nat.count_succ]
  rw [count_673]
  simp [prime_673, not_prime_674, not_prime_675, not_prime_676]

theorem prime_677 : (677 : Nat).Prime := by norm_num

theorem nth_122 : Nat.nth Nat.Prime 122 = 677 := by
  rw [← count_677]
  exact Nat.nth_count prime_677

theorem not_prime_678 : ¬Nat.Prime 678 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 339) (n := 678)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_679 : ¬Nat.Prime 679 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 97) (n := 679)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_680 : ¬Nat.Prime 680 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 340) (n := 680)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_681 : ¬Nat.Prime 681 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 227) (n := 681)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_682 : ¬Nat.Prime 682 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 341) (n := 682)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_683 : Nat.count Nat.Prime 683 = 123 := by
  rw [show 683 = 682 + 1 by norm_num, Nat.count_succ]
  rw [show 682 = 681 + 1 by norm_num, Nat.count_succ]
  rw [show 681 = 680 + 1 by norm_num, Nat.count_succ]
  rw [show 680 = 679 + 1 by norm_num, Nat.count_succ]
  rw [show 679 = 678 + 1 by norm_num, Nat.count_succ]
  rw [show 678 = 677 + 1 by norm_num, Nat.count_succ]
  rw [count_677]
  simp [prime_677, not_prime_678, not_prime_679, not_prime_680, not_prime_681, not_prime_682]

theorem prime_683 : (683 : Nat).Prime := by norm_num

theorem nth_123 : Nat.nth Nat.Prime 123 = 683 := by
  rw [← count_683]
  exact Nat.nth_count prime_683

theorem not_prime_684 : ¬Nat.Prime 684 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 342) (n := 684)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_685 : ¬Nat.Prime 685 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 137) (n := 685)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_686 : ¬Nat.Prime 686 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 343) (n := 686)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_687 : ¬Nat.Prime 687 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 229) (n := 687)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_688 : ¬Nat.Prime 688 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 344) (n := 688)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_689 : ¬Nat.Prime 689 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 53) (n := 689)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_690 : ¬Nat.Prime 690 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 345) (n := 690)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_691 : Nat.count Nat.Prime 691 = 124 := by
  rw [show 691 = 690 + 1 by norm_num, Nat.count_succ]
  rw [show 690 = 689 + 1 by norm_num, Nat.count_succ]
  rw [show 689 = 688 + 1 by norm_num, Nat.count_succ]
  rw [show 688 = 687 + 1 by norm_num, Nat.count_succ]
  rw [show 687 = 686 + 1 by norm_num, Nat.count_succ]
  rw [show 686 = 685 + 1 by norm_num, Nat.count_succ]
  rw [show 685 = 684 + 1 by norm_num, Nat.count_succ]
  rw [show 684 = 683 + 1 by norm_num, Nat.count_succ]
  rw [count_683]
  simp [prime_683, not_prime_684, not_prime_685, not_prime_686, not_prime_687, not_prime_688, not_prime_689, not_prime_690]

theorem prime_691 : (691 : Nat).Prime := by norm_num

theorem nth_124 : Nat.nth Nat.Prime 124 = 691 := by
  rw [← count_691]
  exact Nat.nth_count prime_691

end OeisA100474.PrimeCertificate
