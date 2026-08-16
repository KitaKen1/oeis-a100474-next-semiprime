import OeisA100474PrimeCertificate.Chunk24

/-! Kernel prime/count certificate, chunk 25 (625–649). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_4638 : ¬Nat.Prime 4638 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2319) (n := 4638)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4639 : Nat.count Nat.Prime 4639 = 625 := by
  rw [show 4639 = 4638 + 1 by norm_num, Nat.count_succ]
  rw [show 4638 = 4637 + 1 by norm_num, Nat.count_succ]
  rw [count_4637]
  simp [prime_4637, not_prime_4638]

theorem prime_4639 : (4639 : Nat).Prime := by norm_num

theorem nth_625 : Nat.nth Nat.Prime 625 = 4639 := by
  rw [← count_4639]
  exact Nat.nth_count prime_4639

theorem not_prime_4640 : ¬Nat.Prime 4640 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2320) (n := 4640)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4641 : ¬Nat.Prime 4641 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1547) (n := 4641)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4642 : ¬Nat.Prime 4642 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2321) (n := 4642)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4643 : Nat.count Nat.Prime 4643 = 626 := by
  rw [show 4643 = 4642 + 1 by norm_num, Nat.count_succ]
  rw [show 4642 = 4641 + 1 by norm_num, Nat.count_succ]
  rw [show 4641 = 4640 + 1 by norm_num, Nat.count_succ]
  rw [show 4640 = 4639 + 1 by norm_num, Nat.count_succ]
  rw [count_4639]
  simp [prime_4639, not_prime_4640, not_prime_4641, not_prime_4642]

theorem prime_4643 : (4643 : Nat).Prime := by norm_num

theorem nth_626 : Nat.nth Nat.Prime 626 = 4643 := by
  rw [← count_4643]
  exact Nat.nth_count prime_4643

theorem not_prime_4644 : ¬Nat.Prime 4644 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2322) (n := 4644)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4645 : ¬Nat.Prime 4645 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 929) (n := 4645)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4646 : ¬Nat.Prime 4646 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2323) (n := 4646)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4647 : ¬Nat.Prime 4647 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1549) (n := 4647)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4648 : ¬Nat.Prime 4648 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2324) (n := 4648)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4649 : Nat.count Nat.Prime 4649 = 627 := by
  rw [show 4649 = 4648 + 1 by norm_num, Nat.count_succ]
  rw [show 4648 = 4647 + 1 by norm_num, Nat.count_succ]
  rw [show 4647 = 4646 + 1 by norm_num, Nat.count_succ]
  rw [show 4646 = 4645 + 1 by norm_num, Nat.count_succ]
  rw [show 4645 = 4644 + 1 by norm_num, Nat.count_succ]
  rw [show 4644 = 4643 + 1 by norm_num, Nat.count_succ]
  rw [count_4643]
  simp [prime_4643, not_prime_4644, not_prime_4645, not_prime_4646, not_prime_4647, not_prime_4648]

theorem prime_4649 : (4649 : Nat).Prime := by norm_num

theorem nth_627 : Nat.nth Nat.Prime 627 = 4649 := by
  rw [← count_4649]
  exact Nat.nth_count prime_4649

theorem not_prime_4650 : ¬Nat.Prime 4650 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2325) (n := 4650)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4651 : Nat.count Nat.Prime 4651 = 628 := by
  rw [show 4651 = 4650 + 1 by norm_num, Nat.count_succ]
  rw [show 4650 = 4649 + 1 by norm_num, Nat.count_succ]
  rw [count_4649]
  simp [prime_4649, not_prime_4650]

theorem prime_4651 : (4651 : Nat).Prime := by norm_num

theorem nth_628 : Nat.nth Nat.Prime 628 = 4651 := by
  rw [← count_4651]
  exact Nat.nth_count prime_4651

theorem not_prime_4652 : ¬Nat.Prime 4652 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2326) (n := 4652)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4653 : ¬Nat.Prime 4653 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1551) (n := 4653)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4654 : ¬Nat.Prime 4654 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2327) (n := 4654)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4655 : ¬Nat.Prime 4655 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 931) (n := 4655)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4656 : ¬Nat.Prime 4656 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2328) (n := 4656)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4657 : Nat.count Nat.Prime 4657 = 629 := by
  rw [show 4657 = 4656 + 1 by norm_num, Nat.count_succ]
  rw [show 4656 = 4655 + 1 by norm_num, Nat.count_succ]
  rw [show 4655 = 4654 + 1 by norm_num, Nat.count_succ]
  rw [show 4654 = 4653 + 1 by norm_num, Nat.count_succ]
  rw [show 4653 = 4652 + 1 by norm_num, Nat.count_succ]
  rw [show 4652 = 4651 + 1 by norm_num, Nat.count_succ]
  rw [count_4651]
  simp [prime_4651, not_prime_4652, not_prime_4653, not_prime_4654, not_prime_4655, not_prime_4656]

theorem prime_4657 : (4657 : Nat).Prime := by norm_num

theorem nth_629 : Nat.nth Nat.Prime 629 = 4657 := by
  rw [← count_4657]
  exact Nat.nth_count prime_4657

theorem not_prime_4658 : ¬Nat.Prime 4658 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2329) (n := 4658)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4659 : ¬Nat.Prime 4659 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1553) (n := 4659)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4660 : ¬Nat.Prime 4660 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2330) (n := 4660)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4661 : ¬Nat.Prime 4661 :=
  Nat.not_prime_of_mul_eq (a := 59) (b := 79) (n := 4661)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4662 : ¬Nat.Prime 4662 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2331) (n := 4662)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4663 : Nat.count Nat.Prime 4663 = 630 := by
  rw [show 4663 = 4662 + 1 by norm_num, Nat.count_succ]
  rw [show 4662 = 4661 + 1 by norm_num, Nat.count_succ]
  rw [show 4661 = 4660 + 1 by norm_num, Nat.count_succ]
  rw [show 4660 = 4659 + 1 by norm_num, Nat.count_succ]
  rw [show 4659 = 4658 + 1 by norm_num, Nat.count_succ]
  rw [show 4658 = 4657 + 1 by norm_num, Nat.count_succ]
  rw [count_4657]
  simp [prime_4657, not_prime_4658, not_prime_4659, not_prime_4660, not_prime_4661, not_prime_4662]

theorem prime_4663 : (4663 : Nat).Prime := by norm_num

theorem nth_630 : Nat.nth Nat.Prime 630 = 4663 := by
  rw [← count_4663]
  exact Nat.nth_count prime_4663

theorem not_prime_4664 : ¬Nat.Prime 4664 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2332) (n := 4664)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4665 : ¬Nat.Prime 4665 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1555) (n := 4665)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4666 : ¬Nat.Prime 4666 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2333) (n := 4666)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4667 : ¬Nat.Prime 4667 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 359) (n := 4667)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4668 : ¬Nat.Prime 4668 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2334) (n := 4668)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4669 : ¬Nat.Prime 4669 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 667) (n := 4669)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4670 : ¬Nat.Prime 4670 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2335) (n := 4670)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4671 : ¬Nat.Prime 4671 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1557) (n := 4671)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4672 : ¬Nat.Prime 4672 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2336) (n := 4672)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4673 : Nat.count Nat.Prime 4673 = 631 := by
  rw [show 4673 = 4672 + 1 by norm_num, Nat.count_succ]
  rw [show 4672 = 4671 + 1 by norm_num, Nat.count_succ]
  rw [show 4671 = 4670 + 1 by norm_num, Nat.count_succ]
  rw [show 4670 = 4669 + 1 by norm_num, Nat.count_succ]
  rw [show 4669 = 4668 + 1 by norm_num, Nat.count_succ]
  rw [show 4668 = 4667 + 1 by norm_num, Nat.count_succ]
  rw [show 4667 = 4666 + 1 by norm_num, Nat.count_succ]
  rw [show 4666 = 4665 + 1 by norm_num, Nat.count_succ]
  rw [show 4665 = 4664 + 1 by norm_num, Nat.count_succ]
  rw [show 4664 = 4663 + 1 by norm_num, Nat.count_succ]
  rw [count_4663]
  simp [prime_4663, not_prime_4664, not_prime_4665, not_prime_4666, not_prime_4667, not_prime_4668, not_prime_4669, not_prime_4670, not_prime_4671, not_prime_4672]

theorem prime_4673 : (4673 : Nat).Prime := by norm_num

theorem nth_631 : Nat.nth Nat.Prime 631 = 4673 := by
  rw [← count_4673]
  exact Nat.nth_count prime_4673

theorem not_prime_4674 : ¬Nat.Prime 4674 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2337) (n := 4674)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4675 : ¬Nat.Prime 4675 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 935) (n := 4675)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4676 : ¬Nat.Prime 4676 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2338) (n := 4676)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4677 : ¬Nat.Prime 4677 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1559) (n := 4677)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4678 : ¬Nat.Prime 4678 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2339) (n := 4678)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4679 : Nat.count Nat.Prime 4679 = 632 := by
  rw [show 4679 = 4678 + 1 by norm_num, Nat.count_succ]
  rw [show 4678 = 4677 + 1 by norm_num, Nat.count_succ]
  rw [show 4677 = 4676 + 1 by norm_num, Nat.count_succ]
  rw [show 4676 = 4675 + 1 by norm_num, Nat.count_succ]
  rw [show 4675 = 4674 + 1 by norm_num, Nat.count_succ]
  rw [show 4674 = 4673 + 1 by norm_num, Nat.count_succ]
  rw [count_4673]
  simp [prime_4673, not_prime_4674, not_prime_4675, not_prime_4676, not_prime_4677, not_prime_4678]

theorem prime_4679 : (4679 : Nat).Prime := by norm_num

theorem nth_632 : Nat.nth Nat.Prime 632 = 4679 := by
  rw [← count_4679]
  exact Nat.nth_count prime_4679

theorem not_prime_4680 : ¬Nat.Prime 4680 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2340) (n := 4680)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4681 : ¬Nat.Prime 4681 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 151) (n := 4681)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4682 : ¬Nat.Prime 4682 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2341) (n := 4682)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4683 : ¬Nat.Prime 4683 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1561) (n := 4683)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4684 : ¬Nat.Prime 4684 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2342) (n := 4684)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4685 : ¬Nat.Prime 4685 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 937) (n := 4685)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4686 : ¬Nat.Prime 4686 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2343) (n := 4686)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4687 : ¬Nat.Prime 4687 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 109) (n := 4687)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4688 : ¬Nat.Prime 4688 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2344) (n := 4688)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4689 : ¬Nat.Prime 4689 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1563) (n := 4689)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4690 : ¬Nat.Prime 4690 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2345) (n := 4690)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4691 : Nat.count Nat.Prime 4691 = 633 := by
  rw [show 4691 = 4690 + 1 by norm_num, Nat.count_succ]
  rw [show 4690 = 4689 + 1 by norm_num, Nat.count_succ]
  rw [show 4689 = 4688 + 1 by norm_num, Nat.count_succ]
  rw [show 4688 = 4687 + 1 by norm_num, Nat.count_succ]
  rw [show 4687 = 4686 + 1 by norm_num, Nat.count_succ]
  rw [show 4686 = 4685 + 1 by norm_num, Nat.count_succ]
  rw [show 4685 = 4684 + 1 by norm_num, Nat.count_succ]
  rw [show 4684 = 4683 + 1 by norm_num, Nat.count_succ]
  rw [show 4683 = 4682 + 1 by norm_num, Nat.count_succ]
  rw [show 4682 = 4681 + 1 by norm_num, Nat.count_succ]
  rw [show 4681 = 4680 + 1 by norm_num, Nat.count_succ]
  rw [show 4680 = 4679 + 1 by norm_num, Nat.count_succ]
  rw [count_4679]
  simp [prime_4679, not_prime_4680, not_prime_4681, not_prime_4682, not_prime_4683, not_prime_4684, not_prime_4685, not_prime_4686, not_prime_4687, not_prime_4688, not_prime_4689, not_prime_4690]

theorem prime_4691 : (4691 : Nat).Prime := by norm_num

theorem nth_633 : Nat.nth Nat.Prime 633 = 4691 := by
  rw [← count_4691]
  exact Nat.nth_count prime_4691

theorem not_prime_4692 : ¬Nat.Prime 4692 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2346) (n := 4692)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4693 : ¬Nat.Prime 4693 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 361) (n := 4693)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4694 : ¬Nat.Prime 4694 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2347) (n := 4694)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4695 : ¬Nat.Prime 4695 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1565) (n := 4695)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4696 : ¬Nat.Prime 4696 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2348) (n := 4696)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4697 : ¬Nat.Prime 4697 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 671) (n := 4697)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4698 : ¬Nat.Prime 4698 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2349) (n := 4698)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4699 : ¬Nat.Prime 4699 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 127) (n := 4699)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4700 : ¬Nat.Prime 4700 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2350) (n := 4700)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4701 : ¬Nat.Prime 4701 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1567) (n := 4701)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4702 : ¬Nat.Prime 4702 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2351) (n := 4702)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4703 : Nat.count Nat.Prime 4703 = 634 := by
  rw [show 4703 = 4702 + 1 by norm_num, Nat.count_succ]
  rw [show 4702 = 4701 + 1 by norm_num, Nat.count_succ]
  rw [show 4701 = 4700 + 1 by norm_num, Nat.count_succ]
  rw [show 4700 = 4699 + 1 by norm_num, Nat.count_succ]
  rw [show 4699 = 4698 + 1 by norm_num, Nat.count_succ]
  rw [show 4698 = 4697 + 1 by norm_num, Nat.count_succ]
  rw [show 4697 = 4696 + 1 by norm_num, Nat.count_succ]
  rw [show 4696 = 4695 + 1 by norm_num, Nat.count_succ]
  rw [show 4695 = 4694 + 1 by norm_num, Nat.count_succ]
  rw [show 4694 = 4693 + 1 by norm_num, Nat.count_succ]
  rw [show 4693 = 4692 + 1 by norm_num, Nat.count_succ]
  rw [show 4692 = 4691 + 1 by norm_num, Nat.count_succ]
  rw [count_4691]
  simp [prime_4691, not_prime_4692, not_prime_4693, not_prime_4694, not_prime_4695, not_prime_4696, not_prime_4697, not_prime_4698, not_prime_4699, not_prime_4700, not_prime_4701, not_prime_4702]

theorem prime_4703 : (4703 : Nat).Prime := by norm_num

theorem nth_634 : Nat.nth Nat.Prime 634 = 4703 := by
  rw [← count_4703]
  exact Nat.nth_count prime_4703

theorem not_prime_4704 : ¬Nat.Prime 4704 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2352) (n := 4704)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4705 : ¬Nat.Prime 4705 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 941) (n := 4705)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4706 : ¬Nat.Prime 4706 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2353) (n := 4706)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4707 : ¬Nat.Prime 4707 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1569) (n := 4707)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4708 : ¬Nat.Prime 4708 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2354) (n := 4708)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4709 : ¬Nat.Prime 4709 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 277) (n := 4709)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4710 : ¬Nat.Prime 4710 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2355) (n := 4710)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4711 : ¬Nat.Prime 4711 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 673) (n := 4711)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4712 : ¬Nat.Prime 4712 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2356) (n := 4712)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4713 : ¬Nat.Prime 4713 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1571) (n := 4713)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4714 : ¬Nat.Prime 4714 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2357) (n := 4714)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4715 : ¬Nat.Prime 4715 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 943) (n := 4715)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4716 : ¬Nat.Prime 4716 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2358) (n := 4716)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4717 : ¬Nat.Prime 4717 :=
  Nat.not_prime_of_mul_eq (a := 53) (b := 89) (n := 4717)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4718 : ¬Nat.Prime 4718 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2359) (n := 4718)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4719 : ¬Nat.Prime 4719 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1573) (n := 4719)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4720 : ¬Nat.Prime 4720 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2360) (n := 4720)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4721 : Nat.count Nat.Prime 4721 = 635 := by
  rw [show 4721 = 4720 + 1 by norm_num, Nat.count_succ]
  rw [show 4720 = 4719 + 1 by norm_num, Nat.count_succ]
  rw [show 4719 = 4718 + 1 by norm_num, Nat.count_succ]
  rw [show 4718 = 4717 + 1 by norm_num, Nat.count_succ]
  rw [show 4717 = 4716 + 1 by norm_num, Nat.count_succ]
  rw [show 4716 = 4715 + 1 by norm_num, Nat.count_succ]
  rw [show 4715 = 4714 + 1 by norm_num, Nat.count_succ]
  rw [show 4714 = 4713 + 1 by norm_num, Nat.count_succ]
  rw [show 4713 = 4712 + 1 by norm_num, Nat.count_succ]
  rw [show 4712 = 4711 + 1 by norm_num, Nat.count_succ]
  rw [show 4711 = 4710 + 1 by norm_num, Nat.count_succ]
  rw [show 4710 = 4709 + 1 by norm_num, Nat.count_succ]
  rw [show 4709 = 4708 + 1 by norm_num, Nat.count_succ]
  rw [show 4708 = 4707 + 1 by norm_num, Nat.count_succ]
  rw [show 4707 = 4706 + 1 by norm_num, Nat.count_succ]
  rw [show 4706 = 4705 + 1 by norm_num, Nat.count_succ]
  rw [show 4705 = 4704 + 1 by norm_num, Nat.count_succ]
  rw [show 4704 = 4703 + 1 by norm_num, Nat.count_succ]
  rw [count_4703]
  simp [prime_4703, not_prime_4704, not_prime_4705, not_prime_4706, not_prime_4707, not_prime_4708, not_prime_4709, not_prime_4710, not_prime_4711, not_prime_4712, not_prime_4713, not_prime_4714, not_prime_4715, not_prime_4716, not_prime_4717, not_prime_4718, not_prime_4719, not_prime_4720]

theorem prime_4721 : (4721 : Nat).Prime := by norm_num

theorem nth_635 : Nat.nth Nat.Prime 635 = 4721 := by
  rw [← count_4721]
  exact Nat.nth_count prime_4721

theorem not_prime_4722 : ¬Nat.Prime 4722 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2361) (n := 4722)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4723 : Nat.count Nat.Prime 4723 = 636 := by
  rw [show 4723 = 4722 + 1 by norm_num, Nat.count_succ]
  rw [show 4722 = 4721 + 1 by norm_num, Nat.count_succ]
  rw [count_4721]
  simp [prime_4721, not_prime_4722]

theorem prime_4723 : (4723 : Nat).Prime := by norm_num

theorem nth_636 : Nat.nth Nat.Prime 636 = 4723 := by
  rw [← count_4723]
  exact Nat.nth_count prime_4723

theorem not_prime_4724 : ¬Nat.Prime 4724 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2362) (n := 4724)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4725 : ¬Nat.Prime 4725 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1575) (n := 4725)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4726 : ¬Nat.Prime 4726 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2363) (n := 4726)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4727 : ¬Nat.Prime 4727 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 163) (n := 4727)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4728 : ¬Nat.Prime 4728 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2364) (n := 4728)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4729 : Nat.count Nat.Prime 4729 = 637 := by
  rw [show 4729 = 4728 + 1 by norm_num, Nat.count_succ]
  rw [show 4728 = 4727 + 1 by norm_num, Nat.count_succ]
  rw [show 4727 = 4726 + 1 by norm_num, Nat.count_succ]
  rw [show 4726 = 4725 + 1 by norm_num, Nat.count_succ]
  rw [show 4725 = 4724 + 1 by norm_num, Nat.count_succ]
  rw [show 4724 = 4723 + 1 by norm_num, Nat.count_succ]
  rw [count_4723]
  simp [prime_4723, not_prime_4724, not_prime_4725, not_prime_4726, not_prime_4727, not_prime_4728]

theorem prime_4729 : (4729 : Nat).Prime := by norm_num

theorem nth_637 : Nat.nth Nat.Prime 637 = 4729 := by
  rw [← count_4729]
  exact Nat.nth_count prime_4729

theorem not_prime_4730 : ¬Nat.Prime 4730 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2365) (n := 4730)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4731 : ¬Nat.Prime 4731 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1577) (n := 4731)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4732 : ¬Nat.Prime 4732 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2366) (n := 4732)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4733 : Nat.count Nat.Prime 4733 = 638 := by
  rw [show 4733 = 4732 + 1 by norm_num, Nat.count_succ]
  rw [show 4732 = 4731 + 1 by norm_num, Nat.count_succ]
  rw [show 4731 = 4730 + 1 by norm_num, Nat.count_succ]
  rw [show 4730 = 4729 + 1 by norm_num, Nat.count_succ]
  rw [count_4729]
  simp [prime_4729, not_prime_4730, not_prime_4731, not_prime_4732]

theorem prime_4733 : (4733 : Nat).Prime := by norm_num

theorem nth_638 : Nat.nth Nat.Prime 638 = 4733 := by
  rw [← count_4733]
  exact Nat.nth_count prime_4733

theorem not_prime_4734 : ¬Nat.Prime 4734 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2367) (n := 4734)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4735 : ¬Nat.Prime 4735 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 947) (n := 4735)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4736 : ¬Nat.Prime 4736 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2368) (n := 4736)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4737 : ¬Nat.Prime 4737 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1579) (n := 4737)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4738 : ¬Nat.Prime 4738 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2369) (n := 4738)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4739 : ¬Nat.Prime 4739 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 677) (n := 4739)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4740 : ¬Nat.Prime 4740 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2370) (n := 4740)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4741 : ¬Nat.Prime 4741 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 431) (n := 4741)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4742 : ¬Nat.Prime 4742 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2371) (n := 4742)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4743 : ¬Nat.Prime 4743 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1581) (n := 4743)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4744 : ¬Nat.Prime 4744 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2372) (n := 4744)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4745 : ¬Nat.Prime 4745 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 949) (n := 4745)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4746 : ¬Nat.Prime 4746 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2373) (n := 4746)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4747 : ¬Nat.Prime 4747 :=
  Nat.not_prime_of_mul_eq (a := 47) (b := 101) (n := 4747)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4748 : ¬Nat.Prime 4748 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2374) (n := 4748)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4749 : ¬Nat.Prime 4749 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1583) (n := 4749)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4750 : ¬Nat.Prime 4750 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2375) (n := 4750)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4751 : Nat.count Nat.Prime 4751 = 639 := by
  rw [show 4751 = 4750 + 1 by norm_num, Nat.count_succ]
  rw [show 4750 = 4749 + 1 by norm_num, Nat.count_succ]
  rw [show 4749 = 4748 + 1 by norm_num, Nat.count_succ]
  rw [show 4748 = 4747 + 1 by norm_num, Nat.count_succ]
  rw [show 4747 = 4746 + 1 by norm_num, Nat.count_succ]
  rw [show 4746 = 4745 + 1 by norm_num, Nat.count_succ]
  rw [show 4745 = 4744 + 1 by norm_num, Nat.count_succ]
  rw [show 4744 = 4743 + 1 by norm_num, Nat.count_succ]
  rw [show 4743 = 4742 + 1 by norm_num, Nat.count_succ]
  rw [show 4742 = 4741 + 1 by norm_num, Nat.count_succ]
  rw [show 4741 = 4740 + 1 by norm_num, Nat.count_succ]
  rw [show 4740 = 4739 + 1 by norm_num, Nat.count_succ]
  rw [show 4739 = 4738 + 1 by norm_num, Nat.count_succ]
  rw [show 4738 = 4737 + 1 by norm_num, Nat.count_succ]
  rw [show 4737 = 4736 + 1 by norm_num, Nat.count_succ]
  rw [show 4736 = 4735 + 1 by norm_num, Nat.count_succ]
  rw [show 4735 = 4734 + 1 by norm_num, Nat.count_succ]
  rw [show 4734 = 4733 + 1 by norm_num, Nat.count_succ]
  rw [count_4733]
  simp [prime_4733, not_prime_4734, not_prime_4735, not_prime_4736, not_prime_4737, not_prime_4738, not_prime_4739, not_prime_4740, not_prime_4741, not_prime_4742, not_prime_4743, not_prime_4744, not_prime_4745, not_prime_4746, not_prime_4747, not_prime_4748, not_prime_4749, not_prime_4750]

theorem prime_4751 : (4751 : Nat).Prime := by norm_num

theorem nth_639 : Nat.nth Nat.Prime 639 = 4751 := by
  rw [← count_4751]
  exact Nat.nth_count prime_4751

theorem not_prime_4752 : ¬Nat.Prime 4752 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2376) (n := 4752)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4753 : ¬Nat.Prime 4753 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 679) (n := 4753)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4754 : ¬Nat.Prime 4754 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2377) (n := 4754)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4755 : ¬Nat.Prime 4755 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1585) (n := 4755)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4756 : ¬Nat.Prime 4756 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2378) (n := 4756)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4757 : ¬Nat.Prime 4757 :=
  Nat.not_prime_of_mul_eq (a := 67) (b := 71) (n := 4757)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4758 : ¬Nat.Prime 4758 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2379) (n := 4758)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4759 : Nat.count Nat.Prime 4759 = 640 := by
  rw [show 4759 = 4758 + 1 by norm_num, Nat.count_succ]
  rw [show 4758 = 4757 + 1 by norm_num, Nat.count_succ]
  rw [show 4757 = 4756 + 1 by norm_num, Nat.count_succ]
  rw [show 4756 = 4755 + 1 by norm_num, Nat.count_succ]
  rw [show 4755 = 4754 + 1 by norm_num, Nat.count_succ]
  rw [show 4754 = 4753 + 1 by norm_num, Nat.count_succ]
  rw [show 4753 = 4752 + 1 by norm_num, Nat.count_succ]
  rw [show 4752 = 4751 + 1 by norm_num, Nat.count_succ]
  rw [count_4751]
  simp [prime_4751, not_prime_4752, not_prime_4753, not_prime_4754, not_prime_4755, not_prime_4756, not_prime_4757, not_prime_4758]

theorem prime_4759 : (4759 : Nat).Prime := by norm_num

theorem nth_640 : Nat.nth Nat.Prime 640 = 4759 := by
  rw [← count_4759]
  exact Nat.nth_count prime_4759

theorem not_prime_4760 : ¬Nat.Prime 4760 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2380) (n := 4760)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4761 : ¬Nat.Prime 4761 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1587) (n := 4761)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4762 : ¬Nat.Prime 4762 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2381) (n := 4762)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4763 : ¬Nat.Prime 4763 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 433) (n := 4763)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4764 : ¬Nat.Prime 4764 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2382) (n := 4764)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4765 : ¬Nat.Prime 4765 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 953) (n := 4765)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4766 : ¬Nat.Prime 4766 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2383) (n := 4766)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4767 : ¬Nat.Prime 4767 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1589) (n := 4767)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4768 : ¬Nat.Prime 4768 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2384) (n := 4768)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4769 : ¬Nat.Prime 4769 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 251) (n := 4769)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4770 : ¬Nat.Prime 4770 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2385) (n := 4770)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4771 : ¬Nat.Prime 4771 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 367) (n := 4771)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4772 : ¬Nat.Prime 4772 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2386) (n := 4772)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4773 : ¬Nat.Prime 4773 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1591) (n := 4773)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4774 : ¬Nat.Prime 4774 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2387) (n := 4774)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4775 : ¬Nat.Prime 4775 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 955) (n := 4775)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4776 : ¬Nat.Prime 4776 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2388) (n := 4776)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4777 : ¬Nat.Prime 4777 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 281) (n := 4777)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4778 : ¬Nat.Prime 4778 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2389) (n := 4778)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4779 : ¬Nat.Prime 4779 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1593) (n := 4779)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4780 : ¬Nat.Prime 4780 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2390) (n := 4780)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4781 : ¬Nat.Prime 4781 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 683) (n := 4781)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4782 : ¬Nat.Prime 4782 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2391) (n := 4782)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4783 : Nat.count Nat.Prime 4783 = 641 := by
  rw [show 4783 = 4782 + 1 by norm_num, Nat.count_succ]
  rw [show 4782 = 4781 + 1 by norm_num, Nat.count_succ]
  rw [show 4781 = 4780 + 1 by norm_num, Nat.count_succ]
  rw [show 4780 = 4779 + 1 by norm_num, Nat.count_succ]
  rw [show 4779 = 4778 + 1 by norm_num, Nat.count_succ]
  rw [show 4778 = 4777 + 1 by norm_num, Nat.count_succ]
  rw [show 4777 = 4776 + 1 by norm_num, Nat.count_succ]
  rw [show 4776 = 4775 + 1 by norm_num, Nat.count_succ]
  rw [show 4775 = 4774 + 1 by norm_num, Nat.count_succ]
  rw [show 4774 = 4773 + 1 by norm_num, Nat.count_succ]
  rw [show 4773 = 4772 + 1 by norm_num, Nat.count_succ]
  rw [show 4772 = 4771 + 1 by norm_num, Nat.count_succ]
  rw [show 4771 = 4770 + 1 by norm_num, Nat.count_succ]
  rw [show 4770 = 4769 + 1 by norm_num, Nat.count_succ]
  rw [show 4769 = 4768 + 1 by norm_num, Nat.count_succ]
  rw [show 4768 = 4767 + 1 by norm_num, Nat.count_succ]
  rw [show 4767 = 4766 + 1 by norm_num, Nat.count_succ]
  rw [show 4766 = 4765 + 1 by norm_num, Nat.count_succ]
  rw [show 4765 = 4764 + 1 by norm_num, Nat.count_succ]
  rw [show 4764 = 4763 + 1 by norm_num, Nat.count_succ]
  rw [show 4763 = 4762 + 1 by norm_num, Nat.count_succ]
  rw [show 4762 = 4761 + 1 by norm_num, Nat.count_succ]
  rw [show 4761 = 4760 + 1 by norm_num, Nat.count_succ]
  rw [show 4760 = 4759 + 1 by norm_num, Nat.count_succ]
  rw [count_4759]
  simp [prime_4759, not_prime_4760, not_prime_4761, not_prime_4762, not_prime_4763, not_prime_4764, not_prime_4765, not_prime_4766, not_prime_4767, not_prime_4768, not_prime_4769, not_prime_4770, not_prime_4771, not_prime_4772, not_prime_4773, not_prime_4774, not_prime_4775, not_prime_4776, not_prime_4777, not_prime_4778, not_prime_4779, not_prime_4780, not_prime_4781, not_prime_4782]

theorem prime_4783 : (4783 : Nat).Prime := by norm_num

theorem nth_641 : Nat.nth Nat.Prime 641 = 4783 := by
  rw [← count_4783]
  exact Nat.nth_count prime_4783

theorem not_prime_4784 : ¬Nat.Prime 4784 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2392) (n := 4784)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4785 : ¬Nat.Prime 4785 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1595) (n := 4785)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4786 : ¬Nat.Prime 4786 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2393) (n := 4786)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4787 : Nat.count Nat.Prime 4787 = 642 := by
  rw [show 4787 = 4786 + 1 by norm_num, Nat.count_succ]
  rw [show 4786 = 4785 + 1 by norm_num, Nat.count_succ]
  rw [show 4785 = 4784 + 1 by norm_num, Nat.count_succ]
  rw [show 4784 = 4783 + 1 by norm_num, Nat.count_succ]
  rw [count_4783]
  simp [prime_4783, not_prime_4784, not_prime_4785, not_prime_4786]

theorem prime_4787 : (4787 : Nat).Prime := by norm_num

theorem nth_642 : Nat.nth Nat.Prime 642 = 4787 := by
  rw [← count_4787]
  exact Nat.nth_count prime_4787

theorem not_prime_4788 : ¬Nat.Prime 4788 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2394) (n := 4788)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4789 : Nat.count Nat.Prime 4789 = 643 := by
  rw [show 4789 = 4788 + 1 by norm_num, Nat.count_succ]
  rw [show 4788 = 4787 + 1 by norm_num, Nat.count_succ]
  rw [count_4787]
  simp [prime_4787, not_prime_4788]

theorem prime_4789 : (4789 : Nat).Prime := by norm_num

theorem nth_643 : Nat.nth Nat.Prime 643 = 4789 := by
  rw [← count_4789]
  exact Nat.nth_count prime_4789

theorem not_prime_4790 : ¬Nat.Prime 4790 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2395) (n := 4790)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4791 : ¬Nat.Prime 4791 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1597) (n := 4791)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4792 : ¬Nat.Prime 4792 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2396) (n := 4792)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4793 : Nat.count Nat.Prime 4793 = 644 := by
  rw [show 4793 = 4792 + 1 by norm_num, Nat.count_succ]
  rw [show 4792 = 4791 + 1 by norm_num, Nat.count_succ]
  rw [show 4791 = 4790 + 1 by norm_num, Nat.count_succ]
  rw [show 4790 = 4789 + 1 by norm_num, Nat.count_succ]
  rw [count_4789]
  simp [prime_4789, not_prime_4790, not_prime_4791, not_prime_4792]

theorem prime_4793 : (4793 : Nat).Prime := by norm_num

theorem nth_644 : Nat.nth Nat.Prime 644 = 4793 := by
  rw [← count_4793]
  exact Nat.nth_count prime_4793

theorem not_prime_4794 : ¬Nat.Prime 4794 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2397) (n := 4794)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4795 : ¬Nat.Prime 4795 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 959) (n := 4795)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4796 : ¬Nat.Prime 4796 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2398) (n := 4796)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4797 : ¬Nat.Prime 4797 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1599) (n := 4797)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4798 : ¬Nat.Prime 4798 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2399) (n := 4798)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4799 : Nat.count Nat.Prime 4799 = 645 := by
  rw [show 4799 = 4798 + 1 by norm_num, Nat.count_succ]
  rw [show 4798 = 4797 + 1 by norm_num, Nat.count_succ]
  rw [show 4797 = 4796 + 1 by norm_num, Nat.count_succ]
  rw [show 4796 = 4795 + 1 by norm_num, Nat.count_succ]
  rw [show 4795 = 4794 + 1 by norm_num, Nat.count_succ]
  rw [show 4794 = 4793 + 1 by norm_num, Nat.count_succ]
  rw [count_4793]
  simp [prime_4793, not_prime_4794, not_prime_4795, not_prime_4796, not_prime_4797, not_prime_4798]

theorem prime_4799 : (4799 : Nat).Prime := by norm_num

theorem nth_645 : Nat.nth Nat.Prime 645 = 4799 := by
  rw [← count_4799]
  exact Nat.nth_count prime_4799

theorem not_prime_4800 : ¬Nat.Prime 4800 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2400) (n := 4800)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4801 : Nat.count Nat.Prime 4801 = 646 := by
  rw [show 4801 = 4800 + 1 by norm_num, Nat.count_succ]
  rw [show 4800 = 4799 + 1 by norm_num, Nat.count_succ]
  rw [count_4799]
  simp [prime_4799, not_prime_4800]

theorem prime_4801 : (4801 : Nat).Prime := by norm_num

theorem nth_646 : Nat.nth Nat.Prime 646 = 4801 := by
  rw [← count_4801]
  exact Nat.nth_count prime_4801

theorem not_prime_4802 : ¬Nat.Prime 4802 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2401) (n := 4802)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4803 : ¬Nat.Prime 4803 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1601) (n := 4803)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4804 : ¬Nat.Prime 4804 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2402) (n := 4804)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4805 : ¬Nat.Prime 4805 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 961) (n := 4805)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4806 : ¬Nat.Prime 4806 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2403) (n := 4806)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4807 : ¬Nat.Prime 4807 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 437) (n := 4807)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4808 : ¬Nat.Prime 4808 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2404) (n := 4808)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4809 : ¬Nat.Prime 4809 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1603) (n := 4809)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4810 : ¬Nat.Prime 4810 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2405) (n := 4810)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4811 : ¬Nat.Prime 4811 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 283) (n := 4811)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4812 : ¬Nat.Prime 4812 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2406) (n := 4812)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4813 : Nat.count Nat.Prime 4813 = 647 := by
  rw [show 4813 = 4812 + 1 by norm_num, Nat.count_succ]
  rw [show 4812 = 4811 + 1 by norm_num, Nat.count_succ]
  rw [show 4811 = 4810 + 1 by norm_num, Nat.count_succ]
  rw [show 4810 = 4809 + 1 by norm_num, Nat.count_succ]
  rw [show 4809 = 4808 + 1 by norm_num, Nat.count_succ]
  rw [show 4808 = 4807 + 1 by norm_num, Nat.count_succ]
  rw [show 4807 = 4806 + 1 by norm_num, Nat.count_succ]
  rw [show 4806 = 4805 + 1 by norm_num, Nat.count_succ]
  rw [show 4805 = 4804 + 1 by norm_num, Nat.count_succ]
  rw [show 4804 = 4803 + 1 by norm_num, Nat.count_succ]
  rw [show 4803 = 4802 + 1 by norm_num, Nat.count_succ]
  rw [show 4802 = 4801 + 1 by norm_num, Nat.count_succ]
  rw [count_4801]
  simp [prime_4801, not_prime_4802, not_prime_4803, not_prime_4804, not_prime_4805, not_prime_4806, not_prime_4807, not_prime_4808, not_prime_4809, not_prime_4810, not_prime_4811, not_prime_4812]

theorem prime_4813 : (4813 : Nat).Prime := by norm_num

theorem nth_647 : Nat.nth Nat.Prime 647 = 4813 := by
  rw [← count_4813]
  exact Nat.nth_count prime_4813

theorem not_prime_4814 : ¬Nat.Prime 4814 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2407) (n := 4814)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4815 : ¬Nat.Prime 4815 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1605) (n := 4815)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4816 : ¬Nat.Prime 4816 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2408) (n := 4816)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4817 : Nat.count Nat.Prime 4817 = 648 := by
  rw [show 4817 = 4816 + 1 by norm_num, Nat.count_succ]
  rw [show 4816 = 4815 + 1 by norm_num, Nat.count_succ]
  rw [show 4815 = 4814 + 1 by norm_num, Nat.count_succ]
  rw [show 4814 = 4813 + 1 by norm_num, Nat.count_succ]
  rw [count_4813]
  simp [prime_4813, not_prime_4814, not_prime_4815, not_prime_4816]

theorem prime_4817 : (4817 : Nat).Prime := by norm_num

theorem nth_648 : Nat.nth Nat.Prime 648 = 4817 := by
  rw [← count_4817]
  exact Nat.nth_count prime_4817

theorem not_prime_4818 : ¬Nat.Prime 4818 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2409) (n := 4818)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4819 : ¬Nat.Prime 4819 :=
  Nat.not_prime_of_mul_eq (a := 61) (b := 79) (n := 4819)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4820 : ¬Nat.Prime 4820 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2410) (n := 4820)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4821 : ¬Nat.Prime 4821 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1607) (n := 4821)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4822 : ¬Nat.Prime 4822 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2411) (n := 4822)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4823 : ¬Nat.Prime 4823 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 689) (n := 4823)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4824 : ¬Nat.Prime 4824 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2412) (n := 4824)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4825 : ¬Nat.Prime 4825 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 965) (n := 4825)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4826 : ¬Nat.Prime 4826 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2413) (n := 4826)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4827 : ¬Nat.Prime 4827 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1609) (n := 4827)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4828 : ¬Nat.Prime 4828 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2414) (n := 4828)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4829 : ¬Nat.Prime 4829 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 439) (n := 4829)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_4830 : ¬Nat.Prime 4830 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 2415) (n := 4830)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_4831 : Nat.count Nat.Prime 4831 = 649 := by
  rw [show 4831 = 4830 + 1 by norm_num, Nat.count_succ]
  rw [show 4830 = 4829 + 1 by norm_num, Nat.count_succ]
  rw [show 4829 = 4828 + 1 by norm_num, Nat.count_succ]
  rw [show 4828 = 4827 + 1 by norm_num, Nat.count_succ]
  rw [show 4827 = 4826 + 1 by norm_num, Nat.count_succ]
  rw [show 4826 = 4825 + 1 by norm_num, Nat.count_succ]
  rw [show 4825 = 4824 + 1 by norm_num, Nat.count_succ]
  rw [show 4824 = 4823 + 1 by norm_num, Nat.count_succ]
  rw [show 4823 = 4822 + 1 by norm_num, Nat.count_succ]
  rw [show 4822 = 4821 + 1 by norm_num, Nat.count_succ]
  rw [show 4821 = 4820 + 1 by norm_num, Nat.count_succ]
  rw [show 4820 = 4819 + 1 by norm_num, Nat.count_succ]
  rw [show 4819 = 4818 + 1 by norm_num, Nat.count_succ]
  rw [show 4818 = 4817 + 1 by norm_num, Nat.count_succ]
  rw [count_4817]
  simp [prime_4817, not_prime_4818, not_prime_4819, not_prime_4820, not_prime_4821, not_prime_4822, not_prime_4823, not_prime_4824, not_prime_4825, not_prime_4826, not_prime_4827, not_prime_4828, not_prime_4829, not_prime_4830]

theorem prime_4831 : (4831 : Nat).Prime := by norm_num

theorem nth_649 : Nat.nth Nat.Prime 649 = 4831 := by
  rw [← count_4831]
  exact Nat.nth_count prime_4831

end OeisA100474.PrimeCertificate
