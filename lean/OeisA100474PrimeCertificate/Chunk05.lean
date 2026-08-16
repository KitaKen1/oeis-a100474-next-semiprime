import OeisA100474PrimeCertificate.Chunk04

/-! Kernel prime/count certificate, chunk 05 (125–149). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_692 : ¬Nat.Prime 692 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 346) (n := 692)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_693 : ¬Nat.Prime 693 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 231) (n := 693)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_694 : ¬Nat.Prime 694 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 347) (n := 694)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_695 : ¬Nat.Prime 695 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 139) (n := 695)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_696 : ¬Nat.Prime 696 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 348) (n := 696)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_697 : ¬Nat.Prime 697 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 41) (n := 697)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_698 : ¬Nat.Prime 698 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 349) (n := 698)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_699 : ¬Nat.Prime 699 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 233) (n := 699)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_700 : ¬Nat.Prime 700 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 350) (n := 700)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_701 : Nat.count Nat.Prime 701 = 125 := by
  rw [show 701 = 700 + 1 by norm_num, Nat.count_succ]
  rw [show 700 = 699 + 1 by norm_num, Nat.count_succ]
  rw [show 699 = 698 + 1 by norm_num, Nat.count_succ]
  rw [show 698 = 697 + 1 by norm_num, Nat.count_succ]
  rw [show 697 = 696 + 1 by norm_num, Nat.count_succ]
  rw [show 696 = 695 + 1 by norm_num, Nat.count_succ]
  rw [show 695 = 694 + 1 by norm_num, Nat.count_succ]
  rw [show 694 = 693 + 1 by norm_num, Nat.count_succ]
  rw [show 693 = 692 + 1 by norm_num, Nat.count_succ]
  rw [show 692 = 691 + 1 by norm_num, Nat.count_succ]
  rw [count_691]
  simp [prime_691, not_prime_692, not_prime_693, not_prime_694, not_prime_695, not_prime_696, not_prime_697, not_prime_698, not_prime_699, not_prime_700]

theorem prime_701 : (701 : Nat).Prime := by norm_num

theorem nth_125 : Nat.nth Nat.Prime 125 = 701 := by
  rw [← count_701]
  exact Nat.nth_count prime_701

theorem not_prime_702 : ¬Nat.Prime 702 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 351) (n := 702)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_703 : ¬Nat.Prime 703 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 37) (n := 703)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_704 : ¬Nat.Prime 704 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 352) (n := 704)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_705 : ¬Nat.Prime 705 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 235) (n := 705)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_706 : ¬Nat.Prime 706 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 353) (n := 706)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_707 : ¬Nat.Prime 707 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 101) (n := 707)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_708 : ¬Nat.Prime 708 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 354) (n := 708)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_709 : Nat.count Nat.Prime 709 = 126 := by
  rw [show 709 = 708 + 1 by norm_num, Nat.count_succ]
  rw [show 708 = 707 + 1 by norm_num, Nat.count_succ]
  rw [show 707 = 706 + 1 by norm_num, Nat.count_succ]
  rw [show 706 = 705 + 1 by norm_num, Nat.count_succ]
  rw [show 705 = 704 + 1 by norm_num, Nat.count_succ]
  rw [show 704 = 703 + 1 by norm_num, Nat.count_succ]
  rw [show 703 = 702 + 1 by norm_num, Nat.count_succ]
  rw [show 702 = 701 + 1 by norm_num, Nat.count_succ]
  rw [count_701]
  simp [prime_701, not_prime_702, not_prime_703, not_prime_704, not_prime_705, not_prime_706, not_prime_707, not_prime_708]

theorem prime_709 : (709 : Nat).Prime := by norm_num

theorem nth_126 : Nat.nth Nat.Prime 126 = 709 := by
  rw [← count_709]
  exact Nat.nth_count prime_709

theorem not_prime_710 : ¬Nat.Prime 710 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 355) (n := 710)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_711 : ¬Nat.Prime 711 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 237) (n := 711)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_712 : ¬Nat.Prime 712 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 356) (n := 712)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_713 : ¬Nat.Prime 713 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 31) (n := 713)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_714 : ¬Nat.Prime 714 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 357) (n := 714)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_715 : ¬Nat.Prime 715 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 143) (n := 715)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_716 : ¬Nat.Prime 716 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 358) (n := 716)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_717 : ¬Nat.Prime 717 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 239) (n := 717)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_718 : ¬Nat.Prime 718 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 359) (n := 718)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_719 : Nat.count Nat.Prime 719 = 127 := by
  rw [show 719 = 718 + 1 by norm_num, Nat.count_succ]
  rw [show 718 = 717 + 1 by norm_num, Nat.count_succ]
  rw [show 717 = 716 + 1 by norm_num, Nat.count_succ]
  rw [show 716 = 715 + 1 by norm_num, Nat.count_succ]
  rw [show 715 = 714 + 1 by norm_num, Nat.count_succ]
  rw [show 714 = 713 + 1 by norm_num, Nat.count_succ]
  rw [show 713 = 712 + 1 by norm_num, Nat.count_succ]
  rw [show 712 = 711 + 1 by norm_num, Nat.count_succ]
  rw [show 711 = 710 + 1 by norm_num, Nat.count_succ]
  rw [show 710 = 709 + 1 by norm_num, Nat.count_succ]
  rw [count_709]
  simp [prime_709, not_prime_710, not_prime_711, not_prime_712, not_prime_713, not_prime_714, not_prime_715, not_prime_716, not_prime_717, not_prime_718]

theorem prime_719 : (719 : Nat).Prime := by norm_num

theorem nth_127 : Nat.nth Nat.Prime 127 = 719 := by
  rw [← count_719]
  exact Nat.nth_count prime_719

theorem not_prime_720 : ¬Nat.Prime 720 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 360) (n := 720)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_721 : ¬Nat.Prime 721 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 103) (n := 721)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_722 : ¬Nat.Prime 722 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 361) (n := 722)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_723 : ¬Nat.Prime 723 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 241) (n := 723)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_724 : ¬Nat.Prime 724 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 362) (n := 724)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_725 : ¬Nat.Prime 725 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 145) (n := 725)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_726 : ¬Nat.Prime 726 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 363) (n := 726)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_727 : Nat.count Nat.Prime 727 = 128 := by
  rw [show 727 = 726 + 1 by norm_num, Nat.count_succ]
  rw [show 726 = 725 + 1 by norm_num, Nat.count_succ]
  rw [show 725 = 724 + 1 by norm_num, Nat.count_succ]
  rw [show 724 = 723 + 1 by norm_num, Nat.count_succ]
  rw [show 723 = 722 + 1 by norm_num, Nat.count_succ]
  rw [show 722 = 721 + 1 by norm_num, Nat.count_succ]
  rw [show 721 = 720 + 1 by norm_num, Nat.count_succ]
  rw [show 720 = 719 + 1 by norm_num, Nat.count_succ]
  rw [count_719]
  simp [prime_719, not_prime_720, not_prime_721, not_prime_722, not_prime_723, not_prime_724, not_prime_725, not_prime_726]

theorem prime_727 : (727 : Nat).Prime := by norm_num

theorem nth_128 : Nat.nth Nat.Prime 128 = 727 := by
  rw [← count_727]
  exact Nat.nth_count prime_727

theorem not_prime_728 : ¬Nat.Prime 728 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 364) (n := 728)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_729 : ¬Nat.Prime 729 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 243) (n := 729)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_730 : ¬Nat.Prime 730 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 365) (n := 730)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_731 : ¬Nat.Prime 731 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 43) (n := 731)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_732 : ¬Nat.Prime 732 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 366) (n := 732)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_733 : Nat.count Nat.Prime 733 = 129 := by
  rw [show 733 = 732 + 1 by norm_num, Nat.count_succ]
  rw [show 732 = 731 + 1 by norm_num, Nat.count_succ]
  rw [show 731 = 730 + 1 by norm_num, Nat.count_succ]
  rw [show 730 = 729 + 1 by norm_num, Nat.count_succ]
  rw [show 729 = 728 + 1 by norm_num, Nat.count_succ]
  rw [show 728 = 727 + 1 by norm_num, Nat.count_succ]
  rw [count_727]
  simp [prime_727, not_prime_728, not_prime_729, not_prime_730, not_prime_731, not_prime_732]

theorem prime_733 : (733 : Nat).Prime := by norm_num

theorem nth_129 : Nat.nth Nat.Prime 129 = 733 := by
  rw [← count_733]
  exact Nat.nth_count prime_733

theorem not_prime_734 : ¬Nat.Prime 734 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 367) (n := 734)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_735 : ¬Nat.Prime 735 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 245) (n := 735)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_736 : ¬Nat.Prime 736 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 368) (n := 736)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_737 : ¬Nat.Prime 737 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 67) (n := 737)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_738 : ¬Nat.Prime 738 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 369) (n := 738)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_739 : Nat.count Nat.Prime 739 = 130 := by
  rw [show 739 = 738 + 1 by norm_num, Nat.count_succ]
  rw [show 738 = 737 + 1 by norm_num, Nat.count_succ]
  rw [show 737 = 736 + 1 by norm_num, Nat.count_succ]
  rw [show 736 = 735 + 1 by norm_num, Nat.count_succ]
  rw [show 735 = 734 + 1 by norm_num, Nat.count_succ]
  rw [show 734 = 733 + 1 by norm_num, Nat.count_succ]
  rw [count_733]
  simp [prime_733, not_prime_734, not_prime_735, not_prime_736, not_prime_737, not_prime_738]

theorem prime_739 : (739 : Nat).Prime := by norm_num

theorem nth_130 : Nat.nth Nat.Prime 130 = 739 := by
  rw [← count_739]
  exact Nat.nth_count prime_739

theorem not_prime_740 : ¬Nat.Prime 740 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 370) (n := 740)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_741 : ¬Nat.Prime 741 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 247) (n := 741)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_742 : ¬Nat.Prime 742 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 371) (n := 742)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_743 : Nat.count Nat.Prime 743 = 131 := by
  rw [show 743 = 742 + 1 by norm_num, Nat.count_succ]
  rw [show 742 = 741 + 1 by norm_num, Nat.count_succ]
  rw [show 741 = 740 + 1 by norm_num, Nat.count_succ]
  rw [show 740 = 739 + 1 by norm_num, Nat.count_succ]
  rw [count_739]
  simp [prime_739, not_prime_740, not_prime_741, not_prime_742]

theorem prime_743 : (743 : Nat).Prime := by norm_num

theorem nth_131 : Nat.nth Nat.Prime 131 = 743 := by
  rw [← count_743]
  exact Nat.nth_count prime_743

theorem not_prime_744 : ¬Nat.Prime 744 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 372) (n := 744)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_745 : ¬Nat.Prime 745 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 149) (n := 745)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_746 : ¬Nat.Prime 746 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 373) (n := 746)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_747 : ¬Nat.Prime 747 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 249) (n := 747)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_748 : ¬Nat.Prime 748 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 374) (n := 748)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_749 : ¬Nat.Prime 749 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 107) (n := 749)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_750 : ¬Nat.Prime 750 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 375) (n := 750)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_751 : Nat.count Nat.Prime 751 = 132 := by
  rw [show 751 = 750 + 1 by norm_num, Nat.count_succ]
  rw [show 750 = 749 + 1 by norm_num, Nat.count_succ]
  rw [show 749 = 748 + 1 by norm_num, Nat.count_succ]
  rw [show 748 = 747 + 1 by norm_num, Nat.count_succ]
  rw [show 747 = 746 + 1 by norm_num, Nat.count_succ]
  rw [show 746 = 745 + 1 by norm_num, Nat.count_succ]
  rw [show 745 = 744 + 1 by norm_num, Nat.count_succ]
  rw [show 744 = 743 + 1 by norm_num, Nat.count_succ]
  rw [count_743]
  simp [prime_743, not_prime_744, not_prime_745, not_prime_746, not_prime_747, not_prime_748, not_prime_749, not_prime_750]

theorem prime_751 : (751 : Nat).Prime := by norm_num

theorem nth_132 : Nat.nth Nat.Prime 132 = 751 := by
  rw [← count_751]
  exact Nat.nth_count prime_751

theorem not_prime_752 : ¬Nat.Prime 752 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 376) (n := 752)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_753 : ¬Nat.Prime 753 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 251) (n := 753)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_754 : ¬Nat.Prime 754 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 377) (n := 754)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_755 : ¬Nat.Prime 755 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 151) (n := 755)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_756 : ¬Nat.Prime 756 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 378) (n := 756)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_757 : Nat.count Nat.Prime 757 = 133 := by
  rw [show 757 = 756 + 1 by norm_num, Nat.count_succ]
  rw [show 756 = 755 + 1 by norm_num, Nat.count_succ]
  rw [show 755 = 754 + 1 by norm_num, Nat.count_succ]
  rw [show 754 = 753 + 1 by norm_num, Nat.count_succ]
  rw [show 753 = 752 + 1 by norm_num, Nat.count_succ]
  rw [show 752 = 751 + 1 by norm_num, Nat.count_succ]
  rw [count_751]
  simp [prime_751, not_prime_752, not_prime_753, not_prime_754, not_prime_755, not_prime_756]

theorem prime_757 : (757 : Nat).Prime := by norm_num

theorem nth_133 : Nat.nth Nat.Prime 133 = 757 := by
  rw [← count_757]
  exact Nat.nth_count prime_757

theorem not_prime_758 : ¬Nat.Prime 758 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 379) (n := 758)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_759 : ¬Nat.Prime 759 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 253) (n := 759)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_760 : ¬Nat.Prime 760 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 380) (n := 760)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_761 : Nat.count Nat.Prime 761 = 134 := by
  rw [show 761 = 760 + 1 by norm_num, Nat.count_succ]
  rw [show 760 = 759 + 1 by norm_num, Nat.count_succ]
  rw [show 759 = 758 + 1 by norm_num, Nat.count_succ]
  rw [show 758 = 757 + 1 by norm_num, Nat.count_succ]
  rw [count_757]
  simp [prime_757, not_prime_758, not_prime_759, not_prime_760]

theorem prime_761 : (761 : Nat).Prime := by norm_num

theorem nth_134 : Nat.nth Nat.Prime 134 = 761 := by
  rw [← count_761]
  exact Nat.nth_count prime_761

theorem not_prime_762 : ¬Nat.Prime 762 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 381) (n := 762)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_763 : ¬Nat.Prime 763 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 109) (n := 763)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_764 : ¬Nat.Prime 764 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 382) (n := 764)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_765 : ¬Nat.Prime 765 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 255) (n := 765)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_766 : ¬Nat.Prime 766 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 383) (n := 766)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_767 : ¬Nat.Prime 767 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 59) (n := 767)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_768 : ¬Nat.Prime 768 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 384) (n := 768)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_769 : Nat.count Nat.Prime 769 = 135 := by
  rw [show 769 = 768 + 1 by norm_num, Nat.count_succ]
  rw [show 768 = 767 + 1 by norm_num, Nat.count_succ]
  rw [show 767 = 766 + 1 by norm_num, Nat.count_succ]
  rw [show 766 = 765 + 1 by norm_num, Nat.count_succ]
  rw [show 765 = 764 + 1 by norm_num, Nat.count_succ]
  rw [show 764 = 763 + 1 by norm_num, Nat.count_succ]
  rw [show 763 = 762 + 1 by norm_num, Nat.count_succ]
  rw [show 762 = 761 + 1 by norm_num, Nat.count_succ]
  rw [count_761]
  simp [prime_761, not_prime_762, not_prime_763, not_prime_764, not_prime_765, not_prime_766, not_prime_767, not_prime_768]

theorem prime_769 : (769 : Nat).Prime := by norm_num

theorem nth_135 : Nat.nth Nat.Prime 135 = 769 := by
  rw [← count_769]
  exact Nat.nth_count prime_769

theorem not_prime_770 : ¬Nat.Prime 770 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 385) (n := 770)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_771 : ¬Nat.Prime 771 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 257) (n := 771)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_772 : ¬Nat.Prime 772 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 386) (n := 772)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_773 : Nat.count Nat.Prime 773 = 136 := by
  rw [show 773 = 772 + 1 by norm_num, Nat.count_succ]
  rw [show 772 = 771 + 1 by norm_num, Nat.count_succ]
  rw [show 771 = 770 + 1 by norm_num, Nat.count_succ]
  rw [show 770 = 769 + 1 by norm_num, Nat.count_succ]
  rw [count_769]
  simp [prime_769, not_prime_770, not_prime_771, not_prime_772]

theorem prime_773 : (773 : Nat).Prime := by norm_num

theorem nth_136 : Nat.nth Nat.Prime 136 = 773 := by
  rw [← count_773]
  exact Nat.nth_count prime_773

theorem not_prime_774 : ¬Nat.Prime 774 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 387) (n := 774)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_775 : ¬Nat.Prime 775 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 155) (n := 775)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_776 : ¬Nat.Prime 776 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 388) (n := 776)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_777 : ¬Nat.Prime 777 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 259) (n := 777)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_778 : ¬Nat.Prime 778 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 389) (n := 778)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_779 : ¬Nat.Prime 779 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 41) (n := 779)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_780 : ¬Nat.Prime 780 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 390) (n := 780)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_781 : ¬Nat.Prime 781 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 71) (n := 781)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_782 : ¬Nat.Prime 782 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 391) (n := 782)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_783 : ¬Nat.Prime 783 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 261) (n := 783)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_784 : ¬Nat.Prime 784 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 392) (n := 784)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_785 : ¬Nat.Prime 785 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 157) (n := 785)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_786 : ¬Nat.Prime 786 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 393) (n := 786)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_787 : Nat.count Nat.Prime 787 = 137 := by
  rw [show 787 = 786 + 1 by norm_num, Nat.count_succ]
  rw [show 786 = 785 + 1 by norm_num, Nat.count_succ]
  rw [show 785 = 784 + 1 by norm_num, Nat.count_succ]
  rw [show 784 = 783 + 1 by norm_num, Nat.count_succ]
  rw [show 783 = 782 + 1 by norm_num, Nat.count_succ]
  rw [show 782 = 781 + 1 by norm_num, Nat.count_succ]
  rw [show 781 = 780 + 1 by norm_num, Nat.count_succ]
  rw [show 780 = 779 + 1 by norm_num, Nat.count_succ]
  rw [show 779 = 778 + 1 by norm_num, Nat.count_succ]
  rw [show 778 = 777 + 1 by norm_num, Nat.count_succ]
  rw [show 777 = 776 + 1 by norm_num, Nat.count_succ]
  rw [show 776 = 775 + 1 by norm_num, Nat.count_succ]
  rw [show 775 = 774 + 1 by norm_num, Nat.count_succ]
  rw [show 774 = 773 + 1 by norm_num, Nat.count_succ]
  rw [count_773]
  simp [prime_773, not_prime_774, not_prime_775, not_prime_776, not_prime_777, not_prime_778, not_prime_779, not_prime_780, not_prime_781, not_prime_782, not_prime_783, not_prime_784, not_prime_785, not_prime_786]

theorem prime_787 : (787 : Nat).Prime := by norm_num

theorem nth_137 : Nat.nth Nat.Prime 137 = 787 := by
  rw [← count_787]
  exact Nat.nth_count prime_787

theorem not_prime_788 : ¬Nat.Prime 788 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 394) (n := 788)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_789 : ¬Nat.Prime 789 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 263) (n := 789)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_790 : ¬Nat.Prime 790 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 395) (n := 790)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_791 : ¬Nat.Prime 791 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 113) (n := 791)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_792 : ¬Nat.Prime 792 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 396) (n := 792)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_793 : ¬Nat.Prime 793 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 61) (n := 793)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_794 : ¬Nat.Prime 794 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 397) (n := 794)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_795 : ¬Nat.Prime 795 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 265) (n := 795)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_796 : ¬Nat.Prime 796 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 398) (n := 796)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_797 : Nat.count Nat.Prime 797 = 138 := by
  rw [show 797 = 796 + 1 by norm_num, Nat.count_succ]
  rw [show 796 = 795 + 1 by norm_num, Nat.count_succ]
  rw [show 795 = 794 + 1 by norm_num, Nat.count_succ]
  rw [show 794 = 793 + 1 by norm_num, Nat.count_succ]
  rw [show 793 = 792 + 1 by norm_num, Nat.count_succ]
  rw [show 792 = 791 + 1 by norm_num, Nat.count_succ]
  rw [show 791 = 790 + 1 by norm_num, Nat.count_succ]
  rw [show 790 = 789 + 1 by norm_num, Nat.count_succ]
  rw [show 789 = 788 + 1 by norm_num, Nat.count_succ]
  rw [show 788 = 787 + 1 by norm_num, Nat.count_succ]
  rw [count_787]
  simp [prime_787, not_prime_788, not_prime_789, not_prime_790, not_prime_791, not_prime_792, not_prime_793, not_prime_794, not_prime_795, not_prime_796]

theorem prime_797 : (797 : Nat).Prime := by norm_num

theorem nth_138 : Nat.nth Nat.Prime 138 = 797 := by
  rw [← count_797]
  exact Nat.nth_count prime_797

theorem not_prime_798 : ¬Nat.Prime 798 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 399) (n := 798)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_799 : ¬Nat.Prime 799 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 47) (n := 799)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_800 : ¬Nat.Prime 800 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 400) (n := 800)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_801 : ¬Nat.Prime 801 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 267) (n := 801)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_802 : ¬Nat.Prime 802 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 401) (n := 802)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_803 : ¬Nat.Prime 803 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 73) (n := 803)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_804 : ¬Nat.Prime 804 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 402) (n := 804)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_805 : ¬Nat.Prime 805 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 161) (n := 805)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_806 : ¬Nat.Prime 806 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 403) (n := 806)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_807 : ¬Nat.Prime 807 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 269) (n := 807)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_808 : ¬Nat.Prime 808 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 404) (n := 808)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_809 : Nat.count Nat.Prime 809 = 139 := by
  rw [show 809 = 808 + 1 by norm_num, Nat.count_succ]
  rw [show 808 = 807 + 1 by norm_num, Nat.count_succ]
  rw [show 807 = 806 + 1 by norm_num, Nat.count_succ]
  rw [show 806 = 805 + 1 by norm_num, Nat.count_succ]
  rw [show 805 = 804 + 1 by norm_num, Nat.count_succ]
  rw [show 804 = 803 + 1 by norm_num, Nat.count_succ]
  rw [show 803 = 802 + 1 by norm_num, Nat.count_succ]
  rw [show 802 = 801 + 1 by norm_num, Nat.count_succ]
  rw [show 801 = 800 + 1 by norm_num, Nat.count_succ]
  rw [show 800 = 799 + 1 by norm_num, Nat.count_succ]
  rw [show 799 = 798 + 1 by norm_num, Nat.count_succ]
  rw [show 798 = 797 + 1 by norm_num, Nat.count_succ]
  rw [count_797]
  simp [prime_797, not_prime_798, not_prime_799, not_prime_800, not_prime_801, not_prime_802, not_prime_803, not_prime_804, not_prime_805, not_prime_806, not_prime_807, not_prime_808]

theorem prime_809 : (809 : Nat).Prime := by norm_num

theorem nth_139 : Nat.nth Nat.Prime 139 = 809 := by
  rw [← count_809]
  exact Nat.nth_count prime_809

theorem not_prime_810 : ¬Nat.Prime 810 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 405) (n := 810)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_811 : Nat.count Nat.Prime 811 = 140 := by
  rw [show 811 = 810 + 1 by norm_num, Nat.count_succ]
  rw [show 810 = 809 + 1 by norm_num, Nat.count_succ]
  rw [count_809]
  simp [prime_809, not_prime_810]

theorem prime_811 : (811 : Nat).Prime := by norm_num

theorem nth_140 : Nat.nth Nat.Prime 140 = 811 := by
  rw [← count_811]
  exact Nat.nth_count prime_811

theorem not_prime_812 : ¬Nat.Prime 812 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 406) (n := 812)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_813 : ¬Nat.Prime 813 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 271) (n := 813)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_814 : ¬Nat.Prime 814 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 407) (n := 814)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_815 : ¬Nat.Prime 815 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 163) (n := 815)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_816 : ¬Nat.Prime 816 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 408) (n := 816)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_817 : ¬Nat.Prime 817 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 43) (n := 817)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_818 : ¬Nat.Prime 818 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 409) (n := 818)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_819 : ¬Nat.Prime 819 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 273) (n := 819)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_820 : ¬Nat.Prime 820 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 410) (n := 820)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_821 : Nat.count Nat.Prime 821 = 141 := by
  rw [show 821 = 820 + 1 by norm_num, Nat.count_succ]
  rw [show 820 = 819 + 1 by norm_num, Nat.count_succ]
  rw [show 819 = 818 + 1 by norm_num, Nat.count_succ]
  rw [show 818 = 817 + 1 by norm_num, Nat.count_succ]
  rw [show 817 = 816 + 1 by norm_num, Nat.count_succ]
  rw [show 816 = 815 + 1 by norm_num, Nat.count_succ]
  rw [show 815 = 814 + 1 by norm_num, Nat.count_succ]
  rw [show 814 = 813 + 1 by norm_num, Nat.count_succ]
  rw [show 813 = 812 + 1 by norm_num, Nat.count_succ]
  rw [show 812 = 811 + 1 by norm_num, Nat.count_succ]
  rw [count_811]
  simp [prime_811, not_prime_812, not_prime_813, not_prime_814, not_prime_815, not_prime_816, not_prime_817, not_prime_818, not_prime_819, not_prime_820]

theorem prime_821 : (821 : Nat).Prime := by norm_num

theorem nth_141 : Nat.nth Nat.Prime 141 = 821 := by
  rw [← count_821]
  exact Nat.nth_count prime_821

theorem not_prime_822 : ¬Nat.Prime 822 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 411) (n := 822)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_823 : Nat.count Nat.Prime 823 = 142 := by
  rw [show 823 = 822 + 1 by norm_num, Nat.count_succ]
  rw [show 822 = 821 + 1 by norm_num, Nat.count_succ]
  rw [count_821]
  simp [prime_821, not_prime_822]

theorem prime_823 : (823 : Nat).Prime := by norm_num

theorem nth_142 : Nat.nth Nat.Prime 142 = 823 := by
  rw [← count_823]
  exact Nat.nth_count prime_823

theorem not_prime_824 : ¬Nat.Prime 824 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 412) (n := 824)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_825 : ¬Nat.Prime 825 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 275) (n := 825)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_826 : ¬Nat.Prime 826 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 413) (n := 826)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_827 : Nat.count Nat.Prime 827 = 143 := by
  rw [show 827 = 826 + 1 by norm_num, Nat.count_succ]
  rw [show 826 = 825 + 1 by norm_num, Nat.count_succ]
  rw [show 825 = 824 + 1 by norm_num, Nat.count_succ]
  rw [show 824 = 823 + 1 by norm_num, Nat.count_succ]
  rw [count_823]
  simp [prime_823, not_prime_824, not_prime_825, not_prime_826]

theorem prime_827 : (827 : Nat).Prime := by norm_num

theorem nth_143 : Nat.nth Nat.Prime 143 = 827 := by
  rw [← count_827]
  exact Nat.nth_count prime_827

theorem not_prime_828 : ¬Nat.Prime 828 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 414) (n := 828)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_829 : Nat.count Nat.Prime 829 = 144 := by
  rw [show 829 = 828 + 1 by norm_num, Nat.count_succ]
  rw [show 828 = 827 + 1 by norm_num, Nat.count_succ]
  rw [count_827]
  simp [prime_827, not_prime_828]

theorem prime_829 : (829 : Nat).Prime := by norm_num

theorem nth_144 : Nat.nth Nat.Prime 144 = 829 := by
  rw [← count_829]
  exact Nat.nth_count prime_829

theorem not_prime_830 : ¬Nat.Prime 830 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 415) (n := 830)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_831 : ¬Nat.Prime 831 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 277) (n := 831)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_832 : ¬Nat.Prime 832 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 416) (n := 832)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_833 : ¬Nat.Prime 833 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 119) (n := 833)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_834 : ¬Nat.Prime 834 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 417) (n := 834)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_835 : ¬Nat.Prime 835 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 167) (n := 835)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_836 : ¬Nat.Prime 836 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 418) (n := 836)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_837 : ¬Nat.Prime 837 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 279) (n := 837)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_838 : ¬Nat.Prime 838 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 419) (n := 838)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_839 : Nat.count Nat.Prime 839 = 145 := by
  rw [show 839 = 838 + 1 by norm_num, Nat.count_succ]
  rw [show 838 = 837 + 1 by norm_num, Nat.count_succ]
  rw [show 837 = 836 + 1 by norm_num, Nat.count_succ]
  rw [show 836 = 835 + 1 by norm_num, Nat.count_succ]
  rw [show 835 = 834 + 1 by norm_num, Nat.count_succ]
  rw [show 834 = 833 + 1 by norm_num, Nat.count_succ]
  rw [show 833 = 832 + 1 by norm_num, Nat.count_succ]
  rw [show 832 = 831 + 1 by norm_num, Nat.count_succ]
  rw [show 831 = 830 + 1 by norm_num, Nat.count_succ]
  rw [show 830 = 829 + 1 by norm_num, Nat.count_succ]
  rw [count_829]
  simp [prime_829, not_prime_830, not_prime_831, not_prime_832, not_prime_833, not_prime_834, not_prime_835, not_prime_836, not_prime_837, not_prime_838]

theorem prime_839 : (839 : Nat).Prime := by norm_num

theorem nth_145 : Nat.nth Nat.Prime 145 = 839 := by
  rw [← count_839]
  exact Nat.nth_count prime_839

theorem not_prime_840 : ¬Nat.Prime 840 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 420) (n := 840)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_841 : ¬Nat.Prime 841 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 29) (n := 841)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_842 : ¬Nat.Prime 842 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 421) (n := 842)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_843 : ¬Nat.Prime 843 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 281) (n := 843)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_844 : ¬Nat.Prime 844 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 422) (n := 844)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_845 : ¬Nat.Prime 845 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 169) (n := 845)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_846 : ¬Nat.Prime 846 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 423) (n := 846)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_847 : ¬Nat.Prime 847 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 121) (n := 847)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_848 : ¬Nat.Prime 848 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 424) (n := 848)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_849 : ¬Nat.Prime 849 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 283) (n := 849)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_850 : ¬Nat.Prime 850 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 425) (n := 850)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_851 : ¬Nat.Prime 851 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 37) (n := 851)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_852 : ¬Nat.Prime 852 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 426) (n := 852)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_853 : Nat.count Nat.Prime 853 = 146 := by
  rw [show 853 = 852 + 1 by norm_num, Nat.count_succ]
  rw [show 852 = 851 + 1 by norm_num, Nat.count_succ]
  rw [show 851 = 850 + 1 by norm_num, Nat.count_succ]
  rw [show 850 = 849 + 1 by norm_num, Nat.count_succ]
  rw [show 849 = 848 + 1 by norm_num, Nat.count_succ]
  rw [show 848 = 847 + 1 by norm_num, Nat.count_succ]
  rw [show 847 = 846 + 1 by norm_num, Nat.count_succ]
  rw [show 846 = 845 + 1 by norm_num, Nat.count_succ]
  rw [show 845 = 844 + 1 by norm_num, Nat.count_succ]
  rw [show 844 = 843 + 1 by norm_num, Nat.count_succ]
  rw [show 843 = 842 + 1 by norm_num, Nat.count_succ]
  rw [show 842 = 841 + 1 by norm_num, Nat.count_succ]
  rw [show 841 = 840 + 1 by norm_num, Nat.count_succ]
  rw [show 840 = 839 + 1 by norm_num, Nat.count_succ]
  rw [count_839]
  simp [prime_839, not_prime_840, not_prime_841, not_prime_842, not_prime_843, not_prime_844, not_prime_845, not_prime_846, not_prime_847, not_prime_848, not_prime_849, not_prime_850, not_prime_851, not_prime_852]

theorem prime_853 : (853 : Nat).Prime := by norm_num

theorem nth_146 : Nat.nth Nat.Prime 146 = 853 := by
  rw [← count_853]
  exact Nat.nth_count prime_853

theorem not_prime_854 : ¬Nat.Prime 854 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 427) (n := 854)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_855 : ¬Nat.Prime 855 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 285) (n := 855)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_856 : ¬Nat.Prime 856 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 428) (n := 856)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_857 : Nat.count Nat.Prime 857 = 147 := by
  rw [show 857 = 856 + 1 by norm_num, Nat.count_succ]
  rw [show 856 = 855 + 1 by norm_num, Nat.count_succ]
  rw [show 855 = 854 + 1 by norm_num, Nat.count_succ]
  rw [show 854 = 853 + 1 by norm_num, Nat.count_succ]
  rw [count_853]
  simp [prime_853, not_prime_854, not_prime_855, not_prime_856]

theorem prime_857 : (857 : Nat).Prime := by norm_num

theorem nth_147 : Nat.nth Nat.Prime 147 = 857 := by
  rw [← count_857]
  exact Nat.nth_count prime_857

theorem not_prime_858 : ¬Nat.Prime 858 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 429) (n := 858)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_859 : Nat.count Nat.Prime 859 = 148 := by
  rw [show 859 = 858 + 1 by norm_num, Nat.count_succ]
  rw [show 858 = 857 + 1 by norm_num, Nat.count_succ]
  rw [count_857]
  simp [prime_857, not_prime_858]

theorem prime_859 : (859 : Nat).Prime := by norm_num

theorem nth_148 : Nat.nth Nat.Prime 148 = 859 := by
  rw [← count_859]
  exact Nat.nth_count prime_859

theorem not_prime_860 : ¬Nat.Prime 860 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 430) (n := 860)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_861 : ¬Nat.Prime 861 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 287) (n := 861)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_862 : ¬Nat.Prime 862 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 431) (n := 862)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_863 : Nat.count Nat.Prime 863 = 149 := by
  rw [show 863 = 862 + 1 by norm_num, Nat.count_succ]
  rw [show 862 = 861 + 1 by norm_num, Nat.count_succ]
  rw [show 861 = 860 + 1 by norm_num, Nat.count_succ]
  rw [show 860 = 859 + 1 by norm_num, Nat.count_succ]
  rw [count_859]
  simp [prime_859, not_prime_860, not_prime_861, not_prime_862]

theorem prime_863 : (863 : Nat).Prime := by norm_num

theorem nth_149 : Nat.nth Nat.Prime 149 = 863 := by
  rw [← count_863]
  exact Nat.nth_count prime_863

end OeisA100474.PrimeCertificate
