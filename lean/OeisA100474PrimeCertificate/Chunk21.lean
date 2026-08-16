import OeisA100474PrimeCertificate.Chunk20

/-! Kernel prime/count certificate, chunk 21 (525–549). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_3770 : ¬Nat.Prime 3770 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1885) (n := 3770)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3771 : ¬Nat.Prime 3771 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1257) (n := 3771)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3772 : ¬Nat.Prime 3772 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1886) (n := 3772)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3773 : ¬Nat.Prime 3773 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 539) (n := 3773)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3774 : ¬Nat.Prime 3774 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1887) (n := 3774)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3775 : ¬Nat.Prime 3775 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 755) (n := 3775)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3776 : ¬Nat.Prime 3776 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1888) (n := 3776)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3777 : ¬Nat.Prime 3777 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1259) (n := 3777)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3778 : ¬Nat.Prime 3778 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1889) (n := 3778)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3779 : Nat.count Nat.Prime 3779 = 525 := by
  rw [show 3779 = 3778 + 1 by norm_num, Nat.count_succ]
  rw [show 3778 = 3777 + 1 by norm_num, Nat.count_succ]
  rw [show 3777 = 3776 + 1 by norm_num, Nat.count_succ]
  rw [show 3776 = 3775 + 1 by norm_num, Nat.count_succ]
  rw [show 3775 = 3774 + 1 by norm_num, Nat.count_succ]
  rw [show 3774 = 3773 + 1 by norm_num, Nat.count_succ]
  rw [show 3773 = 3772 + 1 by norm_num, Nat.count_succ]
  rw [show 3772 = 3771 + 1 by norm_num, Nat.count_succ]
  rw [show 3771 = 3770 + 1 by norm_num, Nat.count_succ]
  rw [show 3770 = 3769 + 1 by norm_num, Nat.count_succ]
  rw [count_3769]
  simp [prime_3769, not_prime_3770, not_prime_3771, not_prime_3772, not_prime_3773, not_prime_3774, not_prime_3775, not_prime_3776, not_prime_3777, not_prime_3778]

theorem prime_3779 : (3779 : Nat).Prime := by norm_num

theorem nth_525 : Nat.nth Nat.Prime 525 = 3779 := by
  rw [← count_3779]
  exact Nat.nth_count prime_3779

theorem not_prime_3780 : ¬Nat.Prime 3780 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1890) (n := 3780)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3781 : ¬Nat.Prime 3781 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 199) (n := 3781)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3782 : ¬Nat.Prime 3782 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1891) (n := 3782)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3783 : ¬Nat.Prime 3783 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1261) (n := 3783)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3784 : ¬Nat.Prime 3784 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1892) (n := 3784)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3785 : ¬Nat.Prime 3785 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 757) (n := 3785)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3786 : ¬Nat.Prime 3786 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1893) (n := 3786)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3787 : ¬Nat.Prime 3787 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 541) (n := 3787)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3788 : ¬Nat.Prime 3788 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1894) (n := 3788)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3789 : ¬Nat.Prime 3789 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1263) (n := 3789)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3790 : ¬Nat.Prime 3790 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1895) (n := 3790)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3791 : ¬Nat.Prime 3791 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 223) (n := 3791)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3792 : ¬Nat.Prime 3792 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1896) (n := 3792)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3793 : Nat.count Nat.Prime 3793 = 526 := by
  rw [show 3793 = 3792 + 1 by norm_num, Nat.count_succ]
  rw [show 3792 = 3791 + 1 by norm_num, Nat.count_succ]
  rw [show 3791 = 3790 + 1 by norm_num, Nat.count_succ]
  rw [show 3790 = 3789 + 1 by norm_num, Nat.count_succ]
  rw [show 3789 = 3788 + 1 by norm_num, Nat.count_succ]
  rw [show 3788 = 3787 + 1 by norm_num, Nat.count_succ]
  rw [show 3787 = 3786 + 1 by norm_num, Nat.count_succ]
  rw [show 3786 = 3785 + 1 by norm_num, Nat.count_succ]
  rw [show 3785 = 3784 + 1 by norm_num, Nat.count_succ]
  rw [show 3784 = 3783 + 1 by norm_num, Nat.count_succ]
  rw [show 3783 = 3782 + 1 by norm_num, Nat.count_succ]
  rw [show 3782 = 3781 + 1 by norm_num, Nat.count_succ]
  rw [show 3781 = 3780 + 1 by norm_num, Nat.count_succ]
  rw [show 3780 = 3779 + 1 by norm_num, Nat.count_succ]
  rw [count_3779]
  simp [prime_3779, not_prime_3780, not_prime_3781, not_prime_3782, not_prime_3783, not_prime_3784, not_prime_3785, not_prime_3786, not_prime_3787, not_prime_3788, not_prime_3789, not_prime_3790, not_prime_3791, not_prime_3792]

theorem prime_3793 : (3793 : Nat).Prime := by norm_num

theorem nth_526 : Nat.nth Nat.Prime 526 = 3793 := by
  rw [← count_3793]
  exact Nat.nth_count prime_3793

theorem not_prime_3794 : ¬Nat.Prime 3794 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1897) (n := 3794)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3795 : ¬Nat.Prime 3795 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1265) (n := 3795)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3796 : ¬Nat.Prime 3796 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1898) (n := 3796)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3797 : Nat.count Nat.Prime 3797 = 527 := by
  rw [show 3797 = 3796 + 1 by norm_num, Nat.count_succ]
  rw [show 3796 = 3795 + 1 by norm_num, Nat.count_succ]
  rw [show 3795 = 3794 + 1 by norm_num, Nat.count_succ]
  rw [show 3794 = 3793 + 1 by norm_num, Nat.count_succ]
  rw [count_3793]
  simp [prime_3793, not_prime_3794, not_prime_3795, not_prime_3796]

theorem prime_3797 : (3797 : Nat).Prime := by norm_num

theorem nth_527 : Nat.nth Nat.Prime 527 = 3797 := by
  rw [← count_3797]
  exact Nat.nth_count prime_3797

theorem not_prime_3798 : ¬Nat.Prime 3798 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1899) (n := 3798)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3799 : ¬Nat.Prime 3799 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 131) (n := 3799)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3800 : ¬Nat.Prime 3800 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1900) (n := 3800)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3801 : ¬Nat.Prime 3801 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1267) (n := 3801)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3802 : ¬Nat.Prime 3802 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1901) (n := 3802)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3803 : Nat.count Nat.Prime 3803 = 528 := by
  rw [show 3803 = 3802 + 1 by norm_num, Nat.count_succ]
  rw [show 3802 = 3801 + 1 by norm_num, Nat.count_succ]
  rw [show 3801 = 3800 + 1 by norm_num, Nat.count_succ]
  rw [show 3800 = 3799 + 1 by norm_num, Nat.count_succ]
  rw [show 3799 = 3798 + 1 by norm_num, Nat.count_succ]
  rw [show 3798 = 3797 + 1 by norm_num, Nat.count_succ]
  rw [count_3797]
  simp [prime_3797, not_prime_3798, not_prime_3799, not_prime_3800, not_prime_3801, not_prime_3802]

theorem prime_3803 : (3803 : Nat).Prime := by norm_num

theorem nth_528 : Nat.nth Nat.Prime 528 = 3803 := by
  rw [← count_3803]
  exact Nat.nth_count prime_3803

theorem not_prime_3804 : ¬Nat.Prime 3804 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1902) (n := 3804)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3805 : ¬Nat.Prime 3805 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 761) (n := 3805)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3806 : ¬Nat.Prime 3806 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1903) (n := 3806)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3807 : ¬Nat.Prime 3807 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1269) (n := 3807)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3808 : ¬Nat.Prime 3808 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1904) (n := 3808)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3809 : ¬Nat.Prime 3809 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 293) (n := 3809)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3810 : ¬Nat.Prime 3810 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1905) (n := 3810)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3811 : ¬Nat.Prime 3811 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 103) (n := 3811)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3812 : ¬Nat.Prime 3812 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1906) (n := 3812)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3813 : ¬Nat.Prime 3813 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1271) (n := 3813)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3814 : ¬Nat.Prime 3814 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1907) (n := 3814)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3815 : ¬Nat.Prime 3815 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 763) (n := 3815)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3816 : ¬Nat.Prime 3816 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1908) (n := 3816)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3817 : ¬Nat.Prime 3817 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 347) (n := 3817)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3818 : ¬Nat.Prime 3818 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1909) (n := 3818)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3819 : ¬Nat.Prime 3819 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1273) (n := 3819)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3820 : ¬Nat.Prime 3820 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1910) (n := 3820)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3821 : Nat.count Nat.Prime 3821 = 529 := by
  rw [show 3821 = 3820 + 1 by norm_num, Nat.count_succ]
  rw [show 3820 = 3819 + 1 by norm_num, Nat.count_succ]
  rw [show 3819 = 3818 + 1 by norm_num, Nat.count_succ]
  rw [show 3818 = 3817 + 1 by norm_num, Nat.count_succ]
  rw [show 3817 = 3816 + 1 by norm_num, Nat.count_succ]
  rw [show 3816 = 3815 + 1 by norm_num, Nat.count_succ]
  rw [show 3815 = 3814 + 1 by norm_num, Nat.count_succ]
  rw [show 3814 = 3813 + 1 by norm_num, Nat.count_succ]
  rw [show 3813 = 3812 + 1 by norm_num, Nat.count_succ]
  rw [show 3812 = 3811 + 1 by norm_num, Nat.count_succ]
  rw [show 3811 = 3810 + 1 by norm_num, Nat.count_succ]
  rw [show 3810 = 3809 + 1 by norm_num, Nat.count_succ]
  rw [show 3809 = 3808 + 1 by norm_num, Nat.count_succ]
  rw [show 3808 = 3807 + 1 by norm_num, Nat.count_succ]
  rw [show 3807 = 3806 + 1 by norm_num, Nat.count_succ]
  rw [show 3806 = 3805 + 1 by norm_num, Nat.count_succ]
  rw [show 3805 = 3804 + 1 by norm_num, Nat.count_succ]
  rw [show 3804 = 3803 + 1 by norm_num, Nat.count_succ]
  rw [count_3803]
  simp [prime_3803, not_prime_3804, not_prime_3805, not_prime_3806, not_prime_3807, not_prime_3808, not_prime_3809, not_prime_3810, not_prime_3811, not_prime_3812, not_prime_3813, not_prime_3814, not_prime_3815, not_prime_3816, not_prime_3817, not_prime_3818, not_prime_3819, not_prime_3820]

theorem prime_3821 : (3821 : Nat).Prime := by norm_num

theorem nth_529 : Nat.nth Nat.Prime 529 = 3821 := by
  rw [← count_3821]
  exact Nat.nth_count prime_3821

theorem not_prime_3822 : ¬Nat.Prime 3822 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1911) (n := 3822)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3823 : Nat.count Nat.Prime 3823 = 530 := by
  rw [show 3823 = 3822 + 1 by norm_num, Nat.count_succ]
  rw [show 3822 = 3821 + 1 by norm_num, Nat.count_succ]
  rw [count_3821]
  simp [prime_3821, not_prime_3822]

theorem prime_3823 : (3823 : Nat).Prime := by norm_num

theorem nth_530 : Nat.nth Nat.Prime 530 = 3823 := by
  rw [← count_3823]
  exact Nat.nth_count prime_3823

theorem not_prime_3824 : ¬Nat.Prime 3824 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1912) (n := 3824)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3825 : ¬Nat.Prime 3825 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1275) (n := 3825)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3826 : ¬Nat.Prime 3826 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1913) (n := 3826)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3827 : ¬Nat.Prime 3827 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 89) (n := 3827)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3828 : ¬Nat.Prime 3828 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1914) (n := 3828)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3829 : ¬Nat.Prime 3829 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 547) (n := 3829)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3830 : ¬Nat.Prime 3830 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1915) (n := 3830)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3831 : ¬Nat.Prime 3831 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1277) (n := 3831)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3832 : ¬Nat.Prime 3832 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1916) (n := 3832)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3833 : Nat.count Nat.Prime 3833 = 531 := by
  rw [show 3833 = 3832 + 1 by norm_num, Nat.count_succ]
  rw [show 3832 = 3831 + 1 by norm_num, Nat.count_succ]
  rw [show 3831 = 3830 + 1 by norm_num, Nat.count_succ]
  rw [show 3830 = 3829 + 1 by norm_num, Nat.count_succ]
  rw [show 3829 = 3828 + 1 by norm_num, Nat.count_succ]
  rw [show 3828 = 3827 + 1 by norm_num, Nat.count_succ]
  rw [show 3827 = 3826 + 1 by norm_num, Nat.count_succ]
  rw [show 3826 = 3825 + 1 by norm_num, Nat.count_succ]
  rw [show 3825 = 3824 + 1 by norm_num, Nat.count_succ]
  rw [show 3824 = 3823 + 1 by norm_num, Nat.count_succ]
  rw [count_3823]
  simp [prime_3823, not_prime_3824, not_prime_3825, not_prime_3826, not_prime_3827, not_prime_3828, not_prime_3829, not_prime_3830, not_prime_3831, not_prime_3832]

theorem prime_3833 : (3833 : Nat).Prime := by norm_num

theorem nth_531 : Nat.nth Nat.Prime 531 = 3833 := by
  rw [← count_3833]
  exact Nat.nth_count prime_3833

theorem not_prime_3834 : ¬Nat.Prime 3834 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1917) (n := 3834)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3835 : ¬Nat.Prime 3835 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 767) (n := 3835)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3836 : ¬Nat.Prime 3836 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1918) (n := 3836)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3837 : ¬Nat.Prime 3837 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1279) (n := 3837)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3838 : ¬Nat.Prime 3838 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1919) (n := 3838)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3839 : ¬Nat.Prime 3839 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 349) (n := 3839)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3840 : ¬Nat.Prime 3840 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1920) (n := 3840)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3841 : ¬Nat.Prime 3841 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 167) (n := 3841)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3842 : ¬Nat.Prime 3842 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1921) (n := 3842)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3843 : ¬Nat.Prime 3843 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1281) (n := 3843)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3844 : ¬Nat.Prime 3844 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1922) (n := 3844)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3845 : ¬Nat.Prime 3845 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 769) (n := 3845)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3846 : ¬Nat.Prime 3846 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1923) (n := 3846)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3847 : Nat.count Nat.Prime 3847 = 532 := by
  rw [show 3847 = 3846 + 1 by norm_num, Nat.count_succ]
  rw [show 3846 = 3845 + 1 by norm_num, Nat.count_succ]
  rw [show 3845 = 3844 + 1 by norm_num, Nat.count_succ]
  rw [show 3844 = 3843 + 1 by norm_num, Nat.count_succ]
  rw [show 3843 = 3842 + 1 by norm_num, Nat.count_succ]
  rw [show 3842 = 3841 + 1 by norm_num, Nat.count_succ]
  rw [show 3841 = 3840 + 1 by norm_num, Nat.count_succ]
  rw [show 3840 = 3839 + 1 by norm_num, Nat.count_succ]
  rw [show 3839 = 3838 + 1 by norm_num, Nat.count_succ]
  rw [show 3838 = 3837 + 1 by norm_num, Nat.count_succ]
  rw [show 3837 = 3836 + 1 by norm_num, Nat.count_succ]
  rw [show 3836 = 3835 + 1 by norm_num, Nat.count_succ]
  rw [show 3835 = 3834 + 1 by norm_num, Nat.count_succ]
  rw [show 3834 = 3833 + 1 by norm_num, Nat.count_succ]
  rw [count_3833]
  simp [prime_3833, not_prime_3834, not_prime_3835, not_prime_3836, not_prime_3837, not_prime_3838, not_prime_3839, not_prime_3840, not_prime_3841, not_prime_3842, not_prime_3843, not_prime_3844, not_prime_3845, not_prime_3846]

theorem prime_3847 : (3847 : Nat).Prime := by norm_num

theorem nth_532 : Nat.nth Nat.Prime 532 = 3847 := by
  rw [← count_3847]
  exact Nat.nth_count prime_3847

theorem not_prime_3848 : ¬Nat.Prime 3848 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1924) (n := 3848)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3849 : ¬Nat.Prime 3849 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1283) (n := 3849)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3850 : ¬Nat.Prime 3850 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1925) (n := 3850)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3851 : Nat.count Nat.Prime 3851 = 533 := by
  rw [show 3851 = 3850 + 1 by norm_num, Nat.count_succ]
  rw [show 3850 = 3849 + 1 by norm_num, Nat.count_succ]
  rw [show 3849 = 3848 + 1 by norm_num, Nat.count_succ]
  rw [show 3848 = 3847 + 1 by norm_num, Nat.count_succ]
  rw [count_3847]
  simp [prime_3847, not_prime_3848, not_prime_3849, not_prime_3850]

theorem prime_3851 : (3851 : Nat).Prime := by norm_num

theorem nth_533 : Nat.nth Nat.Prime 533 = 3851 := by
  rw [← count_3851]
  exact Nat.nth_count prime_3851

theorem not_prime_3852 : ¬Nat.Prime 3852 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1926) (n := 3852)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3853 : Nat.count Nat.Prime 3853 = 534 := by
  rw [show 3853 = 3852 + 1 by norm_num, Nat.count_succ]
  rw [show 3852 = 3851 + 1 by norm_num, Nat.count_succ]
  rw [count_3851]
  simp [prime_3851, not_prime_3852]

theorem prime_3853 : (3853 : Nat).Prime := by norm_num

theorem nth_534 : Nat.nth Nat.Prime 534 = 3853 := by
  rw [← count_3853]
  exact Nat.nth_count prime_3853

theorem not_prime_3854 : ¬Nat.Prime 3854 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1927) (n := 3854)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3855 : ¬Nat.Prime 3855 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1285) (n := 3855)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3856 : ¬Nat.Prime 3856 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1928) (n := 3856)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3857 : ¬Nat.Prime 3857 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 551) (n := 3857)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3858 : ¬Nat.Prime 3858 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1929) (n := 3858)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3859 : ¬Nat.Prime 3859 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 227) (n := 3859)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3860 : ¬Nat.Prime 3860 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1930) (n := 3860)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3861 : ¬Nat.Prime 3861 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1287) (n := 3861)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3862 : ¬Nat.Prime 3862 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1931) (n := 3862)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3863 : Nat.count Nat.Prime 3863 = 535 := by
  rw [show 3863 = 3862 + 1 by norm_num, Nat.count_succ]
  rw [show 3862 = 3861 + 1 by norm_num, Nat.count_succ]
  rw [show 3861 = 3860 + 1 by norm_num, Nat.count_succ]
  rw [show 3860 = 3859 + 1 by norm_num, Nat.count_succ]
  rw [show 3859 = 3858 + 1 by norm_num, Nat.count_succ]
  rw [show 3858 = 3857 + 1 by norm_num, Nat.count_succ]
  rw [show 3857 = 3856 + 1 by norm_num, Nat.count_succ]
  rw [show 3856 = 3855 + 1 by norm_num, Nat.count_succ]
  rw [show 3855 = 3854 + 1 by norm_num, Nat.count_succ]
  rw [show 3854 = 3853 + 1 by norm_num, Nat.count_succ]
  rw [count_3853]
  simp [prime_3853, not_prime_3854, not_prime_3855, not_prime_3856, not_prime_3857, not_prime_3858, not_prime_3859, not_prime_3860, not_prime_3861, not_prime_3862]

theorem prime_3863 : (3863 : Nat).Prime := by norm_num

theorem nth_535 : Nat.nth Nat.Prime 535 = 3863 := by
  rw [← count_3863]
  exact Nat.nth_count prime_3863

theorem not_prime_3864 : ¬Nat.Prime 3864 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1932) (n := 3864)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3865 : ¬Nat.Prime 3865 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 773) (n := 3865)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3866 : ¬Nat.Prime 3866 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1933) (n := 3866)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3867 : ¬Nat.Prime 3867 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1289) (n := 3867)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3868 : ¬Nat.Prime 3868 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1934) (n := 3868)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3869 : ¬Nat.Prime 3869 :=
  Nat.not_prime_of_mul_eq (a := 53) (b := 73) (n := 3869)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3870 : ¬Nat.Prime 3870 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1935) (n := 3870)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3871 : ¬Nat.Prime 3871 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 553) (n := 3871)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3872 : ¬Nat.Prime 3872 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1936) (n := 3872)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3873 : ¬Nat.Prime 3873 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1291) (n := 3873)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3874 : ¬Nat.Prime 3874 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1937) (n := 3874)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3875 : ¬Nat.Prime 3875 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 775) (n := 3875)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3876 : ¬Nat.Prime 3876 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1938) (n := 3876)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3877 : Nat.count Nat.Prime 3877 = 536 := by
  rw [show 3877 = 3876 + 1 by norm_num, Nat.count_succ]
  rw [show 3876 = 3875 + 1 by norm_num, Nat.count_succ]
  rw [show 3875 = 3874 + 1 by norm_num, Nat.count_succ]
  rw [show 3874 = 3873 + 1 by norm_num, Nat.count_succ]
  rw [show 3873 = 3872 + 1 by norm_num, Nat.count_succ]
  rw [show 3872 = 3871 + 1 by norm_num, Nat.count_succ]
  rw [show 3871 = 3870 + 1 by norm_num, Nat.count_succ]
  rw [show 3870 = 3869 + 1 by norm_num, Nat.count_succ]
  rw [show 3869 = 3868 + 1 by norm_num, Nat.count_succ]
  rw [show 3868 = 3867 + 1 by norm_num, Nat.count_succ]
  rw [show 3867 = 3866 + 1 by norm_num, Nat.count_succ]
  rw [show 3866 = 3865 + 1 by norm_num, Nat.count_succ]
  rw [show 3865 = 3864 + 1 by norm_num, Nat.count_succ]
  rw [show 3864 = 3863 + 1 by norm_num, Nat.count_succ]
  rw [count_3863]
  simp [prime_3863, not_prime_3864, not_prime_3865, not_prime_3866, not_prime_3867, not_prime_3868, not_prime_3869, not_prime_3870, not_prime_3871, not_prime_3872, not_prime_3873, not_prime_3874, not_prime_3875, not_prime_3876]

theorem prime_3877 : (3877 : Nat).Prime := by norm_num

theorem nth_536 : Nat.nth Nat.Prime 536 = 3877 := by
  rw [← count_3877]
  exact Nat.nth_count prime_3877

theorem not_prime_3878 : ¬Nat.Prime 3878 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1939) (n := 3878)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3879 : ¬Nat.Prime 3879 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1293) (n := 3879)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3880 : ¬Nat.Prime 3880 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1940) (n := 3880)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3881 : Nat.count Nat.Prime 3881 = 537 := by
  rw [show 3881 = 3880 + 1 by norm_num, Nat.count_succ]
  rw [show 3880 = 3879 + 1 by norm_num, Nat.count_succ]
  rw [show 3879 = 3878 + 1 by norm_num, Nat.count_succ]
  rw [show 3878 = 3877 + 1 by norm_num, Nat.count_succ]
  rw [count_3877]
  simp [prime_3877, not_prime_3878, not_prime_3879, not_prime_3880]

theorem prime_3881 : (3881 : Nat).Prime := by norm_num

theorem nth_537 : Nat.nth Nat.Prime 537 = 3881 := by
  rw [← count_3881]
  exact Nat.nth_count prime_3881

theorem not_prime_3882 : ¬Nat.Prime 3882 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1941) (n := 3882)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3883 : ¬Nat.Prime 3883 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 353) (n := 3883)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3884 : ¬Nat.Prime 3884 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1942) (n := 3884)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3885 : ¬Nat.Prime 3885 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1295) (n := 3885)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3886 : ¬Nat.Prime 3886 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1943) (n := 3886)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3887 : ¬Nat.Prime 3887 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 299) (n := 3887)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3888 : ¬Nat.Prime 3888 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1944) (n := 3888)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3889 : Nat.count Nat.Prime 3889 = 538 := by
  rw [show 3889 = 3888 + 1 by norm_num, Nat.count_succ]
  rw [show 3888 = 3887 + 1 by norm_num, Nat.count_succ]
  rw [show 3887 = 3886 + 1 by norm_num, Nat.count_succ]
  rw [show 3886 = 3885 + 1 by norm_num, Nat.count_succ]
  rw [show 3885 = 3884 + 1 by norm_num, Nat.count_succ]
  rw [show 3884 = 3883 + 1 by norm_num, Nat.count_succ]
  rw [show 3883 = 3882 + 1 by norm_num, Nat.count_succ]
  rw [show 3882 = 3881 + 1 by norm_num, Nat.count_succ]
  rw [count_3881]
  simp [prime_3881, not_prime_3882, not_prime_3883, not_prime_3884, not_prime_3885, not_prime_3886, not_prime_3887, not_prime_3888]

theorem prime_3889 : (3889 : Nat).Prime := by norm_num

theorem nth_538 : Nat.nth Nat.Prime 538 = 3889 := by
  rw [← count_3889]
  exact Nat.nth_count prime_3889

theorem not_prime_3890 : ¬Nat.Prime 3890 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1945) (n := 3890)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3891 : ¬Nat.Prime 3891 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1297) (n := 3891)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3892 : ¬Nat.Prime 3892 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1946) (n := 3892)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3893 : ¬Nat.Prime 3893 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 229) (n := 3893)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3894 : ¬Nat.Prime 3894 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1947) (n := 3894)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3895 : ¬Nat.Prime 3895 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 779) (n := 3895)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3896 : ¬Nat.Prime 3896 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1948) (n := 3896)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3897 : ¬Nat.Prime 3897 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1299) (n := 3897)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3898 : ¬Nat.Prime 3898 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1949) (n := 3898)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3899 : ¬Nat.Prime 3899 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 557) (n := 3899)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3900 : ¬Nat.Prime 3900 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1950) (n := 3900)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3901 : ¬Nat.Prime 3901 :=
  Nat.not_prime_of_mul_eq (a := 47) (b := 83) (n := 3901)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3902 : ¬Nat.Prime 3902 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1951) (n := 3902)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3903 : ¬Nat.Prime 3903 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1301) (n := 3903)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3904 : ¬Nat.Prime 3904 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1952) (n := 3904)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3905 : ¬Nat.Prime 3905 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 781) (n := 3905)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3906 : ¬Nat.Prime 3906 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1953) (n := 3906)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3907 : Nat.count Nat.Prime 3907 = 539 := by
  rw [show 3907 = 3906 + 1 by norm_num, Nat.count_succ]
  rw [show 3906 = 3905 + 1 by norm_num, Nat.count_succ]
  rw [show 3905 = 3904 + 1 by norm_num, Nat.count_succ]
  rw [show 3904 = 3903 + 1 by norm_num, Nat.count_succ]
  rw [show 3903 = 3902 + 1 by norm_num, Nat.count_succ]
  rw [show 3902 = 3901 + 1 by norm_num, Nat.count_succ]
  rw [show 3901 = 3900 + 1 by norm_num, Nat.count_succ]
  rw [show 3900 = 3899 + 1 by norm_num, Nat.count_succ]
  rw [show 3899 = 3898 + 1 by norm_num, Nat.count_succ]
  rw [show 3898 = 3897 + 1 by norm_num, Nat.count_succ]
  rw [show 3897 = 3896 + 1 by norm_num, Nat.count_succ]
  rw [show 3896 = 3895 + 1 by norm_num, Nat.count_succ]
  rw [show 3895 = 3894 + 1 by norm_num, Nat.count_succ]
  rw [show 3894 = 3893 + 1 by norm_num, Nat.count_succ]
  rw [show 3893 = 3892 + 1 by norm_num, Nat.count_succ]
  rw [show 3892 = 3891 + 1 by norm_num, Nat.count_succ]
  rw [show 3891 = 3890 + 1 by norm_num, Nat.count_succ]
  rw [show 3890 = 3889 + 1 by norm_num, Nat.count_succ]
  rw [count_3889]
  simp [prime_3889, not_prime_3890, not_prime_3891, not_prime_3892, not_prime_3893, not_prime_3894, not_prime_3895, not_prime_3896, not_prime_3897, not_prime_3898, not_prime_3899, not_prime_3900, not_prime_3901, not_prime_3902, not_prime_3903, not_prime_3904, not_prime_3905, not_prime_3906]

theorem prime_3907 : (3907 : Nat).Prime := by norm_num

theorem nth_539 : Nat.nth Nat.Prime 539 = 3907 := by
  rw [← count_3907]
  exact Nat.nth_count prime_3907

theorem not_prime_3908 : ¬Nat.Prime 3908 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1954) (n := 3908)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3909 : ¬Nat.Prime 3909 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1303) (n := 3909)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3910 : ¬Nat.Prime 3910 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1955) (n := 3910)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3911 : Nat.count Nat.Prime 3911 = 540 := by
  rw [show 3911 = 3910 + 1 by norm_num, Nat.count_succ]
  rw [show 3910 = 3909 + 1 by norm_num, Nat.count_succ]
  rw [show 3909 = 3908 + 1 by norm_num, Nat.count_succ]
  rw [show 3908 = 3907 + 1 by norm_num, Nat.count_succ]
  rw [count_3907]
  simp [prime_3907, not_prime_3908, not_prime_3909, not_prime_3910]

theorem prime_3911 : (3911 : Nat).Prime := by norm_num

theorem nth_540 : Nat.nth Nat.Prime 540 = 3911 := by
  rw [← count_3911]
  exact Nat.nth_count prime_3911

theorem not_prime_3912 : ¬Nat.Prime 3912 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1956) (n := 3912)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3913 : ¬Nat.Prime 3913 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 559) (n := 3913)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3914 : ¬Nat.Prime 3914 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1957) (n := 3914)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3915 : ¬Nat.Prime 3915 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1305) (n := 3915)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3916 : ¬Nat.Prime 3916 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1958) (n := 3916)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3917 : Nat.count Nat.Prime 3917 = 541 := by
  rw [show 3917 = 3916 + 1 by norm_num, Nat.count_succ]
  rw [show 3916 = 3915 + 1 by norm_num, Nat.count_succ]
  rw [show 3915 = 3914 + 1 by norm_num, Nat.count_succ]
  rw [show 3914 = 3913 + 1 by norm_num, Nat.count_succ]
  rw [show 3913 = 3912 + 1 by norm_num, Nat.count_succ]
  rw [show 3912 = 3911 + 1 by norm_num, Nat.count_succ]
  rw [count_3911]
  simp [prime_3911, not_prime_3912, not_prime_3913, not_prime_3914, not_prime_3915, not_prime_3916]

theorem prime_3917 : (3917 : Nat).Prime := by norm_num

theorem nth_541 : Nat.nth Nat.Prime 541 = 3917 := by
  rw [← count_3917]
  exact Nat.nth_count prime_3917

theorem not_prime_3918 : ¬Nat.Prime 3918 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1959) (n := 3918)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3919 : Nat.count Nat.Prime 3919 = 542 := by
  rw [show 3919 = 3918 + 1 by norm_num, Nat.count_succ]
  rw [show 3918 = 3917 + 1 by norm_num, Nat.count_succ]
  rw [count_3917]
  simp [prime_3917, not_prime_3918]

theorem prime_3919 : (3919 : Nat).Prime := by norm_num

theorem nth_542 : Nat.nth Nat.Prime 542 = 3919 := by
  rw [← count_3919]
  exact Nat.nth_count prime_3919

theorem not_prime_3920 : ¬Nat.Prime 3920 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1960) (n := 3920)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3921 : ¬Nat.Prime 3921 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1307) (n := 3921)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3922 : ¬Nat.Prime 3922 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1961) (n := 3922)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3923 : Nat.count Nat.Prime 3923 = 543 := by
  rw [show 3923 = 3922 + 1 by norm_num, Nat.count_succ]
  rw [show 3922 = 3921 + 1 by norm_num, Nat.count_succ]
  rw [show 3921 = 3920 + 1 by norm_num, Nat.count_succ]
  rw [show 3920 = 3919 + 1 by norm_num, Nat.count_succ]
  rw [count_3919]
  simp [prime_3919, not_prime_3920, not_prime_3921, not_prime_3922]

theorem prime_3923 : (3923 : Nat).Prime := by norm_num

theorem nth_543 : Nat.nth Nat.Prime 543 = 3923 := by
  rw [← count_3923]
  exact Nat.nth_count prime_3923

theorem not_prime_3924 : ¬Nat.Prime 3924 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1962) (n := 3924)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3925 : ¬Nat.Prime 3925 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 785) (n := 3925)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3926 : ¬Nat.Prime 3926 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1963) (n := 3926)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3927 : ¬Nat.Prime 3927 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1309) (n := 3927)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3928 : ¬Nat.Prime 3928 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1964) (n := 3928)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3929 : Nat.count Nat.Prime 3929 = 544 := by
  rw [show 3929 = 3928 + 1 by norm_num, Nat.count_succ]
  rw [show 3928 = 3927 + 1 by norm_num, Nat.count_succ]
  rw [show 3927 = 3926 + 1 by norm_num, Nat.count_succ]
  rw [show 3926 = 3925 + 1 by norm_num, Nat.count_succ]
  rw [show 3925 = 3924 + 1 by norm_num, Nat.count_succ]
  rw [show 3924 = 3923 + 1 by norm_num, Nat.count_succ]
  rw [count_3923]
  simp [prime_3923, not_prime_3924, not_prime_3925, not_prime_3926, not_prime_3927, not_prime_3928]

theorem prime_3929 : (3929 : Nat).Prime := by norm_num

theorem nth_544 : Nat.nth Nat.Prime 544 = 3929 := by
  rw [← count_3929]
  exact Nat.nth_count prime_3929

theorem not_prime_3930 : ¬Nat.Prime 3930 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1965) (n := 3930)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3931 : Nat.count Nat.Prime 3931 = 545 := by
  rw [show 3931 = 3930 + 1 by norm_num, Nat.count_succ]
  rw [show 3930 = 3929 + 1 by norm_num, Nat.count_succ]
  rw [count_3929]
  simp [prime_3929, not_prime_3930]

theorem prime_3931 : (3931 : Nat).Prime := by norm_num

theorem nth_545 : Nat.nth Nat.Prime 545 = 3931 := by
  rw [← count_3931]
  exact Nat.nth_count prime_3931

theorem not_prime_3932 : ¬Nat.Prime 3932 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1966) (n := 3932)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3933 : ¬Nat.Prime 3933 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1311) (n := 3933)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3934 : ¬Nat.Prime 3934 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1967) (n := 3934)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3935 : ¬Nat.Prime 3935 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 787) (n := 3935)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3936 : ¬Nat.Prime 3936 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1968) (n := 3936)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3937 : ¬Nat.Prime 3937 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 127) (n := 3937)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3938 : ¬Nat.Prime 3938 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1969) (n := 3938)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3939 : ¬Nat.Prime 3939 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1313) (n := 3939)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3940 : ¬Nat.Prime 3940 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1970) (n := 3940)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3941 : ¬Nat.Prime 3941 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 563) (n := 3941)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3942 : ¬Nat.Prime 3942 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1971) (n := 3942)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3943 : Nat.count Nat.Prime 3943 = 546 := by
  rw [show 3943 = 3942 + 1 by norm_num, Nat.count_succ]
  rw [show 3942 = 3941 + 1 by norm_num, Nat.count_succ]
  rw [show 3941 = 3940 + 1 by norm_num, Nat.count_succ]
  rw [show 3940 = 3939 + 1 by norm_num, Nat.count_succ]
  rw [show 3939 = 3938 + 1 by norm_num, Nat.count_succ]
  rw [show 3938 = 3937 + 1 by norm_num, Nat.count_succ]
  rw [show 3937 = 3936 + 1 by norm_num, Nat.count_succ]
  rw [show 3936 = 3935 + 1 by norm_num, Nat.count_succ]
  rw [show 3935 = 3934 + 1 by norm_num, Nat.count_succ]
  rw [show 3934 = 3933 + 1 by norm_num, Nat.count_succ]
  rw [show 3933 = 3932 + 1 by norm_num, Nat.count_succ]
  rw [show 3932 = 3931 + 1 by norm_num, Nat.count_succ]
  rw [count_3931]
  simp [prime_3931, not_prime_3932, not_prime_3933, not_prime_3934, not_prime_3935, not_prime_3936, not_prime_3937, not_prime_3938, not_prime_3939, not_prime_3940, not_prime_3941, not_prime_3942]

theorem prime_3943 : (3943 : Nat).Prime := by norm_num

theorem nth_546 : Nat.nth Nat.Prime 546 = 3943 := by
  rw [← count_3943]
  exact Nat.nth_count prime_3943

theorem not_prime_3944 : ¬Nat.Prime 3944 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1972) (n := 3944)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3945 : ¬Nat.Prime 3945 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1315) (n := 3945)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3946 : ¬Nat.Prime 3946 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1973) (n := 3946)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3947 : Nat.count Nat.Prime 3947 = 547 := by
  rw [show 3947 = 3946 + 1 by norm_num, Nat.count_succ]
  rw [show 3946 = 3945 + 1 by norm_num, Nat.count_succ]
  rw [show 3945 = 3944 + 1 by norm_num, Nat.count_succ]
  rw [show 3944 = 3943 + 1 by norm_num, Nat.count_succ]
  rw [count_3943]
  simp [prime_3943, not_prime_3944, not_prime_3945, not_prime_3946]

theorem prime_3947 : (3947 : Nat).Prime := by norm_num

theorem nth_547 : Nat.nth Nat.Prime 547 = 3947 := by
  rw [← count_3947]
  exact Nat.nth_count prime_3947

theorem not_prime_3948 : ¬Nat.Prime 3948 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1974) (n := 3948)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3949 : ¬Nat.Prime 3949 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 359) (n := 3949)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3950 : ¬Nat.Prime 3950 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1975) (n := 3950)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3951 : ¬Nat.Prime 3951 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1317) (n := 3951)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3952 : ¬Nat.Prime 3952 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1976) (n := 3952)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3953 : ¬Nat.Prime 3953 :=
  Nat.not_prime_of_mul_eq (a := 59) (b := 67) (n := 3953)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3954 : ¬Nat.Prime 3954 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1977) (n := 3954)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3955 : ¬Nat.Prime 3955 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 791) (n := 3955)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3956 : ¬Nat.Prime 3956 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1978) (n := 3956)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3957 : ¬Nat.Prime 3957 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1319) (n := 3957)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3958 : ¬Nat.Prime 3958 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1979) (n := 3958)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3959 : ¬Nat.Prime 3959 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 107) (n := 3959)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3960 : ¬Nat.Prime 3960 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1980) (n := 3960)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3961 : ¬Nat.Prime 3961 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 233) (n := 3961)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3962 : ¬Nat.Prime 3962 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1981) (n := 3962)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3963 : ¬Nat.Prime 3963 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1321) (n := 3963)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3964 : ¬Nat.Prime 3964 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1982) (n := 3964)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3965 : ¬Nat.Prime 3965 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 793) (n := 3965)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3966 : ¬Nat.Prime 3966 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1983) (n := 3966)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3967 : Nat.count Nat.Prime 3967 = 548 := by
  rw [show 3967 = 3966 + 1 by norm_num, Nat.count_succ]
  rw [show 3966 = 3965 + 1 by norm_num, Nat.count_succ]
  rw [show 3965 = 3964 + 1 by norm_num, Nat.count_succ]
  rw [show 3964 = 3963 + 1 by norm_num, Nat.count_succ]
  rw [show 3963 = 3962 + 1 by norm_num, Nat.count_succ]
  rw [show 3962 = 3961 + 1 by norm_num, Nat.count_succ]
  rw [show 3961 = 3960 + 1 by norm_num, Nat.count_succ]
  rw [show 3960 = 3959 + 1 by norm_num, Nat.count_succ]
  rw [show 3959 = 3958 + 1 by norm_num, Nat.count_succ]
  rw [show 3958 = 3957 + 1 by norm_num, Nat.count_succ]
  rw [show 3957 = 3956 + 1 by norm_num, Nat.count_succ]
  rw [show 3956 = 3955 + 1 by norm_num, Nat.count_succ]
  rw [show 3955 = 3954 + 1 by norm_num, Nat.count_succ]
  rw [show 3954 = 3953 + 1 by norm_num, Nat.count_succ]
  rw [show 3953 = 3952 + 1 by norm_num, Nat.count_succ]
  rw [show 3952 = 3951 + 1 by norm_num, Nat.count_succ]
  rw [show 3951 = 3950 + 1 by norm_num, Nat.count_succ]
  rw [show 3950 = 3949 + 1 by norm_num, Nat.count_succ]
  rw [show 3949 = 3948 + 1 by norm_num, Nat.count_succ]
  rw [show 3948 = 3947 + 1 by norm_num, Nat.count_succ]
  rw [count_3947]
  simp [prime_3947, not_prime_3948, not_prime_3949, not_prime_3950, not_prime_3951, not_prime_3952, not_prime_3953, not_prime_3954, not_prime_3955, not_prime_3956, not_prime_3957, not_prime_3958, not_prime_3959, not_prime_3960, not_prime_3961, not_prime_3962, not_prime_3963, not_prime_3964, not_prime_3965, not_prime_3966]

theorem prime_3967 : (3967 : Nat).Prime := by norm_num

theorem nth_548 : Nat.nth Nat.Prime 548 = 3967 := by
  rw [← count_3967]
  exact Nat.nth_count prime_3967

theorem not_prime_3968 : ¬Nat.Prime 3968 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1984) (n := 3968)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3969 : ¬Nat.Prime 3969 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1323) (n := 3969)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3970 : ¬Nat.Prime 3970 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1985) (n := 3970)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3971 : ¬Nat.Prime 3971 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 361) (n := 3971)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3972 : ¬Nat.Prime 3972 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1986) (n := 3972)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3973 : ¬Nat.Prime 3973 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 137) (n := 3973)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3974 : ¬Nat.Prime 3974 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1987) (n := 3974)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3975 : ¬Nat.Prime 3975 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1325) (n := 3975)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3976 : ¬Nat.Prime 3976 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1988) (n := 3976)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3977 : ¬Nat.Prime 3977 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 97) (n := 3977)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3978 : ¬Nat.Prime 3978 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1989) (n := 3978)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3979 : ¬Nat.Prime 3979 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 173) (n := 3979)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3980 : ¬Nat.Prime 3980 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1990) (n := 3980)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3981 : ¬Nat.Prime 3981 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1327) (n := 3981)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3982 : ¬Nat.Prime 3982 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1991) (n := 3982)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3983 : ¬Nat.Prime 3983 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 569) (n := 3983)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3984 : ¬Nat.Prime 3984 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1992) (n := 3984)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3985 : ¬Nat.Prime 3985 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 797) (n := 3985)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3986 : ¬Nat.Prime 3986 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1993) (n := 3986)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3987 : ¬Nat.Prime 3987 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1329) (n := 3987)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3988 : ¬Nat.Prime 3988 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1994) (n := 3988)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3989 : Nat.count Nat.Prime 3989 = 549 := by
  rw [show 3989 = 3988 + 1 by norm_num, Nat.count_succ]
  rw [show 3988 = 3987 + 1 by norm_num, Nat.count_succ]
  rw [show 3987 = 3986 + 1 by norm_num, Nat.count_succ]
  rw [show 3986 = 3985 + 1 by norm_num, Nat.count_succ]
  rw [show 3985 = 3984 + 1 by norm_num, Nat.count_succ]
  rw [show 3984 = 3983 + 1 by norm_num, Nat.count_succ]
  rw [show 3983 = 3982 + 1 by norm_num, Nat.count_succ]
  rw [show 3982 = 3981 + 1 by norm_num, Nat.count_succ]
  rw [show 3981 = 3980 + 1 by norm_num, Nat.count_succ]
  rw [show 3980 = 3979 + 1 by norm_num, Nat.count_succ]
  rw [show 3979 = 3978 + 1 by norm_num, Nat.count_succ]
  rw [show 3978 = 3977 + 1 by norm_num, Nat.count_succ]
  rw [show 3977 = 3976 + 1 by norm_num, Nat.count_succ]
  rw [show 3976 = 3975 + 1 by norm_num, Nat.count_succ]
  rw [show 3975 = 3974 + 1 by norm_num, Nat.count_succ]
  rw [show 3974 = 3973 + 1 by norm_num, Nat.count_succ]
  rw [show 3973 = 3972 + 1 by norm_num, Nat.count_succ]
  rw [show 3972 = 3971 + 1 by norm_num, Nat.count_succ]
  rw [show 3971 = 3970 + 1 by norm_num, Nat.count_succ]
  rw [show 3970 = 3969 + 1 by norm_num, Nat.count_succ]
  rw [show 3969 = 3968 + 1 by norm_num, Nat.count_succ]
  rw [show 3968 = 3967 + 1 by norm_num, Nat.count_succ]
  rw [count_3967]
  simp [prime_3967, not_prime_3968, not_prime_3969, not_prime_3970, not_prime_3971, not_prime_3972, not_prime_3973, not_prime_3974, not_prime_3975, not_prime_3976, not_prime_3977, not_prime_3978, not_prime_3979, not_prime_3980, not_prime_3981, not_prime_3982, not_prime_3983, not_prime_3984, not_prime_3985, not_prime_3986, not_prime_3987, not_prime_3988]

theorem prime_3989 : (3989 : Nat).Prime := by norm_num

theorem nth_549 : Nat.nth Nat.Prime 549 = 3989 := by
  rw [← count_3989]
  exact Nat.nth_count prime_3989

end OeisA100474.PrimeCertificate
