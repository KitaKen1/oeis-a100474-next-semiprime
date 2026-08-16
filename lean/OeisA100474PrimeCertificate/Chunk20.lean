import OeisA100474PrimeCertificate.Chunk19

/-! Kernel prime/count certificate, chunk 20 (500–524). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_3572 : ¬Nat.Prime 3572 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1786) (n := 3572)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3573 : ¬Nat.Prime 3573 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1191) (n := 3573)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3574 : ¬Nat.Prime 3574 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1787) (n := 3574)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3575 : ¬Nat.Prime 3575 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 715) (n := 3575)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3576 : ¬Nat.Prime 3576 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1788) (n := 3576)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3577 : ¬Nat.Prime 3577 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 511) (n := 3577)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3578 : ¬Nat.Prime 3578 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1789) (n := 3578)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3579 : ¬Nat.Prime 3579 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1193) (n := 3579)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3580 : ¬Nat.Prime 3580 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1790) (n := 3580)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3581 : Nat.count Nat.Prime 3581 = 500 := by
  rw [show 3581 = 3580 + 1 by norm_num, Nat.count_succ]
  rw [show 3580 = 3579 + 1 by norm_num, Nat.count_succ]
  rw [show 3579 = 3578 + 1 by norm_num, Nat.count_succ]
  rw [show 3578 = 3577 + 1 by norm_num, Nat.count_succ]
  rw [show 3577 = 3576 + 1 by norm_num, Nat.count_succ]
  rw [show 3576 = 3575 + 1 by norm_num, Nat.count_succ]
  rw [show 3575 = 3574 + 1 by norm_num, Nat.count_succ]
  rw [show 3574 = 3573 + 1 by norm_num, Nat.count_succ]
  rw [show 3573 = 3572 + 1 by norm_num, Nat.count_succ]
  rw [show 3572 = 3571 + 1 by norm_num, Nat.count_succ]
  rw [count_3571]
  simp [prime_3571, not_prime_3572, not_prime_3573, not_prime_3574, not_prime_3575, not_prime_3576, not_prime_3577, not_prime_3578, not_prime_3579, not_prime_3580]

theorem prime_3581 : (3581 : Nat).Prime := by norm_num

theorem nth_500 : Nat.nth Nat.Prime 500 = 3581 := by
  rw [← count_3581]
  exact Nat.nth_count prime_3581

theorem not_prime_3582 : ¬Nat.Prime 3582 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1791) (n := 3582)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3583 : Nat.count Nat.Prime 3583 = 501 := by
  rw [show 3583 = 3582 + 1 by norm_num, Nat.count_succ]
  rw [show 3582 = 3581 + 1 by norm_num, Nat.count_succ]
  rw [count_3581]
  simp [prime_3581, not_prime_3582]

theorem prime_3583 : (3583 : Nat).Prime := by norm_num

theorem nth_501 : Nat.nth Nat.Prime 501 = 3583 := by
  rw [← count_3583]
  exact Nat.nth_count prime_3583

theorem not_prime_3584 : ¬Nat.Prime 3584 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1792) (n := 3584)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3585 : ¬Nat.Prime 3585 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1195) (n := 3585)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3586 : ¬Nat.Prime 3586 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1793) (n := 3586)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3587 : ¬Nat.Prime 3587 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 211) (n := 3587)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3588 : ¬Nat.Prime 3588 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1794) (n := 3588)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3589 : ¬Nat.Prime 3589 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 97) (n := 3589)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3590 : ¬Nat.Prime 3590 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1795) (n := 3590)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3591 : ¬Nat.Prime 3591 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1197) (n := 3591)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3592 : ¬Nat.Prime 3592 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1796) (n := 3592)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3593 : Nat.count Nat.Prime 3593 = 502 := by
  rw [show 3593 = 3592 + 1 by norm_num, Nat.count_succ]
  rw [show 3592 = 3591 + 1 by norm_num, Nat.count_succ]
  rw [show 3591 = 3590 + 1 by norm_num, Nat.count_succ]
  rw [show 3590 = 3589 + 1 by norm_num, Nat.count_succ]
  rw [show 3589 = 3588 + 1 by norm_num, Nat.count_succ]
  rw [show 3588 = 3587 + 1 by norm_num, Nat.count_succ]
  rw [show 3587 = 3586 + 1 by norm_num, Nat.count_succ]
  rw [show 3586 = 3585 + 1 by norm_num, Nat.count_succ]
  rw [show 3585 = 3584 + 1 by norm_num, Nat.count_succ]
  rw [show 3584 = 3583 + 1 by norm_num, Nat.count_succ]
  rw [count_3583]
  simp [prime_3583, not_prime_3584, not_prime_3585, not_prime_3586, not_prime_3587, not_prime_3588, not_prime_3589, not_prime_3590, not_prime_3591, not_prime_3592]

theorem prime_3593 : (3593 : Nat).Prime := by norm_num

theorem nth_502 : Nat.nth Nat.Prime 502 = 3593 := by
  rw [← count_3593]
  exact Nat.nth_count prime_3593

theorem not_prime_3594 : ¬Nat.Prime 3594 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1797) (n := 3594)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3595 : ¬Nat.Prime 3595 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 719) (n := 3595)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3596 : ¬Nat.Prime 3596 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1798) (n := 3596)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3597 : ¬Nat.Prime 3597 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1199) (n := 3597)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3598 : ¬Nat.Prime 3598 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1799) (n := 3598)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3599 : ¬Nat.Prime 3599 :=
  Nat.not_prime_of_mul_eq (a := 59) (b := 61) (n := 3599)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3600 : ¬Nat.Prime 3600 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1800) (n := 3600)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3601 : ¬Nat.Prime 3601 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 277) (n := 3601)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3602 : ¬Nat.Prime 3602 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1801) (n := 3602)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3603 : ¬Nat.Prime 3603 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1201) (n := 3603)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3604 : ¬Nat.Prime 3604 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1802) (n := 3604)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3605 : ¬Nat.Prime 3605 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 721) (n := 3605)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3606 : ¬Nat.Prime 3606 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1803) (n := 3606)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3607 : Nat.count Nat.Prime 3607 = 503 := by
  rw [show 3607 = 3606 + 1 by norm_num, Nat.count_succ]
  rw [show 3606 = 3605 + 1 by norm_num, Nat.count_succ]
  rw [show 3605 = 3604 + 1 by norm_num, Nat.count_succ]
  rw [show 3604 = 3603 + 1 by norm_num, Nat.count_succ]
  rw [show 3603 = 3602 + 1 by norm_num, Nat.count_succ]
  rw [show 3602 = 3601 + 1 by norm_num, Nat.count_succ]
  rw [show 3601 = 3600 + 1 by norm_num, Nat.count_succ]
  rw [show 3600 = 3599 + 1 by norm_num, Nat.count_succ]
  rw [show 3599 = 3598 + 1 by norm_num, Nat.count_succ]
  rw [show 3598 = 3597 + 1 by norm_num, Nat.count_succ]
  rw [show 3597 = 3596 + 1 by norm_num, Nat.count_succ]
  rw [show 3596 = 3595 + 1 by norm_num, Nat.count_succ]
  rw [show 3595 = 3594 + 1 by norm_num, Nat.count_succ]
  rw [show 3594 = 3593 + 1 by norm_num, Nat.count_succ]
  rw [count_3593]
  simp [prime_3593, not_prime_3594, not_prime_3595, not_prime_3596, not_prime_3597, not_prime_3598, not_prime_3599, not_prime_3600, not_prime_3601, not_prime_3602, not_prime_3603, not_prime_3604, not_prime_3605, not_prime_3606]

theorem prime_3607 : (3607 : Nat).Prime := by norm_num

theorem nth_503 : Nat.nth Nat.Prime 503 = 3607 := by
  rw [← count_3607]
  exact Nat.nth_count prime_3607

theorem not_prime_3608 : ¬Nat.Prime 3608 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1804) (n := 3608)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3609 : ¬Nat.Prime 3609 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1203) (n := 3609)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3610 : ¬Nat.Prime 3610 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1805) (n := 3610)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3611 : ¬Nat.Prime 3611 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 157) (n := 3611)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3612 : ¬Nat.Prime 3612 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1806) (n := 3612)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3613 : Nat.count Nat.Prime 3613 = 504 := by
  rw [show 3613 = 3612 + 1 by norm_num, Nat.count_succ]
  rw [show 3612 = 3611 + 1 by norm_num, Nat.count_succ]
  rw [show 3611 = 3610 + 1 by norm_num, Nat.count_succ]
  rw [show 3610 = 3609 + 1 by norm_num, Nat.count_succ]
  rw [show 3609 = 3608 + 1 by norm_num, Nat.count_succ]
  rw [show 3608 = 3607 + 1 by norm_num, Nat.count_succ]
  rw [count_3607]
  simp [prime_3607, not_prime_3608, not_prime_3609, not_prime_3610, not_prime_3611, not_prime_3612]

theorem prime_3613 : (3613 : Nat).Prime := by norm_num

theorem nth_504 : Nat.nth Nat.Prime 504 = 3613 := by
  rw [← count_3613]
  exact Nat.nth_count prime_3613

theorem not_prime_3614 : ¬Nat.Prime 3614 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1807) (n := 3614)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3615 : ¬Nat.Prime 3615 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1205) (n := 3615)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3616 : ¬Nat.Prime 3616 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1808) (n := 3616)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3617 : Nat.count Nat.Prime 3617 = 505 := by
  rw [show 3617 = 3616 + 1 by norm_num, Nat.count_succ]
  rw [show 3616 = 3615 + 1 by norm_num, Nat.count_succ]
  rw [show 3615 = 3614 + 1 by norm_num, Nat.count_succ]
  rw [show 3614 = 3613 + 1 by norm_num, Nat.count_succ]
  rw [count_3613]
  simp [prime_3613, not_prime_3614, not_prime_3615, not_prime_3616]

theorem prime_3617 : (3617 : Nat).Prime := by norm_num

theorem nth_505 : Nat.nth Nat.Prime 505 = 3617 := by
  rw [← count_3617]
  exact Nat.nth_count prime_3617

theorem not_prime_3618 : ¬Nat.Prime 3618 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1809) (n := 3618)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3619 : ¬Nat.Prime 3619 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 517) (n := 3619)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3620 : ¬Nat.Prime 3620 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1810) (n := 3620)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3621 : ¬Nat.Prime 3621 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1207) (n := 3621)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3622 : ¬Nat.Prime 3622 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1811) (n := 3622)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3623 : Nat.count Nat.Prime 3623 = 506 := by
  rw [show 3623 = 3622 + 1 by norm_num, Nat.count_succ]
  rw [show 3622 = 3621 + 1 by norm_num, Nat.count_succ]
  rw [show 3621 = 3620 + 1 by norm_num, Nat.count_succ]
  rw [show 3620 = 3619 + 1 by norm_num, Nat.count_succ]
  rw [show 3619 = 3618 + 1 by norm_num, Nat.count_succ]
  rw [show 3618 = 3617 + 1 by norm_num, Nat.count_succ]
  rw [count_3617]
  simp [prime_3617, not_prime_3618, not_prime_3619, not_prime_3620, not_prime_3621, not_prime_3622]

theorem prime_3623 : (3623 : Nat).Prime := by norm_num

theorem nth_506 : Nat.nth Nat.Prime 506 = 3623 := by
  rw [← count_3623]
  exact Nat.nth_count prime_3623

theorem not_prime_3624 : ¬Nat.Prime 3624 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1812) (n := 3624)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3625 : ¬Nat.Prime 3625 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 725) (n := 3625)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3626 : ¬Nat.Prime 3626 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1813) (n := 3626)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3627 : ¬Nat.Prime 3627 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1209) (n := 3627)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3628 : ¬Nat.Prime 3628 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1814) (n := 3628)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3629 : ¬Nat.Prime 3629 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 191) (n := 3629)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3630 : ¬Nat.Prime 3630 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1815) (n := 3630)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3631 : Nat.count Nat.Prime 3631 = 507 := by
  rw [show 3631 = 3630 + 1 by norm_num, Nat.count_succ]
  rw [show 3630 = 3629 + 1 by norm_num, Nat.count_succ]
  rw [show 3629 = 3628 + 1 by norm_num, Nat.count_succ]
  rw [show 3628 = 3627 + 1 by norm_num, Nat.count_succ]
  rw [show 3627 = 3626 + 1 by norm_num, Nat.count_succ]
  rw [show 3626 = 3625 + 1 by norm_num, Nat.count_succ]
  rw [show 3625 = 3624 + 1 by norm_num, Nat.count_succ]
  rw [show 3624 = 3623 + 1 by norm_num, Nat.count_succ]
  rw [count_3623]
  simp [prime_3623, not_prime_3624, not_prime_3625, not_prime_3626, not_prime_3627, not_prime_3628, not_prime_3629, not_prime_3630]

theorem prime_3631 : (3631 : Nat).Prime := by norm_num

theorem nth_507 : Nat.nth Nat.Prime 507 = 3631 := by
  rw [← count_3631]
  exact Nat.nth_count prime_3631

theorem not_prime_3632 : ¬Nat.Prime 3632 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1816) (n := 3632)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3633 : ¬Nat.Prime 3633 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1211) (n := 3633)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3634 : ¬Nat.Prime 3634 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1817) (n := 3634)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3635 : ¬Nat.Prime 3635 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 727) (n := 3635)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3636 : ¬Nat.Prime 3636 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1818) (n := 3636)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3637 : Nat.count Nat.Prime 3637 = 508 := by
  rw [show 3637 = 3636 + 1 by norm_num, Nat.count_succ]
  rw [show 3636 = 3635 + 1 by norm_num, Nat.count_succ]
  rw [show 3635 = 3634 + 1 by norm_num, Nat.count_succ]
  rw [show 3634 = 3633 + 1 by norm_num, Nat.count_succ]
  rw [show 3633 = 3632 + 1 by norm_num, Nat.count_succ]
  rw [show 3632 = 3631 + 1 by norm_num, Nat.count_succ]
  rw [count_3631]
  simp [prime_3631, not_prime_3632, not_prime_3633, not_prime_3634, not_prime_3635, not_prime_3636]

theorem prime_3637 : (3637 : Nat).Prime := by norm_num

theorem nth_508 : Nat.nth Nat.Prime 508 = 3637 := by
  rw [← count_3637]
  exact Nat.nth_count prime_3637

theorem not_prime_3638 : ¬Nat.Prime 3638 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1819) (n := 3638)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3639 : ¬Nat.Prime 3639 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1213) (n := 3639)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3640 : ¬Nat.Prime 3640 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1820) (n := 3640)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3641 : ¬Nat.Prime 3641 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 331) (n := 3641)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3642 : ¬Nat.Prime 3642 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1821) (n := 3642)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3643 : Nat.count Nat.Prime 3643 = 509 := by
  rw [show 3643 = 3642 + 1 by norm_num, Nat.count_succ]
  rw [show 3642 = 3641 + 1 by norm_num, Nat.count_succ]
  rw [show 3641 = 3640 + 1 by norm_num, Nat.count_succ]
  rw [show 3640 = 3639 + 1 by norm_num, Nat.count_succ]
  rw [show 3639 = 3638 + 1 by norm_num, Nat.count_succ]
  rw [show 3638 = 3637 + 1 by norm_num, Nat.count_succ]
  rw [count_3637]
  simp [prime_3637, not_prime_3638, not_prime_3639, not_prime_3640, not_prime_3641, not_prime_3642]

theorem prime_3643 : (3643 : Nat).Prime := by norm_num

theorem nth_509 : Nat.nth Nat.Prime 509 = 3643 := by
  rw [← count_3643]
  exact Nat.nth_count prime_3643

theorem not_prime_3644 : ¬Nat.Prime 3644 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1822) (n := 3644)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3645 : ¬Nat.Prime 3645 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1215) (n := 3645)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3646 : ¬Nat.Prime 3646 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1823) (n := 3646)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3647 : ¬Nat.Prime 3647 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 521) (n := 3647)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3648 : ¬Nat.Prime 3648 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1824) (n := 3648)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3649 : ¬Nat.Prime 3649 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 89) (n := 3649)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3650 : ¬Nat.Prime 3650 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1825) (n := 3650)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3651 : ¬Nat.Prime 3651 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1217) (n := 3651)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3652 : ¬Nat.Prime 3652 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1826) (n := 3652)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3653 : ¬Nat.Prime 3653 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 281) (n := 3653)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3654 : ¬Nat.Prime 3654 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1827) (n := 3654)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3655 : ¬Nat.Prime 3655 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 731) (n := 3655)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3656 : ¬Nat.Prime 3656 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1828) (n := 3656)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3657 : ¬Nat.Prime 3657 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1219) (n := 3657)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3658 : ¬Nat.Prime 3658 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1829) (n := 3658)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3659 : Nat.count Nat.Prime 3659 = 510 := by
  rw [show 3659 = 3658 + 1 by norm_num, Nat.count_succ]
  rw [show 3658 = 3657 + 1 by norm_num, Nat.count_succ]
  rw [show 3657 = 3656 + 1 by norm_num, Nat.count_succ]
  rw [show 3656 = 3655 + 1 by norm_num, Nat.count_succ]
  rw [show 3655 = 3654 + 1 by norm_num, Nat.count_succ]
  rw [show 3654 = 3653 + 1 by norm_num, Nat.count_succ]
  rw [show 3653 = 3652 + 1 by norm_num, Nat.count_succ]
  rw [show 3652 = 3651 + 1 by norm_num, Nat.count_succ]
  rw [show 3651 = 3650 + 1 by norm_num, Nat.count_succ]
  rw [show 3650 = 3649 + 1 by norm_num, Nat.count_succ]
  rw [show 3649 = 3648 + 1 by norm_num, Nat.count_succ]
  rw [show 3648 = 3647 + 1 by norm_num, Nat.count_succ]
  rw [show 3647 = 3646 + 1 by norm_num, Nat.count_succ]
  rw [show 3646 = 3645 + 1 by norm_num, Nat.count_succ]
  rw [show 3645 = 3644 + 1 by norm_num, Nat.count_succ]
  rw [show 3644 = 3643 + 1 by norm_num, Nat.count_succ]
  rw [count_3643]
  simp [prime_3643, not_prime_3644, not_prime_3645, not_prime_3646, not_prime_3647, not_prime_3648, not_prime_3649, not_prime_3650, not_prime_3651, not_prime_3652, not_prime_3653, not_prime_3654, not_prime_3655, not_prime_3656, not_prime_3657, not_prime_3658]

theorem prime_3659 : (3659 : Nat).Prime := by norm_num

theorem nth_510 : Nat.nth Nat.Prime 510 = 3659 := by
  rw [← count_3659]
  exact Nat.nth_count prime_3659

theorem not_prime_3660 : ¬Nat.Prime 3660 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1830) (n := 3660)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3661 : ¬Nat.Prime 3661 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 523) (n := 3661)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3662 : ¬Nat.Prime 3662 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1831) (n := 3662)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3663 : ¬Nat.Prime 3663 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1221) (n := 3663)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3664 : ¬Nat.Prime 3664 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1832) (n := 3664)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3665 : ¬Nat.Prime 3665 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 733) (n := 3665)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3666 : ¬Nat.Prime 3666 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1833) (n := 3666)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3667 : ¬Nat.Prime 3667 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 193) (n := 3667)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3668 : ¬Nat.Prime 3668 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1834) (n := 3668)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3669 : ¬Nat.Prime 3669 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1223) (n := 3669)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3670 : ¬Nat.Prime 3670 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1835) (n := 3670)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3671 : Nat.count Nat.Prime 3671 = 511 := by
  rw [show 3671 = 3670 + 1 by norm_num, Nat.count_succ]
  rw [show 3670 = 3669 + 1 by norm_num, Nat.count_succ]
  rw [show 3669 = 3668 + 1 by norm_num, Nat.count_succ]
  rw [show 3668 = 3667 + 1 by norm_num, Nat.count_succ]
  rw [show 3667 = 3666 + 1 by norm_num, Nat.count_succ]
  rw [show 3666 = 3665 + 1 by norm_num, Nat.count_succ]
  rw [show 3665 = 3664 + 1 by norm_num, Nat.count_succ]
  rw [show 3664 = 3663 + 1 by norm_num, Nat.count_succ]
  rw [show 3663 = 3662 + 1 by norm_num, Nat.count_succ]
  rw [show 3662 = 3661 + 1 by norm_num, Nat.count_succ]
  rw [show 3661 = 3660 + 1 by norm_num, Nat.count_succ]
  rw [show 3660 = 3659 + 1 by norm_num, Nat.count_succ]
  rw [count_3659]
  simp [prime_3659, not_prime_3660, not_prime_3661, not_prime_3662, not_prime_3663, not_prime_3664, not_prime_3665, not_prime_3666, not_prime_3667, not_prime_3668, not_prime_3669, not_prime_3670]

theorem prime_3671 : (3671 : Nat).Prime := by norm_num

theorem nth_511 : Nat.nth Nat.Prime 511 = 3671 := by
  rw [← count_3671]
  exact Nat.nth_count prime_3671

theorem not_prime_3672 : ¬Nat.Prime 3672 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1836) (n := 3672)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3673 : Nat.count Nat.Prime 3673 = 512 := by
  rw [show 3673 = 3672 + 1 by norm_num, Nat.count_succ]
  rw [show 3672 = 3671 + 1 by norm_num, Nat.count_succ]
  rw [count_3671]
  simp [prime_3671, not_prime_3672]

theorem prime_3673 : (3673 : Nat).Prime := by norm_num

theorem nth_512 : Nat.nth Nat.Prime 512 = 3673 := by
  rw [← count_3673]
  exact Nat.nth_count prime_3673

theorem not_prime_3674 : ¬Nat.Prime 3674 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1837) (n := 3674)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3675 : ¬Nat.Prime 3675 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1225) (n := 3675)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3676 : ¬Nat.Prime 3676 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1838) (n := 3676)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3677 : Nat.count Nat.Prime 3677 = 513 := by
  rw [show 3677 = 3676 + 1 by norm_num, Nat.count_succ]
  rw [show 3676 = 3675 + 1 by norm_num, Nat.count_succ]
  rw [show 3675 = 3674 + 1 by norm_num, Nat.count_succ]
  rw [show 3674 = 3673 + 1 by norm_num, Nat.count_succ]
  rw [count_3673]
  simp [prime_3673, not_prime_3674, not_prime_3675, not_prime_3676]

theorem prime_3677 : (3677 : Nat).Prime := by norm_num

theorem nth_513 : Nat.nth Nat.Prime 513 = 3677 := by
  rw [← count_3677]
  exact Nat.nth_count prime_3677

theorem not_prime_3678 : ¬Nat.Prime 3678 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1839) (n := 3678)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3679 : ¬Nat.Prime 3679 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 283) (n := 3679)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3680 : ¬Nat.Prime 3680 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1840) (n := 3680)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3681 : ¬Nat.Prime 3681 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1227) (n := 3681)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3682 : ¬Nat.Prime 3682 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1841) (n := 3682)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3683 : ¬Nat.Prime 3683 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 127) (n := 3683)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3684 : ¬Nat.Prime 3684 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1842) (n := 3684)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3685 : ¬Nat.Prime 3685 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 737) (n := 3685)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3686 : ¬Nat.Prime 3686 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1843) (n := 3686)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3687 : ¬Nat.Prime 3687 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1229) (n := 3687)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3688 : ¬Nat.Prime 3688 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1844) (n := 3688)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3689 : ¬Nat.Prime 3689 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 527) (n := 3689)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3690 : ¬Nat.Prime 3690 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1845) (n := 3690)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3691 : Nat.count Nat.Prime 3691 = 514 := by
  rw [show 3691 = 3690 + 1 by norm_num, Nat.count_succ]
  rw [show 3690 = 3689 + 1 by norm_num, Nat.count_succ]
  rw [show 3689 = 3688 + 1 by norm_num, Nat.count_succ]
  rw [show 3688 = 3687 + 1 by norm_num, Nat.count_succ]
  rw [show 3687 = 3686 + 1 by norm_num, Nat.count_succ]
  rw [show 3686 = 3685 + 1 by norm_num, Nat.count_succ]
  rw [show 3685 = 3684 + 1 by norm_num, Nat.count_succ]
  rw [show 3684 = 3683 + 1 by norm_num, Nat.count_succ]
  rw [show 3683 = 3682 + 1 by norm_num, Nat.count_succ]
  rw [show 3682 = 3681 + 1 by norm_num, Nat.count_succ]
  rw [show 3681 = 3680 + 1 by norm_num, Nat.count_succ]
  rw [show 3680 = 3679 + 1 by norm_num, Nat.count_succ]
  rw [show 3679 = 3678 + 1 by norm_num, Nat.count_succ]
  rw [show 3678 = 3677 + 1 by norm_num, Nat.count_succ]
  rw [count_3677]
  simp [prime_3677, not_prime_3678, not_prime_3679, not_prime_3680, not_prime_3681, not_prime_3682, not_prime_3683, not_prime_3684, not_prime_3685, not_prime_3686, not_prime_3687, not_prime_3688, not_prime_3689, not_prime_3690]

theorem prime_3691 : (3691 : Nat).Prime := by norm_num

theorem nth_514 : Nat.nth Nat.Prime 514 = 3691 := by
  rw [← count_3691]
  exact Nat.nth_count prime_3691

theorem not_prime_3692 : ¬Nat.Prime 3692 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1846) (n := 3692)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3693 : ¬Nat.Prime 3693 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1231) (n := 3693)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3694 : ¬Nat.Prime 3694 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1847) (n := 3694)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3695 : ¬Nat.Prime 3695 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 739) (n := 3695)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3696 : ¬Nat.Prime 3696 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1848) (n := 3696)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3697 : Nat.count Nat.Prime 3697 = 515 := by
  rw [show 3697 = 3696 + 1 by norm_num, Nat.count_succ]
  rw [show 3696 = 3695 + 1 by norm_num, Nat.count_succ]
  rw [show 3695 = 3694 + 1 by norm_num, Nat.count_succ]
  rw [show 3694 = 3693 + 1 by norm_num, Nat.count_succ]
  rw [show 3693 = 3692 + 1 by norm_num, Nat.count_succ]
  rw [show 3692 = 3691 + 1 by norm_num, Nat.count_succ]
  rw [count_3691]
  simp [prime_3691, not_prime_3692, not_prime_3693, not_prime_3694, not_prime_3695, not_prime_3696]

theorem prime_3697 : (3697 : Nat).Prime := by norm_num

theorem nth_515 : Nat.nth Nat.Prime 515 = 3697 := by
  rw [← count_3697]
  exact Nat.nth_count prime_3697

theorem not_prime_3698 : ¬Nat.Prime 3698 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1849) (n := 3698)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3699 : ¬Nat.Prime 3699 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1233) (n := 3699)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3700 : ¬Nat.Prime 3700 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1850) (n := 3700)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3701 : Nat.count Nat.Prime 3701 = 516 := by
  rw [show 3701 = 3700 + 1 by norm_num, Nat.count_succ]
  rw [show 3700 = 3699 + 1 by norm_num, Nat.count_succ]
  rw [show 3699 = 3698 + 1 by norm_num, Nat.count_succ]
  rw [show 3698 = 3697 + 1 by norm_num, Nat.count_succ]
  rw [count_3697]
  simp [prime_3697, not_prime_3698, not_prime_3699, not_prime_3700]

theorem prime_3701 : (3701 : Nat).Prime := by norm_num

theorem nth_516 : Nat.nth Nat.Prime 516 = 3701 := by
  rw [← count_3701]
  exact Nat.nth_count prime_3701

theorem not_prime_3702 : ¬Nat.Prime 3702 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1851) (n := 3702)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3703 : ¬Nat.Prime 3703 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 529) (n := 3703)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3704 : ¬Nat.Prime 3704 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1852) (n := 3704)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3705 : ¬Nat.Prime 3705 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1235) (n := 3705)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3706 : ¬Nat.Prime 3706 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1853) (n := 3706)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3707 : ¬Nat.Prime 3707 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 337) (n := 3707)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3708 : ¬Nat.Prime 3708 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1854) (n := 3708)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3709 : Nat.count Nat.Prime 3709 = 517 := by
  rw [show 3709 = 3708 + 1 by norm_num, Nat.count_succ]
  rw [show 3708 = 3707 + 1 by norm_num, Nat.count_succ]
  rw [show 3707 = 3706 + 1 by norm_num, Nat.count_succ]
  rw [show 3706 = 3705 + 1 by norm_num, Nat.count_succ]
  rw [show 3705 = 3704 + 1 by norm_num, Nat.count_succ]
  rw [show 3704 = 3703 + 1 by norm_num, Nat.count_succ]
  rw [show 3703 = 3702 + 1 by norm_num, Nat.count_succ]
  rw [show 3702 = 3701 + 1 by norm_num, Nat.count_succ]
  rw [count_3701]
  simp [prime_3701, not_prime_3702, not_prime_3703, not_prime_3704, not_prime_3705, not_prime_3706, not_prime_3707, not_prime_3708]

theorem prime_3709 : (3709 : Nat).Prime := by norm_num

theorem nth_517 : Nat.nth Nat.Prime 517 = 3709 := by
  rw [← count_3709]
  exact Nat.nth_count prime_3709

theorem not_prime_3710 : ¬Nat.Prime 3710 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1855) (n := 3710)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3711 : ¬Nat.Prime 3711 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1237) (n := 3711)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3712 : ¬Nat.Prime 3712 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1856) (n := 3712)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3713 : ¬Nat.Prime 3713 :=
  Nat.not_prime_of_mul_eq (a := 47) (b := 79) (n := 3713)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3714 : ¬Nat.Prime 3714 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1857) (n := 3714)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3715 : ¬Nat.Prime 3715 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 743) (n := 3715)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3716 : ¬Nat.Prime 3716 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1858) (n := 3716)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3717 : ¬Nat.Prime 3717 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1239) (n := 3717)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3718 : ¬Nat.Prime 3718 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1859) (n := 3718)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3719 : Nat.count Nat.Prime 3719 = 518 := by
  rw [show 3719 = 3718 + 1 by norm_num, Nat.count_succ]
  rw [show 3718 = 3717 + 1 by norm_num, Nat.count_succ]
  rw [show 3717 = 3716 + 1 by norm_num, Nat.count_succ]
  rw [show 3716 = 3715 + 1 by norm_num, Nat.count_succ]
  rw [show 3715 = 3714 + 1 by norm_num, Nat.count_succ]
  rw [show 3714 = 3713 + 1 by norm_num, Nat.count_succ]
  rw [show 3713 = 3712 + 1 by norm_num, Nat.count_succ]
  rw [show 3712 = 3711 + 1 by norm_num, Nat.count_succ]
  rw [show 3711 = 3710 + 1 by norm_num, Nat.count_succ]
  rw [show 3710 = 3709 + 1 by norm_num, Nat.count_succ]
  rw [count_3709]
  simp [prime_3709, not_prime_3710, not_prime_3711, not_prime_3712, not_prime_3713, not_prime_3714, not_prime_3715, not_prime_3716, not_prime_3717, not_prime_3718]

theorem prime_3719 : (3719 : Nat).Prime := by norm_num

theorem nth_518 : Nat.nth Nat.Prime 518 = 3719 := by
  rw [← count_3719]
  exact Nat.nth_count prime_3719

theorem not_prime_3720 : ¬Nat.Prime 3720 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1860) (n := 3720)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3721 : ¬Nat.Prime 3721 :=
  Nat.not_prime_of_mul_eq (a := 61) (b := 61) (n := 3721)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3722 : ¬Nat.Prime 3722 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1861) (n := 3722)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3723 : ¬Nat.Prime 3723 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1241) (n := 3723)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3724 : ¬Nat.Prime 3724 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1862) (n := 3724)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3725 : ¬Nat.Prime 3725 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 745) (n := 3725)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3726 : ¬Nat.Prime 3726 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1863) (n := 3726)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3727 : Nat.count Nat.Prime 3727 = 519 := by
  rw [show 3727 = 3726 + 1 by norm_num, Nat.count_succ]
  rw [show 3726 = 3725 + 1 by norm_num, Nat.count_succ]
  rw [show 3725 = 3724 + 1 by norm_num, Nat.count_succ]
  rw [show 3724 = 3723 + 1 by norm_num, Nat.count_succ]
  rw [show 3723 = 3722 + 1 by norm_num, Nat.count_succ]
  rw [show 3722 = 3721 + 1 by norm_num, Nat.count_succ]
  rw [show 3721 = 3720 + 1 by norm_num, Nat.count_succ]
  rw [show 3720 = 3719 + 1 by norm_num, Nat.count_succ]
  rw [count_3719]
  simp [prime_3719, not_prime_3720, not_prime_3721, not_prime_3722, not_prime_3723, not_prime_3724, not_prime_3725, not_prime_3726]

theorem prime_3727 : (3727 : Nat).Prime := by norm_num

theorem nth_519 : Nat.nth Nat.Prime 519 = 3727 := by
  rw [← count_3727]
  exact Nat.nth_count prime_3727

theorem not_prime_3728 : ¬Nat.Prime 3728 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1864) (n := 3728)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3729 : ¬Nat.Prime 3729 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1243) (n := 3729)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3730 : ¬Nat.Prime 3730 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1865) (n := 3730)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3731 : ¬Nat.Prime 3731 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 533) (n := 3731)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3732 : ¬Nat.Prime 3732 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1866) (n := 3732)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3733 : Nat.count Nat.Prime 3733 = 520 := by
  rw [show 3733 = 3732 + 1 by norm_num, Nat.count_succ]
  rw [show 3732 = 3731 + 1 by norm_num, Nat.count_succ]
  rw [show 3731 = 3730 + 1 by norm_num, Nat.count_succ]
  rw [show 3730 = 3729 + 1 by norm_num, Nat.count_succ]
  rw [show 3729 = 3728 + 1 by norm_num, Nat.count_succ]
  rw [show 3728 = 3727 + 1 by norm_num, Nat.count_succ]
  rw [count_3727]
  simp [prime_3727, not_prime_3728, not_prime_3729, not_prime_3730, not_prime_3731, not_prime_3732]

theorem prime_3733 : (3733 : Nat).Prime := by norm_num

theorem nth_520 : Nat.nth Nat.Prime 520 = 3733 := by
  rw [← count_3733]
  exact Nat.nth_count prime_3733

theorem not_prime_3734 : ¬Nat.Prime 3734 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1867) (n := 3734)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3735 : ¬Nat.Prime 3735 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1245) (n := 3735)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3736 : ¬Nat.Prime 3736 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1868) (n := 3736)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3737 : ¬Nat.Prime 3737 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 101) (n := 3737)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3738 : ¬Nat.Prime 3738 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1869) (n := 3738)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3739 : Nat.count Nat.Prime 3739 = 521 := by
  rw [show 3739 = 3738 + 1 by norm_num, Nat.count_succ]
  rw [show 3738 = 3737 + 1 by norm_num, Nat.count_succ]
  rw [show 3737 = 3736 + 1 by norm_num, Nat.count_succ]
  rw [show 3736 = 3735 + 1 by norm_num, Nat.count_succ]
  rw [show 3735 = 3734 + 1 by norm_num, Nat.count_succ]
  rw [show 3734 = 3733 + 1 by norm_num, Nat.count_succ]
  rw [count_3733]
  simp [prime_3733, not_prime_3734, not_prime_3735, not_prime_3736, not_prime_3737, not_prime_3738]

theorem prime_3739 : (3739 : Nat).Prime := by norm_num

theorem nth_521 : Nat.nth Nat.Prime 521 = 3739 := by
  rw [← count_3739]
  exact Nat.nth_count prime_3739

theorem not_prime_3740 : ¬Nat.Prime 3740 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1870) (n := 3740)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3741 : ¬Nat.Prime 3741 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1247) (n := 3741)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3742 : ¬Nat.Prime 3742 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1871) (n := 3742)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3743 : ¬Nat.Prime 3743 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 197) (n := 3743)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3744 : ¬Nat.Prime 3744 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1872) (n := 3744)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3745 : ¬Nat.Prime 3745 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 749) (n := 3745)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3746 : ¬Nat.Prime 3746 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1873) (n := 3746)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3747 : ¬Nat.Prime 3747 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1249) (n := 3747)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3748 : ¬Nat.Prime 3748 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1874) (n := 3748)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3749 : ¬Nat.Prime 3749 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 163) (n := 3749)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3750 : ¬Nat.Prime 3750 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1875) (n := 3750)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3751 : ¬Nat.Prime 3751 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 341) (n := 3751)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3752 : ¬Nat.Prime 3752 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1876) (n := 3752)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3753 : ¬Nat.Prime 3753 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1251) (n := 3753)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3754 : ¬Nat.Prime 3754 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1877) (n := 3754)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3755 : ¬Nat.Prime 3755 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 751) (n := 3755)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3756 : ¬Nat.Prime 3756 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1878) (n := 3756)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3757 : ¬Nat.Prime 3757 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 289) (n := 3757)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3758 : ¬Nat.Prime 3758 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1879) (n := 3758)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3759 : ¬Nat.Prime 3759 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1253) (n := 3759)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3760 : ¬Nat.Prime 3760 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1880) (n := 3760)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3761 : Nat.count Nat.Prime 3761 = 522 := by
  rw [show 3761 = 3760 + 1 by norm_num, Nat.count_succ]
  rw [show 3760 = 3759 + 1 by norm_num, Nat.count_succ]
  rw [show 3759 = 3758 + 1 by norm_num, Nat.count_succ]
  rw [show 3758 = 3757 + 1 by norm_num, Nat.count_succ]
  rw [show 3757 = 3756 + 1 by norm_num, Nat.count_succ]
  rw [show 3756 = 3755 + 1 by norm_num, Nat.count_succ]
  rw [show 3755 = 3754 + 1 by norm_num, Nat.count_succ]
  rw [show 3754 = 3753 + 1 by norm_num, Nat.count_succ]
  rw [show 3753 = 3752 + 1 by norm_num, Nat.count_succ]
  rw [show 3752 = 3751 + 1 by norm_num, Nat.count_succ]
  rw [show 3751 = 3750 + 1 by norm_num, Nat.count_succ]
  rw [show 3750 = 3749 + 1 by norm_num, Nat.count_succ]
  rw [show 3749 = 3748 + 1 by norm_num, Nat.count_succ]
  rw [show 3748 = 3747 + 1 by norm_num, Nat.count_succ]
  rw [show 3747 = 3746 + 1 by norm_num, Nat.count_succ]
  rw [show 3746 = 3745 + 1 by norm_num, Nat.count_succ]
  rw [show 3745 = 3744 + 1 by norm_num, Nat.count_succ]
  rw [show 3744 = 3743 + 1 by norm_num, Nat.count_succ]
  rw [show 3743 = 3742 + 1 by norm_num, Nat.count_succ]
  rw [show 3742 = 3741 + 1 by norm_num, Nat.count_succ]
  rw [show 3741 = 3740 + 1 by norm_num, Nat.count_succ]
  rw [show 3740 = 3739 + 1 by norm_num, Nat.count_succ]
  rw [count_3739]
  simp [prime_3739, not_prime_3740, not_prime_3741, not_prime_3742, not_prime_3743, not_prime_3744, not_prime_3745, not_prime_3746, not_prime_3747, not_prime_3748, not_prime_3749, not_prime_3750, not_prime_3751, not_prime_3752, not_prime_3753, not_prime_3754, not_prime_3755, not_prime_3756, not_prime_3757, not_prime_3758, not_prime_3759, not_prime_3760]

theorem prime_3761 : (3761 : Nat).Prime := by norm_num

theorem nth_522 : Nat.nth Nat.Prime 522 = 3761 := by
  rw [← count_3761]
  exact Nat.nth_count prime_3761

theorem not_prime_3762 : ¬Nat.Prime 3762 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1881) (n := 3762)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3763 : ¬Nat.Prime 3763 :=
  Nat.not_prime_of_mul_eq (a := 53) (b := 71) (n := 3763)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3764 : ¬Nat.Prime 3764 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1882) (n := 3764)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3765 : ¬Nat.Prime 3765 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1255) (n := 3765)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3766 : ¬Nat.Prime 3766 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1883) (n := 3766)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3767 : Nat.count Nat.Prime 3767 = 523 := by
  rw [show 3767 = 3766 + 1 by norm_num, Nat.count_succ]
  rw [show 3766 = 3765 + 1 by norm_num, Nat.count_succ]
  rw [show 3765 = 3764 + 1 by norm_num, Nat.count_succ]
  rw [show 3764 = 3763 + 1 by norm_num, Nat.count_succ]
  rw [show 3763 = 3762 + 1 by norm_num, Nat.count_succ]
  rw [show 3762 = 3761 + 1 by norm_num, Nat.count_succ]
  rw [count_3761]
  simp [prime_3761, not_prime_3762, not_prime_3763, not_prime_3764, not_prime_3765, not_prime_3766]

theorem prime_3767 : (3767 : Nat).Prime := by norm_num

theorem nth_523 : Nat.nth Nat.Prime 523 = 3767 := by
  rw [← count_3767]
  exact Nat.nth_count prime_3767

theorem not_prime_3768 : ¬Nat.Prime 3768 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1884) (n := 3768)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3769 : Nat.count Nat.Prime 3769 = 524 := by
  rw [show 3769 = 3768 + 1 by norm_num, Nat.count_succ]
  rw [show 3768 = 3767 + 1 by norm_num, Nat.count_succ]
  rw [count_3767]
  simp [prime_3767, not_prime_3768]

theorem prime_3769 : (3769 : Nat).Prime := by norm_num

theorem nth_524 : Nat.nth Nat.Prime 524 = 3769 := by
  rw [← count_3769]
  exact Nat.nth_count prime_3769

end OeisA100474.PrimeCertificate
