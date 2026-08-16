import OeisA100474PrimeCertificate.Chunk09

/-! Kernel prime/count certificate, chunk 10 (250–274). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_1584 : ¬Nat.Prime 1584 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 792) (n := 1584)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1585 : ¬Nat.Prime 1585 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 317) (n := 1585)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1586 : ¬Nat.Prime 1586 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 793) (n := 1586)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1587 : ¬Nat.Prime 1587 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 529) (n := 1587)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1588 : ¬Nat.Prime 1588 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 794) (n := 1588)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1589 : ¬Nat.Prime 1589 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 227) (n := 1589)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1590 : ¬Nat.Prime 1590 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 795) (n := 1590)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1591 : ¬Nat.Prime 1591 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 43) (n := 1591)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1592 : ¬Nat.Prime 1592 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 796) (n := 1592)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1593 : ¬Nat.Prime 1593 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 531) (n := 1593)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1594 : ¬Nat.Prime 1594 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 797) (n := 1594)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1595 : ¬Nat.Prime 1595 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 319) (n := 1595)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1596 : ¬Nat.Prime 1596 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 798) (n := 1596)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1597 : Nat.count Nat.Prime 1597 = 250 := by
  rw [show 1597 = 1596 + 1 by norm_num, Nat.count_succ]
  rw [show 1596 = 1595 + 1 by norm_num, Nat.count_succ]
  rw [show 1595 = 1594 + 1 by norm_num, Nat.count_succ]
  rw [show 1594 = 1593 + 1 by norm_num, Nat.count_succ]
  rw [show 1593 = 1592 + 1 by norm_num, Nat.count_succ]
  rw [show 1592 = 1591 + 1 by norm_num, Nat.count_succ]
  rw [show 1591 = 1590 + 1 by norm_num, Nat.count_succ]
  rw [show 1590 = 1589 + 1 by norm_num, Nat.count_succ]
  rw [show 1589 = 1588 + 1 by norm_num, Nat.count_succ]
  rw [show 1588 = 1587 + 1 by norm_num, Nat.count_succ]
  rw [show 1587 = 1586 + 1 by norm_num, Nat.count_succ]
  rw [show 1586 = 1585 + 1 by norm_num, Nat.count_succ]
  rw [show 1585 = 1584 + 1 by norm_num, Nat.count_succ]
  rw [show 1584 = 1583 + 1 by norm_num, Nat.count_succ]
  rw [count_1583]
  simp [prime_1583, not_prime_1584, not_prime_1585, not_prime_1586, not_prime_1587, not_prime_1588, not_prime_1589, not_prime_1590, not_prime_1591, not_prime_1592, not_prime_1593, not_prime_1594, not_prime_1595, not_prime_1596]

theorem prime_1597 : (1597 : Nat).Prime := by norm_num

theorem nth_250 : Nat.nth Nat.Prime 250 = 1597 := by
  rw [← count_1597]
  exact Nat.nth_count prime_1597

theorem not_prime_1598 : ¬Nat.Prime 1598 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 799) (n := 1598)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1599 : ¬Nat.Prime 1599 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 533) (n := 1599)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1600 : ¬Nat.Prime 1600 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 800) (n := 1600)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1601 : Nat.count Nat.Prime 1601 = 251 := by
  rw [show 1601 = 1600 + 1 by norm_num, Nat.count_succ]
  rw [show 1600 = 1599 + 1 by norm_num, Nat.count_succ]
  rw [show 1599 = 1598 + 1 by norm_num, Nat.count_succ]
  rw [show 1598 = 1597 + 1 by norm_num, Nat.count_succ]
  rw [count_1597]
  simp [prime_1597, not_prime_1598, not_prime_1599, not_prime_1600]

theorem prime_1601 : (1601 : Nat).Prime := by norm_num

theorem nth_251 : Nat.nth Nat.Prime 251 = 1601 := by
  rw [← count_1601]
  exact Nat.nth_count prime_1601

theorem not_prime_1602 : ¬Nat.Prime 1602 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 801) (n := 1602)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1603 : ¬Nat.Prime 1603 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 229) (n := 1603)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1604 : ¬Nat.Prime 1604 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 802) (n := 1604)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1605 : ¬Nat.Prime 1605 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 535) (n := 1605)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1606 : ¬Nat.Prime 1606 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 803) (n := 1606)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1607 : Nat.count Nat.Prime 1607 = 252 := by
  rw [show 1607 = 1606 + 1 by norm_num, Nat.count_succ]
  rw [show 1606 = 1605 + 1 by norm_num, Nat.count_succ]
  rw [show 1605 = 1604 + 1 by norm_num, Nat.count_succ]
  rw [show 1604 = 1603 + 1 by norm_num, Nat.count_succ]
  rw [show 1603 = 1602 + 1 by norm_num, Nat.count_succ]
  rw [show 1602 = 1601 + 1 by norm_num, Nat.count_succ]
  rw [count_1601]
  simp [prime_1601, not_prime_1602, not_prime_1603, not_prime_1604, not_prime_1605, not_prime_1606]

theorem prime_1607 : (1607 : Nat).Prime := by norm_num

theorem nth_252 : Nat.nth Nat.Prime 252 = 1607 := by
  rw [← count_1607]
  exact Nat.nth_count prime_1607

theorem not_prime_1608 : ¬Nat.Prime 1608 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 804) (n := 1608)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1609 : Nat.count Nat.Prime 1609 = 253 := by
  rw [show 1609 = 1608 + 1 by norm_num, Nat.count_succ]
  rw [show 1608 = 1607 + 1 by norm_num, Nat.count_succ]
  rw [count_1607]
  simp [prime_1607, not_prime_1608]

theorem prime_1609 : (1609 : Nat).Prime := by norm_num

theorem nth_253 : Nat.nth Nat.Prime 253 = 1609 := by
  rw [← count_1609]
  exact Nat.nth_count prime_1609

theorem not_prime_1610 : ¬Nat.Prime 1610 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 805) (n := 1610)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1611 : ¬Nat.Prime 1611 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 537) (n := 1611)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1612 : ¬Nat.Prime 1612 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 806) (n := 1612)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1613 : Nat.count Nat.Prime 1613 = 254 := by
  rw [show 1613 = 1612 + 1 by norm_num, Nat.count_succ]
  rw [show 1612 = 1611 + 1 by norm_num, Nat.count_succ]
  rw [show 1611 = 1610 + 1 by norm_num, Nat.count_succ]
  rw [show 1610 = 1609 + 1 by norm_num, Nat.count_succ]
  rw [count_1609]
  simp [prime_1609, not_prime_1610, not_prime_1611, not_prime_1612]

theorem prime_1613 : (1613 : Nat).Prime := by norm_num

theorem nth_254 : Nat.nth Nat.Prime 254 = 1613 := by
  rw [← count_1613]
  exact Nat.nth_count prime_1613

theorem not_prime_1614 : ¬Nat.Prime 1614 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 807) (n := 1614)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1615 : ¬Nat.Prime 1615 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 323) (n := 1615)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1616 : ¬Nat.Prime 1616 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 808) (n := 1616)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1617 : ¬Nat.Prime 1617 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 539) (n := 1617)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1618 : ¬Nat.Prime 1618 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 809) (n := 1618)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1619 : Nat.count Nat.Prime 1619 = 255 := by
  rw [show 1619 = 1618 + 1 by norm_num, Nat.count_succ]
  rw [show 1618 = 1617 + 1 by norm_num, Nat.count_succ]
  rw [show 1617 = 1616 + 1 by norm_num, Nat.count_succ]
  rw [show 1616 = 1615 + 1 by norm_num, Nat.count_succ]
  rw [show 1615 = 1614 + 1 by norm_num, Nat.count_succ]
  rw [show 1614 = 1613 + 1 by norm_num, Nat.count_succ]
  rw [count_1613]
  simp [prime_1613, not_prime_1614, not_prime_1615, not_prime_1616, not_prime_1617, not_prime_1618]

theorem prime_1619 : (1619 : Nat).Prime := by norm_num

theorem nth_255 : Nat.nth Nat.Prime 255 = 1619 := by
  rw [← count_1619]
  exact Nat.nth_count prime_1619

theorem not_prime_1620 : ¬Nat.Prime 1620 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 810) (n := 1620)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1621 : Nat.count Nat.Prime 1621 = 256 := by
  rw [show 1621 = 1620 + 1 by norm_num, Nat.count_succ]
  rw [show 1620 = 1619 + 1 by norm_num, Nat.count_succ]
  rw [count_1619]
  simp [prime_1619, not_prime_1620]

theorem prime_1621 : (1621 : Nat).Prime := by norm_num

theorem nth_256 : Nat.nth Nat.Prime 256 = 1621 := by
  rw [← count_1621]
  exact Nat.nth_count prime_1621

theorem not_prime_1622 : ¬Nat.Prime 1622 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 811) (n := 1622)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1623 : ¬Nat.Prime 1623 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 541) (n := 1623)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1624 : ¬Nat.Prime 1624 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 812) (n := 1624)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1625 : ¬Nat.Prime 1625 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 325) (n := 1625)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1626 : ¬Nat.Prime 1626 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 813) (n := 1626)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1627 : Nat.count Nat.Prime 1627 = 257 := by
  rw [show 1627 = 1626 + 1 by norm_num, Nat.count_succ]
  rw [show 1626 = 1625 + 1 by norm_num, Nat.count_succ]
  rw [show 1625 = 1624 + 1 by norm_num, Nat.count_succ]
  rw [show 1624 = 1623 + 1 by norm_num, Nat.count_succ]
  rw [show 1623 = 1622 + 1 by norm_num, Nat.count_succ]
  rw [show 1622 = 1621 + 1 by norm_num, Nat.count_succ]
  rw [count_1621]
  simp [prime_1621, not_prime_1622, not_prime_1623, not_prime_1624, not_prime_1625, not_prime_1626]

theorem prime_1627 : (1627 : Nat).Prime := by norm_num

theorem nth_257 : Nat.nth Nat.Prime 257 = 1627 := by
  rw [← count_1627]
  exact Nat.nth_count prime_1627

theorem not_prime_1628 : ¬Nat.Prime 1628 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 814) (n := 1628)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1629 : ¬Nat.Prime 1629 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 543) (n := 1629)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1630 : ¬Nat.Prime 1630 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 815) (n := 1630)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1631 : ¬Nat.Prime 1631 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 233) (n := 1631)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1632 : ¬Nat.Prime 1632 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 816) (n := 1632)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1633 : ¬Nat.Prime 1633 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 71) (n := 1633)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1634 : ¬Nat.Prime 1634 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 817) (n := 1634)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1635 : ¬Nat.Prime 1635 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 545) (n := 1635)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1636 : ¬Nat.Prime 1636 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 818) (n := 1636)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1637 : Nat.count Nat.Prime 1637 = 258 := by
  rw [show 1637 = 1636 + 1 by norm_num, Nat.count_succ]
  rw [show 1636 = 1635 + 1 by norm_num, Nat.count_succ]
  rw [show 1635 = 1634 + 1 by norm_num, Nat.count_succ]
  rw [show 1634 = 1633 + 1 by norm_num, Nat.count_succ]
  rw [show 1633 = 1632 + 1 by norm_num, Nat.count_succ]
  rw [show 1632 = 1631 + 1 by norm_num, Nat.count_succ]
  rw [show 1631 = 1630 + 1 by norm_num, Nat.count_succ]
  rw [show 1630 = 1629 + 1 by norm_num, Nat.count_succ]
  rw [show 1629 = 1628 + 1 by norm_num, Nat.count_succ]
  rw [show 1628 = 1627 + 1 by norm_num, Nat.count_succ]
  rw [count_1627]
  simp [prime_1627, not_prime_1628, not_prime_1629, not_prime_1630, not_prime_1631, not_prime_1632, not_prime_1633, not_prime_1634, not_prime_1635, not_prime_1636]

theorem prime_1637 : (1637 : Nat).Prime := by norm_num

theorem nth_258 : Nat.nth Nat.Prime 258 = 1637 := by
  rw [← count_1637]
  exact Nat.nth_count prime_1637

theorem not_prime_1638 : ¬Nat.Prime 1638 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 819) (n := 1638)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1639 : ¬Nat.Prime 1639 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 149) (n := 1639)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1640 : ¬Nat.Prime 1640 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 820) (n := 1640)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1641 : ¬Nat.Prime 1641 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 547) (n := 1641)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1642 : ¬Nat.Prime 1642 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 821) (n := 1642)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1643 : ¬Nat.Prime 1643 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 53) (n := 1643)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1644 : ¬Nat.Prime 1644 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 822) (n := 1644)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1645 : ¬Nat.Prime 1645 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 329) (n := 1645)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1646 : ¬Nat.Prime 1646 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 823) (n := 1646)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1647 : ¬Nat.Prime 1647 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 549) (n := 1647)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1648 : ¬Nat.Prime 1648 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 824) (n := 1648)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1649 : ¬Nat.Prime 1649 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 97) (n := 1649)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1650 : ¬Nat.Prime 1650 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 825) (n := 1650)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1651 : ¬Nat.Prime 1651 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 127) (n := 1651)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1652 : ¬Nat.Prime 1652 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 826) (n := 1652)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1653 : ¬Nat.Prime 1653 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 551) (n := 1653)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1654 : ¬Nat.Prime 1654 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 827) (n := 1654)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1655 : ¬Nat.Prime 1655 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 331) (n := 1655)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1656 : ¬Nat.Prime 1656 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 828) (n := 1656)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1657 : Nat.count Nat.Prime 1657 = 259 := by
  rw [show 1657 = 1656 + 1 by norm_num, Nat.count_succ]
  rw [show 1656 = 1655 + 1 by norm_num, Nat.count_succ]
  rw [show 1655 = 1654 + 1 by norm_num, Nat.count_succ]
  rw [show 1654 = 1653 + 1 by norm_num, Nat.count_succ]
  rw [show 1653 = 1652 + 1 by norm_num, Nat.count_succ]
  rw [show 1652 = 1651 + 1 by norm_num, Nat.count_succ]
  rw [show 1651 = 1650 + 1 by norm_num, Nat.count_succ]
  rw [show 1650 = 1649 + 1 by norm_num, Nat.count_succ]
  rw [show 1649 = 1648 + 1 by norm_num, Nat.count_succ]
  rw [show 1648 = 1647 + 1 by norm_num, Nat.count_succ]
  rw [show 1647 = 1646 + 1 by norm_num, Nat.count_succ]
  rw [show 1646 = 1645 + 1 by norm_num, Nat.count_succ]
  rw [show 1645 = 1644 + 1 by norm_num, Nat.count_succ]
  rw [show 1644 = 1643 + 1 by norm_num, Nat.count_succ]
  rw [show 1643 = 1642 + 1 by norm_num, Nat.count_succ]
  rw [show 1642 = 1641 + 1 by norm_num, Nat.count_succ]
  rw [show 1641 = 1640 + 1 by norm_num, Nat.count_succ]
  rw [show 1640 = 1639 + 1 by norm_num, Nat.count_succ]
  rw [show 1639 = 1638 + 1 by norm_num, Nat.count_succ]
  rw [show 1638 = 1637 + 1 by norm_num, Nat.count_succ]
  rw [count_1637]
  simp [prime_1637, not_prime_1638, not_prime_1639, not_prime_1640, not_prime_1641, not_prime_1642, not_prime_1643, not_prime_1644, not_prime_1645, not_prime_1646, not_prime_1647, not_prime_1648, not_prime_1649, not_prime_1650, not_prime_1651, not_prime_1652, not_prime_1653, not_prime_1654, not_prime_1655, not_prime_1656]

theorem prime_1657 : (1657 : Nat).Prime := by norm_num

theorem nth_259 : Nat.nth Nat.Prime 259 = 1657 := by
  rw [← count_1657]
  exact Nat.nth_count prime_1657

theorem not_prime_1658 : ¬Nat.Prime 1658 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 829) (n := 1658)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1659 : ¬Nat.Prime 1659 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 553) (n := 1659)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1660 : ¬Nat.Prime 1660 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 830) (n := 1660)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1661 : ¬Nat.Prime 1661 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 151) (n := 1661)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1662 : ¬Nat.Prime 1662 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 831) (n := 1662)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1663 : Nat.count Nat.Prime 1663 = 260 := by
  rw [show 1663 = 1662 + 1 by norm_num, Nat.count_succ]
  rw [show 1662 = 1661 + 1 by norm_num, Nat.count_succ]
  rw [show 1661 = 1660 + 1 by norm_num, Nat.count_succ]
  rw [show 1660 = 1659 + 1 by norm_num, Nat.count_succ]
  rw [show 1659 = 1658 + 1 by norm_num, Nat.count_succ]
  rw [show 1658 = 1657 + 1 by norm_num, Nat.count_succ]
  rw [count_1657]
  simp [prime_1657, not_prime_1658, not_prime_1659, not_prime_1660, not_prime_1661, not_prime_1662]

theorem prime_1663 : (1663 : Nat).Prime := by norm_num

theorem nth_260 : Nat.nth Nat.Prime 260 = 1663 := by
  rw [← count_1663]
  exact Nat.nth_count prime_1663

theorem not_prime_1664 : ¬Nat.Prime 1664 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 832) (n := 1664)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1665 : ¬Nat.Prime 1665 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 555) (n := 1665)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1666 : ¬Nat.Prime 1666 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 833) (n := 1666)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1667 : Nat.count Nat.Prime 1667 = 261 := by
  rw [show 1667 = 1666 + 1 by norm_num, Nat.count_succ]
  rw [show 1666 = 1665 + 1 by norm_num, Nat.count_succ]
  rw [show 1665 = 1664 + 1 by norm_num, Nat.count_succ]
  rw [show 1664 = 1663 + 1 by norm_num, Nat.count_succ]
  rw [count_1663]
  simp [prime_1663, not_prime_1664, not_prime_1665, not_prime_1666]

theorem prime_1667 : (1667 : Nat).Prime := by norm_num

theorem nth_261 : Nat.nth Nat.Prime 261 = 1667 := by
  rw [← count_1667]
  exact Nat.nth_count prime_1667

theorem not_prime_1668 : ¬Nat.Prime 1668 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 834) (n := 1668)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1669 : Nat.count Nat.Prime 1669 = 262 := by
  rw [show 1669 = 1668 + 1 by norm_num, Nat.count_succ]
  rw [show 1668 = 1667 + 1 by norm_num, Nat.count_succ]
  rw [count_1667]
  simp [prime_1667, not_prime_1668]

theorem prime_1669 : (1669 : Nat).Prime := by norm_num

theorem nth_262 : Nat.nth Nat.Prime 262 = 1669 := by
  rw [← count_1669]
  exact Nat.nth_count prime_1669

theorem not_prime_1670 : ¬Nat.Prime 1670 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 835) (n := 1670)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1671 : ¬Nat.Prime 1671 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 557) (n := 1671)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1672 : ¬Nat.Prime 1672 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 836) (n := 1672)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1673 : ¬Nat.Prime 1673 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 239) (n := 1673)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1674 : ¬Nat.Prime 1674 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 837) (n := 1674)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1675 : ¬Nat.Prime 1675 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 335) (n := 1675)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1676 : ¬Nat.Prime 1676 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 838) (n := 1676)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1677 : ¬Nat.Prime 1677 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 559) (n := 1677)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1678 : ¬Nat.Prime 1678 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 839) (n := 1678)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1679 : ¬Nat.Prime 1679 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 73) (n := 1679)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1680 : ¬Nat.Prime 1680 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 840) (n := 1680)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1681 : ¬Nat.Prime 1681 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 41) (n := 1681)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1682 : ¬Nat.Prime 1682 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 841) (n := 1682)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1683 : ¬Nat.Prime 1683 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 561) (n := 1683)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1684 : ¬Nat.Prime 1684 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 842) (n := 1684)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1685 : ¬Nat.Prime 1685 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 337) (n := 1685)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1686 : ¬Nat.Prime 1686 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 843) (n := 1686)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1687 : ¬Nat.Prime 1687 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 241) (n := 1687)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1688 : ¬Nat.Prime 1688 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 844) (n := 1688)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1689 : ¬Nat.Prime 1689 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 563) (n := 1689)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1690 : ¬Nat.Prime 1690 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 845) (n := 1690)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1691 : ¬Nat.Prime 1691 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 89) (n := 1691)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1692 : ¬Nat.Prime 1692 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 846) (n := 1692)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1693 : Nat.count Nat.Prime 1693 = 263 := by
  rw [show 1693 = 1692 + 1 by norm_num, Nat.count_succ]
  rw [show 1692 = 1691 + 1 by norm_num, Nat.count_succ]
  rw [show 1691 = 1690 + 1 by norm_num, Nat.count_succ]
  rw [show 1690 = 1689 + 1 by norm_num, Nat.count_succ]
  rw [show 1689 = 1688 + 1 by norm_num, Nat.count_succ]
  rw [show 1688 = 1687 + 1 by norm_num, Nat.count_succ]
  rw [show 1687 = 1686 + 1 by norm_num, Nat.count_succ]
  rw [show 1686 = 1685 + 1 by norm_num, Nat.count_succ]
  rw [show 1685 = 1684 + 1 by norm_num, Nat.count_succ]
  rw [show 1684 = 1683 + 1 by norm_num, Nat.count_succ]
  rw [show 1683 = 1682 + 1 by norm_num, Nat.count_succ]
  rw [show 1682 = 1681 + 1 by norm_num, Nat.count_succ]
  rw [show 1681 = 1680 + 1 by norm_num, Nat.count_succ]
  rw [show 1680 = 1679 + 1 by norm_num, Nat.count_succ]
  rw [show 1679 = 1678 + 1 by norm_num, Nat.count_succ]
  rw [show 1678 = 1677 + 1 by norm_num, Nat.count_succ]
  rw [show 1677 = 1676 + 1 by norm_num, Nat.count_succ]
  rw [show 1676 = 1675 + 1 by norm_num, Nat.count_succ]
  rw [show 1675 = 1674 + 1 by norm_num, Nat.count_succ]
  rw [show 1674 = 1673 + 1 by norm_num, Nat.count_succ]
  rw [show 1673 = 1672 + 1 by norm_num, Nat.count_succ]
  rw [show 1672 = 1671 + 1 by norm_num, Nat.count_succ]
  rw [show 1671 = 1670 + 1 by norm_num, Nat.count_succ]
  rw [show 1670 = 1669 + 1 by norm_num, Nat.count_succ]
  rw [count_1669]
  simp [prime_1669, not_prime_1670, not_prime_1671, not_prime_1672, not_prime_1673, not_prime_1674, not_prime_1675, not_prime_1676, not_prime_1677, not_prime_1678, not_prime_1679, not_prime_1680, not_prime_1681, not_prime_1682, not_prime_1683, not_prime_1684, not_prime_1685, not_prime_1686, not_prime_1687, not_prime_1688, not_prime_1689, not_prime_1690, not_prime_1691, not_prime_1692]

theorem prime_1693 : (1693 : Nat).Prime := by norm_num

theorem nth_263 : Nat.nth Nat.Prime 263 = 1693 := by
  rw [← count_1693]
  exact Nat.nth_count prime_1693

theorem not_prime_1694 : ¬Nat.Prime 1694 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 847) (n := 1694)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1695 : ¬Nat.Prime 1695 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 565) (n := 1695)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1696 : ¬Nat.Prime 1696 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 848) (n := 1696)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1697 : Nat.count Nat.Prime 1697 = 264 := by
  rw [show 1697 = 1696 + 1 by norm_num, Nat.count_succ]
  rw [show 1696 = 1695 + 1 by norm_num, Nat.count_succ]
  rw [show 1695 = 1694 + 1 by norm_num, Nat.count_succ]
  rw [show 1694 = 1693 + 1 by norm_num, Nat.count_succ]
  rw [count_1693]
  simp [prime_1693, not_prime_1694, not_prime_1695, not_prime_1696]

theorem prime_1697 : (1697 : Nat).Prime := by norm_num

theorem nth_264 : Nat.nth Nat.Prime 264 = 1697 := by
  rw [← count_1697]
  exact Nat.nth_count prime_1697

theorem not_prime_1698 : ¬Nat.Prime 1698 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 849) (n := 1698)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1699 : Nat.count Nat.Prime 1699 = 265 := by
  rw [show 1699 = 1698 + 1 by norm_num, Nat.count_succ]
  rw [show 1698 = 1697 + 1 by norm_num, Nat.count_succ]
  rw [count_1697]
  simp [prime_1697, not_prime_1698]

theorem prime_1699 : (1699 : Nat).Prime := by norm_num

theorem nth_265 : Nat.nth Nat.Prime 265 = 1699 := by
  rw [← count_1699]
  exact Nat.nth_count prime_1699

theorem not_prime_1700 : ¬Nat.Prime 1700 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 850) (n := 1700)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1701 : ¬Nat.Prime 1701 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 567) (n := 1701)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1702 : ¬Nat.Prime 1702 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 851) (n := 1702)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1703 : ¬Nat.Prime 1703 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 131) (n := 1703)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1704 : ¬Nat.Prime 1704 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 852) (n := 1704)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1705 : ¬Nat.Prime 1705 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 341) (n := 1705)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1706 : ¬Nat.Prime 1706 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 853) (n := 1706)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1707 : ¬Nat.Prime 1707 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 569) (n := 1707)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1708 : ¬Nat.Prime 1708 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 854) (n := 1708)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1709 : Nat.count Nat.Prime 1709 = 266 := by
  rw [show 1709 = 1708 + 1 by norm_num, Nat.count_succ]
  rw [show 1708 = 1707 + 1 by norm_num, Nat.count_succ]
  rw [show 1707 = 1706 + 1 by norm_num, Nat.count_succ]
  rw [show 1706 = 1705 + 1 by norm_num, Nat.count_succ]
  rw [show 1705 = 1704 + 1 by norm_num, Nat.count_succ]
  rw [show 1704 = 1703 + 1 by norm_num, Nat.count_succ]
  rw [show 1703 = 1702 + 1 by norm_num, Nat.count_succ]
  rw [show 1702 = 1701 + 1 by norm_num, Nat.count_succ]
  rw [show 1701 = 1700 + 1 by norm_num, Nat.count_succ]
  rw [show 1700 = 1699 + 1 by norm_num, Nat.count_succ]
  rw [count_1699]
  simp [prime_1699, not_prime_1700, not_prime_1701, not_prime_1702, not_prime_1703, not_prime_1704, not_prime_1705, not_prime_1706, not_prime_1707, not_prime_1708]

theorem prime_1709 : (1709 : Nat).Prime := by norm_num

theorem nth_266 : Nat.nth Nat.Prime 266 = 1709 := by
  rw [← count_1709]
  exact Nat.nth_count prime_1709

theorem not_prime_1710 : ¬Nat.Prime 1710 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 855) (n := 1710)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1711 : ¬Nat.Prime 1711 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 59) (n := 1711)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1712 : ¬Nat.Prime 1712 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 856) (n := 1712)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1713 : ¬Nat.Prime 1713 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 571) (n := 1713)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1714 : ¬Nat.Prime 1714 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 857) (n := 1714)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1715 : ¬Nat.Prime 1715 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 343) (n := 1715)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1716 : ¬Nat.Prime 1716 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 858) (n := 1716)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1717 : ¬Nat.Prime 1717 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 101) (n := 1717)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1718 : ¬Nat.Prime 1718 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 859) (n := 1718)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1719 : ¬Nat.Prime 1719 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 573) (n := 1719)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1720 : ¬Nat.Prime 1720 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 860) (n := 1720)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1721 : Nat.count Nat.Prime 1721 = 267 := by
  rw [show 1721 = 1720 + 1 by norm_num, Nat.count_succ]
  rw [show 1720 = 1719 + 1 by norm_num, Nat.count_succ]
  rw [show 1719 = 1718 + 1 by norm_num, Nat.count_succ]
  rw [show 1718 = 1717 + 1 by norm_num, Nat.count_succ]
  rw [show 1717 = 1716 + 1 by norm_num, Nat.count_succ]
  rw [show 1716 = 1715 + 1 by norm_num, Nat.count_succ]
  rw [show 1715 = 1714 + 1 by norm_num, Nat.count_succ]
  rw [show 1714 = 1713 + 1 by norm_num, Nat.count_succ]
  rw [show 1713 = 1712 + 1 by norm_num, Nat.count_succ]
  rw [show 1712 = 1711 + 1 by norm_num, Nat.count_succ]
  rw [show 1711 = 1710 + 1 by norm_num, Nat.count_succ]
  rw [show 1710 = 1709 + 1 by norm_num, Nat.count_succ]
  rw [count_1709]
  simp [prime_1709, not_prime_1710, not_prime_1711, not_prime_1712, not_prime_1713, not_prime_1714, not_prime_1715, not_prime_1716, not_prime_1717, not_prime_1718, not_prime_1719, not_prime_1720]

theorem prime_1721 : (1721 : Nat).Prime := by norm_num

theorem nth_267 : Nat.nth Nat.Prime 267 = 1721 := by
  rw [← count_1721]
  exact Nat.nth_count prime_1721

theorem not_prime_1722 : ¬Nat.Prime 1722 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 861) (n := 1722)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1723 : Nat.count Nat.Prime 1723 = 268 := by
  rw [show 1723 = 1722 + 1 by norm_num, Nat.count_succ]
  rw [show 1722 = 1721 + 1 by norm_num, Nat.count_succ]
  rw [count_1721]
  simp [prime_1721, not_prime_1722]

theorem prime_1723 : (1723 : Nat).Prime := by norm_num

theorem nth_268 : Nat.nth Nat.Prime 268 = 1723 := by
  rw [← count_1723]
  exact Nat.nth_count prime_1723

theorem not_prime_1724 : ¬Nat.Prime 1724 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 862) (n := 1724)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1725 : ¬Nat.Prime 1725 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 575) (n := 1725)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1726 : ¬Nat.Prime 1726 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 863) (n := 1726)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1727 : ¬Nat.Prime 1727 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 157) (n := 1727)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1728 : ¬Nat.Prime 1728 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 864) (n := 1728)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1729 : ¬Nat.Prime 1729 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 247) (n := 1729)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1730 : ¬Nat.Prime 1730 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 865) (n := 1730)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1731 : ¬Nat.Prime 1731 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 577) (n := 1731)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1732 : ¬Nat.Prime 1732 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 866) (n := 1732)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1733 : Nat.count Nat.Prime 1733 = 269 := by
  rw [show 1733 = 1732 + 1 by norm_num, Nat.count_succ]
  rw [show 1732 = 1731 + 1 by norm_num, Nat.count_succ]
  rw [show 1731 = 1730 + 1 by norm_num, Nat.count_succ]
  rw [show 1730 = 1729 + 1 by norm_num, Nat.count_succ]
  rw [show 1729 = 1728 + 1 by norm_num, Nat.count_succ]
  rw [show 1728 = 1727 + 1 by norm_num, Nat.count_succ]
  rw [show 1727 = 1726 + 1 by norm_num, Nat.count_succ]
  rw [show 1726 = 1725 + 1 by norm_num, Nat.count_succ]
  rw [show 1725 = 1724 + 1 by norm_num, Nat.count_succ]
  rw [show 1724 = 1723 + 1 by norm_num, Nat.count_succ]
  rw [count_1723]
  simp [prime_1723, not_prime_1724, not_prime_1725, not_prime_1726, not_prime_1727, not_prime_1728, not_prime_1729, not_prime_1730, not_prime_1731, not_prime_1732]

theorem prime_1733 : (1733 : Nat).Prime := by norm_num

theorem nth_269 : Nat.nth Nat.Prime 269 = 1733 := by
  rw [← count_1733]
  exact Nat.nth_count prime_1733

theorem not_prime_1734 : ¬Nat.Prime 1734 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 867) (n := 1734)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1735 : ¬Nat.Prime 1735 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 347) (n := 1735)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1736 : ¬Nat.Prime 1736 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 868) (n := 1736)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1737 : ¬Nat.Prime 1737 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 579) (n := 1737)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1738 : ¬Nat.Prime 1738 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 869) (n := 1738)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1739 : ¬Nat.Prime 1739 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 47) (n := 1739)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1740 : ¬Nat.Prime 1740 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 870) (n := 1740)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1741 : Nat.count Nat.Prime 1741 = 270 := by
  rw [show 1741 = 1740 + 1 by norm_num, Nat.count_succ]
  rw [show 1740 = 1739 + 1 by norm_num, Nat.count_succ]
  rw [show 1739 = 1738 + 1 by norm_num, Nat.count_succ]
  rw [show 1738 = 1737 + 1 by norm_num, Nat.count_succ]
  rw [show 1737 = 1736 + 1 by norm_num, Nat.count_succ]
  rw [show 1736 = 1735 + 1 by norm_num, Nat.count_succ]
  rw [show 1735 = 1734 + 1 by norm_num, Nat.count_succ]
  rw [show 1734 = 1733 + 1 by norm_num, Nat.count_succ]
  rw [count_1733]
  simp [prime_1733, not_prime_1734, not_prime_1735, not_prime_1736, not_prime_1737, not_prime_1738, not_prime_1739, not_prime_1740]

theorem prime_1741 : (1741 : Nat).Prime := by norm_num

theorem nth_270 : Nat.nth Nat.Prime 270 = 1741 := by
  rw [← count_1741]
  exact Nat.nth_count prime_1741

theorem not_prime_1742 : ¬Nat.Prime 1742 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 871) (n := 1742)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1743 : ¬Nat.Prime 1743 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 581) (n := 1743)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1744 : ¬Nat.Prime 1744 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 872) (n := 1744)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1745 : ¬Nat.Prime 1745 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 349) (n := 1745)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1746 : ¬Nat.Prime 1746 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 873) (n := 1746)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1747 : Nat.count Nat.Prime 1747 = 271 := by
  rw [show 1747 = 1746 + 1 by norm_num, Nat.count_succ]
  rw [show 1746 = 1745 + 1 by norm_num, Nat.count_succ]
  rw [show 1745 = 1744 + 1 by norm_num, Nat.count_succ]
  rw [show 1744 = 1743 + 1 by norm_num, Nat.count_succ]
  rw [show 1743 = 1742 + 1 by norm_num, Nat.count_succ]
  rw [show 1742 = 1741 + 1 by norm_num, Nat.count_succ]
  rw [count_1741]
  simp [prime_1741, not_prime_1742, not_prime_1743, not_prime_1744, not_prime_1745, not_prime_1746]

theorem prime_1747 : (1747 : Nat).Prime := by norm_num

theorem nth_271 : Nat.nth Nat.Prime 271 = 1747 := by
  rw [← count_1747]
  exact Nat.nth_count prime_1747

theorem not_prime_1748 : ¬Nat.Prime 1748 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 874) (n := 1748)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1749 : ¬Nat.Prime 1749 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 583) (n := 1749)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1750 : ¬Nat.Prime 1750 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 875) (n := 1750)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1751 : ¬Nat.Prime 1751 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 103) (n := 1751)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1752 : ¬Nat.Prime 1752 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 876) (n := 1752)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1753 : Nat.count Nat.Prime 1753 = 272 := by
  rw [show 1753 = 1752 + 1 by norm_num, Nat.count_succ]
  rw [show 1752 = 1751 + 1 by norm_num, Nat.count_succ]
  rw [show 1751 = 1750 + 1 by norm_num, Nat.count_succ]
  rw [show 1750 = 1749 + 1 by norm_num, Nat.count_succ]
  rw [show 1749 = 1748 + 1 by norm_num, Nat.count_succ]
  rw [show 1748 = 1747 + 1 by norm_num, Nat.count_succ]
  rw [count_1747]
  simp [prime_1747, not_prime_1748, not_prime_1749, not_prime_1750, not_prime_1751, not_prime_1752]

theorem prime_1753 : (1753 : Nat).Prime := by norm_num

theorem nth_272 : Nat.nth Nat.Prime 272 = 1753 := by
  rw [← count_1753]
  exact Nat.nth_count prime_1753

theorem not_prime_1754 : ¬Nat.Prime 1754 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 877) (n := 1754)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1755 : ¬Nat.Prime 1755 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 585) (n := 1755)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1756 : ¬Nat.Prime 1756 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 878) (n := 1756)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1757 : ¬Nat.Prime 1757 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 251) (n := 1757)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1758 : ¬Nat.Prime 1758 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 879) (n := 1758)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1759 : Nat.count Nat.Prime 1759 = 273 := by
  rw [show 1759 = 1758 + 1 by norm_num, Nat.count_succ]
  rw [show 1758 = 1757 + 1 by norm_num, Nat.count_succ]
  rw [show 1757 = 1756 + 1 by norm_num, Nat.count_succ]
  rw [show 1756 = 1755 + 1 by norm_num, Nat.count_succ]
  rw [show 1755 = 1754 + 1 by norm_num, Nat.count_succ]
  rw [show 1754 = 1753 + 1 by norm_num, Nat.count_succ]
  rw [count_1753]
  simp [prime_1753, not_prime_1754, not_prime_1755, not_prime_1756, not_prime_1757, not_prime_1758]

theorem prime_1759 : (1759 : Nat).Prime := by norm_num

theorem nth_273 : Nat.nth Nat.Prime 273 = 1759 := by
  rw [← count_1759]
  exact Nat.nth_count prime_1759

theorem not_prime_1760 : ¬Nat.Prime 1760 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 880) (n := 1760)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1761 : ¬Nat.Prime 1761 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 587) (n := 1761)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1762 : ¬Nat.Prime 1762 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 881) (n := 1762)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1763 : ¬Nat.Prime 1763 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 43) (n := 1763)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1764 : ¬Nat.Prime 1764 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 882) (n := 1764)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1765 : ¬Nat.Prime 1765 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 353) (n := 1765)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1766 : ¬Nat.Prime 1766 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 883) (n := 1766)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1767 : ¬Nat.Prime 1767 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 589) (n := 1767)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1768 : ¬Nat.Prime 1768 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 884) (n := 1768)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1769 : ¬Nat.Prime 1769 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 61) (n := 1769)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1770 : ¬Nat.Prime 1770 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 885) (n := 1770)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1771 : ¬Nat.Prime 1771 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 253) (n := 1771)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1772 : ¬Nat.Prime 1772 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 886) (n := 1772)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1773 : ¬Nat.Prime 1773 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 591) (n := 1773)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1774 : ¬Nat.Prime 1774 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 887) (n := 1774)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1775 : ¬Nat.Prime 1775 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 355) (n := 1775)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1776 : ¬Nat.Prime 1776 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 888) (n := 1776)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1777 : Nat.count Nat.Prime 1777 = 274 := by
  rw [show 1777 = 1776 + 1 by norm_num, Nat.count_succ]
  rw [show 1776 = 1775 + 1 by norm_num, Nat.count_succ]
  rw [show 1775 = 1774 + 1 by norm_num, Nat.count_succ]
  rw [show 1774 = 1773 + 1 by norm_num, Nat.count_succ]
  rw [show 1773 = 1772 + 1 by norm_num, Nat.count_succ]
  rw [show 1772 = 1771 + 1 by norm_num, Nat.count_succ]
  rw [show 1771 = 1770 + 1 by norm_num, Nat.count_succ]
  rw [show 1770 = 1769 + 1 by norm_num, Nat.count_succ]
  rw [show 1769 = 1768 + 1 by norm_num, Nat.count_succ]
  rw [show 1768 = 1767 + 1 by norm_num, Nat.count_succ]
  rw [show 1767 = 1766 + 1 by norm_num, Nat.count_succ]
  rw [show 1766 = 1765 + 1 by norm_num, Nat.count_succ]
  rw [show 1765 = 1764 + 1 by norm_num, Nat.count_succ]
  rw [show 1764 = 1763 + 1 by norm_num, Nat.count_succ]
  rw [show 1763 = 1762 + 1 by norm_num, Nat.count_succ]
  rw [show 1762 = 1761 + 1 by norm_num, Nat.count_succ]
  rw [show 1761 = 1760 + 1 by norm_num, Nat.count_succ]
  rw [show 1760 = 1759 + 1 by norm_num, Nat.count_succ]
  rw [count_1759]
  simp [prime_1759, not_prime_1760, not_prime_1761, not_prime_1762, not_prime_1763, not_prime_1764, not_prime_1765, not_prime_1766, not_prime_1767, not_prime_1768, not_prime_1769, not_prime_1770, not_prime_1771, not_prime_1772, not_prime_1773, not_prime_1774, not_prime_1775, not_prime_1776]

theorem prime_1777 : (1777 : Nat).Prime := by norm_num

theorem nth_274 : Nat.nth Nat.Prime 274 = 1777 := by
  rw [← count_1777]
  exact Nat.nth_count prime_1777

end OeisA100474.PrimeCertificate
