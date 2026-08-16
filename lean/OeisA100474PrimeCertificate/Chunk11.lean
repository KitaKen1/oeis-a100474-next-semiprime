import OeisA100474PrimeCertificate.Chunk10

/-! Kernel prime/count certificate, chunk 11 (275–299). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_1778 : ¬Nat.Prime 1778 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 889) (n := 1778)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1779 : ¬Nat.Prime 1779 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 593) (n := 1779)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1780 : ¬Nat.Prime 1780 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 890) (n := 1780)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1781 : ¬Nat.Prime 1781 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 137) (n := 1781)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1782 : ¬Nat.Prime 1782 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 891) (n := 1782)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1783 : Nat.count Nat.Prime 1783 = 275 := by
  rw [show 1783 = 1782 + 1 by norm_num, Nat.count_succ]
  rw [show 1782 = 1781 + 1 by norm_num, Nat.count_succ]
  rw [show 1781 = 1780 + 1 by norm_num, Nat.count_succ]
  rw [show 1780 = 1779 + 1 by norm_num, Nat.count_succ]
  rw [show 1779 = 1778 + 1 by norm_num, Nat.count_succ]
  rw [show 1778 = 1777 + 1 by norm_num, Nat.count_succ]
  rw [count_1777]
  simp [prime_1777, not_prime_1778, not_prime_1779, not_prime_1780, not_prime_1781, not_prime_1782]

theorem prime_1783 : (1783 : Nat).Prime := by norm_num

theorem nth_275 : Nat.nth Nat.Prime 275 = 1783 := by
  rw [← count_1783]
  exact Nat.nth_count prime_1783

theorem not_prime_1784 : ¬Nat.Prime 1784 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 892) (n := 1784)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1785 : ¬Nat.Prime 1785 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 595) (n := 1785)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1786 : ¬Nat.Prime 1786 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 893) (n := 1786)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1787 : Nat.count Nat.Prime 1787 = 276 := by
  rw [show 1787 = 1786 + 1 by norm_num, Nat.count_succ]
  rw [show 1786 = 1785 + 1 by norm_num, Nat.count_succ]
  rw [show 1785 = 1784 + 1 by norm_num, Nat.count_succ]
  rw [show 1784 = 1783 + 1 by norm_num, Nat.count_succ]
  rw [count_1783]
  simp [prime_1783, not_prime_1784, not_prime_1785, not_prime_1786]

theorem prime_1787 : (1787 : Nat).Prime := by norm_num

theorem nth_276 : Nat.nth Nat.Prime 276 = 1787 := by
  rw [← count_1787]
  exact Nat.nth_count prime_1787

theorem not_prime_1788 : ¬Nat.Prime 1788 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 894) (n := 1788)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1789 : Nat.count Nat.Prime 1789 = 277 := by
  rw [show 1789 = 1788 + 1 by norm_num, Nat.count_succ]
  rw [show 1788 = 1787 + 1 by norm_num, Nat.count_succ]
  rw [count_1787]
  simp [prime_1787, not_prime_1788]

theorem prime_1789 : (1789 : Nat).Prime := by norm_num

theorem nth_277 : Nat.nth Nat.Prime 277 = 1789 := by
  rw [← count_1789]
  exact Nat.nth_count prime_1789

theorem not_prime_1790 : ¬Nat.Prime 1790 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 895) (n := 1790)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1791 : ¬Nat.Prime 1791 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 597) (n := 1791)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1792 : ¬Nat.Prime 1792 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 896) (n := 1792)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1793 : ¬Nat.Prime 1793 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 163) (n := 1793)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1794 : ¬Nat.Prime 1794 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 897) (n := 1794)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1795 : ¬Nat.Prime 1795 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 359) (n := 1795)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1796 : ¬Nat.Prime 1796 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 898) (n := 1796)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1797 : ¬Nat.Prime 1797 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 599) (n := 1797)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1798 : ¬Nat.Prime 1798 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 899) (n := 1798)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1799 : ¬Nat.Prime 1799 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 257) (n := 1799)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1800 : ¬Nat.Prime 1800 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 900) (n := 1800)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1801 : Nat.count Nat.Prime 1801 = 278 := by
  rw [show 1801 = 1800 + 1 by norm_num, Nat.count_succ]
  rw [show 1800 = 1799 + 1 by norm_num, Nat.count_succ]
  rw [show 1799 = 1798 + 1 by norm_num, Nat.count_succ]
  rw [show 1798 = 1797 + 1 by norm_num, Nat.count_succ]
  rw [show 1797 = 1796 + 1 by norm_num, Nat.count_succ]
  rw [show 1796 = 1795 + 1 by norm_num, Nat.count_succ]
  rw [show 1795 = 1794 + 1 by norm_num, Nat.count_succ]
  rw [show 1794 = 1793 + 1 by norm_num, Nat.count_succ]
  rw [show 1793 = 1792 + 1 by norm_num, Nat.count_succ]
  rw [show 1792 = 1791 + 1 by norm_num, Nat.count_succ]
  rw [show 1791 = 1790 + 1 by norm_num, Nat.count_succ]
  rw [show 1790 = 1789 + 1 by norm_num, Nat.count_succ]
  rw [count_1789]
  simp [prime_1789, not_prime_1790, not_prime_1791, not_prime_1792, not_prime_1793, not_prime_1794, not_prime_1795, not_prime_1796, not_prime_1797, not_prime_1798, not_prime_1799, not_prime_1800]

theorem prime_1801 : (1801 : Nat).Prime := by norm_num

theorem nth_278 : Nat.nth Nat.Prime 278 = 1801 := by
  rw [← count_1801]
  exact Nat.nth_count prime_1801

theorem not_prime_1802 : ¬Nat.Prime 1802 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 901) (n := 1802)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1803 : ¬Nat.Prime 1803 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 601) (n := 1803)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1804 : ¬Nat.Prime 1804 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 902) (n := 1804)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1805 : ¬Nat.Prime 1805 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 361) (n := 1805)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1806 : ¬Nat.Prime 1806 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 903) (n := 1806)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1807 : ¬Nat.Prime 1807 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 139) (n := 1807)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1808 : ¬Nat.Prime 1808 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 904) (n := 1808)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1809 : ¬Nat.Prime 1809 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 603) (n := 1809)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1810 : ¬Nat.Prime 1810 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 905) (n := 1810)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1811 : Nat.count Nat.Prime 1811 = 279 := by
  rw [show 1811 = 1810 + 1 by norm_num, Nat.count_succ]
  rw [show 1810 = 1809 + 1 by norm_num, Nat.count_succ]
  rw [show 1809 = 1808 + 1 by norm_num, Nat.count_succ]
  rw [show 1808 = 1807 + 1 by norm_num, Nat.count_succ]
  rw [show 1807 = 1806 + 1 by norm_num, Nat.count_succ]
  rw [show 1806 = 1805 + 1 by norm_num, Nat.count_succ]
  rw [show 1805 = 1804 + 1 by norm_num, Nat.count_succ]
  rw [show 1804 = 1803 + 1 by norm_num, Nat.count_succ]
  rw [show 1803 = 1802 + 1 by norm_num, Nat.count_succ]
  rw [show 1802 = 1801 + 1 by norm_num, Nat.count_succ]
  rw [count_1801]
  simp [prime_1801, not_prime_1802, not_prime_1803, not_prime_1804, not_prime_1805, not_prime_1806, not_prime_1807, not_prime_1808, not_prime_1809, not_prime_1810]

theorem prime_1811 : (1811 : Nat).Prime := by norm_num

theorem nth_279 : Nat.nth Nat.Prime 279 = 1811 := by
  rw [← count_1811]
  exact Nat.nth_count prime_1811

theorem not_prime_1812 : ¬Nat.Prime 1812 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 906) (n := 1812)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1813 : ¬Nat.Prime 1813 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 259) (n := 1813)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1814 : ¬Nat.Prime 1814 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 907) (n := 1814)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1815 : ¬Nat.Prime 1815 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 605) (n := 1815)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1816 : ¬Nat.Prime 1816 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 908) (n := 1816)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1817 : ¬Nat.Prime 1817 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 79) (n := 1817)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1818 : ¬Nat.Prime 1818 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 909) (n := 1818)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1819 : ¬Nat.Prime 1819 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 107) (n := 1819)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1820 : ¬Nat.Prime 1820 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 910) (n := 1820)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1821 : ¬Nat.Prime 1821 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 607) (n := 1821)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1822 : ¬Nat.Prime 1822 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 911) (n := 1822)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1823 : Nat.count Nat.Prime 1823 = 280 := by
  rw [show 1823 = 1822 + 1 by norm_num, Nat.count_succ]
  rw [show 1822 = 1821 + 1 by norm_num, Nat.count_succ]
  rw [show 1821 = 1820 + 1 by norm_num, Nat.count_succ]
  rw [show 1820 = 1819 + 1 by norm_num, Nat.count_succ]
  rw [show 1819 = 1818 + 1 by norm_num, Nat.count_succ]
  rw [show 1818 = 1817 + 1 by norm_num, Nat.count_succ]
  rw [show 1817 = 1816 + 1 by norm_num, Nat.count_succ]
  rw [show 1816 = 1815 + 1 by norm_num, Nat.count_succ]
  rw [show 1815 = 1814 + 1 by norm_num, Nat.count_succ]
  rw [show 1814 = 1813 + 1 by norm_num, Nat.count_succ]
  rw [show 1813 = 1812 + 1 by norm_num, Nat.count_succ]
  rw [show 1812 = 1811 + 1 by norm_num, Nat.count_succ]
  rw [count_1811]
  simp [prime_1811, not_prime_1812, not_prime_1813, not_prime_1814, not_prime_1815, not_prime_1816, not_prime_1817, not_prime_1818, not_prime_1819, not_prime_1820, not_prime_1821, not_prime_1822]

theorem prime_1823 : (1823 : Nat).Prime := by norm_num

theorem nth_280 : Nat.nth Nat.Prime 280 = 1823 := by
  rw [← count_1823]
  exact Nat.nth_count prime_1823

theorem not_prime_1824 : ¬Nat.Prime 1824 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 912) (n := 1824)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1825 : ¬Nat.Prime 1825 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 365) (n := 1825)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1826 : ¬Nat.Prime 1826 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 913) (n := 1826)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1827 : ¬Nat.Prime 1827 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 609) (n := 1827)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1828 : ¬Nat.Prime 1828 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 914) (n := 1828)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1829 : ¬Nat.Prime 1829 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 59) (n := 1829)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1830 : ¬Nat.Prime 1830 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 915) (n := 1830)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1831 : Nat.count Nat.Prime 1831 = 281 := by
  rw [show 1831 = 1830 + 1 by norm_num, Nat.count_succ]
  rw [show 1830 = 1829 + 1 by norm_num, Nat.count_succ]
  rw [show 1829 = 1828 + 1 by norm_num, Nat.count_succ]
  rw [show 1828 = 1827 + 1 by norm_num, Nat.count_succ]
  rw [show 1827 = 1826 + 1 by norm_num, Nat.count_succ]
  rw [show 1826 = 1825 + 1 by norm_num, Nat.count_succ]
  rw [show 1825 = 1824 + 1 by norm_num, Nat.count_succ]
  rw [show 1824 = 1823 + 1 by norm_num, Nat.count_succ]
  rw [count_1823]
  simp [prime_1823, not_prime_1824, not_prime_1825, not_prime_1826, not_prime_1827, not_prime_1828, not_prime_1829, not_prime_1830]

theorem prime_1831 : (1831 : Nat).Prime := by norm_num

theorem nth_281 : Nat.nth Nat.Prime 281 = 1831 := by
  rw [← count_1831]
  exact Nat.nth_count prime_1831

theorem not_prime_1832 : ¬Nat.Prime 1832 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 916) (n := 1832)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1833 : ¬Nat.Prime 1833 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 611) (n := 1833)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1834 : ¬Nat.Prime 1834 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 917) (n := 1834)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1835 : ¬Nat.Prime 1835 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 367) (n := 1835)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1836 : ¬Nat.Prime 1836 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 918) (n := 1836)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1837 : ¬Nat.Prime 1837 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 167) (n := 1837)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1838 : ¬Nat.Prime 1838 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 919) (n := 1838)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1839 : ¬Nat.Prime 1839 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 613) (n := 1839)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1840 : ¬Nat.Prime 1840 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 920) (n := 1840)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1841 : ¬Nat.Prime 1841 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 263) (n := 1841)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1842 : ¬Nat.Prime 1842 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 921) (n := 1842)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1843 : ¬Nat.Prime 1843 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 97) (n := 1843)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1844 : ¬Nat.Prime 1844 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 922) (n := 1844)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1845 : ¬Nat.Prime 1845 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 615) (n := 1845)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1846 : ¬Nat.Prime 1846 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 923) (n := 1846)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1847 : Nat.count Nat.Prime 1847 = 282 := by
  rw [show 1847 = 1846 + 1 by norm_num, Nat.count_succ]
  rw [show 1846 = 1845 + 1 by norm_num, Nat.count_succ]
  rw [show 1845 = 1844 + 1 by norm_num, Nat.count_succ]
  rw [show 1844 = 1843 + 1 by norm_num, Nat.count_succ]
  rw [show 1843 = 1842 + 1 by norm_num, Nat.count_succ]
  rw [show 1842 = 1841 + 1 by norm_num, Nat.count_succ]
  rw [show 1841 = 1840 + 1 by norm_num, Nat.count_succ]
  rw [show 1840 = 1839 + 1 by norm_num, Nat.count_succ]
  rw [show 1839 = 1838 + 1 by norm_num, Nat.count_succ]
  rw [show 1838 = 1837 + 1 by norm_num, Nat.count_succ]
  rw [show 1837 = 1836 + 1 by norm_num, Nat.count_succ]
  rw [show 1836 = 1835 + 1 by norm_num, Nat.count_succ]
  rw [show 1835 = 1834 + 1 by norm_num, Nat.count_succ]
  rw [show 1834 = 1833 + 1 by norm_num, Nat.count_succ]
  rw [show 1833 = 1832 + 1 by norm_num, Nat.count_succ]
  rw [show 1832 = 1831 + 1 by norm_num, Nat.count_succ]
  rw [count_1831]
  simp [prime_1831, not_prime_1832, not_prime_1833, not_prime_1834, not_prime_1835, not_prime_1836, not_prime_1837, not_prime_1838, not_prime_1839, not_prime_1840, not_prime_1841, not_prime_1842, not_prime_1843, not_prime_1844, not_prime_1845, not_prime_1846]

theorem prime_1847 : (1847 : Nat).Prime := by norm_num

theorem nth_282 : Nat.nth Nat.Prime 282 = 1847 := by
  rw [← count_1847]
  exact Nat.nth_count prime_1847

theorem not_prime_1848 : ¬Nat.Prime 1848 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 924) (n := 1848)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1849 : ¬Nat.Prime 1849 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 43) (n := 1849)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1850 : ¬Nat.Prime 1850 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 925) (n := 1850)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1851 : ¬Nat.Prime 1851 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 617) (n := 1851)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1852 : ¬Nat.Prime 1852 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 926) (n := 1852)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1853 : ¬Nat.Prime 1853 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 109) (n := 1853)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1854 : ¬Nat.Prime 1854 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 927) (n := 1854)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1855 : ¬Nat.Prime 1855 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 371) (n := 1855)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1856 : ¬Nat.Prime 1856 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 928) (n := 1856)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1857 : ¬Nat.Prime 1857 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 619) (n := 1857)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1858 : ¬Nat.Prime 1858 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 929) (n := 1858)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1859 : ¬Nat.Prime 1859 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 169) (n := 1859)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1860 : ¬Nat.Prime 1860 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 930) (n := 1860)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1861 : Nat.count Nat.Prime 1861 = 283 := by
  rw [show 1861 = 1860 + 1 by norm_num, Nat.count_succ]
  rw [show 1860 = 1859 + 1 by norm_num, Nat.count_succ]
  rw [show 1859 = 1858 + 1 by norm_num, Nat.count_succ]
  rw [show 1858 = 1857 + 1 by norm_num, Nat.count_succ]
  rw [show 1857 = 1856 + 1 by norm_num, Nat.count_succ]
  rw [show 1856 = 1855 + 1 by norm_num, Nat.count_succ]
  rw [show 1855 = 1854 + 1 by norm_num, Nat.count_succ]
  rw [show 1854 = 1853 + 1 by norm_num, Nat.count_succ]
  rw [show 1853 = 1852 + 1 by norm_num, Nat.count_succ]
  rw [show 1852 = 1851 + 1 by norm_num, Nat.count_succ]
  rw [show 1851 = 1850 + 1 by norm_num, Nat.count_succ]
  rw [show 1850 = 1849 + 1 by norm_num, Nat.count_succ]
  rw [show 1849 = 1848 + 1 by norm_num, Nat.count_succ]
  rw [show 1848 = 1847 + 1 by norm_num, Nat.count_succ]
  rw [count_1847]
  simp [prime_1847, not_prime_1848, not_prime_1849, not_prime_1850, not_prime_1851, not_prime_1852, not_prime_1853, not_prime_1854, not_prime_1855, not_prime_1856, not_prime_1857, not_prime_1858, not_prime_1859, not_prime_1860]

theorem prime_1861 : (1861 : Nat).Prime := by norm_num

theorem nth_283 : Nat.nth Nat.Prime 283 = 1861 := by
  rw [← count_1861]
  exact Nat.nth_count prime_1861

theorem not_prime_1862 : ¬Nat.Prime 1862 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 931) (n := 1862)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1863 : ¬Nat.Prime 1863 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 621) (n := 1863)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1864 : ¬Nat.Prime 1864 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 932) (n := 1864)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1865 : ¬Nat.Prime 1865 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 373) (n := 1865)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1866 : ¬Nat.Prime 1866 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 933) (n := 1866)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1867 : Nat.count Nat.Prime 1867 = 284 := by
  rw [show 1867 = 1866 + 1 by norm_num, Nat.count_succ]
  rw [show 1866 = 1865 + 1 by norm_num, Nat.count_succ]
  rw [show 1865 = 1864 + 1 by norm_num, Nat.count_succ]
  rw [show 1864 = 1863 + 1 by norm_num, Nat.count_succ]
  rw [show 1863 = 1862 + 1 by norm_num, Nat.count_succ]
  rw [show 1862 = 1861 + 1 by norm_num, Nat.count_succ]
  rw [count_1861]
  simp [prime_1861, not_prime_1862, not_prime_1863, not_prime_1864, not_prime_1865, not_prime_1866]

theorem prime_1867 : (1867 : Nat).Prime := by norm_num

theorem nth_284 : Nat.nth Nat.Prime 284 = 1867 := by
  rw [← count_1867]
  exact Nat.nth_count prime_1867

theorem not_prime_1868 : ¬Nat.Prime 1868 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 934) (n := 1868)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1869 : ¬Nat.Prime 1869 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 623) (n := 1869)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1870 : ¬Nat.Prime 1870 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 935) (n := 1870)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1871 : Nat.count Nat.Prime 1871 = 285 := by
  rw [show 1871 = 1870 + 1 by norm_num, Nat.count_succ]
  rw [show 1870 = 1869 + 1 by norm_num, Nat.count_succ]
  rw [show 1869 = 1868 + 1 by norm_num, Nat.count_succ]
  rw [show 1868 = 1867 + 1 by norm_num, Nat.count_succ]
  rw [count_1867]
  simp [prime_1867, not_prime_1868, not_prime_1869, not_prime_1870]

theorem prime_1871 : (1871 : Nat).Prime := by norm_num

theorem nth_285 : Nat.nth Nat.Prime 285 = 1871 := by
  rw [← count_1871]
  exact Nat.nth_count prime_1871

theorem not_prime_1872 : ¬Nat.Prime 1872 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 936) (n := 1872)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1873 : Nat.count Nat.Prime 1873 = 286 := by
  rw [show 1873 = 1872 + 1 by norm_num, Nat.count_succ]
  rw [show 1872 = 1871 + 1 by norm_num, Nat.count_succ]
  rw [count_1871]
  simp [prime_1871, not_prime_1872]

theorem prime_1873 : (1873 : Nat).Prime := by norm_num

theorem nth_286 : Nat.nth Nat.Prime 286 = 1873 := by
  rw [← count_1873]
  exact Nat.nth_count prime_1873

theorem not_prime_1874 : ¬Nat.Prime 1874 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 937) (n := 1874)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1875 : ¬Nat.Prime 1875 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 625) (n := 1875)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1876 : ¬Nat.Prime 1876 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 938) (n := 1876)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1877 : Nat.count Nat.Prime 1877 = 287 := by
  rw [show 1877 = 1876 + 1 by norm_num, Nat.count_succ]
  rw [show 1876 = 1875 + 1 by norm_num, Nat.count_succ]
  rw [show 1875 = 1874 + 1 by norm_num, Nat.count_succ]
  rw [show 1874 = 1873 + 1 by norm_num, Nat.count_succ]
  rw [count_1873]
  simp [prime_1873, not_prime_1874, not_prime_1875, not_prime_1876]

theorem prime_1877 : (1877 : Nat).Prime := by norm_num

theorem nth_287 : Nat.nth Nat.Prime 287 = 1877 := by
  rw [← count_1877]
  exact Nat.nth_count prime_1877

theorem not_prime_1878 : ¬Nat.Prime 1878 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 939) (n := 1878)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1879 : Nat.count Nat.Prime 1879 = 288 := by
  rw [show 1879 = 1878 + 1 by norm_num, Nat.count_succ]
  rw [show 1878 = 1877 + 1 by norm_num, Nat.count_succ]
  rw [count_1877]
  simp [prime_1877, not_prime_1878]

theorem prime_1879 : (1879 : Nat).Prime := by norm_num

theorem nth_288 : Nat.nth Nat.Prime 288 = 1879 := by
  rw [← count_1879]
  exact Nat.nth_count prime_1879

theorem not_prime_1880 : ¬Nat.Prime 1880 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 940) (n := 1880)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1881 : ¬Nat.Prime 1881 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 627) (n := 1881)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1882 : ¬Nat.Prime 1882 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 941) (n := 1882)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1883 : ¬Nat.Prime 1883 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 269) (n := 1883)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1884 : ¬Nat.Prime 1884 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 942) (n := 1884)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1885 : ¬Nat.Prime 1885 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 377) (n := 1885)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1886 : ¬Nat.Prime 1886 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 943) (n := 1886)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1887 : ¬Nat.Prime 1887 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 629) (n := 1887)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1888 : ¬Nat.Prime 1888 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 944) (n := 1888)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1889 : Nat.count Nat.Prime 1889 = 289 := by
  rw [show 1889 = 1888 + 1 by norm_num, Nat.count_succ]
  rw [show 1888 = 1887 + 1 by norm_num, Nat.count_succ]
  rw [show 1887 = 1886 + 1 by norm_num, Nat.count_succ]
  rw [show 1886 = 1885 + 1 by norm_num, Nat.count_succ]
  rw [show 1885 = 1884 + 1 by norm_num, Nat.count_succ]
  rw [show 1884 = 1883 + 1 by norm_num, Nat.count_succ]
  rw [show 1883 = 1882 + 1 by norm_num, Nat.count_succ]
  rw [show 1882 = 1881 + 1 by norm_num, Nat.count_succ]
  rw [show 1881 = 1880 + 1 by norm_num, Nat.count_succ]
  rw [show 1880 = 1879 + 1 by norm_num, Nat.count_succ]
  rw [count_1879]
  simp [prime_1879, not_prime_1880, not_prime_1881, not_prime_1882, not_prime_1883, not_prime_1884, not_prime_1885, not_prime_1886, not_prime_1887, not_prime_1888]

theorem prime_1889 : (1889 : Nat).Prime := by norm_num

theorem nth_289 : Nat.nth Nat.Prime 289 = 1889 := by
  rw [← count_1889]
  exact Nat.nth_count prime_1889

theorem not_prime_1890 : ¬Nat.Prime 1890 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 945) (n := 1890)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1891 : ¬Nat.Prime 1891 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 61) (n := 1891)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1892 : ¬Nat.Prime 1892 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 946) (n := 1892)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1893 : ¬Nat.Prime 1893 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 631) (n := 1893)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1894 : ¬Nat.Prime 1894 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 947) (n := 1894)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1895 : ¬Nat.Prime 1895 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 379) (n := 1895)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1896 : ¬Nat.Prime 1896 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 948) (n := 1896)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1897 : ¬Nat.Prime 1897 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 271) (n := 1897)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1898 : ¬Nat.Prime 1898 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 949) (n := 1898)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1899 : ¬Nat.Prime 1899 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 633) (n := 1899)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1900 : ¬Nat.Prime 1900 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 950) (n := 1900)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1901 : Nat.count Nat.Prime 1901 = 290 := by
  rw [show 1901 = 1900 + 1 by norm_num, Nat.count_succ]
  rw [show 1900 = 1899 + 1 by norm_num, Nat.count_succ]
  rw [show 1899 = 1898 + 1 by norm_num, Nat.count_succ]
  rw [show 1898 = 1897 + 1 by norm_num, Nat.count_succ]
  rw [show 1897 = 1896 + 1 by norm_num, Nat.count_succ]
  rw [show 1896 = 1895 + 1 by norm_num, Nat.count_succ]
  rw [show 1895 = 1894 + 1 by norm_num, Nat.count_succ]
  rw [show 1894 = 1893 + 1 by norm_num, Nat.count_succ]
  rw [show 1893 = 1892 + 1 by norm_num, Nat.count_succ]
  rw [show 1892 = 1891 + 1 by norm_num, Nat.count_succ]
  rw [show 1891 = 1890 + 1 by norm_num, Nat.count_succ]
  rw [show 1890 = 1889 + 1 by norm_num, Nat.count_succ]
  rw [count_1889]
  simp [prime_1889, not_prime_1890, not_prime_1891, not_prime_1892, not_prime_1893, not_prime_1894, not_prime_1895, not_prime_1896, not_prime_1897, not_prime_1898, not_prime_1899, not_prime_1900]

theorem prime_1901 : (1901 : Nat).Prime := by norm_num

theorem nth_290 : Nat.nth Nat.Prime 290 = 1901 := by
  rw [← count_1901]
  exact Nat.nth_count prime_1901

theorem not_prime_1902 : ¬Nat.Prime 1902 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 951) (n := 1902)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1903 : ¬Nat.Prime 1903 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 173) (n := 1903)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1904 : ¬Nat.Prime 1904 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 952) (n := 1904)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1905 : ¬Nat.Prime 1905 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 635) (n := 1905)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1906 : ¬Nat.Prime 1906 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 953) (n := 1906)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1907 : Nat.count Nat.Prime 1907 = 291 := by
  rw [show 1907 = 1906 + 1 by norm_num, Nat.count_succ]
  rw [show 1906 = 1905 + 1 by norm_num, Nat.count_succ]
  rw [show 1905 = 1904 + 1 by norm_num, Nat.count_succ]
  rw [show 1904 = 1903 + 1 by norm_num, Nat.count_succ]
  rw [show 1903 = 1902 + 1 by norm_num, Nat.count_succ]
  rw [show 1902 = 1901 + 1 by norm_num, Nat.count_succ]
  rw [count_1901]
  simp [prime_1901, not_prime_1902, not_prime_1903, not_prime_1904, not_prime_1905, not_prime_1906]

theorem prime_1907 : (1907 : Nat).Prime := by norm_num

theorem nth_291 : Nat.nth Nat.Prime 291 = 1907 := by
  rw [← count_1907]
  exact Nat.nth_count prime_1907

theorem not_prime_1908 : ¬Nat.Prime 1908 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 954) (n := 1908)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1909 : ¬Nat.Prime 1909 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 83) (n := 1909)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1910 : ¬Nat.Prime 1910 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 955) (n := 1910)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1911 : ¬Nat.Prime 1911 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 637) (n := 1911)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1912 : ¬Nat.Prime 1912 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 956) (n := 1912)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1913 : Nat.count Nat.Prime 1913 = 292 := by
  rw [show 1913 = 1912 + 1 by norm_num, Nat.count_succ]
  rw [show 1912 = 1911 + 1 by norm_num, Nat.count_succ]
  rw [show 1911 = 1910 + 1 by norm_num, Nat.count_succ]
  rw [show 1910 = 1909 + 1 by norm_num, Nat.count_succ]
  rw [show 1909 = 1908 + 1 by norm_num, Nat.count_succ]
  rw [show 1908 = 1907 + 1 by norm_num, Nat.count_succ]
  rw [count_1907]
  simp [prime_1907, not_prime_1908, not_prime_1909, not_prime_1910, not_prime_1911, not_prime_1912]

theorem prime_1913 : (1913 : Nat).Prime := by norm_num

theorem nth_292 : Nat.nth Nat.Prime 292 = 1913 := by
  rw [← count_1913]
  exact Nat.nth_count prime_1913

theorem not_prime_1914 : ¬Nat.Prime 1914 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 957) (n := 1914)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1915 : ¬Nat.Prime 1915 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 383) (n := 1915)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1916 : ¬Nat.Prime 1916 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 958) (n := 1916)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1917 : ¬Nat.Prime 1917 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 639) (n := 1917)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1918 : ¬Nat.Prime 1918 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 959) (n := 1918)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1919 : ¬Nat.Prime 1919 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 101) (n := 1919)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1920 : ¬Nat.Prime 1920 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 960) (n := 1920)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1921 : ¬Nat.Prime 1921 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 113) (n := 1921)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1922 : ¬Nat.Prime 1922 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 961) (n := 1922)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1923 : ¬Nat.Prime 1923 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 641) (n := 1923)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1924 : ¬Nat.Prime 1924 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 962) (n := 1924)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1925 : ¬Nat.Prime 1925 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 385) (n := 1925)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1926 : ¬Nat.Prime 1926 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 963) (n := 1926)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1927 : ¬Nat.Prime 1927 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 47) (n := 1927)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1928 : ¬Nat.Prime 1928 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 964) (n := 1928)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1929 : ¬Nat.Prime 1929 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 643) (n := 1929)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1930 : ¬Nat.Prime 1930 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 965) (n := 1930)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1931 : Nat.count Nat.Prime 1931 = 293 := by
  rw [show 1931 = 1930 + 1 by norm_num, Nat.count_succ]
  rw [show 1930 = 1929 + 1 by norm_num, Nat.count_succ]
  rw [show 1929 = 1928 + 1 by norm_num, Nat.count_succ]
  rw [show 1928 = 1927 + 1 by norm_num, Nat.count_succ]
  rw [show 1927 = 1926 + 1 by norm_num, Nat.count_succ]
  rw [show 1926 = 1925 + 1 by norm_num, Nat.count_succ]
  rw [show 1925 = 1924 + 1 by norm_num, Nat.count_succ]
  rw [show 1924 = 1923 + 1 by norm_num, Nat.count_succ]
  rw [show 1923 = 1922 + 1 by norm_num, Nat.count_succ]
  rw [show 1922 = 1921 + 1 by norm_num, Nat.count_succ]
  rw [show 1921 = 1920 + 1 by norm_num, Nat.count_succ]
  rw [show 1920 = 1919 + 1 by norm_num, Nat.count_succ]
  rw [show 1919 = 1918 + 1 by norm_num, Nat.count_succ]
  rw [show 1918 = 1917 + 1 by norm_num, Nat.count_succ]
  rw [show 1917 = 1916 + 1 by norm_num, Nat.count_succ]
  rw [show 1916 = 1915 + 1 by norm_num, Nat.count_succ]
  rw [show 1915 = 1914 + 1 by norm_num, Nat.count_succ]
  rw [show 1914 = 1913 + 1 by norm_num, Nat.count_succ]
  rw [count_1913]
  simp [prime_1913, not_prime_1914, not_prime_1915, not_prime_1916, not_prime_1917, not_prime_1918, not_prime_1919, not_prime_1920, not_prime_1921, not_prime_1922, not_prime_1923, not_prime_1924, not_prime_1925, not_prime_1926, not_prime_1927, not_prime_1928, not_prime_1929, not_prime_1930]

theorem prime_1931 : (1931 : Nat).Prime := by norm_num

theorem nth_293 : Nat.nth Nat.Prime 293 = 1931 := by
  rw [← count_1931]
  exact Nat.nth_count prime_1931

theorem not_prime_1932 : ¬Nat.Prime 1932 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 966) (n := 1932)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1933 : Nat.count Nat.Prime 1933 = 294 := by
  rw [show 1933 = 1932 + 1 by norm_num, Nat.count_succ]
  rw [show 1932 = 1931 + 1 by norm_num, Nat.count_succ]
  rw [count_1931]
  simp [prime_1931, not_prime_1932]

theorem prime_1933 : (1933 : Nat).Prime := by norm_num

theorem nth_294 : Nat.nth Nat.Prime 294 = 1933 := by
  rw [← count_1933]
  exact Nat.nth_count prime_1933

theorem not_prime_1934 : ¬Nat.Prime 1934 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 967) (n := 1934)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1935 : ¬Nat.Prime 1935 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 645) (n := 1935)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1936 : ¬Nat.Prime 1936 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 968) (n := 1936)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1937 : ¬Nat.Prime 1937 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 149) (n := 1937)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1938 : ¬Nat.Prime 1938 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 969) (n := 1938)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1939 : ¬Nat.Prime 1939 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 277) (n := 1939)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1940 : ¬Nat.Prime 1940 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 970) (n := 1940)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1941 : ¬Nat.Prime 1941 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 647) (n := 1941)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1942 : ¬Nat.Prime 1942 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 971) (n := 1942)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1943 : ¬Nat.Prime 1943 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 67) (n := 1943)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1944 : ¬Nat.Prime 1944 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 972) (n := 1944)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1945 : ¬Nat.Prime 1945 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 389) (n := 1945)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1946 : ¬Nat.Prime 1946 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 973) (n := 1946)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1947 : ¬Nat.Prime 1947 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 649) (n := 1947)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1948 : ¬Nat.Prime 1948 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 974) (n := 1948)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1949 : Nat.count Nat.Prime 1949 = 295 := by
  rw [show 1949 = 1948 + 1 by norm_num, Nat.count_succ]
  rw [show 1948 = 1947 + 1 by norm_num, Nat.count_succ]
  rw [show 1947 = 1946 + 1 by norm_num, Nat.count_succ]
  rw [show 1946 = 1945 + 1 by norm_num, Nat.count_succ]
  rw [show 1945 = 1944 + 1 by norm_num, Nat.count_succ]
  rw [show 1944 = 1943 + 1 by norm_num, Nat.count_succ]
  rw [show 1943 = 1942 + 1 by norm_num, Nat.count_succ]
  rw [show 1942 = 1941 + 1 by norm_num, Nat.count_succ]
  rw [show 1941 = 1940 + 1 by norm_num, Nat.count_succ]
  rw [show 1940 = 1939 + 1 by norm_num, Nat.count_succ]
  rw [show 1939 = 1938 + 1 by norm_num, Nat.count_succ]
  rw [show 1938 = 1937 + 1 by norm_num, Nat.count_succ]
  rw [show 1937 = 1936 + 1 by norm_num, Nat.count_succ]
  rw [show 1936 = 1935 + 1 by norm_num, Nat.count_succ]
  rw [show 1935 = 1934 + 1 by norm_num, Nat.count_succ]
  rw [show 1934 = 1933 + 1 by norm_num, Nat.count_succ]
  rw [count_1933]
  simp [prime_1933, not_prime_1934, not_prime_1935, not_prime_1936, not_prime_1937, not_prime_1938, not_prime_1939, not_prime_1940, not_prime_1941, not_prime_1942, not_prime_1943, not_prime_1944, not_prime_1945, not_prime_1946, not_prime_1947, not_prime_1948]

theorem prime_1949 : (1949 : Nat).Prime := by norm_num

theorem nth_295 : Nat.nth Nat.Prime 295 = 1949 := by
  rw [← count_1949]
  exact Nat.nth_count prime_1949

theorem not_prime_1950 : ¬Nat.Prime 1950 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 975) (n := 1950)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1951 : Nat.count Nat.Prime 1951 = 296 := by
  rw [show 1951 = 1950 + 1 by norm_num, Nat.count_succ]
  rw [show 1950 = 1949 + 1 by norm_num, Nat.count_succ]
  rw [count_1949]
  simp [prime_1949, not_prime_1950]

theorem prime_1951 : (1951 : Nat).Prime := by norm_num

theorem nth_296 : Nat.nth Nat.Prime 296 = 1951 := by
  rw [← count_1951]
  exact Nat.nth_count prime_1951

theorem not_prime_1952 : ¬Nat.Prime 1952 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 976) (n := 1952)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1953 : ¬Nat.Prime 1953 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 651) (n := 1953)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1954 : ¬Nat.Prime 1954 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 977) (n := 1954)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1955 : ¬Nat.Prime 1955 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 391) (n := 1955)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1956 : ¬Nat.Prime 1956 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 978) (n := 1956)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1957 : ¬Nat.Prime 1957 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 103) (n := 1957)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1958 : ¬Nat.Prime 1958 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 979) (n := 1958)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1959 : ¬Nat.Prime 1959 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 653) (n := 1959)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1960 : ¬Nat.Prime 1960 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 980) (n := 1960)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1961 : ¬Nat.Prime 1961 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 53) (n := 1961)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1962 : ¬Nat.Prime 1962 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 981) (n := 1962)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1963 : ¬Nat.Prime 1963 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 151) (n := 1963)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1964 : ¬Nat.Prime 1964 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 982) (n := 1964)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1965 : ¬Nat.Prime 1965 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 655) (n := 1965)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1966 : ¬Nat.Prime 1966 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 983) (n := 1966)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1967 : ¬Nat.Prime 1967 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 281) (n := 1967)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1968 : ¬Nat.Prime 1968 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 984) (n := 1968)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1969 : ¬Nat.Prime 1969 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 179) (n := 1969)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1970 : ¬Nat.Prime 1970 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 985) (n := 1970)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1971 : ¬Nat.Prime 1971 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 657) (n := 1971)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1972 : ¬Nat.Prime 1972 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 986) (n := 1972)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1973 : Nat.count Nat.Prime 1973 = 297 := by
  rw [show 1973 = 1972 + 1 by norm_num, Nat.count_succ]
  rw [show 1972 = 1971 + 1 by norm_num, Nat.count_succ]
  rw [show 1971 = 1970 + 1 by norm_num, Nat.count_succ]
  rw [show 1970 = 1969 + 1 by norm_num, Nat.count_succ]
  rw [show 1969 = 1968 + 1 by norm_num, Nat.count_succ]
  rw [show 1968 = 1967 + 1 by norm_num, Nat.count_succ]
  rw [show 1967 = 1966 + 1 by norm_num, Nat.count_succ]
  rw [show 1966 = 1965 + 1 by norm_num, Nat.count_succ]
  rw [show 1965 = 1964 + 1 by norm_num, Nat.count_succ]
  rw [show 1964 = 1963 + 1 by norm_num, Nat.count_succ]
  rw [show 1963 = 1962 + 1 by norm_num, Nat.count_succ]
  rw [show 1962 = 1961 + 1 by norm_num, Nat.count_succ]
  rw [show 1961 = 1960 + 1 by norm_num, Nat.count_succ]
  rw [show 1960 = 1959 + 1 by norm_num, Nat.count_succ]
  rw [show 1959 = 1958 + 1 by norm_num, Nat.count_succ]
  rw [show 1958 = 1957 + 1 by norm_num, Nat.count_succ]
  rw [show 1957 = 1956 + 1 by norm_num, Nat.count_succ]
  rw [show 1956 = 1955 + 1 by norm_num, Nat.count_succ]
  rw [show 1955 = 1954 + 1 by norm_num, Nat.count_succ]
  rw [show 1954 = 1953 + 1 by norm_num, Nat.count_succ]
  rw [show 1953 = 1952 + 1 by norm_num, Nat.count_succ]
  rw [show 1952 = 1951 + 1 by norm_num, Nat.count_succ]
  rw [count_1951]
  simp [prime_1951, not_prime_1952, not_prime_1953, not_prime_1954, not_prime_1955, not_prime_1956, not_prime_1957, not_prime_1958, not_prime_1959, not_prime_1960, not_prime_1961, not_prime_1962, not_prime_1963, not_prime_1964, not_prime_1965, not_prime_1966, not_prime_1967, not_prime_1968, not_prime_1969, not_prime_1970, not_prime_1971, not_prime_1972]

theorem prime_1973 : (1973 : Nat).Prime := by norm_num

theorem nth_297 : Nat.nth Nat.Prime 297 = 1973 := by
  rw [← count_1973]
  exact Nat.nth_count prime_1973

theorem not_prime_1974 : ¬Nat.Prime 1974 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 987) (n := 1974)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1975 : ¬Nat.Prime 1975 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 395) (n := 1975)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1976 : ¬Nat.Prime 1976 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 988) (n := 1976)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1977 : ¬Nat.Prime 1977 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 659) (n := 1977)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1978 : ¬Nat.Prime 1978 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 989) (n := 1978)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1979 : Nat.count Nat.Prime 1979 = 298 := by
  rw [show 1979 = 1978 + 1 by norm_num, Nat.count_succ]
  rw [show 1978 = 1977 + 1 by norm_num, Nat.count_succ]
  rw [show 1977 = 1976 + 1 by norm_num, Nat.count_succ]
  rw [show 1976 = 1975 + 1 by norm_num, Nat.count_succ]
  rw [show 1975 = 1974 + 1 by norm_num, Nat.count_succ]
  rw [show 1974 = 1973 + 1 by norm_num, Nat.count_succ]
  rw [count_1973]
  simp [prime_1973, not_prime_1974, not_prime_1975, not_prime_1976, not_prime_1977, not_prime_1978]

theorem prime_1979 : (1979 : Nat).Prime := by norm_num

theorem nth_298 : Nat.nth Nat.Prime 298 = 1979 := by
  rw [← count_1979]
  exact Nat.nth_count prime_1979

theorem not_prime_1980 : ¬Nat.Prime 1980 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 990) (n := 1980)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1981 : ¬Nat.Prime 1981 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 283) (n := 1981)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1982 : ¬Nat.Prime 1982 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 991) (n := 1982)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1983 : ¬Nat.Prime 1983 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 661) (n := 1983)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1984 : ¬Nat.Prime 1984 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 992) (n := 1984)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1985 : ¬Nat.Prime 1985 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 397) (n := 1985)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1986 : ¬Nat.Prime 1986 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 993) (n := 1986)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1987 : Nat.count Nat.Prime 1987 = 299 := by
  rw [show 1987 = 1986 + 1 by norm_num, Nat.count_succ]
  rw [show 1986 = 1985 + 1 by norm_num, Nat.count_succ]
  rw [show 1985 = 1984 + 1 by norm_num, Nat.count_succ]
  rw [show 1984 = 1983 + 1 by norm_num, Nat.count_succ]
  rw [show 1983 = 1982 + 1 by norm_num, Nat.count_succ]
  rw [show 1982 = 1981 + 1 by norm_num, Nat.count_succ]
  rw [show 1981 = 1980 + 1 by norm_num, Nat.count_succ]
  rw [show 1980 = 1979 + 1 by norm_num, Nat.count_succ]
  rw [count_1979]
  simp [prime_1979, not_prime_1980, not_prime_1981, not_prime_1982, not_prime_1983, not_prime_1984, not_prime_1985, not_prime_1986]

theorem prime_1987 : (1987 : Nat).Prime := by norm_num

theorem nth_299 : Nat.nth Nat.Prime 299 = 1987 := by
  rw [← count_1987]
  exact Nat.nth_count prime_1987

end OeisA100474.PrimeCertificate
