import OeisA100474PrimeCertificate.Chunk11

/-! Kernel prime/count certificate, chunk 12 (300–324). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_1988 : ¬Nat.Prime 1988 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 994) (n := 1988)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1989 : ¬Nat.Prime 1989 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 663) (n := 1989)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1990 : ¬Nat.Prime 1990 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 995) (n := 1990)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1991 : ¬Nat.Prime 1991 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 181) (n := 1991)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1992 : ¬Nat.Prime 1992 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 996) (n := 1992)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1993 : Nat.count Nat.Prime 1993 = 300 := by
  rw [show 1993 = 1992 + 1 by norm_num, Nat.count_succ]
  rw [show 1992 = 1991 + 1 by norm_num, Nat.count_succ]
  rw [show 1991 = 1990 + 1 by norm_num, Nat.count_succ]
  rw [show 1990 = 1989 + 1 by norm_num, Nat.count_succ]
  rw [show 1989 = 1988 + 1 by norm_num, Nat.count_succ]
  rw [show 1988 = 1987 + 1 by norm_num, Nat.count_succ]
  rw [count_1987]
  simp [prime_1987, not_prime_1988, not_prime_1989, not_prime_1990, not_prime_1991, not_prime_1992]

theorem prime_1993 : (1993 : Nat).Prime := by norm_num

theorem nth_300 : Nat.nth Nat.Prime 300 = 1993 := by
  rw [← count_1993]
  exact Nat.nth_count prime_1993

theorem not_prime_1994 : ¬Nat.Prime 1994 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 997) (n := 1994)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1995 : ¬Nat.Prime 1995 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 665) (n := 1995)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1996 : ¬Nat.Prime 1996 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 998) (n := 1996)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1997 : Nat.count Nat.Prime 1997 = 301 := by
  rw [show 1997 = 1996 + 1 by norm_num, Nat.count_succ]
  rw [show 1996 = 1995 + 1 by norm_num, Nat.count_succ]
  rw [show 1995 = 1994 + 1 by norm_num, Nat.count_succ]
  rw [show 1994 = 1993 + 1 by norm_num, Nat.count_succ]
  rw [count_1993]
  simp [prime_1993, not_prime_1994, not_prime_1995, not_prime_1996]

theorem prime_1997 : (1997 : Nat).Prime := by norm_num

theorem nth_301 : Nat.nth Nat.Prime 301 = 1997 := by
  rw [← count_1997]
  exact Nat.nth_count prime_1997

theorem not_prime_1998 : ¬Nat.Prime 1998 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 999) (n := 1998)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1999 : Nat.count Nat.Prime 1999 = 302 := by
  rw [show 1999 = 1998 + 1 by norm_num, Nat.count_succ]
  rw [show 1998 = 1997 + 1 by norm_num, Nat.count_succ]
  rw [count_1997]
  simp [prime_1997, not_prime_1998]

theorem prime_1999 : (1999 : Nat).Prime := by norm_num

theorem nth_302 : Nat.nth Nat.Prime 302 = 1999 := by
  rw [← count_1999]
  exact Nat.nth_count prime_1999

theorem not_prime_2000 : ¬Nat.Prime 2000 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1000) (n := 2000)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2001 : ¬Nat.Prime 2001 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 667) (n := 2001)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2002 : ¬Nat.Prime 2002 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1001) (n := 2002)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2003 : Nat.count Nat.Prime 2003 = 303 := by
  rw [show 2003 = 2002 + 1 by norm_num, Nat.count_succ]
  rw [show 2002 = 2001 + 1 by norm_num, Nat.count_succ]
  rw [show 2001 = 2000 + 1 by norm_num, Nat.count_succ]
  rw [show 2000 = 1999 + 1 by norm_num, Nat.count_succ]
  rw [count_1999]
  simp [prime_1999, not_prime_2000, not_prime_2001, not_prime_2002]

theorem prime_2003 : (2003 : Nat).Prime := by norm_num

theorem nth_303 : Nat.nth Nat.Prime 303 = 2003 := by
  rw [← count_2003]
  exact Nat.nth_count prime_2003

theorem not_prime_2004 : ¬Nat.Prime 2004 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1002) (n := 2004)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2005 : ¬Nat.Prime 2005 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 401) (n := 2005)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2006 : ¬Nat.Prime 2006 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1003) (n := 2006)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2007 : ¬Nat.Prime 2007 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 669) (n := 2007)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2008 : ¬Nat.Prime 2008 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1004) (n := 2008)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2009 : ¬Nat.Prime 2009 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 287) (n := 2009)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2010 : ¬Nat.Prime 2010 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1005) (n := 2010)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2011 : Nat.count Nat.Prime 2011 = 304 := by
  rw [show 2011 = 2010 + 1 by norm_num, Nat.count_succ]
  rw [show 2010 = 2009 + 1 by norm_num, Nat.count_succ]
  rw [show 2009 = 2008 + 1 by norm_num, Nat.count_succ]
  rw [show 2008 = 2007 + 1 by norm_num, Nat.count_succ]
  rw [show 2007 = 2006 + 1 by norm_num, Nat.count_succ]
  rw [show 2006 = 2005 + 1 by norm_num, Nat.count_succ]
  rw [show 2005 = 2004 + 1 by norm_num, Nat.count_succ]
  rw [show 2004 = 2003 + 1 by norm_num, Nat.count_succ]
  rw [count_2003]
  simp [prime_2003, not_prime_2004, not_prime_2005, not_prime_2006, not_prime_2007, not_prime_2008, not_prime_2009, not_prime_2010]

theorem prime_2011 : (2011 : Nat).Prime := by norm_num

theorem nth_304 : Nat.nth Nat.Prime 304 = 2011 := by
  rw [← count_2011]
  exact Nat.nth_count prime_2011

theorem not_prime_2012 : ¬Nat.Prime 2012 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1006) (n := 2012)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2013 : ¬Nat.Prime 2013 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 671) (n := 2013)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2014 : ¬Nat.Prime 2014 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1007) (n := 2014)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2015 : ¬Nat.Prime 2015 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 403) (n := 2015)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2016 : ¬Nat.Prime 2016 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1008) (n := 2016)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2017 : Nat.count Nat.Prime 2017 = 305 := by
  rw [show 2017 = 2016 + 1 by norm_num, Nat.count_succ]
  rw [show 2016 = 2015 + 1 by norm_num, Nat.count_succ]
  rw [show 2015 = 2014 + 1 by norm_num, Nat.count_succ]
  rw [show 2014 = 2013 + 1 by norm_num, Nat.count_succ]
  rw [show 2013 = 2012 + 1 by norm_num, Nat.count_succ]
  rw [show 2012 = 2011 + 1 by norm_num, Nat.count_succ]
  rw [count_2011]
  simp [prime_2011, not_prime_2012, not_prime_2013, not_prime_2014, not_prime_2015, not_prime_2016]

theorem prime_2017 : (2017 : Nat).Prime := by norm_num

theorem nth_305 : Nat.nth Nat.Prime 305 = 2017 := by
  rw [← count_2017]
  exact Nat.nth_count prime_2017

theorem not_prime_2018 : ¬Nat.Prime 2018 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1009) (n := 2018)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2019 : ¬Nat.Prime 2019 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 673) (n := 2019)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2020 : ¬Nat.Prime 2020 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1010) (n := 2020)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2021 : ¬Nat.Prime 2021 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 47) (n := 2021)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2022 : ¬Nat.Prime 2022 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1011) (n := 2022)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2023 : ¬Nat.Prime 2023 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 289) (n := 2023)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2024 : ¬Nat.Prime 2024 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1012) (n := 2024)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2025 : ¬Nat.Prime 2025 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 675) (n := 2025)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2026 : ¬Nat.Prime 2026 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1013) (n := 2026)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2027 : Nat.count Nat.Prime 2027 = 306 := by
  rw [show 2027 = 2026 + 1 by norm_num, Nat.count_succ]
  rw [show 2026 = 2025 + 1 by norm_num, Nat.count_succ]
  rw [show 2025 = 2024 + 1 by norm_num, Nat.count_succ]
  rw [show 2024 = 2023 + 1 by norm_num, Nat.count_succ]
  rw [show 2023 = 2022 + 1 by norm_num, Nat.count_succ]
  rw [show 2022 = 2021 + 1 by norm_num, Nat.count_succ]
  rw [show 2021 = 2020 + 1 by norm_num, Nat.count_succ]
  rw [show 2020 = 2019 + 1 by norm_num, Nat.count_succ]
  rw [show 2019 = 2018 + 1 by norm_num, Nat.count_succ]
  rw [show 2018 = 2017 + 1 by norm_num, Nat.count_succ]
  rw [count_2017]
  simp [prime_2017, not_prime_2018, not_prime_2019, not_prime_2020, not_prime_2021, not_prime_2022, not_prime_2023, not_prime_2024, not_prime_2025, not_prime_2026]

theorem prime_2027 : (2027 : Nat).Prime := by norm_num

theorem nth_306 : Nat.nth Nat.Prime 306 = 2027 := by
  rw [← count_2027]
  exact Nat.nth_count prime_2027

theorem not_prime_2028 : ¬Nat.Prime 2028 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1014) (n := 2028)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2029 : Nat.count Nat.Prime 2029 = 307 := by
  rw [show 2029 = 2028 + 1 by norm_num, Nat.count_succ]
  rw [show 2028 = 2027 + 1 by norm_num, Nat.count_succ]
  rw [count_2027]
  simp [prime_2027, not_prime_2028]

theorem prime_2029 : (2029 : Nat).Prime := by norm_num

theorem nth_307 : Nat.nth Nat.Prime 307 = 2029 := by
  rw [← count_2029]
  exact Nat.nth_count prime_2029

theorem not_prime_2030 : ¬Nat.Prime 2030 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1015) (n := 2030)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2031 : ¬Nat.Prime 2031 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 677) (n := 2031)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2032 : ¬Nat.Prime 2032 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1016) (n := 2032)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2033 : ¬Nat.Prime 2033 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 107) (n := 2033)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2034 : ¬Nat.Prime 2034 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1017) (n := 2034)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2035 : ¬Nat.Prime 2035 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 407) (n := 2035)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2036 : ¬Nat.Prime 2036 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1018) (n := 2036)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2037 : ¬Nat.Prime 2037 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 679) (n := 2037)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2038 : ¬Nat.Prime 2038 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1019) (n := 2038)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2039 : Nat.count Nat.Prime 2039 = 308 := by
  rw [show 2039 = 2038 + 1 by norm_num, Nat.count_succ]
  rw [show 2038 = 2037 + 1 by norm_num, Nat.count_succ]
  rw [show 2037 = 2036 + 1 by norm_num, Nat.count_succ]
  rw [show 2036 = 2035 + 1 by norm_num, Nat.count_succ]
  rw [show 2035 = 2034 + 1 by norm_num, Nat.count_succ]
  rw [show 2034 = 2033 + 1 by norm_num, Nat.count_succ]
  rw [show 2033 = 2032 + 1 by norm_num, Nat.count_succ]
  rw [show 2032 = 2031 + 1 by norm_num, Nat.count_succ]
  rw [show 2031 = 2030 + 1 by norm_num, Nat.count_succ]
  rw [show 2030 = 2029 + 1 by norm_num, Nat.count_succ]
  rw [count_2029]
  simp [prime_2029, not_prime_2030, not_prime_2031, not_prime_2032, not_prime_2033, not_prime_2034, not_prime_2035, not_prime_2036, not_prime_2037, not_prime_2038]

theorem prime_2039 : (2039 : Nat).Prime := by norm_num

theorem nth_308 : Nat.nth Nat.Prime 308 = 2039 := by
  rw [← count_2039]
  exact Nat.nth_count prime_2039

theorem not_prime_2040 : ¬Nat.Prime 2040 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1020) (n := 2040)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2041 : ¬Nat.Prime 2041 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 157) (n := 2041)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2042 : ¬Nat.Prime 2042 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1021) (n := 2042)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2043 : ¬Nat.Prime 2043 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 681) (n := 2043)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2044 : ¬Nat.Prime 2044 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1022) (n := 2044)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2045 : ¬Nat.Prime 2045 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 409) (n := 2045)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2046 : ¬Nat.Prime 2046 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1023) (n := 2046)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2047 : ¬Nat.Prime 2047 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 89) (n := 2047)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2048 : ¬Nat.Prime 2048 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1024) (n := 2048)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2049 : ¬Nat.Prime 2049 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 683) (n := 2049)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2050 : ¬Nat.Prime 2050 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1025) (n := 2050)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2051 : ¬Nat.Prime 2051 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 293) (n := 2051)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2052 : ¬Nat.Prime 2052 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1026) (n := 2052)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2053 : Nat.count Nat.Prime 2053 = 309 := by
  rw [show 2053 = 2052 + 1 by norm_num, Nat.count_succ]
  rw [show 2052 = 2051 + 1 by norm_num, Nat.count_succ]
  rw [show 2051 = 2050 + 1 by norm_num, Nat.count_succ]
  rw [show 2050 = 2049 + 1 by norm_num, Nat.count_succ]
  rw [show 2049 = 2048 + 1 by norm_num, Nat.count_succ]
  rw [show 2048 = 2047 + 1 by norm_num, Nat.count_succ]
  rw [show 2047 = 2046 + 1 by norm_num, Nat.count_succ]
  rw [show 2046 = 2045 + 1 by norm_num, Nat.count_succ]
  rw [show 2045 = 2044 + 1 by norm_num, Nat.count_succ]
  rw [show 2044 = 2043 + 1 by norm_num, Nat.count_succ]
  rw [show 2043 = 2042 + 1 by norm_num, Nat.count_succ]
  rw [show 2042 = 2041 + 1 by norm_num, Nat.count_succ]
  rw [show 2041 = 2040 + 1 by norm_num, Nat.count_succ]
  rw [show 2040 = 2039 + 1 by norm_num, Nat.count_succ]
  rw [count_2039]
  simp [prime_2039, not_prime_2040, not_prime_2041, not_prime_2042, not_prime_2043, not_prime_2044, not_prime_2045, not_prime_2046, not_prime_2047, not_prime_2048, not_prime_2049, not_prime_2050, not_prime_2051, not_prime_2052]

theorem prime_2053 : (2053 : Nat).Prime := by norm_num

theorem nth_309 : Nat.nth Nat.Prime 309 = 2053 := by
  rw [← count_2053]
  exact Nat.nth_count prime_2053

theorem not_prime_2054 : ¬Nat.Prime 2054 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1027) (n := 2054)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2055 : ¬Nat.Prime 2055 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 685) (n := 2055)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2056 : ¬Nat.Prime 2056 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1028) (n := 2056)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2057 : ¬Nat.Prime 2057 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 187) (n := 2057)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2058 : ¬Nat.Prime 2058 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1029) (n := 2058)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2059 : ¬Nat.Prime 2059 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 71) (n := 2059)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2060 : ¬Nat.Prime 2060 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1030) (n := 2060)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2061 : ¬Nat.Prime 2061 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 687) (n := 2061)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2062 : ¬Nat.Prime 2062 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1031) (n := 2062)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2063 : Nat.count Nat.Prime 2063 = 310 := by
  rw [show 2063 = 2062 + 1 by norm_num, Nat.count_succ]
  rw [show 2062 = 2061 + 1 by norm_num, Nat.count_succ]
  rw [show 2061 = 2060 + 1 by norm_num, Nat.count_succ]
  rw [show 2060 = 2059 + 1 by norm_num, Nat.count_succ]
  rw [show 2059 = 2058 + 1 by norm_num, Nat.count_succ]
  rw [show 2058 = 2057 + 1 by norm_num, Nat.count_succ]
  rw [show 2057 = 2056 + 1 by norm_num, Nat.count_succ]
  rw [show 2056 = 2055 + 1 by norm_num, Nat.count_succ]
  rw [show 2055 = 2054 + 1 by norm_num, Nat.count_succ]
  rw [show 2054 = 2053 + 1 by norm_num, Nat.count_succ]
  rw [count_2053]
  simp [prime_2053, not_prime_2054, not_prime_2055, not_prime_2056, not_prime_2057, not_prime_2058, not_prime_2059, not_prime_2060, not_prime_2061, not_prime_2062]

theorem prime_2063 : (2063 : Nat).Prime := by norm_num

theorem nth_310 : Nat.nth Nat.Prime 310 = 2063 := by
  rw [← count_2063]
  exact Nat.nth_count prime_2063

theorem not_prime_2064 : ¬Nat.Prime 2064 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1032) (n := 2064)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2065 : ¬Nat.Prime 2065 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 413) (n := 2065)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2066 : ¬Nat.Prime 2066 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1033) (n := 2066)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2067 : ¬Nat.Prime 2067 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 689) (n := 2067)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2068 : ¬Nat.Prime 2068 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1034) (n := 2068)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2069 : Nat.count Nat.Prime 2069 = 311 := by
  rw [show 2069 = 2068 + 1 by norm_num, Nat.count_succ]
  rw [show 2068 = 2067 + 1 by norm_num, Nat.count_succ]
  rw [show 2067 = 2066 + 1 by norm_num, Nat.count_succ]
  rw [show 2066 = 2065 + 1 by norm_num, Nat.count_succ]
  rw [show 2065 = 2064 + 1 by norm_num, Nat.count_succ]
  rw [show 2064 = 2063 + 1 by norm_num, Nat.count_succ]
  rw [count_2063]
  simp [prime_2063, not_prime_2064, not_prime_2065, not_prime_2066, not_prime_2067, not_prime_2068]

theorem prime_2069 : (2069 : Nat).Prime := by norm_num

theorem nth_311 : Nat.nth Nat.Prime 311 = 2069 := by
  rw [← count_2069]
  exact Nat.nth_count prime_2069

theorem not_prime_2070 : ¬Nat.Prime 2070 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1035) (n := 2070)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2071 : ¬Nat.Prime 2071 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 109) (n := 2071)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2072 : ¬Nat.Prime 2072 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1036) (n := 2072)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2073 : ¬Nat.Prime 2073 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 691) (n := 2073)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2074 : ¬Nat.Prime 2074 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1037) (n := 2074)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2075 : ¬Nat.Prime 2075 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 415) (n := 2075)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2076 : ¬Nat.Prime 2076 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1038) (n := 2076)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2077 : ¬Nat.Prime 2077 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 67) (n := 2077)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2078 : ¬Nat.Prime 2078 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1039) (n := 2078)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2079 : ¬Nat.Prime 2079 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 693) (n := 2079)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2080 : ¬Nat.Prime 2080 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1040) (n := 2080)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2081 : Nat.count Nat.Prime 2081 = 312 := by
  rw [show 2081 = 2080 + 1 by norm_num, Nat.count_succ]
  rw [show 2080 = 2079 + 1 by norm_num, Nat.count_succ]
  rw [show 2079 = 2078 + 1 by norm_num, Nat.count_succ]
  rw [show 2078 = 2077 + 1 by norm_num, Nat.count_succ]
  rw [show 2077 = 2076 + 1 by norm_num, Nat.count_succ]
  rw [show 2076 = 2075 + 1 by norm_num, Nat.count_succ]
  rw [show 2075 = 2074 + 1 by norm_num, Nat.count_succ]
  rw [show 2074 = 2073 + 1 by norm_num, Nat.count_succ]
  rw [show 2073 = 2072 + 1 by norm_num, Nat.count_succ]
  rw [show 2072 = 2071 + 1 by norm_num, Nat.count_succ]
  rw [show 2071 = 2070 + 1 by norm_num, Nat.count_succ]
  rw [show 2070 = 2069 + 1 by norm_num, Nat.count_succ]
  rw [count_2069]
  simp [prime_2069, not_prime_2070, not_prime_2071, not_prime_2072, not_prime_2073, not_prime_2074, not_prime_2075, not_prime_2076, not_prime_2077, not_prime_2078, not_prime_2079, not_prime_2080]

theorem prime_2081 : (2081 : Nat).Prime := by norm_num

theorem nth_312 : Nat.nth Nat.Prime 312 = 2081 := by
  rw [← count_2081]
  exact Nat.nth_count prime_2081

theorem not_prime_2082 : ¬Nat.Prime 2082 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1041) (n := 2082)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2083 : Nat.count Nat.Prime 2083 = 313 := by
  rw [show 2083 = 2082 + 1 by norm_num, Nat.count_succ]
  rw [show 2082 = 2081 + 1 by norm_num, Nat.count_succ]
  rw [count_2081]
  simp [prime_2081, not_prime_2082]

theorem prime_2083 : (2083 : Nat).Prime := by norm_num

theorem nth_313 : Nat.nth Nat.Prime 313 = 2083 := by
  rw [← count_2083]
  exact Nat.nth_count prime_2083

theorem not_prime_2084 : ¬Nat.Prime 2084 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1042) (n := 2084)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2085 : ¬Nat.Prime 2085 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 695) (n := 2085)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2086 : ¬Nat.Prime 2086 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1043) (n := 2086)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2087 : Nat.count Nat.Prime 2087 = 314 := by
  rw [show 2087 = 2086 + 1 by norm_num, Nat.count_succ]
  rw [show 2086 = 2085 + 1 by norm_num, Nat.count_succ]
  rw [show 2085 = 2084 + 1 by norm_num, Nat.count_succ]
  rw [show 2084 = 2083 + 1 by norm_num, Nat.count_succ]
  rw [count_2083]
  simp [prime_2083, not_prime_2084, not_prime_2085, not_prime_2086]

theorem prime_2087 : (2087 : Nat).Prime := by norm_num

theorem nth_314 : Nat.nth Nat.Prime 314 = 2087 := by
  rw [← count_2087]
  exact Nat.nth_count prime_2087

theorem not_prime_2088 : ¬Nat.Prime 2088 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1044) (n := 2088)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2089 : Nat.count Nat.Prime 2089 = 315 := by
  rw [show 2089 = 2088 + 1 by norm_num, Nat.count_succ]
  rw [show 2088 = 2087 + 1 by norm_num, Nat.count_succ]
  rw [count_2087]
  simp [prime_2087, not_prime_2088]

theorem prime_2089 : (2089 : Nat).Prime := by norm_num

theorem nth_315 : Nat.nth Nat.Prime 315 = 2089 := by
  rw [← count_2089]
  exact Nat.nth_count prime_2089

theorem not_prime_2090 : ¬Nat.Prime 2090 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1045) (n := 2090)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2091 : ¬Nat.Prime 2091 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 697) (n := 2091)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2092 : ¬Nat.Prime 2092 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1046) (n := 2092)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2093 : ¬Nat.Prime 2093 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 299) (n := 2093)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2094 : ¬Nat.Prime 2094 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1047) (n := 2094)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2095 : ¬Nat.Prime 2095 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 419) (n := 2095)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2096 : ¬Nat.Prime 2096 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1048) (n := 2096)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2097 : ¬Nat.Prime 2097 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 699) (n := 2097)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2098 : ¬Nat.Prime 2098 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1049) (n := 2098)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2099 : Nat.count Nat.Prime 2099 = 316 := by
  rw [show 2099 = 2098 + 1 by norm_num, Nat.count_succ]
  rw [show 2098 = 2097 + 1 by norm_num, Nat.count_succ]
  rw [show 2097 = 2096 + 1 by norm_num, Nat.count_succ]
  rw [show 2096 = 2095 + 1 by norm_num, Nat.count_succ]
  rw [show 2095 = 2094 + 1 by norm_num, Nat.count_succ]
  rw [show 2094 = 2093 + 1 by norm_num, Nat.count_succ]
  rw [show 2093 = 2092 + 1 by norm_num, Nat.count_succ]
  rw [show 2092 = 2091 + 1 by norm_num, Nat.count_succ]
  rw [show 2091 = 2090 + 1 by norm_num, Nat.count_succ]
  rw [show 2090 = 2089 + 1 by norm_num, Nat.count_succ]
  rw [count_2089]
  simp [prime_2089, not_prime_2090, not_prime_2091, not_prime_2092, not_prime_2093, not_prime_2094, not_prime_2095, not_prime_2096, not_prime_2097, not_prime_2098]

theorem prime_2099 : (2099 : Nat).Prime := by norm_num

theorem nth_316 : Nat.nth Nat.Prime 316 = 2099 := by
  rw [← count_2099]
  exact Nat.nth_count prime_2099

theorem not_prime_2100 : ¬Nat.Prime 2100 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1050) (n := 2100)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2101 : ¬Nat.Prime 2101 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 191) (n := 2101)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2102 : ¬Nat.Prime 2102 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1051) (n := 2102)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2103 : ¬Nat.Prime 2103 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 701) (n := 2103)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2104 : ¬Nat.Prime 2104 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1052) (n := 2104)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2105 : ¬Nat.Prime 2105 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 421) (n := 2105)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2106 : ¬Nat.Prime 2106 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1053) (n := 2106)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2107 : ¬Nat.Prime 2107 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 301) (n := 2107)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2108 : ¬Nat.Prime 2108 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1054) (n := 2108)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2109 : ¬Nat.Prime 2109 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 703) (n := 2109)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2110 : ¬Nat.Prime 2110 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1055) (n := 2110)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2111 : Nat.count Nat.Prime 2111 = 317 := by
  rw [show 2111 = 2110 + 1 by norm_num, Nat.count_succ]
  rw [show 2110 = 2109 + 1 by norm_num, Nat.count_succ]
  rw [show 2109 = 2108 + 1 by norm_num, Nat.count_succ]
  rw [show 2108 = 2107 + 1 by norm_num, Nat.count_succ]
  rw [show 2107 = 2106 + 1 by norm_num, Nat.count_succ]
  rw [show 2106 = 2105 + 1 by norm_num, Nat.count_succ]
  rw [show 2105 = 2104 + 1 by norm_num, Nat.count_succ]
  rw [show 2104 = 2103 + 1 by norm_num, Nat.count_succ]
  rw [show 2103 = 2102 + 1 by norm_num, Nat.count_succ]
  rw [show 2102 = 2101 + 1 by norm_num, Nat.count_succ]
  rw [show 2101 = 2100 + 1 by norm_num, Nat.count_succ]
  rw [show 2100 = 2099 + 1 by norm_num, Nat.count_succ]
  rw [count_2099]
  simp [prime_2099, not_prime_2100, not_prime_2101, not_prime_2102, not_prime_2103, not_prime_2104, not_prime_2105, not_prime_2106, not_prime_2107, not_prime_2108, not_prime_2109, not_prime_2110]

theorem prime_2111 : (2111 : Nat).Prime := by norm_num

theorem nth_317 : Nat.nth Nat.Prime 317 = 2111 := by
  rw [← count_2111]
  exact Nat.nth_count prime_2111

theorem not_prime_2112 : ¬Nat.Prime 2112 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1056) (n := 2112)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2113 : Nat.count Nat.Prime 2113 = 318 := by
  rw [show 2113 = 2112 + 1 by norm_num, Nat.count_succ]
  rw [show 2112 = 2111 + 1 by norm_num, Nat.count_succ]
  rw [count_2111]
  simp [prime_2111, not_prime_2112]

theorem prime_2113 : (2113 : Nat).Prime := by norm_num

theorem nth_318 : Nat.nth Nat.Prime 318 = 2113 := by
  rw [← count_2113]
  exact Nat.nth_count prime_2113

theorem not_prime_2114 : ¬Nat.Prime 2114 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1057) (n := 2114)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2115 : ¬Nat.Prime 2115 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 705) (n := 2115)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2116 : ¬Nat.Prime 2116 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1058) (n := 2116)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2117 : ¬Nat.Prime 2117 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 73) (n := 2117)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2118 : ¬Nat.Prime 2118 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1059) (n := 2118)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2119 : ¬Nat.Prime 2119 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 163) (n := 2119)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2120 : ¬Nat.Prime 2120 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1060) (n := 2120)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2121 : ¬Nat.Prime 2121 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 707) (n := 2121)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2122 : ¬Nat.Prime 2122 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1061) (n := 2122)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2123 : ¬Nat.Prime 2123 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 193) (n := 2123)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2124 : ¬Nat.Prime 2124 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1062) (n := 2124)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2125 : ¬Nat.Prime 2125 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 425) (n := 2125)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2126 : ¬Nat.Prime 2126 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1063) (n := 2126)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2127 : ¬Nat.Prime 2127 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 709) (n := 2127)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2128 : ¬Nat.Prime 2128 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1064) (n := 2128)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2129 : Nat.count Nat.Prime 2129 = 319 := by
  rw [show 2129 = 2128 + 1 by norm_num, Nat.count_succ]
  rw [show 2128 = 2127 + 1 by norm_num, Nat.count_succ]
  rw [show 2127 = 2126 + 1 by norm_num, Nat.count_succ]
  rw [show 2126 = 2125 + 1 by norm_num, Nat.count_succ]
  rw [show 2125 = 2124 + 1 by norm_num, Nat.count_succ]
  rw [show 2124 = 2123 + 1 by norm_num, Nat.count_succ]
  rw [show 2123 = 2122 + 1 by norm_num, Nat.count_succ]
  rw [show 2122 = 2121 + 1 by norm_num, Nat.count_succ]
  rw [show 2121 = 2120 + 1 by norm_num, Nat.count_succ]
  rw [show 2120 = 2119 + 1 by norm_num, Nat.count_succ]
  rw [show 2119 = 2118 + 1 by norm_num, Nat.count_succ]
  rw [show 2118 = 2117 + 1 by norm_num, Nat.count_succ]
  rw [show 2117 = 2116 + 1 by norm_num, Nat.count_succ]
  rw [show 2116 = 2115 + 1 by norm_num, Nat.count_succ]
  rw [show 2115 = 2114 + 1 by norm_num, Nat.count_succ]
  rw [show 2114 = 2113 + 1 by norm_num, Nat.count_succ]
  rw [count_2113]
  simp [prime_2113, not_prime_2114, not_prime_2115, not_prime_2116, not_prime_2117, not_prime_2118, not_prime_2119, not_prime_2120, not_prime_2121, not_prime_2122, not_prime_2123, not_prime_2124, not_prime_2125, not_prime_2126, not_prime_2127, not_prime_2128]

theorem prime_2129 : (2129 : Nat).Prime := by norm_num

theorem nth_319 : Nat.nth Nat.Prime 319 = 2129 := by
  rw [← count_2129]
  exact Nat.nth_count prime_2129

theorem not_prime_2130 : ¬Nat.Prime 2130 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1065) (n := 2130)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2131 : Nat.count Nat.Prime 2131 = 320 := by
  rw [show 2131 = 2130 + 1 by norm_num, Nat.count_succ]
  rw [show 2130 = 2129 + 1 by norm_num, Nat.count_succ]
  rw [count_2129]
  simp [prime_2129, not_prime_2130]

theorem prime_2131 : (2131 : Nat).Prime := by norm_num

theorem nth_320 : Nat.nth Nat.Prime 320 = 2131 := by
  rw [← count_2131]
  exact Nat.nth_count prime_2131

theorem not_prime_2132 : ¬Nat.Prime 2132 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1066) (n := 2132)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2133 : ¬Nat.Prime 2133 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 711) (n := 2133)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2134 : ¬Nat.Prime 2134 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1067) (n := 2134)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2135 : ¬Nat.Prime 2135 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 427) (n := 2135)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2136 : ¬Nat.Prime 2136 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1068) (n := 2136)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2137 : Nat.count Nat.Prime 2137 = 321 := by
  rw [show 2137 = 2136 + 1 by norm_num, Nat.count_succ]
  rw [show 2136 = 2135 + 1 by norm_num, Nat.count_succ]
  rw [show 2135 = 2134 + 1 by norm_num, Nat.count_succ]
  rw [show 2134 = 2133 + 1 by norm_num, Nat.count_succ]
  rw [show 2133 = 2132 + 1 by norm_num, Nat.count_succ]
  rw [show 2132 = 2131 + 1 by norm_num, Nat.count_succ]
  rw [count_2131]
  simp [prime_2131, not_prime_2132, not_prime_2133, not_prime_2134, not_prime_2135, not_prime_2136]

theorem prime_2137 : (2137 : Nat).Prime := by norm_num

theorem nth_321 : Nat.nth Nat.Prime 321 = 2137 := by
  rw [← count_2137]
  exact Nat.nth_count prime_2137

theorem not_prime_2138 : ¬Nat.Prime 2138 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1069) (n := 2138)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2139 : ¬Nat.Prime 2139 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 713) (n := 2139)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2140 : ¬Nat.Prime 2140 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1070) (n := 2140)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2141 : Nat.count Nat.Prime 2141 = 322 := by
  rw [show 2141 = 2140 + 1 by norm_num, Nat.count_succ]
  rw [show 2140 = 2139 + 1 by norm_num, Nat.count_succ]
  rw [show 2139 = 2138 + 1 by norm_num, Nat.count_succ]
  rw [show 2138 = 2137 + 1 by norm_num, Nat.count_succ]
  rw [count_2137]
  simp [prime_2137, not_prime_2138, not_prime_2139, not_prime_2140]

theorem prime_2141 : (2141 : Nat).Prime := by norm_num

theorem nth_322 : Nat.nth Nat.Prime 322 = 2141 := by
  rw [← count_2141]
  exact Nat.nth_count prime_2141

theorem not_prime_2142 : ¬Nat.Prime 2142 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1071) (n := 2142)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2143 : Nat.count Nat.Prime 2143 = 323 := by
  rw [show 2143 = 2142 + 1 by norm_num, Nat.count_succ]
  rw [show 2142 = 2141 + 1 by norm_num, Nat.count_succ]
  rw [count_2141]
  simp [prime_2141, not_prime_2142]

theorem prime_2143 : (2143 : Nat).Prime := by norm_num

theorem nth_323 : Nat.nth Nat.Prime 323 = 2143 := by
  rw [← count_2143]
  exact Nat.nth_count prime_2143

theorem not_prime_2144 : ¬Nat.Prime 2144 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1072) (n := 2144)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2145 : ¬Nat.Prime 2145 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 715) (n := 2145)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2146 : ¬Nat.Prime 2146 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1073) (n := 2146)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2147 : ¬Nat.Prime 2147 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 113) (n := 2147)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2148 : ¬Nat.Prime 2148 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1074) (n := 2148)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2149 : ¬Nat.Prime 2149 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 307) (n := 2149)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2150 : ¬Nat.Prime 2150 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1075) (n := 2150)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2151 : ¬Nat.Prime 2151 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 717) (n := 2151)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2152 : ¬Nat.Prime 2152 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1076) (n := 2152)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2153 : Nat.count Nat.Prime 2153 = 324 := by
  rw [show 2153 = 2152 + 1 by norm_num, Nat.count_succ]
  rw [show 2152 = 2151 + 1 by norm_num, Nat.count_succ]
  rw [show 2151 = 2150 + 1 by norm_num, Nat.count_succ]
  rw [show 2150 = 2149 + 1 by norm_num, Nat.count_succ]
  rw [show 2149 = 2148 + 1 by norm_num, Nat.count_succ]
  rw [show 2148 = 2147 + 1 by norm_num, Nat.count_succ]
  rw [show 2147 = 2146 + 1 by norm_num, Nat.count_succ]
  rw [show 2146 = 2145 + 1 by norm_num, Nat.count_succ]
  rw [show 2145 = 2144 + 1 by norm_num, Nat.count_succ]
  rw [show 2144 = 2143 + 1 by norm_num, Nat.count_succ]
  rw [count_2143]
  simp [prime_2143, not_prime_2144, not_prime_2145, not_prime_2146, not_prime_2147, not_prime_2148, not_prime_2149, not_prime_2150, not_prime_2151, not_prime_2152]

theorem prime_2153 : (2153 : Nat).Prime := by norm_num

theorem nth_324 : Nat.nth Nat.Prime 324 = 2153 := by
  rw [← count_2153]
  exact Nat.nth_count prime_2153

end OeisA100474.PrimeCertificate
