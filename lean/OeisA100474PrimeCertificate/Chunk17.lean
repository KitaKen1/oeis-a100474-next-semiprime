import OeisA100474PrimeCertificate.Chunk16

/-! Kernel prime/count certificate, chunk 17 (425–449). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_2954 : ¬Nat.Prime 2954 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1477) (n := 2954)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2955 : ¬Nat.Prime 2955 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 985) (n := 2955)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2956 : ¬Nat.Prime 2956 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1478) (n := 2956)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2957 : Nat.count Nat.Prime 2957 = 425 := by
  rw [show 2957 = 2956 + 1 by norm_num, Nat.count_succ]
  rw [show 2956 = 2955 + 1 by norm_num, Nat.count_succ]
  rw [show 2955 = 2954 + 1 by norm_num, Nat.count_succ]
  rw [show 2954 = 2953 + 1 by norm_num, Nat.count_succ]
  rw [count_2953]
  simp [prime_2953, not_prime_2954, not_prime_2955, not_prime_2956]

theorem prime_2957 : (2957 : Nat).Prime := by norm_num

theorem nth_425 : Nat.nth Nat.Prime 425 = 2957 := by
  rw [← count_2957]
  exact Nat.nth_count prime_2957

theorem not_prime_2958 : ¬Nat.Prime 2958 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1479) (n := 2958)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2959 : ¬Nat.Prime 2959 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 269) (n := 2959)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2960 : ¬Nat.Prime 2960 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1480) (n := 2960)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2961 : ¬Nat.Prime 2961 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 987) (n := 2961)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2962 : ¬Nat.Prime 2962 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1481) (n := 2962)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2963 : Nat.count Nat.Prime 2963 = 426 := by
  rw [show 2963 = 2962 + 1 by norm_num, Nat.count_succ]
  rw [show 2962 = 2961 + 1 by norm_num, Nat.count_succ]
  rw [show 2961 = 2960 + 1 by norm_num, Nat.count_succ]
  rw [show 2960 = 2959 + 1 by norm_num, Nat.count_succ]
  rw [show 2959 = 2958 + 1 by norm_num, Nat.count_succ]
  rw [show 2958 = 2957 + 1 by norm_num, Nat.count_succ]
  rw [count_2957]
  simp [prime_2957, not_prime_2958, not_prime_2959, not_prime_2960, not_prime_2961, not_prime_2962]

theorem prime_2963 : (2963 : Nat).Prime := by norm_num

theorem nth_426 : Nat.nth Nat.Prime 426 = 2963 := by
  rw [← count_2963]
  exact Nat.nth_count prime_2963

theorem not_prime_2964 : ¬Nat.Prime 2964 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1482) (n := 2964)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2965 : ¬Nat.Prime 2965 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 593) (n := 2965)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2966 : ¬Nat.Prime 2966 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1483) (n := 2966)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2967 : ¬Nat.Prime 2967 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 989) (n := 2967)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2968 : ¬Nat.Prime 2968 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1484) (n := 2968)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2969 : Nat.count Nat.Prime 2969 = 427 := by
  rw [show 2969 = 2968 + 1 by norm_num, Nat.count_succ]
  rw [show 2968 = 2967 + 1 by norm_num, Nat.count_succ]
  rw [show 2967 = 2966 + 1 by norm_num, Nat.count_succ]
  rw [show 2966 = 2965 + 1 by norm_num, Nat.count_succ]
  rw [show 2965 = 2964 + 1 by norm_num, Nat.count_succ]
  rw [show 2964 = 2963 + 1 by norm_num, Nat.count_succ]
  rw [count_2963]
  simp [prime_2963, not_prime_2964, not_prime_2965, not_prime_2966, not_prime_2967, not_prime_2968]

theorem prime_2969 : (2969 : Nat).Prime := by norm_num

theorem nth_427 : Nat.nth Nat.Prime 427 = 2969 := by
  rw [← count_2969]
  exact Nat.nth_count prime_2969

theorem not_prime_2970 : ¬Nat.Prime 2970 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1485) (n := 2970)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2971 : Nat.count Nat.Prime 2971 = 428 := by
  rw [show 2971 = 2970 + 1 by norm_num, Nat.count_succ]
  rw [show 2970 = 2969 + 1 by norm_num, Nat.count_succ]
  rw [count_2969]
  simp [prime_2969, not_prime_2970]

theorem prime_2971 : (2971 : Nat).Prime := by norm_num

theorem nth_428 : Nat.nth Nat.Prime 428 = 2971 := by
  rw [← count_2971]
  exact Nat.nth_count prime_2971

theorem not_prime_2972 : ¬Nat.Prime 2972 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1486) (n := 2972)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2973 : ¬Nat.Prime 2973 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 991) (n := 2973)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2974 : ¬Nat.Prime 2974 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1487) (n := 2974)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2975 : ¬Nat.Prime 2975 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 595) (n := 2975)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2976 : ¬Nat.Prime 2976 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1488) (n := 2976)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2977 : ¬Nat.Prime 2977 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 229) (n := 2977)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2978 : ¬Nat.Prime 2978 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1489) (n := 2978)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2979 : ¬Nat.Prime 2979 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 993) (n := 2979)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2980 : ¬Nat.Prime 2980 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1490) (n := 2980)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2981 : ¬Nat.Prime 2981 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 271) (n := 2981)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2982 : ¬Nat.Prime 2982 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1491) (n := 2982)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2983 : ¬Nat.Prime 2983 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 157) (n := 2983)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2984 : ¬Nat.Prime 2984 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1492) (n := 2984)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2985 : ¬Nat.Prime 2985 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 995) (n := 2985)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2986 : ¬Nat.Prime 2986 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1493) (n := 2986)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2987 : ¬Nat.Prime 2987 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 103) (n := 2987)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2988 : ¬Nat.Prime 2988 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1494) (n := 2988)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2989 : ¬Nat.Prime 2989 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 427) (n := 2989)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2990 : ¬Nat.Prime 2990 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1495) (n := 2990)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2991 : ¬Nat.Prime 2991 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 997) (n := 2991)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2992 : ¬Nat.Prime 2992 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1496) (n := 2992)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2993 : ¬Nat.Prime 2993 :=
  Nat.not_prime_of_mul_eq (a := 41) (b := 73) (n := 2993)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2994 : ¬Nat.Prime 2994 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1497) (n := 2994)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2995 : ¬Nat.Prime 2995 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 599) (n := 2995)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2996 : ¬Nat.Prime 2996 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1498) (n := 2996)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2997 : ¬Nat.Prime 2997 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 999) (n := 2997)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_2998 : ¬Nat.Prime 2998 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1499) (n := 2998)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_2999 : Nat.count Nat.Prime 2999 = 429 := by
  rw [show 2999 = 2998 + 1 by norm_num, Nat.count_succ]
  rw [show 2998 = 2997 + 1 by norm_num, Nat.count_succ]
  rw [show 2997 = 2996 + 1 by norm_num, Nat.count_succ]
  rw [show 2996 = 2995 + 1 by norm_num, Nat.count_succ]
  rw [show 2995 = 2994 + 1 by norm_num, Nat.count_succ]
  rw [show 2994 = 2993 + 1 by norm_num, Nat.count_succ]
  rw [show 2993 = 2992 + 1 by norm_num, Nat.count_succ]
  rw [show 2992 = 2991 + 1 by norm_num, Nat.count_succ]
  rw [show 2991 = 2990 + 1 by norm_num, Nat.count_succ]
  rw [show 2990 = 2989 + 1 by norm_num, Nat.count_succ]
  rw [show 2989 = 2988 + 1 by norm_num, Nat.count_succ]
  rw [show 2988 = 2987 + 1 by norm_num, Nat.count_succ]
  rw [show 2987 = 2986 + 1 by norm_num, Nat.count_succ]
  rw [show 2986 = 2985 + 1 by norm_num, Nat.count_succ]
  rw [show 2985 = 2984 + 1 by norm_num, Nat.count_succ]
  rw [show 2984 = 2983 + 1 by norm_num, Nat.count_succ]
  rw [show 2983 = 2982 + 1 by norm_num, Nat.count_succ]
  rw [show 2982 = 2981 + 1 by norm_num, Nat.count_succ]
  rw [show 2981 = 2980 + 1 by norm_num, Nat.count_succ]
  rw [show 2980 = 2979 + 1 by norm_num, Nat.count_succ]
  rw [show 2979 = 2978 + 1 by norm_num, Nat.count_succ]
  rw [show 2978 = 2977 + 1 by norm_num, Nat.count_succ]
  rw [show 2977 = 2976 + 1 by norm_num, Nat.count_succ]
  rw [show 2976 = 2975 + 1 by norm_num, Nat.count_succ]
  rw [show 2975 = 2974 + 1 by norm_num, Nat.count_succ]
  rw [show 2974 = 2973 + 1 by norm_num, Nat.count_succ]
  rw [show 2973 = 2972 + 1 by norm_num, Nat.count_succ]
  rw [show 2972 = 2971 + 1 by norm_num, Nat.count_succ]
  rw [count_2971]
  simp [prime_2971, not_prime_2972, not_prime_2973, not_prime_2974, not_prime_2975, not_prime_2976, not_prime_2977, not_prime_2978, not_prime_2979, not_prime_2980, not_prime_2981, not_prime_2982, not_prime_2983, not_prime_2984, not_prime_2985, not_prime_2986, not_prime_2987, not_prime_2988, not_prime_2989, not_prime_2990, not_prime_2991, not_prime_2992, not_prime_2993, not_prime_2994, not_prime_2995, not_prime_2996, not_prime_2997, not_prime_2998]

theorem prime_2999 : (2999 : Nat).Prime := by norm_num

theorem nth_429 : Nat.nth Nat.Prime 429 = 2999 := by
  rw [← count_2999]
  exact Nat.nth_count prime_2999

theorem not_prime_3000 : ¬Nat.Prime 3000 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1500) (n := 3000)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3001 : Nat.count Nat.Prime 3001 = 430 := by
  rw [show 3001 = 3000 + 1 by norm_num, Nat.count_succ]
  rw [show 3000 = 2999 + 1 by norm_num, Nat.count_succ]
  rw [count_2999]
  simp [prime_2999, not_prime_3000]

theorem prime_3001 : (3001 : Nat).Prime := by norm_num

theorem nth_430 : Nat.nth Nat.Prime 430 = 3001 := by
  rw [← count_3001]
  exact Nat.nth_count prime_3001

theorem not_prime_3002 : ¬Nat.Prime 3002 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1501) (n := 3002)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3003 : ¬Nat.Prime 3003 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1001) (n := 3003)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3004 : ¬Nat.Prime 3004 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1502) (n := 3004)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3005 : ¬Nat.Prime 3005 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 601) (n := 3005)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3006 : ¬Nat.Prime 3006 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1503) (n := 3006)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3007 : ¬Nat.Prime 3007 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 97) (n := 3007)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3008 : ¬Nat.Prime 3008 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1504) (n := 3008)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3009 : ¬Nat.Prime 3009 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1003) (n := 3009)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3010 : ¬Nat.Prime 3010 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1505) (n := 3010)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3011 : Nat.count Nat.Prime 3011 = 431 := by
  rw [show 3011 = 3010 + 1 by norm_num, Nat.count_succ]
  rw [show 3010 = 3009 + 1 by norm_num, Nat.count_succ]
  rw [show 3009 = 3008 + 1 by norm_num, Nat.count_succ]
  rw [show 3008 = 3007 + 1 by norm_num, Nat.count_succ]
  rw [show 3007 = 3006 + 1 by norm_num, Nat.count_succ]
  rw [show 3006 = 3005 + 1 by norm_num, Nat.count_succ]
  rw [show 3005 = 3004 + 1 by norm_num, Nat.count_succ]
  rw [show 3004 = 3003 + 1 by norm_num, Nat.count_succ]
  rw [show 3003 = 3002 + 1 by norm_num, Nat.count_succ]
  rw [show 3002 = 3001 + 1 by norm_num, Nat.count_succ]
  rw [count_3001]
  simp [prime_3001, not_prime_3002, not_prime_3003, not_prime_3004, not_prime_3005, not_prime_3006, not_prime_3007, not_prime_3008, not_prime_3009, not_prime_3010]

theorem prime_3011 : (3011 : Nat).Prime := by norm_num

theorem nth_431 : Nat.nth Nat.Prime 431 = 3011 := by
  rw [← count_3011]
  exact Nat.nth_count prime_3011

theorem not_prime_3012 : ¬Nat.Prime 3012 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1506) (n := 3012)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3013 : ¬Nat.Prime 3013 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 131) (n := 3013)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3014 : ¬Nat.Prime 3014 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1507) (n := 3014)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3015 : ¬Nat.Prime 3015 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1005) (n := 3015)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3016 : ¬Nat.Prime 3016 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1508) (n := 3016)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3017 : ¬Nat.Prime 3017 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 431) (n := 3017)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3018 : ¬Nat.Prime 3018 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1509) (n := 3018)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3019 : Nat.count Nat.Prime 3019 = 432 := by
  rw [show 3019 = 3018 + 1 by norm_num, Nat.count_succ]
  rw [show 3018 = 3017 + 1 by norm_num, Nat.count_succ]
  rw [show 3017 = 3016 + 1 by norm_num, Nat.count_succ]
  rw [show 3016 = 3015 + 1 by norm_num, Nat.count_succ]
  rw [show 3015 = 3014 + 1 by norm_num, Nat.count_succ]
  rw [show 3014 = 3013 + 1 by norm_num, Nat.count_succ]
  rw [show 3013 = 3012 + 1 by norm_num, Nat.count_succ]
  rw [show 3012 = 3011 + 1 by norm_num, Nat.count_succ]
  rw [count_3011]
  simp [prime_3011, not_prime_3012, not_prime_3013, not_prime_3014, not_prime_3015, not_prime_3016, not_prime_3017, not_prime_3018]

theorem prime_3019 : (3019 : Nat).Prime := by norm_num

theorem nth_432 : Nat.nth Nat.Prime 432 = 3019 := by
  rw [← count_3019]
  exact Nat.nth_count prime_3019

theorem not_prime_3020 : ¬Nat.Prime 3020 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1510) (n := 3020)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3021 : ¬Nat.Prime 3021 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1007) (n := 3021)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3022 : ¬Nat.Prime 3022 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1511) (n := 3022)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3023 : Nat.count Nat.Prime 3023 = 433 := by
  rw [show 3023 = 3022 + 1 by norm_num, Nat.count_succ]
  rw [show 3022 = 3021 + 1 by norm_num, Nat.count_succ]
  rw [show 3021 = 3020 + 1 by norm_num, Nat.count_succ]
  rw [show 3020 = 3019 + 1 by norm_num, Nat.count_succ]
  rw [count_3019]
  simp [prime_3019, not_prime_3020, not_prime_3021, not_prime_3022]

theorem prime_3023 : (3023 : Nat).Prime := by norm_num

theorem nth_433 : Nat.nth Nat.Prime 433 = 3023 := by
  rw [← count_3023]
  exact Nat.nth_count prime_3023

theorem not_prime_3024 : ¬Nat.Prime 3024 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1512) (n := 3024)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3025 : ¬Nat.Prime 3025 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 605) (n := 3025)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3026 : ¬Nat.Prime 3026 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1513) (n := 3026)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3027 : ¬Nat.Prime 3027 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1009) (n := 3027)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3028 : ¬Nat.Prime 3028 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1514) (n := 3028)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3029 : ¬Nat.Prime 3029 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 233) (n := 3029)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3030 : ¬Nat.Prime 3030 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1515) (n := 3030)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3031 : ¬Nat.Prime 3031 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 433) (n := 3031)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3032 : ¬Nat.Prime 3032 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1516) (n := 3032)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3033 : ¬Nat.Prime 3033 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1011) (n := 3033)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3034 : ¬Nat.Prime 3034 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1517) (n := 3034)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3035 : ¬Nat.Prime 3035 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 607) (n := 3035)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3036 : ¬Nat.Prime 3036 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1518) (n := 3036)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3037 : Nat.count Nat.Prime 3037 = 434 := by
  rw [show 3037 = 3036 + 1 by norm_num, Nat.count_succ]
  rw [show 3036 = 3035 + 1 by norm_num, Nat.count_succ]
  rw [show 3035 = 3034 + 1 by norm_num, Nat.count_succ]
  rw [show 3034 = 3033 + 1 by norm_num, Nat.count_succ]
  rw [show 3033 = 3032 + 1 by norm_num, Nat.count_succ]
  rw [show 3032 = 3031 + 1 by norm_num, Nat.count_succ]
  rw [show 3031 = 3030 + 1 by norm_num, Nat.count_succ]
  rw [show 3030 = 3029 + 1 by norm_num, Nat.count_succ]
  rw [show 3029 = 3028 + 1 by norm_num, Nat.count_succ]
  rw [show 3028 = 3027 + 1 by norm_num, Nat.count_succ]
  rw [show 3027 = 3026 + 1 by norm_num, Nat.count_succ]
  rw [show 3026 = 3025 + 1 by norm_num, Nat.count_succ]
  rw [show 3025 = 3024 + 1 by norm_num, Nat.count_succ]
  rw [show 3024 = 3023 + 1 by norm_num, Nat.count_succ]
  rw [count_3023]
  simp [prime_3023, not_prime_3024, not_prime_3025, not_prime_3026, not_prime_3027, not_prime_3028, not_prime_3029, not_prime_3030, not_prime_3031, not_prime_3032, not_prime_3033, not_prime_3034, not_prime_3035, not_prime_3036]

theorem prime_3037 : (3037 : Nat).Prime := by norm_num

theorem nth_434 : Nat.nth Nat.Prime 434 = 3037 := by
  rw [← count_3037]
  exact Nat.nth_count prime_3037

theorem not_prime_3038 : ¬Nat.Prime 3038 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1519) (n := 3038)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3039 : ¬Nat.Prime 3039 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1013) (n := 3039)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3040 : ¬Nat.Prime 3040 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1520) (n := 3040)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3041 : Nat.count Nat.Prime 3041 = 435 := by
  rw [show 3041 = 3040 + 1 by norm_num, Nat.count_succ]
  rw [show 3040 = 3039 + 1 by norm_num, Nat.count_succ]
  rw [show 3039 = 3038 + 1 by norm_num, Nat.count_succ]
  rw [show 3038 = 3037 + 1 by norm_num, Nat.count_succ]
  rw [count_3037]
  simp [prime_3037, not_prime_3038, not_prime_3039, not_prime_3040]

theorem prime_3041 : (3041 : Nat).Prime := by norm_num

theorem nth_435 : Nat.nth Nat.Prime 435 = 3041 := by
  rw [← count_3041]
  exact Nat.nth_count prime_3041

theorem not_prime_3042 : ¬Nat.Prime 3042 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1521) (n := 3042)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3043 : ¬Nat.Prime 3043 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 179) (n := 3043)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3044 : ¬Nat.Prime 3044 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1522) (n := 3044)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3045 : ¬Nat.Prime 3045 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1015) (n := 3045)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3046 : ¬Nat.Prime 3046 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1523) (n := 3046)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3047 : ¬Nat.Prime 3047 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 277) (n := 3047)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3048 : ¬Nat.Prime 3048 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1524) (n := 3048)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3049 : Nat.count Nat.Prime 3049 = 436 := by
  rw [show 3049 = 3048 + 1 by norm_num, Nat.count_succ]
  rw [show 3048 = 3047 + 1 by norm_num, Nat.count_succ]
  rw [show 3047 = 3046 + 1 by norm_num, Nat.count_succ]
  rw [show 3046 = 3045 + 1 by norm_num, Nat.count_succ]
  rw [show 3045 = 3044 + 1 by norm_num, Nat.count_succ]
  rw [show 3044 = 3043 + 1 by norm_num, Nat.count_succ]
  rw [show 3043 = 3042 + 1 by norm_num, Nat.count_succ]
  rw [show 3042 = 3041 + 1 by norm_num, Nat.count_succ]
  rw [count_3041]
  simp [prime_3041, not_prime_3042, not_prime_3043, not_prime_3044, not_prime_3045, not_prime_3046, not_prime_3047, not_prime_3048]

theorem prime_3049 : (3049 : Nat).Prime := by norm_num

theorem nth_436 : Nat.nth Nat.Prime 436 = 3049 := by
  rw [← count_3049]
  exact Nat.nth_count prime_3049

theorem not_prime_3050 : ¬Nat.Prime 3050 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1525) (n := 3050)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3051 : ¬Nat.Prime 3051 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1017) (n := 3051)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3052 : ¬Nat.Prime 3052 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1526) (n := 3052)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3053 : ¬Nat.Prime 3053 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 71) (n := 3053)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3054 : ¬Nat.Prime 3054 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1527) (n := 3054)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3055 : ¬Nat.Prime 3055 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 611) (n := 3055)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3056 : ¬Nat.Prime 3056 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1528) (n := 3056)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3057 : ¬Nat.Prime 3057 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1019) (n := 3057)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3058 : ¬Nat.Prime 3058 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1529) (n := 3058)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3059 : ¬Nat.Prime 3059 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 437) (n := 3059)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3060 : ¬Nat.Prime 3060 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1530) (n := 3060)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3061 : Nat.count Nat.Prime 3061 = 437 := by
  rw [show 3061 = 3060 + 1 by norm_num, Nat.count_succ]
  rw [show 3060 = 3059 + 1 by norm_num, Nat.count_succ]
  rw [show 3059 = 3058 + 1 by norm_num, Nat.count_succ]
  rw [show 3058 = 3057 + 1 by norm_num, Nat.count_succ]
  rw [show 3057 = 3056 + 1 by norm_num, Nat.count_succ]
  rw [show 3056 = 3055 + 1 by norm_num, Nat.count_succ]
  rw [show 3055 = 3054 + 1 by norm_num, Nat.count_succ]
  rw [show 3054 = 3053 + 1 by norm_num, Nat.count_succ]
  rw [show 3053 = 3052 + 1 by norm_num, Nat.count_succ]
  rw [show 3052 = 3051 + 1 by norm_num, Nat.count_succ]
  rw [show 3051 = 3050 + 1 by norm_num, Nat.count_succ]
  rw [show 3050 = 3049 + 1 by norm_num, Nat.count_succ]
  rw [count_3049]
  simp [prime_3049, not_prime_3050, not_prime_3051, not_prime_3052, not_prime_3053, not_prime_3054, not_prime_3055, not_prime_3056, not_prime_3057, not_prime_3058, not_prime_3059, not_prime_3060]

theorem prime_3061 : (3061 : Nat).Prime := by norm_num

theorem nth_437 : Nat.nth Nat.Prime 437 = 3061 := by
  rw [← count_3061]
  exact Nat.nth_count prime_3061

theorem not_prime_3062 : ¬Nat.Prime 3062 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1531) (n := 3062)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3063 : ¬Nat.Prime 3063 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1021) (n := 3063)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3064 : ¬Nat.Prime 3064 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1532) (n := 3064)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3065 : ¬Nat.Prime 3065 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 613) (n := 3065)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3066 : ¬Nat.Prime 3066 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1533) (n := 3066)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3067 : Nat.count Nat.Prime 3067 = 438 := by
  rw [show 3067 = 3066 + 1 by norm_num, Nat.count_succ]
  rw [show 3066 = 3065 + 1 by norm_num, Nat.count_succ]
  rw [show 3065 = 3064 + 1 by norm_num, Nat.count_succ]
  rw [show 3064 = 3063 + 1 by norm_num, Nat.count_succ]
  rw [show 3063 = 3062 + 1 by norm_num, Nat.count_succ]
  rw [show 3062 = 3061 + 1 by norm_num, Nat.count_succ]
  rw [count_3061]
  simp [prime_3061, not_prime_3062, not_prime_3063, not_prime_3064, not_prime_3065, not_prime_3066]

theorem prime_3067 : (3067 : Nat).Prime := by norm_num

theorem nth_438 : Nat.nth Nat.Prime 438 = 3067 := by
  rw [← count_3067]
  exact Nat.nth_count prime_3067

theorem not_prime_3068 : ¬Nat.Prime 3068 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1534) (n := 3068)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3069 : ¬Nat.Prime 3069 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1023) (n := 3069)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3070 : ¬Nat.Prime 3070 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1535) (n := 3070)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3071 : ¬Nat.Prime 3071 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 83) (n := 3071)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3072 : ¬Nat.Prime 3072 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1536) (n := 3072)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3073 : ¬Nat.Prime 3073 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 439) (n := 3073)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3074 : ¬Nat.Prime 3074 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1537) (n := 3074)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3075 : ¬Nat.Prime 3075 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1025) (n := 3075)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3076 : ¬Nat.Prime 3076 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1538) (n := 3076)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3077 : ¬Nat.Prime 3077 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 181) (n := 3077)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3078 : ¬Nat.Prime 3078 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1539) (n := 3078)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3079 : Nat.count Nat.Prime 3079 = 439 := by
  rw [show 3079 = 3078 + 1 by norm_num, Nat.count_succ]
  rw [show 3078 = 3077 + 1 by norm_num, Nat.count_succ]
  rw [show 3077 = 3076 + 1 by norm_num, Nat.count_succ]
  rw [show 3076 = 3075 + 1 by norm_num, Nat.count_succ]
  rw [show 3075 = 3074 + 1 by norm_num, Nat.count_succ]
  rw [show 3074 = 3073 + 1 by norm_num, Nat.count_succ]
  rw [show 3073 = 3072 + 1 by norm_num, Nat.count_succ]
  rw [show 3072 = 3071 + 1 by norm_num, Nat.count_succ]
  rw [show 3071 = 3070 + 1 by norm_num, Nat.count_succ]
  rw [show 3070 = 3069 + 1 by norm_num, Nat.count_succ]
  rw [show 3069 = 3068 + 1 by norm_num, Nat.count_succ]
  rw [show 3068 = 3067 + 1 by norm_num, Nat.count_succ]
  rw [count_3067]
  simp [prime_3067, not_prime_3068, not_prime_3069, not_prime_3070, not_prime_3071, not_prime_3072, not_prime_3073, not_prime_3074, not_prime_3075, not_prime_3076, not_prime_3077, not_prime_3078]

theorem prime_3079 : (3079 : Nat).Prime := by norm_num

theorem nth_439 : Nat.nth Nat.Prime 439 = 3079 := by
  rw [← count_3079]
  exact Nat.nth_count prime_3079

theorem not_prime_3080 : ¬Nat.Prime 3080 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1540) (n := 3080)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3081 : ¬Nat.Prime 3081 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1027) (n := 3081)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3082 : ¬Nat.Prime 3082 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1541) (n := 3082)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3083 : Nat.count Nat.Prime 3083 = 440 := by
  rw [show 3083 = 3082 + 1 by norm_num, Nat.count_succ]
  rw [show 3082 = 3081 + 1 by norm_num, Nat.count_succ]
  rw [show 3081 = 3080 + 1 by norm_num, Nat.count_succ]
  rw [show 3080 = 3079 + 1 by norm_num, Nat.count_succ]
  rw [count_3079]
  simp [prime_3079, not_prime_3080, not_prime_3081, not_prime_3082]

theorem prime_3083 : (3083 : Nat).Prime := by norm_num

theorem nth_440 : Nat.nth Nat.Prime 440 = 3083 := by
  rw [← count_3083]
  exact Nat.nth_count prime_3083

theorem not_prime_3084 : ¬Nat.Prime 3084 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1542) (n := 3084)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3085 : ¬Nat.Prime 3085 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 617) (n := 3085)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3086 : ¬Nat.Prime 3086 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1543) (n := 3086)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3087 : ¬Nat.Prime 3087 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1029) (n := 3087)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3088 : ¬Nat.Prime 3088 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1544) (n := 3088)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3089 : Nat.count Nat.Prime 3089 = 441 := by
  rw [show 3089 = 3088 + 1 by norm_num, Nat.count_succ]
  rw [show 3088 = 3087 + 1 by norm_num, Nat.count_succ]
  rw [show 3087 = 3086 + 1 by norm_num, Nat.count_succ]
  rw [show 3086 = 3085 + 1 by norm_num, Nat.count_succ]
  rw [show 3085 = 3084 + 1 by norm_num, Nat.count_succ]
  rw [show 3084 = 3083 + 1 by norm_num, Nat.count_succ]
  rw [count_3083]
  simp [prime_3083, not_prime_3084, not_prime_3085, not_prime_3086, not_prime_3087, not_prime_3088]

theorem prime_3089 : (3089 : Nat).Prime := by norm_num

theorem nth_441 : Nat.nth Nat.Prime 441 = 3089 := by
  rw [← count_3089]
  exact Nat.nth_count prime_3089

theorem not_prime_3090 : ¬Nat.Prime 3090 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1545) (n := 3090)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3091 : ¬Nat.Prime 3091 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 281) (n := 3091)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3092 : ¬Nat.Prime 3092 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1546) (n := 3092)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3093 : ¬Nat.Prime 3093 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1031) (n := 3093)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3094 : ¬Nat.Prime 3094 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1547) (n := 3094)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3095 : ¬Nat.Prime 3095 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 619) (n := 3095)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3096 : ¬Nat.Prime 3096 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1548) (n := 3096)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3097 : ¬Nat.Prime 3097 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 163) (n := 3097)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3098 : ¬Nat.Prime 3098 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1549) (n := 3098)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3099 : ¬Nat.Prime 3099 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1033) (n := 3099)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3100 : ¬Nat.Prime 3100 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1550) (n := 3100)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3101 : ¬Nat.Prime 3101 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 443) (n := 3101)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3102 : ¬Nat.Prime 3102 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1551) (n := 3102)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3103 : ¬Nat.Prime 3103 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 107) (n := 3103)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3104 : ¬Nat.Prime 3104 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1552) (n := 3104)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3105 : ¬Nat.Prime 3105 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1035) (n := 3105)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3106 : ¬Nat.Prime 3106 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1553) (n := 3106)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3107 : ¬Nat.Prime 3107 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 239) (n := 3107)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3108 : ¬Nat.Prime 3108 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1554) (n := 3108)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3109 : Nat.count Nat.Prime 3109 = 442 := by
  rw [show 3109 = 3108 + 1 by norm_num, Nat.count_succ]
  rw [show 3108 = 3107 + 1 by norm_num, Nat.count_succ]
  rw [show 3107 = 3106 + 1 by norm_num, Nat.count_succ]
  rw [show 3106 = 3105 + 1 by norm_num, Nat.count_succ]
  rw [show 3105 = 3104 + 1 by norm_num, Nat.count_succ]
  rw [show 3104 = 3103 + 1 by norm_num, Nat.count_succ]
  rw [show 3103 = 3102 + 1 by norm_num, Nat.count_succ]
  rw [show 3102 = 3101 + 1 by norm_num, Nat.count_succ]
  rw [show 3101 = 3100 + 1 by norm_num, Nat.count_succ]
  rw [show 3100 = 3099 + 1 by norm_num, Nat.count_succ]
  rw [show 3099 = 3098 + 1 by norm_num, Nat.count_succ]
  rw [show 3098 = 3097 + 1 by norm_num, Nat.count_succ]
  rw [show 3097 = 3096 + 1 by norm_num, Nat.count_succ]
  rw [show 3096 = 3095 + 1 by norm_num, Nat.count_succ]
  rw [show 3095 = 3094 + 1 by norm_num, Nat.count_succ]
  rw [show 3094 = 3093 + 1 by norm_num, Nat.count_succ]
  rw [show 3093 = 3092 + 1 by norm_num, Nat.count_succ]
  rw [show 3092 = 3091 + 1 by norm_num, Nat.count_succ]
  rw [show 3091 = 3090 + 1 by norm_num, Nat.count_succ]
  rw [show 3090 = 3089 + 1 by norm_num, Nat.count_succ]
  rw [count_3089]
  simp [prime_3089, not_prime_3090, not_prime_3091, not_prime_3092, not_prime_3093, not_prime_3094, not_prime_3095, not_prime_3096, not_prime_3097, not_prime_3098, not_prime_3099, not_prime_3100, not_prime_3101, not_prime_3102, not_prime_3103, not_prime_3104, not_prime_3105, not_prime_3106, not_prime_3107, not_prime_3108]

theorem prime_3109 : (3109 : Nat).Prime := by norm_num

theorem nth_442 : Nat.nth Nat.Prime 442 = 3109 := by
  rw [← count_3109]
  exact Nat.nth_count prime_3109

theorem not_prime_3110 : ¬Nat.Prime 3110 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1555) (n := 3110)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3111 : ¬Nat.Prime 3111 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1037) (n := 3111)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3112 : ¬Nat.Prime 3112 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1556) (n := 3112)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3113 : ¬Nat.Prime 3113 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 283) (n := 3113)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3114 : ¬Nat.Prime 3114 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1557) (n := 3114)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3115 : ¬Nat.Prime 3115 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 623) (n := 3115)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3116 : ¬Nat.Prime 3116 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1558) (n := 3116)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3117 : ¬Nat.Prime 3117 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1039) (n := 3117)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3118 : ¬Nat.Prime 3118 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1559) (n := 3118)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3119 : Nat.count Nat.Prime 3119 = 443 := by
  rw [show 3119 = 3118 + 1 by norm_num, Nat.count_succ]
  rw [show 3118 = 3117 + 1 by norm_num, Nat.count_succ]
  rw [show 3117 = 3116 + 1 by norm_num, Nat.count_succ]
  rw [show 3116 = 3115 + 1 by norm_num, Nat.count_succ]
  rw [show 3115 = 3114 + 1 by norm_num, Nat.count_succ]
  rw [show 3114 = 3113 + 1 by norm_num, Nat.count_succ]
  rw [show 3113 = 3112 + 1 by norm_num, Nat.count_succ]
  rw [show 3112 = 3111 + 1 by norm_num, Nat.count_succ]
  rw [show 3111 = 3110 + 1 by norm_num, Nat.count_succ]
  rw [show 3110 = 3109 + 1 by norm_num, Nat.count_succ]
  rw [count_3109]
  simp [prime_3109, not_prime_3110, not_prime_3111, not_prime_3112, not_prime_3113, not_prime_3114, not_prime_3115, not_prime_3116, not_prime_3117, not_prime_3118]

theorem prime_3119 : (3119 : Nat).Prime := by norm_num

theorem nth_443 : Nat.nth Nat.Prime 443 = 3119 := by
  rw [← count_3119]
  exact Nat.nth_count prime_3119

theorem not_prime_3120 : ¬Nat.Prime 3120 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1560) (n := 3120)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3121 : Nat.count Nat.Prime 3121 = 444 := by
  rw [show 3121 = 3120 + 1 by norm_num, Nat.count_succ]
  rw [show 3120 = 3119 + 1 by norm_num, Nat.count_succ]
  rw [count_3119]
  simp [prime_3119, not_prime_3120]

theorem prime_3121 : (3121 : Nat).Prime := by norm_num

theorem nth_444 : Nat.nth Nat.Prime 444 = 3121 := by
  rw [← count_3121]
  exact Nat.nth_count prime_3121

theorem not_prime_3122 : ¬Nat.Prime 3122 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1561) (n := 3122)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3123 : ¬Nat.Prime 3123 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1041) (n := 3123)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3124 : ¬Nat.Prime 3124 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1562) (n := 3124)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3125 : ¬Nat.Prime 3125 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 625) (n := 3125)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3126 : ¬Nat.Prime 3126 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1563) (n := 3126)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3127 : ¬Nat.Prime 3127 :=
  Nat.not_prime_of_mul_eq (a := 53) (b := 59) (n := 3127)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3128 : ¬Nat.Prime 3128 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1564) (n := 3128)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3129 : ¬Nat.Prime 3129 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1043) (n := 3129)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3130 : ¬Nat.Prime 3130 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1565) (n := 3130)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3131 : ¬Nat.Prime 3131 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 101) (n := 3131)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3132 : ¬Nat.Prime 3132 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1566) (n := 3132)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3133 : ¬Nat.Prime 3133 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 241) (n := 3133)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3134 : ¬Nat.Prime 3134 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1567) (n := 3134)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3135 : ¬Nat.Prime 3135 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1045) (n := 3135)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3136 : ¬Nat.Prime 3136 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1568) (n := 3136)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3137 : Nat.count Nat.Prime 3137 = 445 := by
  rw [show 3137 = 3136 + 1 by norm_num, Nat.count_succ]
  rw [show 3136 = 3135 + 1 by norm_num, Nat.count_succ]
  rw [show 3135 = 3134 + 1 by norm_num, Nat.count_succ]
  rw [show 3134 = 3133 + 1 by norm_num, Nat.count_succ]
  rw [show 3133 = 3132 + 1 by norm_num, Nat.count_succ]
  rw [show 3132 = 3131 + 1 by norm_num, Nat.count_succ]
  rw [show 3131 = 3130 + 1 by norm_num, Nat.count_succ]
  rw [show 3130 = 3129 + 1 by norm_num, Nat.count_succ]
  rw [show 3129 = 3128 + 1 by norm_num, Nat.count_succ]
  rw [show 3128 = 3127 + 1 by norm_num, Nat.count_succ]
  rw [show 3127 = 3126 + 1 by norm_num, Nat.count_succ]
  rw [show 3126 = 3125 + 1 by norm_num, Nat.count_succ]
  rw [show 3125 = 3124 + 1 by norm_num, Nat.count_succ]
  rw [show 3124 = 3123 + 1 by norm_num, Nat.count_succ]
  rw [show 3123 = 3122 + 1 by norm_num, Nat.count_succ]
  rw [show 3122 = 3121 + 1 by norm_num, Nat.count_succ]
  rw [count_3121]
  simp [prime_3121, not_prime_3122, not_prime_3123, not_prime_3124, not_prime_3125, not_prime_3126, not_prime_3127, not_prime_3128, not_prime_3129, not_prime_3130, not_prime_3131, not_prime_3132, not_prime_3133, not_prime_3134, not_prime_3135, not_prime_3136]

theorem prime_3137 : (3137 : Nat).Prime := by norm_num

theorem nth_445 : Nat.nth Nat.Prime 445 = 3137 := by
  rw [← count_3137]
  exact Nat.nth_count prime_3137

theorem not_prime_3138 : ¬Nat.Prime 3138 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1569) (n := 3138)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3139 : ¬Nat.Prime 3139 :=
  Nat.not_prime_of_mul_eq (a := 43) (b := 73) (n := 3139)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3140 : ¬Nat.Prime 3140 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1570) (n := 3140)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3141 : ¬Nat.Prime 3141 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1047) (n := 3141)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3142 : ¬Nat.Prime 3142 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1571) (n := 3142)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3143 : ¬Nat.Prime 3143 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 449) (n := 3143)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3144 : ¬Nat.Prime 3144 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1572) (n := 3144)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3145 : ¬Nat.Prime 3145 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 629) (n := 3145)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3146 : ¬Nat.Prime 3146 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1573) (n := 3146)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3147 : ¬Nat.Prime 3147 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1049) (n := 3147)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3148 : ¬Nat.Prime 3148 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1574) (n := 3148)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3149 : ¬Nat.Prime 3149 :=
  Nat.not_prime_of_mul_eq (a := 47) (b := 67) (n := 3149)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3150 : ¬Nat.Prime 3150 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1575) (n := 3150)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3151 : ¬Nat.Prime 3151 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 137) (n := 3151)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3152 : ¬Nat.Prime 3152 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1576) (n := 3152)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3153 : ¬Nat.Prime 3153 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1051) (n := 3153)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3154 : ¬Nat.Prime 3154 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1577) (n := 3154)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3155 : ¬Nat.Prime 3155 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 631) (n := 3155)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3156 : ¬Nat.Prime 3156 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1578) (n := 3156)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3157 : ¬Nat.Prime 3157 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 451) (n := 3157)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3158 : ¬Nat.Prime 3158 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1579) (n := 3158)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3159 : ¬Nat.Prime 3159 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1053) (n := 3159)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3160 : ¬Nat.Prime 3160 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1580) (n := 3160)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3161 : ¬Nat.Prime 3161 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 109) (n := 3161)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3162 : ¬Nat.Prime 3162 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1581) (n := 3162)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3163 : Nat.count Nat.Prime 3163 = 446 := by
  rw [show 3163 = 3162 + 1 by norm_num, Nat.count_succ]
  rw [show 3162 = 3161 + 1 by norm_num, Nat.count_succ]
  rw [show 3161 = 3160 + 1 by norm_num, Nat.count_succ]
  rw [show 3160 = 3159 + 1 by norm_num, Nat.count_succ]
  rw [show 3159 = 3158 + 1 by norm_num, Nat.count_succ]
  rw [show 3158 = 3157 + 1 by norm_num, Nat.count_succ]
  rw [show 3157 = 3156 + 1 by norm_num, Nat.count_succ]
  rw [show 3156 = 3155 + 1 by norm_num, Nat.count_succ]
  rw [show 3155 = 3154 + 1 by norm_num, Nat.count_succ]
  rw [show 3154 = 3153 + 1 by norm_num, Nat.count_succ]
  rw [show 3153 = 3152 + 1 by norm_num, Nat.count_succ]
  rw [show 3152 = 3151 + 1 by norm_num, Nat.count_succ]
  rw [show 3151 = 3150 + 1 by norm_num, Nat.count_succ]
  rw [show 3150 = 3149 + 1 by norm_num, Nat.count_succ]
  rw [show 3149 = 3148 + 1 by norm_num, Nat.count_succ]
  rw [show 3148 = 3147 + 1 by norm_num, Nat.count_succ]
  rw [show 3147 = 3146 + 1 by norm_num, Nat.count_succ]
  rw [show 3146 = 3145 + 1 by norm_num, Nat.count_succ]
  rw [show 3145 = 3144 + 1 by norm_num, Nat.count_succ]
  rw [show 3144 = 3143 + 1 by norm_num, Nat.count_succ]
  rw [show 3143 = 3142 + 1 by norm_num, Nat.count_succ]
  rw [show 3142 = 3141 + 1 by norm_num, Nat.count_succ]
  rw [show 3141 = 3140 + 1 by norm_num, Nat.count_succ]
  rw [show 3140 = 3139 + 1 by norm_num, Nat.count_succ]
  rw [show 3139 = 3138 + 1 by norm_num, Nat.count_succ]
  rw [show 3138 = 3137 + 1 by norm_num, Nat.count_succ]
  rw [count_3137]
  simp [prime_3137, not_prime_3138, not_prime_3139, not_prime_3140, not_prime_3141, not_prime_3142, not_prime_3143, not_prime_3144, not_prime_3145, not_prime_3146, not_prime_3147, not_prime_3148, not_prime_3149, not_prime_3150, not_prime_3151, not_prime_3152, not_prime_3153, not_prime_3154, not_prime_3155, not_prime_3156, not_prime_3157, not_prime_3158, not_prime_3159, not_prime_3160, not_prime_3161, not_prime_3162]

theorem prime_3163 : (3163 : Nat).Prime := by norm_num

theorem nth_446 : Nat.nth Nat.Prime 446 = 3163 := by
  rw [← count_3163]
  exact Nat.nth_count prime_3163

theorem not_prime_3164 : ¬Nat.Prime 3164 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1582) (n := 3164)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3165 : ¬Nat.Prime 3165 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1055) (n := 3165)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3166 : ¬Nat.Prime 3166 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1583) (n := 3166)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3167 : Nat.count Nat.Prime 3167 = 447 := by
  rw [show 3167 = 3166 + 1 by norm_num, Nat.count_succ]
  rw [show 3166 = 3165 + 1 by norm_num, Nat.count_succ]
  rw [show 3165 = 3164 + 1 by norm_num, Nat.count_succ]
  rw [show 3164 = 3163 + 1 by norm_num, Nat.count_succ]
  rw [count_3163]
  simp [prime_3163, not_prime_3164, not_prime_3165, not_prime_3166]

theorem prime_3167 : (3167 : Nat).Prime := by norm_num

theorem nth_447 : Nat.nth Nat.Prime 447 = 3167 := by
  rw [← count_3167]
  exact Nat.nth_count prime_3167

theorem not_prime_3168 : ¬Nat.Prime 3168 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1584) (n := 3168)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3169 : Nat.count Nat.Prime 3169 = 448 := by
  rw [show 3169 = 3168 + 1 by norm_num, Nat.count_succ]
  rw [show 3168 = 3167 + 1 by norm_num, Nat.count_succ]
  rw [count_3167]
  simp [prime_3167, not_prime_3168]

theorem prime_3169 : (3169 : Nat).Prime := by norm_num

theorem nth_448 : Nat.nth Nat.Prime 448 = 3169 := by
  rw [← count_3169]
  exact Nat.nth_count prime_3169

theorem not_prime_3170 : ¬Nat.Prime 3170 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1585) (n := 3170)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3171 : ¬Nat.Prime 3171 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1057) (n := 3171)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3172 : ¬Nat.Prime 3172 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1586) (n := 3172)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3173 : ¬Nat.Prime 3173 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 167) (n := 3173)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3174 : ¬Nat.Prime 3174 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1587) (n := 3174)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3175 : ¬Nat.Prime 3175 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 635) (n := 3175)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3176 : ¬Nat.Prime 3176 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1588) (n := 3176)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3177 : ¬Nat.Prime 3177 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 1059) (n := 3177)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3178 : ¬Nat.Prime 3178 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1589) (n := 3178)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3179 : ¬Nat.Prime 3179 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 289) (n := 3179)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_3180 : ¬Nat.Prime 3180 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 1590) (n := 3180)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_3181 : Nat.count Nat.Prime 3181 = 449 := by
  rw [show 3181 = 3180 + 1 by norm_num, Nat.count_succ]
  rw [show 3180 = 3179 + 1 by norm_num, Nat.count_succ]
  rw [show 3179 = 3178 + 1 by norm_num, Nat.count_succ]
  rw [show 3178 = 3177 + 1 by norm_num, Nat.count_succ]
  rw [show 3177 = 3176 + 1 by norm_num, Nat.count_succ]
  rw [show 3176 = 3175 + 1 by norm_num, Nat.count_succ]
  rw [show 3175 = 3174 + 1 by norm_num, Nat.count_succ]
  rw [show 3174 = 3173 + 1 by norm_num, Nat.count_succ]
  rw [show 3173 = 3172 + 1 by norm_num, Nat.count_succ]
  rw [show 3172 = 3171 + 1 by norm_num, Nat.count_succ]
  rw [show 3171 = 3170 + 1 by norm_num, Nat.count_succ]
  rw [show 3170 = 3169 + 1 by norm_num, Nat.count_succ]
  rw [count_3169]
  simp [prime_3169, not_prime_3170, not_prime_3171, not_prime_3172, not_prime_3173, not_prime_3174, not_prime_3175, not_prime_3176, not_prime_3177, not_prime_3178, not_prime_3179, not_prime_3180]

theorem prime_3181 : (3181 : Nat).Prime := by norm_num

theorem nth_449 : Nat.nth Nat.Prime 449 = 3181 := by
  rw [← count_3181]
  exact Nat.nth_count prime_3181

end OeisA100474.PrimeCertificate
