import OeisA100474PrimeCertificate.Chunk05

/-! Kernel prime/count certificate, chunk 06 (150–174). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_864 : ¬Nat.Prime 864 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 432) (n := 864)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_865 : ¬Nat.Prime 865 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 173) (n := 865)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_866 : ¬Nat.Prime 866 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 433) (n := 866)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_867 : ¬Nat.Prime 867 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 289) (n := 867)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_868 : ¬Nat.Prime 868 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 434) (n := 868)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_869 : ¬Nat.Prime 869 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 79) (n := 869)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_870 : ¬Nat.Prime 870 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 435) (n := 870)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_871 : ¬Nat.Prime 871 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 67) (n := 871)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_872 : ¬Nat.Prime 872 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 436) (n := 872)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_873 : ¬Nat.Prime 873 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 291) (n := 873)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_874 : ¬Nat.Prime 874 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 437) (n := 874)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_875 : ¬Nat.Prime 875 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 175) (n := 875)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_876 : ¬Nat.Prime 876 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 438) (n := 876)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_877 : Nat.count Nat.Prime 877 = 150 := by
  rw [show 877 = 876 + 1 by norm_num, Nat.count_succ]
  rw [show 876 = 875 + 1 by norm_num, Nat.count_succ]
  rw [show 875 = 874 + 1 by norm_num, Nat.count_succ]
  rw [show 874 = 873 + 1 by norm_num, Nat.count_succ]
  rw [show 873 = 872 + 1 by norm_num, Nat.count_succ]
  rw [show 872 = 871 + 1 by norm_num, Nat.count_succ]
  rw [show 871 = 870 + 1 by norm_num, Nat.count_succ]
  rw [show 870 = 869 + 1 by norm_num, Nat.count_succ]
  rw [show 869 = 868 + 1 by norm_num, Nat.count_succ]
  rw [show 868 = 867 + 1 by norm_num, Nat.count_succ]
  rw [show 867 = 866 + 1 by norm_num, Nat.count_succ]
  rw [show 866 = 865 + 1 by norm_num, Nat.count_succ]
  rw [show 865 = 864 + 1 by norm_num, Nat.count_succ]
  rw [show 864 = 863 + 1 by norm_num, Nat.count_succ]
  rw [count_863]
  simp [prime_863, not_prime_864, not_prime_865, not_prime_866, not_prime_867, not_prime_868, not_prime_869, not_prime_870, not_prime_871, not_prime_872, not_prime_873, not_prime_874, not_prime_875, not_prime_876]

theorem prime_877 : (877 : Nat).Prime := by norm_num

theorem nth_150 : Nat.nth Nat.Prime 150 = 877 := by
  rw [← count_877]
  exact Nat.nth_count prime_877

theorem not_prime_878 : ¬Nat.Prime 878 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 439) (n := 878)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_879 : ¬Nat.Prime 879 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 293) (n := 879)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_880 : ¬Nat.Prime 880 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 440) (n := 880)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_881 : Nat.count Nat.Prime 881 = 151 := by
  rw [show 881 = 880 + 1 by norm_num, Nat.count_succ]
  rw [show 880 = 879 + 1 by norm_num, Nat.count_succ]
  rw [show 879 = 878 + 1 by norm_num, Nat.count_succ]
  rw [show 878 = 877 + 1 by norm_num, Nat.count_succ]
  rw [count_877]
  simp [prime_877, not_prime_878, not_prime_879, not_prime_880]

theorem prime_881 : (881 : Nat).Prime := by norm_num

theorem nth_151 : Nat.nth Nat.Prime 151 = 881 := by
  rw [← count_881]
  exact Nat.nth_count prime_881

theorem not_prime_882 : ¬Nat.Prime 882 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 441) (n := 882)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_883 : Nat.count Nat.Prime 883 = 152 := by
  rw [show 883 = 882 + 1 by norm_num, Nat.count_succ]
  rw [show 882 = 881 + 1 by norm_num, Nat.count_succ]
  rw [count_881]
  simp [prime_881, not_prime_882]

theorem prime_883 : (883 : Nat).Prime := by norm_num

theorem nth_152 : Nat.nth Nat.Prime 152 = 883 := by
  rw [← count_883]
  exact Nat.nth_count prime_883

theorem not_prime_884 : ¬Nat.Prime 884 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 442) (n := 884)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_885 : ¬Nat.Prime 885 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 295) (n := 885)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_886 : ¬Nat.Prime 886 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 443) (n := 886)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_887 : Nat.count Nat.Prime 887 = 153 := by
  rw [show 887 = 886 + 1 by norm_num, Nat.count_succ]
  rw [show 886 = 885 + 1 by norm_num, Nat.count_succ]
  rw [show 885 = 884 + 1 by norm_num, Nat.count_succ]
  rw [show 884 = 883 + 1 by norm_num, Nat.count_succ]
  rw [count_883]
  simp [prime_883, not_prime_884, not_prime_885, not_prime_886]

theorem prime_887 : (887 : Nat).Prime := by norm_num

theorem nth_153 : Nat.nth Nat.Prime 153 = 887 := by
  rw [← count_887]
  exact Nat.nth_count prime_887

theorem not_prime_888 : ¬Nat.Prime 888 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 444) (n := 888)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_889 : ¬Nat.Prime 889 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 127) (n := 889)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_890 : ¬Nat.Prime 890 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 445) (n := 890)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_891 : ¬Nat.Prime 891 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 297) (n := 891)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_892 : ¬Nat.Prime 892 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 446) (n := 892)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_893 : ¬Nat.Prime 893 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 47) (n := 893)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_894 : ¬Nat.Prime 894 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 447) (n := 894)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_895 : ¬Nat.Prime 895 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 179) (n := 895)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_896 : ¬Nat.Prime 896 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 448) (n := 896)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_897 : ¬Nat.Prime 897 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 299) (n := 897)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_898 : ¬Nat.Prime 898 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 449) (n := 898)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_899 : ¬Nat.Prime 899 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 31) (n := 899)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_900 : ¬Nat.Prime 900 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 450) (n := 900)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_901 : ¬Nat.Prime 901 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 53) (n := 901)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_902 : ¬Nat.Prime 902 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 451) (n := 902)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_903 : ¬Nat.Prime 903 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 301) (n := 903)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_904 : ¬Nat.Prime 904 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 452) (n := 904)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_905 : ¬Nat.Prime 905 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 181) (n := 905)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_906 : ¬Nat.Prime 906 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 453) (n := 906)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_907 : Nat.count Nat.Prime 907 = 154 := by
  rw [show 907 = 906 + 1 by norm_num, Nat.count_succ]
  rw [show 906 = 905 + 1 by norm_num, Nat.count_succ]
  rw [show 905 = 904 + 1 by norm_num, Nat.count_succ]
  rw [show 904 = 903 + 1 by norm_num, Nat.count_succ]
  rw [show 903 = 902 + 1 by norm_num, Nat.count_succ]
  rw [show 902 = 901 + 1 by norm_num, Nat.count_succ]
  rw [show 901 = 900 + 1 by norm_num, Nat.count_succ]
  rw [show 900 = 899 + 1 by norm_num, Nat.count_succ]
  rw [show 899 = 898 + 1 by norm_num, Nat.count_succ]
  rw [show 898 = 897 + 1 by norm_num, Nat.count_succ]
  rw [show 897 = 896 + 1 by norm_num, Nat.count_succ]
  rw [show 896 = 895 + 1 by norm_num, Nat.count_succ]
  rw [show 895 = 894 + 1 by norm_num, Nat.count_succ]
  rw [show 894 = 893 + 1 by norm_num, Nat.count_succ]
  rw [show 893 = 892 + 1 by norm_num, Nat.count_succ]
  rw [show 892 = 891 + 1 by norm_num, Nat.count_succ]
  rw [show 891 = 890 + 1 by norm_num, Nat.count_succ]
  rw [show 890 = 889 + 1 by norm_num, Nat.count_succ]
  rw [show 889 = 888 + 1 by norm_num, Nat.count_succ]
  rw [show 888 = 887 + 1 by norm_num, Nat.count_succ]
  rw [count_887]
  simp [prime_887, not_prime_888, not_prime_889, not_prime_890, not_prime_891, not_prime_892, not_prime_893, not_prime_894, not_prime_895, not_prime_896, not_prime_897, not_prime_898, not_prime_899, not_prime_900, not_prime_901, not_prime_902, not_prime_903, not_prime_904, not_prime_905, not_prime_906]

theorem prime_907 : (907 : Nat).Prime := by norm_num

theorem nth_154 : Nat.nth Nat.Prime 154 = 907 := by
  rw [← count_907]
  exact Nat.nth_count prime_907

theorem not_prime_908 : ¬Nat.Prime 908 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 454) (n := 908)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_909 : ¬Nat.Prime 909 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 303) (n := 909)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_910 : ¬Nat.Prime 910 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 455) (n := 910)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_911 : Nat.count Nat.Prime 911 = 155 := by
  rw [show 911 = 910 + 1 by norm_num, Nat.count_succ]
  rw [show 910 = 909 + 1 by norm_num, Nat.count_succ]
  rw [show 909 = 908 + 1 by norm_num, Nat.count_succ]
  rw [show 908 = 907 + 1 by norm_num, Nat.count_succ]
  rw [count_907]
  simp [prime_907, not_prime_908, not_prime_909, not_prime_910]

theorem prime_911 : (911 : Nat).Prime := by norm_num

theorem nth_155 : Nat.nth Nat.Prime 155 = 911 := by
  rw [← count_911]
  exact Nat.nth_count prime_911

theorem not_prime_912 : ¬Nat.Prime 912 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 456) (n := 912)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_913 : ¬Nat.Prime 913 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 83) (n := 913)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_914 : ¬Nat.Prime 914 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 457) (n := 914)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_915 : ¬Nat.Prime 915 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 305) (n := 915)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_916 : ¬Nat.Prime 916 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 458) (n := 916)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_917 : ¬Nat.Prime 917 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 131) (n := 917)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_918 : ¬Nat.Prime 918 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 459) (n := 918)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_919 : Nat.count Nat.Prime 919 = 156 := by
  rw [show 919 = 918 + 1 by norm_num, Nat.count_succ]
  rw [show 918 = 917 + 1 by norm_num, Nat.count_succ]
  rw [show 917 = 916 + 1 by norm_num, Nat.count_succ]
  rw [show 916 = 915 + 1 by norm_num, Nat.count_succ]
  rw [show 915 = 914 + 1 by norm_num, Nat.count_succ]
  rw [show 914 = 913 + 1 by norm_num, Nat.count_succ]
  rw [show 913 = 912 + 1 by norm_num, Nat.count_succ]
  rw [show 912 = 911 + 1 by norm_num, Nat.count_succ]
  rw [count_911]
  simp [prime_911, not_prime_912, not_prime_913, not_prime_914, not_prime_915, not_prime_916, not_prime_917, not_prime_918]

theorem prime_919 : (919 : Nat).Prime := by norm_num

theorem nth_156 : Nat.nth Nat.Prime 156 = 919 := by
  rw [← count_919]
  exact Nat.nth_count prime_919

theorem not_prime_920 : ¬Nat.Prime 920 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 460) (n := 920)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_921 : ¬Nat.Prime 921 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 307) (n := 921)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_922 : ¬Nat.Prime 922 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 461) (n := 922)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_923 : ¬Nat.Prime 923 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 71) (n := 923)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_924 : ¬Nat.Prime 924 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 462) (n := 924)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_925 : ¬Nat.Prime 925 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 185) (n := 925)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_926 : ¬Nat.Prime 926 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 463) (n := 926)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_927 : ¬Nat.Prime 927 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 309) (n := 927)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_928 : ¬Nat.Prime 928 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 464) (n := 928)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_929 : Nat.count Nat.Prime 929 = 157 := by
  rw [show 929 = 928 + 1 by norm_num, Nat.count_succ]
  rw [show 928 = 927 + 1 by norm_num, Nat.count_succ]
  rw [show 927 = 926 + 1 by norm_num, Nat.count_succ]
  rw [show 926 = 925 + 1 by norm_num, Nat.count_succ]
  rw [show 925 = 924 + 1 by norm_num, Nat.count_succ]
  rw [show 924 = 923 + 1 by norm_num, Nat.count_succ]
  rw [show 923 = 922 + 1 by norm_num, Nat.count_succ]
  rw [show 922 = 921 + 1 by norm_num, Nat.count_succ]
  rw [show 921 = 920 + 1 by norm_num, Nat.count_succ]
  rw [show 920 = 919 + 1 by norm_num, Nat.count_succ]
  rw [count_919]
  simp [prime_919, not_prime_920, not_prime_921, not_prime_922, not_prime_923, not_prime_924, not_prime_925, not_prime_926, not_prime_927, not_prime_928]

theorem prime_929 : (929 : Nat).Prime := by norm_num

theorem nth_157 : Nat.nth Nat.Prime 157 = 929 := by
  rw [← count_929]
  exact Nat.nth_count prime_929

theorem not_prime_930 : ¬Nat.Prime 930 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 465) (n := 930)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_931 : ¬Nat.Prime 931 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 133) (n := 931)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_932 : ¬Nat.Prime 932 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 466) (n := 932)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_933 : ¬Nat.Prime 933 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 311) (n := 933)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_934 : ¬Nat.Prime 934 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 467) (n := 934)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_935 : ¬Nat.Prime 935 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 187) (n := 935)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_936 : ¬Nat.Prime 936 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 468) (n := 936)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_937 : Nat.count Nat.Prime 937 = 158 := by
  rw [show 937 = 936 + 1 by norm_num, Nat.count_succ]
  rw [show 936 = 935 + 1 by norm_num, Nat.count_succ]
  rw [show 935 = 934 + 1 by norm_num, Nat.count_succ]
  rw [show 934 = 933 + 1 by norm_num, Nat.count_succ]
  rw [show 933 = 932 + 1 by norm_num, Nat.count_succ]
  rw [show 932 = 931 + 1 by norm_num, Nat.count_succ]
  rw [show 931 = 930 + 1 by norm_num, Nat.count_succ]
  rw [show 930 = 929 + 1 by norm_num, Nat.count_succ]
  rw [count_929]
  simp [prime_929, not_prime_930, not_prime_931, not_prime_932, not_prime_933, not_prime_934, not_prime_935, not_prime_936]

theorem prime_937 : (937 : Nat).Prime := by norm_num

theorem nth_158 : Nat.nth Nat.Prime 158 = 937 := by
  rw [← count_937]
  exact Nat.nth_count prime_937

theorem not_prime_938 : ¬Nat.Prime 938 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 469) (n := 938)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_939 : ¬Nat.Prime 939 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 313) (n := 939)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_940 : ¬Nat.Prime 940 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 470) (n := 940)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_941 : Nat.count Nat.Prime 941 = 159 := by
  rw [show 941 = 940 + 1 by norm_num, Nat.count_succ]
  rw [show 940 = 939 + 1 by norm_num, Nat.count_succ]
  rw [show 939 = 938 + 1 by norm_num, Nat.count_succ]
  rw [show 938 = 937 + 1 by norm_num, Nat.count_succ]
  rw [count_937]
  simp [prime_937, not_prime_938, not_prime_939, not_prime_940]

theorem prime_941 : (941 : Nat).Prime := by norm_num

theorem nth_159 : Nat.nth Nat.Prime 159 = 941 := by
  rw [← count_941]
  exact Nat.nth_count prime_941

theorem not_prime_942 : ¬Nat.Prime 942 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 471) (n := 942)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_943 : ¬Nat.Prime 943 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 41) (n := 943)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_944 : ¬Nat.Prime 944 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 472) (n := 944)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_945 : ¬Nat.Prime 945 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 315) (n := 945)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_946 : ¬Nat.Prime 946 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 473) (n := 946)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_947 : Nat.count Nat.Prime 947 = 160 := by
  rw [show 947 = 946 + 1 by norm_num, Nat.count_succ]
  rw [show 946 = 945 + 1 by norm_num, Nat.count_succ]
  rw [show 945 = 944 + 1 by norm_num, Nat.count_succ]
  rw [show 944 = 943 + 1 by norm_num, Nat.count_succ]
  rw [show 943 = 942 + 1 by norm_num, Nat.count_succ]
  rw [show 942 = 941 + 1 by norm_num, Nat.count_succ]
  rw [count_941]
  simp [prime_941, not_prime_942, not_prime_943, not_prime_944, not_prime_945, not_prime_946]

theorem prime_947 : (947 : Nat).Prime := by norm_num

theorem nth_160 : Nat.nth Nat.Prime 160 = 947 := by
  rw [← count_947]
  exact Nat.nth_count prime_947

theorem not_prime_948 : ¬Nat.Prime 948 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 474) (n := 948)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_949 : ¬Nat.Prime 949 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 73) (n := 949)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_950 : ¬Nat.Prime 950 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 475) (n := 950)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_951 : ¬Nat.Prime 951 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 317) (n := 951)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_952 : ¬Nat.Prime 952 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 476) (n := 952)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_953 : Nat.count Nat.Prime 953 = 161 := by
  rw [show 953 = 952 + 1 by norm_num, Nat.count_succ]
  rw [show 952 = 951 + 1 by norm_num, Nat.count_succ]
  rw [show 951 = 950 + 1 by norm_num, Nat.count_succ]
  rw [show 950 = 949 + 1 by norm_num, Nat.count_succ]
  rw [show 949 = 948 + 1 by norm_num, Nat.count_succ]
  rw [show 948 = 947 + 1 by norm_num, Nat.count_succ]
  rw [count_947]
  simp [prime_947, not_prime_948, not_prime_949, not_prime_950, not_prime_951, not_prime_952]

theorem prime_953 : (953 : Nat).Prime := by norm_num

theorem nth_161 : Nat.nth Nat.Prime 161 = 953 := by
  rw [← count_953]
  exact Nat.nth_count prime_953

theorem not_prime_954 : ¬Nat.Prime 954 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 477) (n := 954)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_955 : ¬Nat.Prime 955 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 191) (n := 955)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_956 : ¬Nat.Prime 956 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 478) (n := 956)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_957 : ¬Nat.Prime 957 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 319) (n := 957)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_958 : ¬Nat.Prime 958 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 479) (n := 958)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_959 : ¬Nat.Prime 959 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 137) (n := 959)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_960 : ¬Nat.Prime 960 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 480) (n := 960)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_961 : ¬Nat.Prime 961 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 31) (n := 961)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_962 : ¬Nat.Prime 962 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 481) (n := 962)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_963 : ¬Nat.Prime 963 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 321) (n := 963)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_964 : ¬Nat.Prime 964 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 482) (n := 964)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_965 : ¬Nat.Prime 965 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 193) (n := 965)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_966 : ¬Nat.Prime 966 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 483) (n := 966)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_967 : Nat.count Nat.Prime 967 = 162 := by
  rw [show 967 = 966 + 1 by norm_num, Nat.count_succ]
  rw [show 966 = 965 + 1 by norm_num, Nat.count_succ]
  rw [show 965 = 964 + 1 by norm_num, Nat.count_succ]
  rw [show 964 = 963 + 1 by norm_num, Nat.count_succ]
  rw [show 963 = 962 + 1 by norm_num, Nat.count_succ]
  rw [show 962 = 961 + 1 by norm_num, Nat.count_succ]
  rw [show 961 = 960 + 1 by norm_num, Nat.count_succ]
  rw [show 960 = 959 + 1 by norm_num, Nat.count_succ]
  rw [show 959 = 958 + 1 by norm_num, Nat.count_succ]
  rw [show 958 = 957 + 1 by norm_num, Nat.count_succ]
  rw [show 957 = 956 + 1 by norm_num, Nat.count_succ]
  rw [show 956 = 955 + 1 by norm_num, Nat.count_succ]
  rw [show 955 = 954 + 1 by norm_num, Nat.count_succ]
  rw [show 954 = 953 + 1 by norm_num, Nat.count_succ]
  rw [count_953]
  simp [prime_953, not_prime_954, not_prime_955, not_prime_956, not_prime_957, not_prime_958, not_prime_959, not_prime_960, not_prime_961, not_prime_962, not_prime_963, not_prime_964, not_prime_965, not_prime_966]

theorem prime_967 : (967 : Nat).Prime := by norm_num

theorem nth_162 : Nat.nth Nat.Prime 162 = 967 := by
  rw [← count_967]
  exact Nat.nth_count prime_967

theorem not_prime_968 : ¬Nat.Prime 968 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 484) (n := 968)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_969 : ¬Nat.Prime 969 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 323) (n := 969)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_970 : ¬Nat.Prime 970 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 485) (n := 970)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_971 : Nat.count Nat.Prime 971 = 163 := by
  rw [show 971 = 970 + 1 by norm_num, Nat.count_succ]
  rw [show 970 = 969 + 1 by norm_num, Nat.count_succ]
  rw [show 969 = 968 + 1 by norm_num, Nat.count_succ]
  rw [show 968 = 967 + 1 by norm_num, Nat.count_succ]
  rw [count_967]
  simp [prime_967, not_prime_968, not_prime_969, not_prime_970]

theorem prime_971 : (971 : Nat).Prime := by norm_num

theorem nth_163 : Nat.nth Nat.Prime 163 = 971 := by
  rw [← count_971]
  exact Nat.nth_count prime_971

theorem not_prime_972 : ¬Nat.Prime 972 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 486) (n := 972)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_973 : ¬Nat.Prime 973 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 139) (n := 973)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_974 : ¬Nat.Prime 974 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 487) (n := 974)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_975 : ¬Nat.Prime 975 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 325) (n := 975)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_976 : ¬Nat.Prime 976 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 488) (n := 976)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_977 : Nat.count Nat.Prime 977 = 164 := by
  rw [show 977 = 976 + 1 by norm_num, Nat.count_succ]
  rw [show 976 = 975 + 1 by norm_num, Nat.count_succ]
  rw [show 975 = 974 + 1 by norm_num, Nat.count_succ]
  rw [show 974 = 973 + 1 by norm_num, Nat.count_succ]
  rw [show 973 = 972 + 1 by norm_num, Nat.count_succ]
  rw [show 972 = 971 + 1 by norm_num, Nat.count_succ]
  rw [count_971]
  simp [prime_971, not_prime_972, not_prime_973, not_prime_974, not_prime_975, not_prime_976]

theorem prime_977 : (977 : Nat).Prime := by norm_num

theorem nth_164 : Nat.nth Nat.Prime 164 = 977 := by
  rw [← count_977]
  exact Nat.nth_count prime_977

theorem not_prime_978 : ¬Nat.Prime 978 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 489) (n := 978)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_979 : ¬Nat.Prime 979 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 89) (n := 979)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_980 : ¬Nat.Prime 980 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 490) (n := 980)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_981 : ¬Nat.Prime 981 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 327) (n := 981)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_982 : ¬Nat.Prime 982 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 491) (n := 982)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_983 : Nat.count Nat.Prime 983 = 165 := by
  rw [show 983 = 982 + 1 by norm_num, Nat.count_succ]
  rw [show 982 = 981 + 1 by norm_num, Nat.count_succ]
  rw [show 981 = 980 + 1 by norm_num, Nat.count_succ]
  rw [show 980 = 979 + 1 by norm_num, Nat.count_succ]
  rw [show 979 = 978 + 1 by norm_num, Nat.count_succ]
  rw [show 978 = 977 + 1 by norm_num, Nat.count_succ]
  rw [count_977]
  simp [prime_977, not_prime_978, not_prime_979, not_prime_980, not_prime_981, not_prime_982]

theorem prime_983 : (983 : Nat).Prime := by norm_num

theorem nth_165 : Nat.nth Nat.Prime 165 = 983 := by
  rw [← count_983]
  exact Nat.nth_count prime_983

theorem not_prime_984 : ¬Nat.Prime 984 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 492) (n := 984)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_985 : ¬Nat.Prime 985 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 197) (n := 985)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_986 : ¬Nat.Prime 986 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 493) (n := 986)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_987 : ¬Nat.Prime 987 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 329) (n := 987)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_988 : ¬Nat.Prime 988 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 494) (n := 988)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_989 : ¬Nat.Prime 989 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 43) (n := 989)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_990 : ¬Nat.Prime 990 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 495) (n := 990)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_991 : Nat.count Nat.Prime 991 = 166 := by
  rw [show 991 = 990 + 1 by norm_num, Nat.count_succ]
  rw [show 990 = 989 + 1 by norm_num, Nat.count_succ]
  rw [show 989 = 988 + 1 by norm_num, Nat.count_succ]
  rw [show 988 = 987 + 1 by norm_num, Nat.count_succ]
  rw [show 987 = 986 + 1 by norm_num, Nat.count_succ]
  rw [show 986 = 985 + 1 by norm_num, Nat.count_succ]
  rw [show 985 = 984 + 1 by norm_num, Nat.count_succ]
  rw [show 984 = 983 + 1 by norm_num, Nat.count_succ]
  rw [count_983]
  simp [prime_983, not_prime_984, not_prime_985, not_prime_986, not_prime_987, not_prime_988, not_prime_989, not_prime_990]

theorem prime_991 : (991 : Nat).Prime := by norm_num

theorem nth_166 : Nat.nth Nat.Prime 166 = 991 := by
  rw [← count_991]
  exact Nat.nth_count prime_991

theorem not_prime_992 : ¬Nat.Prime 992 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 496) (n := 992)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_993 : ¬Nat.Prime 993 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 331) (n := 993)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_994 : ¬Nat.Prime 994 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 497) (n := 994)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_995 : ¬Nat.Prime 995 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 199) (n := 995)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_996 : ¬Nat.Prime 996 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 498) (n := 996)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_997 : Nat.count Nat.Prime 997 = 167 := by
  rw [show 997 = 996 + 1 by norm_num, Nat.count_succ]
  rw [show 996 = 995 + 1 by norm_num, Nat.count_succ]
  rw [show 995 = 994 + 1 by norm_num, Nat.count_succ]
  rw [show 994 = 993 + 1 by norm_num, Nat.count_succ]
  rw [show 993 = 992 + 1 by norm_num, Nat.count_succ]
  rw [show 992 = 991 + 1 by norm_num, Nat.count_succ]
  rw [count_991]
  simp [prime_991, not_prime_992, not_prime_993, not_prime_994, not_prime_995, not_prime_996]

theorem prime_997 : (997 : Nat).Prime := by norm_num

theorem nth_167 : Nat.nth Nat.Prime 167 = 997 := by
  rw [← count_997]
  exact Nat.nth_count prime_997

theorem not_prime_998 : ¬Nat.Prime 998 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 499) (n := 998)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_999 : ¬Nat.Prime 999 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 333) (n := 999)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1000 : ¬Nat.Prime 1000 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 500) (n := 1000)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1001 : ¬Nat.Prime 1001 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 143) (n := 1001)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1002 : ¬Nat.Prime 1002 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 501) (n := 1002)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1003 : ¬Nat.Prime 1003 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 59) (n := 1003)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1004 : ¬Nat.Prime 1004 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 502) (n := 1004)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1005 : ¬Nat.Prime 1005 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 335) (n := 1005)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1006 : ¬Nat.Prime 1006 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 503) (n := 1006)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1007 : ¬Nat.Prime 1007 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 53) (n := 1007)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1008 : ¬Nat.Prime 1008 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 504) (n := 1008)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1009 : Nat.count Nat.Prime 1009 = 168 := by
  rw [show 1009 = 1008 + 1 by norm_num, Nat.count_succ]
  rw [show 1008 = 1007 + 1 by norm_num, Nat.count_succ]
  rw [show 1007 = 1006 + 1 by norm_num, Nat.count_succ]
  rw [show 1006 = 1005 + 1 by norm_num, Nat.count_succ]
  rw [show 1005 = 1004 + 1 by norm_num, Nat.count_succ]
  rw [show 1004 = 1003 + 1 by norm_num, Nat.count_succ]
  rw [show 1003 = 1002 + 1 by norm_num, Nat.count_succ]
  rw [show 1002 = 1001 + 1 by norm_num, Nat.count_succ]
  rw [show 1001 = 1000 + 1 by norm_num, Nat.count_succ]
  rw [show 1000 = 999 + 1 by norm_num, Nat.count_succ]
  rw [show 999 = 998 + 1 by norm_num, Nat.count_succ]
  rw [show 998 = 997 + 1 by norm_num, Nat.count_succ]
  rw [count_997]
  simp [prime_997, not_prime_998, not_prime_999, not_prime_1000, not_prime_1001, not_prime_1002, not_prime_1003, not_prime_1004, not_prime_1005, not_prime_1006, not_prime_1007, not_prime_1008]

theorem prime_1009 : (1009 : Nat).Prime := by norm_num

theorem nth_168 : Nat.nth Nat.Prime 168 = 1009 := by
  rw [← count_1009]
  exact Nat.nth_count prime_1009

theorem not_prime_1010 : ¬Nat.Prime 1010 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 505) (n := 1010)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1011 : ¬Nat.Prime 1011 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 337) (n := 1011)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1012 : ¬Nat.Prime 1012 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 506) (n := 1012)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1013 : Nat.count Nat.Prime 1013 = 169 := by
  rw [show 1013 = 1012 + 1 by norm_num, Nat.count_succ]
  rw [show 1012 = 1011 + 1 by norm_num, Nat.count_succ]
  rw [show 1011 = 1010 + 1 by norm_num, Nat.count_succ]
  rw [show 1010 = 1009 + 1 by norm_num, Nat.count_succ]
  rw [count_1009]
  simp [prime_1009, not_prime_1010, not_prime_1011, not_prime_1012]

theorem prime_1013 : (1013 : Nat).Prime := by norm_num

theorem nth_169 : Nat.nth Nat.Prime 169 = 1013 := by
  rw [← count_1013]
  exact Nat.nth_count prime_1013

theorem not_prime_1014 : ¬Nat.Prime 1014 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 507) (n := 1014)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1015 : ¬Nat.Prime 1015 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 203) (n := 1015)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1016 : ¬Nat.Prime 1016 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 508) (n := 1016)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1017 : ¬Nat.Prime 1017 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 339) (n := 1017)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1018 : ¬Nat.Prime 1018 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 509) (n := 1018)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1019 : Nat.count Nat.Prime 1019 = 170 := by
  rw [show 1019 = 1018 + 1 by norm_num, Nat.count_succ]
  rw [show 1018 = 1017 + 1 by norm_num, Nat.count_succ]
  rw [show 1017 = 1016 + 1 by norm_num, Nat.count_succ]
  rw [show 1016 = 1015 + 1 by norm_num, Nat.count_succ]
  rw [show 1015 = 1014 + 1 by norm_num, Nat.count_succ]
  rw [show 1014 = 1013 + 1 by norm_num, Nat.count_succ]
  rw [count_1013]
  simp [prime_1013, not_prime_1014, not_prime_1015, not_prime_1016, not_prime_1017, not_prime_1018]

theorem prime_1019 : (1019 : Nat).Prime := by norm_num

theorem nth_170 : Nat.nth Nat.Prime 170 = 1019 := by
  rw [← count_1019]
  exact Nat.nth_count prime_1019

theorem not_prime_1020 : ¬Nat.Prime 1020 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 510) (n := 1020)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1021 : Nat.count Nat.Prime 1021 = 171 := by
  rw [show 1021 = 1020 + 1 by norm_num, Nat.count_succ]
  rw [show 1020 = 1019 + 1 by norm_num, Nat.count_succ]
  rw [count_1019]
  simp [prime_1019, not_prime_1020]

theorem prime_1021 : (1021 : Nat).Prime := by norm_num

theorem nth_171 : Nat.nth Nat.Prime 171 = 1021 := by
  rw [← count_1021]
  exact Nat.nth_count prime_1021

theorem not_prime_1022 : ¬Nat.Prime 1022 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 511) (n := 1022)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1023 : ¬Nat.Prime 1023 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 341) (n := 1023)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1024 : ¬Nat.Prime 1024 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 512) (n := 1024)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1025 : ¬Nat.Prime 1025 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 205) (n := 1025)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1026 : ¬Nat.Prime 1026 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 513) (n := 1026)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1027 : ¬Nat.Prime 1027 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 79) (n := 1027)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1028 : ¬Nat.Prime 1028 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 514) (n := 1028)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1029 : ¬Nat.Prime 1029 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 343) (n := 1029)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1030 : ¬Nat.Prime 1030 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 515) (n := 1030)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1031 : Nat.count Nat.Prime 1031 = 172 := by
  rw [show 1031 = 1030 + 1 by norm_num, Nat.count_succ]
  rw [show 1030 = 1029 + 1 by norm_num, Nat.count_succ]
  rw [show 1029 = 1028 + 1 by norm_num, Nat.count_succ]
  rw [show 1028 = 1027 + 1 by norm_num, Nat.count_succ]
  rw [show 1027 = 1026 + 1 by norm_num, Nat.count_succ]
  rw [show 1026 = 1025 + 1 by norm_num, Nat.count_succ]
  rw [show 1025 = 1024 + 1 by norm_num, Nat.count_succ]
  rw [show 1024 = 1023 + 1 by norm_num, Nat.count_succ]
  rw [show 1023 = 1022 + 1 by norm_num, Nat.count_succ]
  rw [show 1022 = 1021 + 1 by norm_num, Nat.count_succ]
  rw [count_1021]
  simp [prime_1021, not_prime_1022, not_prime_1023, not_prime_1024, not_prime_1025, not_prime_1026, not_prime_1027, not_prime_1028, not_prime_1029, not_prime_1030]

theorem prime_1031 : (1031 : Nat).Prime := by norm_num

theorem nth_172 : Nat.nth Nat.Prime 172 = 1031 := by
  rw [← count_1031]
  exact Nat.nth_count prime_1031

theorem not_prime_1032 : ¬Nat.Prime 1032 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 516) (n := 1032)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1033 : Nat.count Nat.Prime 1033 = 173 := by
  rw [show 1033 = 1032 + 1 by norm_num, Nat.count_succ]
  rw [show 1032 = 1031 + 1 by norm_num, Nat.count_succ]
  rw [count_1031]
  simp [prime_1031, not_prime_1032]

theorem prime_1033 : (1033 : Nat).Prime := by norm_num

theorem nth_173 : Nat.nth Nat.Prime 173 = 1033 := by
  rw [← count_1033]
  exact Nat.nth_count prime_1033

theorem not_prime_1034 : ¬Nat.Prime 1034 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 517) (n := 1034)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1035 : ¬Nat.Prime 1035 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 345) (n := 1035)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1036 : ¬Nat.Prime 1036 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 518) (n := 1036)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1037 : ¬Nat.Prime 1037 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 61) (n := 1037)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1038 : ¬Nat.Prime 1038 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 519) (n := 1038)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1039 : Nat.count Nat.Prime 1039 = 174 := by
  rw [show 1039 = 1038 + 1 by norm_num, Nat.count_succ]
  rw [show 1038 = 1037 + 1 by norm_num, Nat.count_succ]
  rw [show 1037 = 1036 + 1 by norm_num, Nat.count_succ]
  rw [show 1036 = 1035 + 1 by norm_num, Nat.count_succ]
  rw [show 1035 = 1034 + 1 by norm_num, Nat.count_succ]
  rw [show 1034 = 1033 + 1 by norm_num, Nat.count_succ]
  rw [count_1033]
  simp [prime_1033, not_prime_1034, not_prime_1035, not_prime_1036, not_prime_1037, not_prime_1038]

theorem prime_1039 : (1039 : Nat).Prime := by norm_num

theorem nth_174 : Nat.nth Nat.Prime 174 = 1039 := by
  rw [← count_1039]
  exact Nat.nth_count prime_1039

end OeisA100474.PrimeCertificate
