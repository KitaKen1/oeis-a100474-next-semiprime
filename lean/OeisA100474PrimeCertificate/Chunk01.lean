import OeisA100474PrimeCertificate.Chunk00

/-! Kernel prime/count certificate, chunk 01 (25–49). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_98 : ¬Nat.Prime 98 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 49) (n := 98)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_99 : ¬Nat.Prime 99 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 33) (n := 99)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_100 : ¬Nat.Prime 100 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 50) (n := 100)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_101 : Nat.count Nat.Prime 101 = 25 := by
  rw [show 101 = 100 + 1 by norm_num, Nat.count_succ]
  rw [show 100 = 99 + 1 by norm_num, Nat.count_succ]
  rw [show 99 = 98 + 1 by norm_num, Nat.count_succ]
  rw [show 98 = 97 + 1 by norm_num, Nat.count_succ]
  rw [count_97]
  simp [prime_97, not_prime_98, not_prime_99, not_prime_100]

theorem prime_101 : (101 : Nat).Prime := by norm_num

theorem nth_25 : Nat.nth Nat.Prime 25 = 101 := by
  rw [← count_101]
  exact Nat.nth_count prime_101

theorem not_prime_102 : ¬Nat.Prime 102 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 51) (n := 102)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_103 : Nat.count Nat.Prime 103 = 26 := by
  rw [show 103 = 102 + 1 by norm_num, Nat.count_succ]
  rw [show 102 = 101 + 1 by norm_num, Nat.count_succ]
  rw [count_101]
  simp [prime_101, not_prime_102]

theorem prime_103 : (103 : Nat).Prime := by norm_num

theorem nth_26 : Nat.nth Nat.Prime 26 = 103 := by
  rw [← count_103]
  exact Nat.nth_count prime_103

theorem not_prime_104 : ¬Nat.Prime 104 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 52) (n := 104)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_105 : ¬Nat.Prime 105 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 35) (n := 105)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_106 : ¬Nat.Prime 106 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 53) (n := 106)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_107 : Nat.count Nat.Prime 107 = 27 := by
  rw [show 107 = 106 + 1 by norm_num, Nat.count_succ]
  rw [show 106 = 105 + 1 by norm_num, Nat.count_succ]
  rw [show 105 = 104 + 1 by norm_num, Nat.count_succ]
  rw [show 104 = 103 + 1 by norm_num, Nat.count_succ]
  rw [count_103]
  simp [prime_103, not_prime_104, not_prime_105, not_prime_106]

theorem prime_107 : (107 : Nat).Prime := by norm_num

theorem nth_27 : Nat.nth Nat.Prime 27 = 107 := by
  rw [← count_107]
  exact Nat.nth_count prime_107

theorem not_prime_108 : ¬Nat.Prime 108 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 54) (n := 108)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_109 : Nat.count Nat.Prime 109 = 28 := by
  rw [show 109 = 108 + 1 by norm_num, Nat.count_succ]
  rw [show 108 = 107 + 1 by norm_num, Nat.count_succ]
  rw [count_107]
  simp [prime_107, not_prime_108]

theorem prime_109 : (109 : Nat).Prime := by norm_num

theorem nth_28 : Nat.nth Nat.Prime 28 = 109 := by
  rw [← count_109]
  exact Nat.nth_count prime_109

theorem not_prime_110 : ¬Nat.Prime 110 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 55) (n := 110)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_111 : ¬Nat.Prime 111 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 37) (n := 111)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_112 : ¬Nat.Prime 112 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 56) (n := 112)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_113 : Nat.count Nat.Prime 113 = 29 := by
  rw [show 113 = 112 + 1 by norm_num, Nat.count_succ]
  rw [show 112 = 111 + 1 by norm_num, Nat.count_succ]
  rw [show 111 = 110 + 1 by norm_num, Nat.count_succ]
  rw [show 110 = 109 + 1 by norm_num, Nat.count_succ]
  rw [count_109]
  simp [prime_109, not_prime_110, not_prime_111, not_prime_112]

theorem prime_113 : (113 : Nat).Prime := by norm_num

theorem nth_29 : Nat.nth Nat.Prime 29 = 113 := by
  rw [← count_113]
  exact Nat.nth_count prime_113

theorem not_prime_114 : ¬Nat.Prime 114 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 57) (n := 114)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_115 : ¬Nat.Prime 115 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 23) (n := 115)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_116 : ¬Nat.Prime 116 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 58) (n := 116)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_117 : ¬Nat.Prime 117 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 39) (n := 117)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_118 : ¬Nat.Prime 118 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 59) (n := 118)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_119 : ¬Nat.Prime 119 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 17) (n := 119)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_120 : ¬Nat.Prime 120 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 60) (n := 120)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_121 : ¬Nat.Prime 121 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 11) (n := 121)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_122 : ¬Nat.Prime 122 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 61) (n := 122)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_123 : ¬Nat.Prime 123 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 41) (n := 123)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_124 : ¬Nat.Prime 124 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 62) (n := 124)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_125 : ¬Nat.Prime 125 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 25) (n := 125)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_126 : ¬Nat.Prime 126 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 63) (n := 126)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_127 : Nat.count Nat.Prime 127 = 30 := by
  rw [show 127 = 126 + 1 by norm_num, Nat.count_succ]
  rw [show 126 = 125 + 1 by norm_num, Nat.count_succ]
  rw [show 125 = 124 + 1 by norm_num, Nat.count_succ]
  rw [show 124 = 123 + 1 by norm_num, Nat.count_succ]
  rw [show 123 = 122 + 1 by norm_num, Nat.count_succ]
  rw [show 122 = 121 + 1 by norm_num, Nat.count_succ]
  rw [show 121 = 120 + 1 by norm_num, Nat.count_succ]
  rw [show 120 = 119 + 1 by norm_num, Nat.count_succ]
  rw [show 119 = 118 + 1 by norm_num, Nat.count_succ]
  rw [show 118 = 117 + 1 by norm_num, Nat.count_succ]
  rw [show 117 = 116 + 1 by norm_num, Nat.count_succ]
  rw [show 116 = 115 + 1 by norm_num, Nat.count_succ]
  rw [show 115 = 114 + 1 by norm_num, Nat.count_succ]
  rw [show 114 = 113 + 1 by norm_num, Nat.count_succ]
  rw [count_113]
  simp [prime_113, not_prime_114, not_prime_115, not_prime_116, not_prime_117, not_prime_118, not_prime_119, not_prime_120, not_prime_121, not_prime_122, not_prime_123, not_prime_124, not_prime_125, not_prime_126]

theorem prime_127 : (127 : Nat).Prime := by norm_num

theorem nth_30 : Nat.nth Nat.Prime 30 = 127 := by
  rw [← count_127]
  exact Nat.nth_count prime_127

theorem not_prime_128 : ¬Nat.Prime 128 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 64) (n := 128)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_129 : ¬Nat.Prime 129 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 43) (n := 129)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_130 : ¬Nat.Prime 130 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 65) (n := 130)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_131 : Nat.count Nat.Prime 131 = 31 := by
  rw [show 131 = 130 + 1 by norm_num, Nat.count_succ]
  rw [show 130 = 129 + 1 by norm_num, Nat.count_succ]
  rw [show 129 = 128 + 1 by norm_num, Nat.count_succ]
  rw [show 128 = 127 + 1 by norm_num, Nat.count_succ]
  rw [count_127]
  simp [prime_127, not_prime_128, not_prime_129, not_prime_130]

theorem prime_131 : (131 : Nat).Prime := by norm_num

theorem nth_31 : Nat.nth Nat.Prime 31 = 131 := by
  rw [← count_131]
  exact Nat.nth_count prime_131

theorem not_prime_132 : ¬Nat.Prime 132 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 66) (n := 132)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_133 : ¬Nat.Prime 133 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 19) (n := 133)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_134 : ¬Nat.Prime 134 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 67) (n := 134)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_135 : ¬Nat.Prime 135 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 45) (n := 135)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_136 : ¬Nat.Prime 136 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 68) (n := 136)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_137 : Nat.count Nat.Prime 137 = 32 := by
  rw [show 137 = 136 + 1 by norm_num, Nat.count_succ]
  rw [show 136 = 135 + 1 by norm_num, Nat.count_succ]
  rw [show 135 = 134 + 1 by norm_num, Nat.count_succ]
  rw [show 134 = 133 + 1 by norm_num, Nat.count_succ]
  rw [show 133 = 132 + 1 by norm_num, Nat.count_succ]
  rw [show 132 = 131 + 1 by norm_num, Nat.count_succ]
  rw [count_131]
  simp [prime_131, not_prime_132, not_prime_133, not_prime_134, not_prime_135, not_prime_136]

theorem prime_137 : (137 : Nat).Prime := by norm_num

theorem nth_32 : Nat.nth Nat.Prime 32 = 137 := by
  rw [← count_137]
  exact Nat.nth_count prime_137

theorem not_prime_138 : ¬Nat.Prime 138 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 69) (n := 138)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_139 : Nat.count Nat.Prime 139 = 33 := by
  rw [show 139 = 138 + 1 by norm_num, Nat.count_succ]
  rw [show 138 = 137 + 1 by norm_num, Nat.count_succ]
  rw [count_137]
  simp [prime_137, not_prime_138]

theorem prime_139 : (139 : Nat).Prime := by norm_num

theorem nth_33 : Nat.nth Nat.Prime 33 = 139 := by
  rw [← count_139]
  exact Nat.nth_count prime_139

theorem not_prime_140 : ¬Nat.Prime 140 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 70) (n := 140)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_141 : ¬Nat.Prime 141 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 47) (n := 141)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_142 : ¬Nat.Prime 142 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 71) (n := 142)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_143 : ¬Nat.Prime 143 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 13) (n := 143)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_144 : ¬Nat.Prime 144 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 72) (n := 144)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_145 : ¬Nat.Prime 145 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 29) (n := 145)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_146 : ¬Nat.Prime 146 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 73) (n := 146)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_147 : ¬Nat.Prime 147 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 49) (n := 147)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_148 : ¬Nat.Prime 148 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 74) (n := 148)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_149 : Nat.count Nat.Prime 149 = 34 := by
  rw [show 149 = 148 + 1 by norm_num, Nat.count_succ]
  rw [show 148 = 147 + 1 by norm_num, Nat.count_succ]
  rw [show 147 = 146 + 1 by norm_num, Nat.count_succ]
  rw [show 146 = 145 + 1 by norm_num, Nat.count_succ]
  rw [show 145 = 144 + 1 by norm_num, Nat.count_succ]
  rw [show 144 = 143 + 1 by norm_num, Nat.count_succ]
  rw [show 143 = 142 + 1 by norm_num, Nat.count_succ]
  rw [show 142 = 141 + 1 by norm_num, Nat.count_succ]
  rw [show 141 = 140 + 1 by norm_num, Nat.count_succ]
  rw [show 140 = 139 + 1 by norm_num, Nat.count_succ]
  rw [count_139]
  simp [prime_139, not_prime_140, not_prime_141, not_prime_142, not_prime_143, not_prime_144, not_prime_145, not_prime_146, not_prime_147, not_prime_148]

theorem prime_149 : (149 : Nat).Prime := by norm_num

theorem nth_34 : Nat.nth Nat.Prime 34 = 149 := by
  rw [← count_149]
  exact Nat.nth_count prime_149

theorem not_prime_150 : ¬Nat.Prime 150 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 75) (n := 150)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_151 : Nat.count Nat.Prime 151 = 35 := by
  rw [show 151 = 150 + 1 by norm_num, Nat.count_succ]
  rw [show 150 = 149 + 1 by norm_num, Nat.count_succ]
  rw [count_149]
  simp [prime_149, not_prime_150]

theorem prime_151 : (151 : Nat).Prime := by norm_num

theorem nth_35 : Nat.nth Nat.Prime 35 = 151 := by
  rw [← count_151]
  exact Nat.nth_count prime_151

theorem not_prime_152 : ¬Nat.Prime 152 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 76) (n := 152)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_153 : ¬Nat.Prime 153 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 51) (n := 153)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_154 : ¬Nat.Prime 154 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 77) (n := 154)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_155 : ¬Nat.Prime 155 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 31) (n := 155)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_156 : ¬Nat.Prime 156 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 78) (n := 156)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_157 : Nat.count Nat.Prime 157 = 36 := by
  rw [show 157 = 156 + 1 by norm_num, Nat.count_succ]
  rw [show 156 = 155 + 1 by norm_num, Nat.count_succ]
  rw [show 155 = 154 + 1 by norm_num, Nat.count_succ]
  rw [show 154 = 153 + 1 by norm_num, Nat.count_succ]
  rw [show 153 = 152 + 1 by norm_num, Nat.count_succ]
  rw [show 152 = 151 + 1 by norm_num, Nat.count_succ]
  rw [count_151]
  simp [prime_151, not_prime_152, not_prime_153, not_prime_154, not_prime_155, not_prime_156]

theorem prime_157 : (157 : Nat).Prime := by norm_num

theorem nth_36 : Nat.nth Nat.Prime 36 = 157 := by
  rw [← count_157]
  exact Nat.nth_count prime_157

theorem not_prime_158 : ¬Nat.Prime 158 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 79) (n := 158)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_159 : ¬Nat.Prime 159 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 53) (n := 159)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_160 : ¬Nat.Prime 160 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 80) (n := 160)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_161 : ¬Nat.Prime 161 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 23) (n := 161)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_162 : ¬Nat.Prime 162 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 81) (n := 162)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_163 : Nat.count Nat.Prime 163 = 37 := by
  rw [show 163 = 162 + 1 by norm_num, Nat.count_succ]
  rw [show 162 = 161 + 1 by norm_num, Nat.count_succ]
  rw [show 161 = 160 + 1 by norm_num, Nat.count_succ]
  rw [show 160 = 159 + 1 by norm_num, Nat.count_succ]
  rw [show 159 = 158 + 1 by norm_num, Nat.count_succ]
  rw [show 158 = 157 + 1 by norm_num, Nat.count_succ]
  rw [count_157]
  simp [prime_157, not_prime_158, not_prime_159, not_prime_160, not_prime_161, not_prime_162]

theorem prime_163 : (163 : Nat).Prime := by norm_num

theorem nth_37 : Nat.nth Nat.Prime 37 = 163 := by
  rw [← count_163]
  exact Nat.nth_count prime_163

theorem not_prime_164 : ¬Nat.Prime 164 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 82) (n := 164)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_165 : ¬Nat.Prime 165 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 55) (n := 165)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_166 : ¬Nat.Prime 166 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 83) (n := 166)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_167 : Nat.count Nat.Prime 167 = 38 := by
  rw [show 167 = 166 + 1 by norm_num, Nat.count_succ]
  rw [show 166 = 165 + 1 by norm_num, Nat.count_succ]
  rw [show 165 = 164 + 1 by norm_num, Nat.count_succ]
  rw [show 164 = 163 + 1 by norm_num, Nat.count_succ]
  rw [count_163]
  simp [prime_163, not_prime_164, not_prime_165, not_prime_166]

theorem prime_167 : (167 : Nat).Prime := by norm_num

theorem nth_38 : Nat.nth Nat.Prime 38 = 167 := by
  rw [← count_167]
  exact Nat.nth_count prime_167

theorem not_prime_168 : ¬Nat.Prime 168 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 84) (n := 168)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_169 : ¬Nat.Prime 169 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 13) (n := 169)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_170 : ¬Nat.Prime 170 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 85) (n := 170)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_171 : ¬Nat.Prime 171 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 57) (n := 171)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_172 : ¬Nat.Prime 172 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 86) (n := 172)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_173 : Nat.count Nat.Prime 173 = 39 := by
  rw [show 173 = 172 + 1 by norm_num, Nat.count_succ]
  rw [show 172 = 171 + 1 by norm_num, Nat.count_succ]
  rw [show 171 = 170 + 1 by norm_num, Nat.count_succ]
  rw [show 170 = 169 + 1 by norm_num, Nat.count_succ]
  rw [show 169 = 168 + 1 by norm_num, Nat.count_succ]
  rw [show 168 = 167 + 1 by norm_num, Nat.count_succ]
  rw [count_167]
  simp [prime_167, not_prime_168, not_prime_169, not_prime_170, not_prime_171, not_prime_172]

theorem prime_173 : (173 : Nat).Prime := by norm_num

theorem nth_39 : Nat.nth Nat.Prime 39 = 173 := by
  rw [← count_173]
  exact Nat.nth_count prime_173

theorem not_prime_174 : ¬Nat.Prime 174 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 87) (n := 174)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_175 : ¬Nat.Prime 175 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 35) (n := 175)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_176 : ¬Nat.Prime 176 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 88) (n := 176)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_177 : ¬Nat.Prime 177 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 59) (n := 177)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_178 : ¬Nat.Prime 178 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 89) (n := 178)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_179 : Nat.count Nat.Prime 179 = 40 := by
  rw [show 179 = 178 + 1 by norm_num, Nat.count_succ]
  rw [show 178 = 177 + 1 by norm_num, Nat.count_succ]
  rw [show 177 = 176 + 1 by norm_num, Nat.count_succ]
  rw [show 176 = 175 + 1 by norm_num, Nat.count_succ]
  rw [show 175 = 174 + 1 by norm_num, Nat.count_succ]
  rw [show 174 = 173 + 1 by norm_num, Nat.count_succ]
  rw [count_173]
  simp [prime_173, not_prime_174, not_prime_175, not_prime_176, not_prime_177, not_prime_178]

theorem prime_179 : (179 : Nat).Prime := by norm_num

theorem nth_40 : Nat.nth Nat.Prime 40 = 179 := by
  rw [← count_179]
  exact Nat.nth_count prime_179

theorem not_prime_180 : ¬Nat.Prime 180 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 90) (n := 180)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_181 : Nat.count Nat.Prime 181 = 41 := by
  rw [show 181 = 180 + 1 by norm_num, Nat.count_succ]
  rw [show 180 = 179 + 1 by norm_num, Nat.count_succ]
  rw [count_179]
  simp [prime_179, not_prime_180]

theorem prime_181 : (181 : Nat).Prime := by norm_num

theorem nth_41 : Nat.nth Nat.Prime 41 = 181 := by
  rw [← count_181]
  exact Nat.nth_count prime_181

theorem not_prime_182 : ¬Nat.Prime 182 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 91) (n := 182)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_183 : ¬Nat.Prime 183 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 61) (n := 183)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_184 : ¬Nat.Prime 184 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 92) (n := 184)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_185 : ¬Nat.Prime 185 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 37) (n := 185)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_186 : ¬Nat.Prime 186 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 93) (n := 186)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_187 : ¬Nat.Prime 187 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 17) (n := 187)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_188 : ¬Nat.Prime 188 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 94) (n := 188)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_189 : ¬Nat.Prime 189 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 63) (n := 189)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_190 : ¬Nat.Prime 190 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 95) (n := 190)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_191 : Nat.count Nat.Prime 191 = 42 := by
  rw [show 191 = 190 + 1 by norm_num, Nat.count_succ]
  rw [show 190 = 189 + 1 by norm_num, Nat.count_succ]
  rw [show 189 = 188 + 1 by norm_num, Nat.count_succ]
  rw [show 188 = 187 + 1 by norm_num, Nat.count_succ]
  rw [show 187 = 186 + 1 by norm_num, Nat.count_succ]
  rw [show 186 = 185 + 1 by norm_num, Nat.count_succ]
  rw [show 185 = 184 + 1 by norm_num, Nat.count_succ]
  rw [show 184 = 183 + 1 by norm_num, Nat.count_succ]
  rw [show 183 = 182 + 1 by norm_num, Nat.count_succ]
  rw [show 182 = 181 + 1 by norm_num, Nat.count_succ]
  rw [count_181]
  simp [prime_181, not_prime_182, not_prime_183, not_prime_184, not_prime_185, not_prime_186, not_prime_187, not_prime_188, not_prime_189, not_prime_190]

theorem prime_191 : (191 : Nat).Prime := by norm_num

theorem nth_42 : Nat.nth Nat.Prime 42 = 191 := by
  rw [← count_191]
  exact Nat.nth_count prime_191

theorem not_prime_192 : ¬Nat.Prime 192 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 96) (n := 192)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_193 : Nat.count Nat.Prime 193 = 43 := by
  rw [show 193 = 192 + 1 by norm_num, Nat.count_succ]
  rw [show 192 = 191 + 1 by norm_num, Nat.count_succ]
  rw [count_191]
  simp [prime_191, not_prime_192]

theorem prime_193 : (193 : Nat).Prime := by norm_num

theorem nth_43 : Nat.nth Nat.Prime 43 = 193 := by
  rw [← count_193]
  exact Nat.nth_count prime_193

theorem not_prime_194 : ¬Nat.Prime 194 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 97) (n := 194)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_195 : ¬Nat.Prime 195 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 65) (n := 195)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_196 : ¬Nat.Prime 196 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 98) (n := 196)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_197 : Nat.count Nat.Prime 197 = 44 := by
  rw [show 197 = 196 + 1 by norm_num, Nat.count_succ]
  rw [show 196 = 195 + 1 by norm_num, Nat.count_succ]
  rw [show 195 = 194 + 1 by norm_num, Nat.count_succ]
  rw [show 194 = 193 + 1 by norm_num, Nat.count_succ]
  rw [count_193]
  simp [prime_193, not_prime_194, not_prime_195, not_prime_196]

theorem prime_197 : (197 : Nat).Prime := by norm_num

theorem nth_44 : Nat.nth Nat.Prime 44 = 197 := by
  rw [← count_197]
  exact Nat.nth_count prime_197

theorem not_prime_198 : ¬Nat.Prime 198 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 99) (n := 198)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_199 : Nat.count Nat.Prime 199 = 45 := by
  rw [show 199 = 198 + 1 by norm_num, Nat.count_succ]
  rw [show 198 = 197 + 1 by norm_num, Nat.count_succ]
  rw [count_197]
  simp [prime_197, not_prime_198]

theorem prime_199 : (199 : Nat).Prime := by norm_num

theorem nth_45 : Nat.nth Nat.Prime 45 = 199 := by
  rw [← count_199]
  exact Nat.nth_count prime_199

theorem not_prime_200 : ¬Nat.Prime 200 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 100) (n := 200)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_201 : ¬Nat.Prime 201 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 67) (n := 201)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_202 : ¬Nat.Prime 202 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 101) (n := 202)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_203 : ¬Nat.Prime 203 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 29) (n := 203)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_204 : ¬Nat.Prime 204 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 102) (n := 204)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_205 : ¬Nat.Prime 205 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 41) (n := 205)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_206 : ¬Nat.Prime 206 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 103) (n := 206)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_207 : ¬Nat.Prime 207 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 69) (n := 207)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_208 : ¬Nat.Prime 208 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 104) (n := 208)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_209 : ¬Nat.Prime 209 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 19) (n := 209)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_210 : ¬Nat.Prime 210 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 105) (n := 210)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_211 : Nat.count Nat.Prime 211 = 46 := by
  rw [show 211 = 210 + 1 by norm_num, Nat.count_succ]
  rw [show 210 = 209 + 1 by norm_num, Nat.count_succ]
  rw [show 209 = 208 + 1 by norm_num, Nat.count_succ]
  rw [show 208 = 207 + 1 by norm_num, Nat.count_succ]
  rw [show 207 = 206 + 1 by norm_num, Nat.count_succ]
  rw [show 206 = 205 + 1 by norm_num, Nat.count_succ]
  rw [show 205 = 204 + 1 by norm_num, Nat.count_succ]
  rw [show 204 = 203 + 1 by norm_num, Nat.count_succ]
  rw [show 203 = 202 + 1 by norm_num, Nat.count_succ]
  rw [show 202 = 201 + 1 by norm_num, Nat.count_succ]
  rw [show 201 = 200 + 1 by norm_num, Nat.count_succ]
  rw [show 200 = 199 + 1 by norm_num, Nat.count_succ]
  rw [count_199]
  simp [prime_199, not_prime_200, not_prime_201, not_prime_202, not_prime_203, not_prime_204, not_prime_205, not_prime_206, not_prime_207, not_prime_208, not_prime_209, not_prime_210]

theorem prime_211 : (211 : Nat).Prime := by norm_num

theorem nth_46 : Nat.nth Nat.Prime 46 = 211 := by
  rw [← count_211]
  exact Nat.nth_count prime_211

theorem not_prime_212 : ¬Nat.Prime 212 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 106) (n := 212)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_213 : ¬Nat.Prime 213 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 71) (n := 213)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_214 : ¬Nat.Prime 214 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 107) (n := 214)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_215 : ¬Nat.Prime 215 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 43) (n := 215)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_216 : ¬Nat.Prime 216 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 108) (n := 216)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_217 : ¬Nat.Prime 217 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 31) (n := 217)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_218 : ¬Nat.Prime 218 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 109) (n := 218)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_219 : ¬Nat.Prime 219 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 73) (n := 219)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_220 : ¬Nat.Prime 220 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 110) (n := 220)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_221 : ¬Nat.Prime 221 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 17) (n := 221)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_222 : ¬Nat.Prime 222 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 111) (n := 222)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_223 : Nat.count Nat.Prime 223 = 47 := by
  rw [show 223 = 222 + 1 by norm_num, Nat.count_succ]
  rw [show 222 = 221 + 1 by norm_num, Nat.count_succ]
  rw [show 221 = 220 + 1 by norm_num, Nat.count_succ]
  rw [show 220 = 219 + 1 by norm_num, Nat.count_succ]
  rw [show 219 = 218 + 1 by norm_num, Nat.count_succ]
  rw [show 218 = 217 + 1 by norm_num, Nat.count_succ]
  rw [show 217 = 216 + 1 by norm_num, Nat.count_succ]
  rw [show 216 = 215 + 1 by norm_num, Nat.count_succ]
  rw [show 215 = 214 + 1 by norm_num, Nat.count_succ]
  rw [show 214 = 213 + 1 by norm_num, Nat.count_succ]
  rw [show 213 = 212 + 1 by norm_num, Nat.count_succ]
  rw [show 212 = 211 + 1 by norm_num, Nat.count_succ]
  rw [count_211]
  simp [prime_211, not_prime_212, not_prime_213, not_prime_214, not_prime_215, not_prime_216, not_prime_217, not_prime_218, not_prime_219, not_prime_220, not_prime_221, not_prime_222]

theorem prime_223 : (223 : Nat).Prime := by norm_num

theorem nth_47 : Nat.nth Nat.Prime 47 = 223 := by
  rw [← count_223]
  exact Nat.nth_count prime_223

theorem not_prime_224 : ¬Nat.Prime 224 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 112) (n := 224)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_225 : ¬Nat.Prime 225 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 75) (n := 225)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_226 : ¬Nat.Prime 226 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 113) (n := 226)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_227 : Nat.count Nat.Prime 227 = 48 := by
  rw [show 227 = 226 + 1 by norm_num, Nat.count_succ]
  rw [show 226 = 225 + 1 by norm_num, Nat.count_succ]
  rw [show 225 = 224 + 1 by norm_num, Nat.count_succ]
  rw [show 224 = 223 + 1 by norm_num, Nat.count_succ]
  rw [count_223]
  simp [prime_223, not_prime_224, not_prime_225, not_prime_226]

theorem prime_227 : (227 : Nat).Prime := by norm_num

theorem nth_48 : Nat.nth Nat.Prime 48 = 227 := by
  rw [← count_227]
  exact Nat.nth_count prime_227

theorem not_prime_228 : ¬Nat.Prime 228 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 114) (n := 228)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_229 : Nat.count Nat.Prime 229 = 49 := by
  rw [show 229 = 228 + 1 by norm_num, Nat.count_succ]
  rw [show 228 = 227 + 1 by norm_num, Nat.count_succ]
  rw [count_227]
  simp [prime_227, not_prime_228]

theorem prime_229 : (229 : Nat).Prime := by norm_num

theorem nth_49 : Nat.nth Nat.Prime 49 = 229 := by
  rw [← count_229]
  exact Nat.nth_count prime_229

end OeisA100474.PrimeCertificate
