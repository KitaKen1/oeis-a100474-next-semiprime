import OeisA100474PrimeCertificate.Chunk01

/-! Kernel prime/count certificate, chunk 02 (50–74). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_230 : ¬Nat.Prime 230 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 115) (n := 230)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_231 : ¬Nat.Prime 231 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 77) (n := 231)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_232 : ¬Nat.Prime 232 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 116) (n := 232)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_233 : Nat.count Nat.Prime 233 = 50 := by
  rw [show 233 = 232 + 1 by norm_num, Nat.count_succ]
  rw [show 232 = 231 + 1 by norm_num, Nat.count_succ]
  rw [show 231 = 230 + 1 by norm_num, Nat.count_succ]
  rw [show 230 = 229 + 1 by norm_num, Nat.count_succ]
  rw [count_229]
  simp [prime_229, not_prime_230, not_prime_231, not_prime_232]

theorem prime_233 : (233 : Nat).Prime := by norm_num

theorem nth_50 : Nat.nth Nat.Prime 50 = 233 := by
  rw [← count_233]
  exact Nat.nth_count prime_233

theorem not_prime_234 : ¬Nat.Prime 234 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 117) (n := 234)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_235 : ¬Nat.Prime 235 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 47) (n := 235)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_236 : ¬Nat.Prime 236 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 118) (n := 236)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_237 : ¬Nat.Prime 237 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 79) (n := 237)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_238 : ¬Nat.Prime 238 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 119) (n := 238)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_239 : Nat.count Nat.Prime 239 = 51 := by
  rw [show 239 = 238 + 1 by norm_num, Nat.count_succ]
  rw [show 238 = 237 + 1 by norm_num, Nat.count_succ]
  rw [show 237 = 236 + 1 by norm_num, Nat.count_succ]
  rw [show 236 = 235 + 1 by norm_num, Nat.count_succ]
  rw [show 235 = 234 + 1 by norm_num, Nat.count_succ]
  rw [show 234 = 233 + 1 by norm_num, Nat.count_succ]
  rw [count_233]
  simp [prime_233, not_prime_234, not_prime_235, not_prime_236, not_prime_237, not_prime_238]

theorem prime_239 : (239 : Nat).Prime := by norm_num

theorem nth_51 : Nat.nth Nat.Prime 51 = 239 := by
  rw [← count_239]
  exact Nat.nth_count prime_239

theorem not_prime_240 : ¬Nat.Prime 240 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 120) (n := 240)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_241 : Nat.count Nat.Prime 241 = 52 := by
  rw [show 241 = 240 + 1 by norm_num, Nat.count_succ]
  rw [show 240 = 239 + 1 by norm_num, Nat.count_succ]
  rw [count_239]
  simp [prime_239, not_prime_240]

theorem prime_241 : (241 : Nat).Prime := by norm_num

theorem nth_52 : Nat.nth Nat.Prime 52 = 241 := by
  rw [← count_241]
  exact Nat.nth_count prime_241

theorem not_prime_242 : ¬Nat.Prime 242 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 121) (n := 242)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_243 : ¬Nat.Prime 243 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 81) (n := 243)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_244 : ¬Nat.Prime 244 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 122) (n := 244)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_245 : ¬Nat.Prime 245 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 49) (n := 245)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_246 : ¬Nat.Prime 246 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 123) (n := 246)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_247 : ¬Nat.Prime 247 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 19) (n := 247)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_248 : ¬Nat.Prime 248 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 124) (n := 248)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_249 : ¬Nat.Prime 249 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 83) (n := 249)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_250 : ¬Nat.Prime 250 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 125) (n := 250)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_251 : Nat.count Nat.Prime 251 = 53 := by
  rw [show 251 = 250 + 1 by norm_num, Nat.count_succ]
  rw [show 250 = 249 + 1 by norm_num, Nat.count_succ]
  rw [show 249 = 248 + 1 by norm_num, Nat.count_succ]
  rw [show 248 = 247 + 1 by norm_num, Nat.count_succ]
  rw [show 247 = 246 + 1 by norm_num, Nat.count_succ]
  rw [show 246 = 245 + 1 by norm_num, Nat.count_succ]
  rw [show 245 = 244 + 1 by norm_num, Nat.count_succ]
  rw [show 244 = 243 + 1 by norm_num, Nat.count_succ]
  rw [show 243 = 242 + 1 by norm_num, Nat.count_succ]
  rw [show 242 = 241 + 1 by norm_num, Nat.count_succ]
  rw [count_241]
  simp [prime_241, not_prime_242, not_prime_243, not_prime_244, not_prime_245, not_prime_246, not_prime_247, not_prime_248, not_prime_249, not_prime_250]

theorem prime_251 : (251 : Nat).Prime := by norm_num

theorem nth_53 : Nat.nth Nat.Prime 53 = 251 := by
  rw [← count_251]
  exact Nat.nth_count prime_251

theorem not_prime_252 : ¬Nat.Prime 252 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 126) (n := 252)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_253 : ¬Nat.Prime 253 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 23) (n := 253)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_254 : ¬Nat.Prime 254 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 127) (n := 254)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_255 : ¬Nat.Prime 255 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 85) (n := 255)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_256 : ¬Nat.Prime 256 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 128) (n := 256)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_257 : Nat.count Nat.Prime 257 = 54 := by
  rw [show 257 = 256 + 1 by norm_num, Nat.count_succ]
  rw [show 256 = 255 + 1 by norm_num, Nat.count_succ]
  rw [show 255 = 254 + 1 by norm_num, Nat.count_succ]
  rw [show 254 = 253 + 1 by norm_num, Nat.count_succ]
  rw [show 253 = 252 + 1 by norm_num, Nat.count_succ]
  rw [show 252 = 251 + 1 by norm_num, Nat.count_succ]
  rw [count_251]
  simp [prime_251, not_prime_252, not_prime_253, not_prime_254, not_prime_255, not_prime_256]

theorem prime_257 : (257 : Nat).Prime := by norm_num

theorem nth_54 : Nat.nth Nat.Prime 54 = 257 := by
  rw [← count_257]
  exact Nat.nth_count prime_257

theorem not_prime_258 : ¬Nat.Prime 258 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 129) (n := 258)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_259 : ¬Nat.Prime 259 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 37) (n := 259)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_260 : ¬Nat.Prime 260 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 130) (n := 260)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_261 : ¬Nat.Prime 261 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 87) (n := 261)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_262 : ¬Nat.Prime 262 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 131) (n := 262)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_263 : Nat.count Nat.Prime 263 = 55 := by
  rw [show 263 = 262 + 1 by norm_num, Nat.count_succ]
  rw [show 262 = 261 + 1 by norm_num, Nat.count_succ]
  rw [show 261 = 260 + 1 by norm_num, Nat.count_succ]
  rw [show 260 = 259 + 1 by norm_num, Nat.count_succ]
  rw [show 259 = 258 + 1 by norm_num, Nat.count_succ]
  rw [show 258 = 257 + 1 by norm_num, Nat.count_succ]
  rw [count_257]
  simp [prime_257, not_prime_258, not_prime_259, not_prime_260, not_prime_261, not_prime_262]

theorem prime_263 : (263 : Nat).Prime := by norm_num

theorem nth_55 : Nat.nth Nat.Prime 55 = 263 := by
  rw [← count_263]
  exact Nat.nth_count prime_263

theorem not_prime_264 : ¬Nat.Prime 264 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 132) (n := 264)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_265 : ¬Nat.Prime 265 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 53) (n := 265)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_266 : ¬Nat.Prime 266 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 133) (n := 266)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_267 : ¬Nat.Prime 267 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 89) (n := 267)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_268 : ¬Nat.Prime 268 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 134) (n := 268)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_269 : Nat.count Nat.Prime 269 = 56 := by
  rw [show 269 = 268 + 1 by norm_num, Nat.count_succ]
  rw [show 268 = 267 + 1 by norm_num, Nat.count_succ]
  rw [show 267 = 266 + 1 by norm_num, Nat.count_succ]
  rw [show 266 = 265 + 1 by norm_num, Nat.count_succ]
  rw [show 265 = 264 + 1 by norm_num, Nat.count_succ]
  rw [show 264 = 263 + 1 by norm_num, Nat.count_succ]
  rw [count_263]
  simp [prime_263, not_prime_264, not_prime_265, not_prime_266, not_prime_267, not_prime_268]

theorem prime_269 : (269 : Nat).Prime := by norm_num

theorem nth_56 : Nat.nth Nat.Prime 56 = 269 := by
  rw [← count_269]
  exact Nat.nth_count prime_269

theorem not_prime_270 : ¬Nat.Prime 270 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 135) (n := 270)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_271 : Nat.count Nat.Prime 271 = 57 := by
  rw [show 271 = 270 + 1 by norm_num, Nat.count_succ]
  rw [show 270 = 269 + 1 by norm_num, Nat.count_succ]
  rw [count_269]
  simp [prime_269, not_prime_270]

theorem prime_271 : (271 : Nat).Prime := by norm_num

theorem nth_57 : Nat.nth Nat.Prime 57 = 271 := by
  rw [← count_271]
  exact Nat.nth_count prime_271

theorem not_prime_272 : ¬Nat.Prime 272 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 136) (n := 272)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_273 : ¬Nat.Prime 273 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 91) (n := 273)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_274 : ¬Nat.Prime 274 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 137) (n := 274)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_275 : ¬Nat.Prime 275 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 55) (n := 275)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_276 : ¬Nat.Prime 276 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 138) (n := 276)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_277 : Nat.count Nat.Prime 277 = 58 := by
  rw [show 277 = 276 + 1 by norm_num, Nat.count_succ]
  rw [show 276 = 275 + 1 by norm_num, Nat.count_succ]
  rw [show 275 = 274 + 1 by norm_num, Nat.count_succ]
  rw [show 274 = 273 + 1 by norm_num, Nat.count_succ]
  rw [show 273 = 272 + 1 by norm_num, Nat.count_succ]
  rw [show 272 = 271 + 1 by norm_num, Nat.count_succ]
  rw [count_271]
  simp [prime_271, not_prime_272, not_prime_273, not_prime_274, not_prime_275, not_prime_276]

theorem prime_277 : (277 : Nat).Prime := by norm_num

theorem nth_58 : Nat.nth Nat.Prime 58 = 277 := by
  rw [← count_277]
  exact Nat.nth_count prime_277

theorem not_prime_278 : ¬Nat.Prime 278 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 139) (n := 278)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_279 : ¬Nat.Prime 279 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 93) (n := 279)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_280 : ¬Nat.Prime 280 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 140) (n := 280)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_281 : Nat.count Nat.Prime 281 = 59 := by
  rw [show 281 = 280 + 1 by norm_num, Nat.count_succ]
  rw [show 280 = 279 + 1 by norm_num, Nat.count_succ]
  rw [show 279 = 278 + 1 by norm_num, Nat.count_succ]
  rw [show 278 = 277 + 1 by norm_num, Nat.count_succ]
  rw [count_277]
  simp [prime_277, not_prime_278, not_prime_279, not_prime_280]

theorem prime_281 : (281 : Nat).Prime := by norm_num

theorem nth_59 : Nat.nth Nat.Prime 59 = 281 := by
  rw [← count_281]
  exact Nat.nth_count prime_281

theorem not_prime_282 : ¬Nat.Prime 282 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 141) (n := 282)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_283 : Nat.count Nat.Prime 283 = 60 := by
  rw [show 283 = 282 + 1 by norm_num, Nat.count_succ]
  rw [show 282 = 281 + 1 by norm_num, Nat.count_succ]
  rw [count_281]
  simp [prime_281, not_prime_282]

theorem prime_283 : (283 : Nat).Prime := by norm_num

theorem nth_60 : Nat.nth Nat.Prime 60 = 283 := by
  rw [← count_283]
  exact Nat.nth_count prime_283

theorem not_prime_284 : ¬Nat.Prime 284 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 142) (n := 284)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_285 : ¬Nat.Prime 285 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 95) (n := 285)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_286 : ¬Nat.Prime 286 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 143) (n := 286)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_287 : ¬Nat.Prime 287 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 41) (n := 287)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_288 : ¬Nat.Prime 288 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 144) (n := 288)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_289 : ¬Nat.Prime 289 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 17) (n := 289)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_290 : ¬Nat.Prime 290 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 145) (n := 290)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_291 : ¬Nat.Prime 291 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 97) (n := 291)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_292 : ¬Nat.Prime 292 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 146) (n := 292)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_293 : Nat.count Nat.Prime 293 = 61 := by
  rw [show 293 = 292 + 1 by norm_num, Nat.count_succ]
  rw [show 292 = 291 + 1 by norm_num, Nat.count_succ]
  rw [show 291 = 290 + 1 by norm_num, Nat.count_succ]
  rw [show 290 = 289 + 1 by norm_num, Nat.count_succ]
  rw [show 289 = 288 + 1 by norm_num, Nat.count_succ]
  rw [show 288 = 287 + 1 by norm_num, Nat.count_succ]
  rw [show 287 = 286 + 1 by norm_num, Nat.count_succ]
  rw [show 286 = 285 + 1 by norm_num, Nat.count_succ]
  rw [show 285 = 284 + 1 by norm_num, Nat.count_succ]
  rw [show 284 = 283 + 1 by norm_num, Nat.count_succ]
  rw [count_283]
  simp [prime_283, not_prime_284, not_prime_285, not_prime_286, not_prime_287, not_prime_288, not_prime_289, not_prime_290, not_prime_291, not_prime_292]

theorem prime_293 : (293 : Nat).Prime := by norm_num

theorem nth_61 : Nat.nth Nat.Prime 61 = 293 := by
  rw [← count_293]
  exact Nat.nth_count prime_293

theorem not_prime_294 : ¬Nat.Prime 294 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 147) (n := 294)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_295 : ¬Nat.Prime 295 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 59) (n := 295)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_296 : ¬Nat.Prime 296 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 148) (n := 296)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_297 : ¬Nat.Prime 297 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 99) (n := 297)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_298 : ¬Nat.Prime 298 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 149) (n := 298)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_299 : ¬Nat.Prime 299 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 23) (n := 299)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_300 : ¬Nat.Prime 300 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 150) (n := 300)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_301 : ¬Nat.Prime 301 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 43) (n := 301)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_302 : ¬Nat.Prime 302 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 151) (n := 302)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_303 : ¬Nat.Prime 303 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 101) (n := 303)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_304 : ¬Nat.Prime 304 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 152) (n := 304)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_305 : ¬Nat.Prime 305 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 61) (n := 305)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_306 : ¬Nat.Prime 306 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 153) (n := 306)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_307 : Nat.count Nat.Prime 307 = 62 := by
  rw [show 307 = 306 + 1 by norm_num, Nat.count_succ]
  rw [show 306 = 305 + 1 by norm_num, Nat.count_succ]
  rw [show 305 = 304 + 1 by norm_num, Nat.count_succ]
  rw [show 304 = 303 + 1 by norm_num, Nat.count_succ]
  rw [show 303 = 302 + 1 by norm_num, Nat.count_succ]
  rw [show 302 = 301 + 1 by norm_num, Nat.count_succ]
  rw [show 301 = 300 + 1 by norm_num, Nat.count_succ]
  rw [show 300 = 299 + 1 by norm_num, Nat.count_succ]
  rw [show 299 = 298 + 1 by norm_num, Nat.count_succ]
  rw [show 298 = 297 + 1 by norm_num, Nat.count_succ]
  rw [show 297 = 296 + 1 by norm_num, Nat.count_succ]
  rw [show 296 = 295 + 1 by norm_num, Nat.count_succ]
  rw [show 295 = 294 + 1 by norm_num, Nat.count_succ]
  rw [show 294 = 293 + 1 by norm_num, Nat.count_succ]
  rw [count_293]
  simp [prime_293, not_prime_294, not_prime_295, not_prime_296, not_prime_297, not_prime_298, not_prime_299, not_prime_300, not_prime_301, not_prime_302, not_prime_303, not_prime_304, not_prime_305, not_prime_306]

theorem prime_307 : (307 : Nat).Prime := by norm_num

theorem nth_62 : Nat.nth Nat.Prime 62 = 307 := by
  rw [← count_307]
  exact Nat.nth_count prime_307

theorem not_prime_308 : ¬Nat.Prime 308 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 154) (n := 308)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_309 : ¬Nat.Prime 309 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 103) (n := 309)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_310 : ¬Nat.Prime 310 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 155) (n := 310)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_311 : Nat.count Nat.Prime 311 = 63 := by
  rw [show 311 = 310 + 1 by norm_num, Nat.count_succ]
  rw [show 310 = 309 + 1 by norm_num, Nat.count_succ]
  rw [show 309 = 308 + 1 by norm_num, Nat.count_succ]
  rw [show 308 = 307 + 1 by norm_num, Nat.count_succ]
  rw [count_307]
  simp [prime_307, not_prime_308, not_prime_309, not_prime_310]

theorem prime_311 : (311 : Nat).Prime := by norm_num

theorem nth_63 : Nat.nth Nat.Prime 63 = 311 := by
  rw [← count_311]
  exact Nat.nth_count prime_311

theorem not_prime_312 : ¬Nat.Prime 312 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 156) (n := 312)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_313 : Nat.count Nat.Prime 313 = 64 := by
  rw [show 313 = 312 + 1 by norm_num, Nat.count_succ]
  rw [show 312 = 311 + 1 by norm_num, Nat.count_succ]
  rw [count_311]
  simp [prime_311, not_prime_312]

theorem prime_313 : (313 : Nat).Prime := by norm_num

theorem nth_64 : Nat.nth Nat.Prime 64 = 313 := by
  rw [← count_313]
  exact Nat.nth_count prime_313

theorem not_prime_314 : ¬Nat.Prime 314 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 157) (n := 314)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_315 : ¬Nat.Prime 315 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 105) (n := 315)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_316 : ¬Nat.Prime 316 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 158) (n := 316)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_317 : Nat.count Nat.Prime 317 = 65 := by
  rw [show 317 = 316 + 1 by norm_num, Nat.count_succ]
  rw [show 316 = 315 + 1 by norm_num, Nat.count_succ]
  rw [show 315 = 314 + 1 by norm_num, Nat.count_succ]
  rw [show 314 = 313 + 1 by norm_num, Nat.count_succ]
  rw [count_313]
  simp [prime_313, not_prime_314, not_prime_315, not_prime_316]

theorem prime_317 : (317 : Nat).Prime := by norm_num

theorem nth_65 : Nat.nth Nat.Prime 65 = 317 := by
  rw [← count_317]
  exact Nat.nth_count prime_317

theorem not_prime_318 : ¬Nat.Prime 318 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 159) (n := 318)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_319 : ¬Nat.Prime 319 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 29) (n := 319)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_320 : ¬Nat.Prime 320 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 160) (n := 320)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_321 : ¬Nat.Prime 321 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 107) (n := 321)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_322 : ¬Nat.Prime 322 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 161) (n := 322)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_323 : ¬Nat.Prime 323 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 19) (n := 323)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_324 : ¬Nat.Prime 324 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 162) (n := 324)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_325 : ¬Nat.Prime 325 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 65) (n := 325)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_326 : ¬Nat.Prime 326 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 163) (n := 326)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_327 : ¬Nat.Prime 327 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 109) (n := 327)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_328 : ¬Nat.Prime 328 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 164) (n := 328)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_329 : ¬Nat.Prime 329 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 47) (n := 329)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_330 : ¬Nat.Prime 330 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 165) (n := 330)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_331 : Nat.count Nat.Prime 331 = 66 := by
  rw [show 331 = 330 + 1 by norm_num, Nat.count_succ]
  rw [show 330 = 329 + 1 by norm_num, Nat.count_succ]
  rw [show 329 = 328 + 1 by norm_num, Nat.count_succ]
  rw [show 328 = 327 + 1 by norm_num, Nat.count_succ]
  rw [show 327 = 326 + 1 by norm_num, Nat.count_succ]
  rw [show 326 = 325 + 1 by norm_num, Nat.count_succ]
  rw [show 325 = 324 + 1 by norm_num, Nat.count_succ]
  rw [show 324 = 323 + 1 by norm_num, Nat.count_succ]
  rw [show 323 = 322 + 1 by norm_num, Nat.count_succ]
  rw [show 322 = 321 + 1 by norm_num, Nat.count_succ]
  rw [show 321 = 320 + 1 by norm_num, Nat.count_succ]
  rw [show 320 = 319 + 1 by norm_num, Nat.count_succ]
  rw [show 319 = 318 + 1 by norm_num, Nat.count_succ]
  rw [show 318 = 317 + 1 by norm_num, Nat.count_succ]
  rw [count_317]
  simp [prime_317, not_prime_318, not_prime_319, not_prime_320, not_prime_321, not_prime_322, not_prime_323, not_prime_324, not_prime_325, not_prime_326, not_prime_327, not_prime_328, not_prime_329, not_prime_330]

theorem prime_331 : (331 : Nat).Prime := by norm_num

theorem nth_66 : Nat.nth Nat.Prime 66 = 331 := by
  rw [← count_331]
  exact Nat.nth_count prime_331

theorem not_prime_332 : ¬Nat.Prime 332 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 166) (n := 332)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_333 : ¬Nat.Prime 333 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 111) (n := 333)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_334 : ¬Nat.Prime 334 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 167) (n := 334)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_335 : ¬Nat.Prime 335 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 67) (n := 335)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_336 : ¬Nat.Prime 336 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 168) (n := 336)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_337 : Nat.count Nat.Prime 337 = 67 := by
  rw [show 337 = 336 + 1 by norm_num, Nat.count_succ]
  rw [show 336 = 335 + 1 by norm_num, Nat.count_succ]
  rw [show 335 = 334 + 1 by norm_num, Nat.count_succ]
  rw [show 334 = 333 + 1 by norm_num, Nat.count_succ]
  rw [show 333 = 332 + 1 by norm_num, Nat.count_succ]
  rw [show 332 = 331 + 1 by norm_num, Nat.count_succ]
  rw [count_331]
  simp [prime_331, not_prime_332, not_prime_333, not_prime_334, not_prime_335, not_prime_336]

theorem prime_337 : (337 : Nat).Prime := by norm_num

theorem nth_67 : Nat.nth Nat.Prime 67 = 337 := by
  rw [← count_337]
  exact Nat.nth_count prime_337

theorem not_prime_338 : ¬Nat.Prime 338 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 169) (n := 338)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_339 : ¬Nat.Prime 339 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 113) (n := 339)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_340 : ¬Nat.Prime 340 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 170) (n := 340)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_341 : ¬Nat.Prime 341 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 31) (n := 341)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_342 : ¬Nat.Prime 342 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 171) (n := 342)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_343 : ¬Nat.Prime 343 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 49) (n := 343)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_344 : ¬Nat.Prime 344 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 172) (n := 344)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_345 : ¬Nat.Prime 345 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 115) (n := 345)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_346 : ¬Nat.Prime 346 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 173) (n := 346)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_347 : Nat.count Nat.Prime 347 = 68 := by
  rw [show 347 = 346 + 1 by norm_num, Nat.count_succ]
  rw [show 346 = 345 + 1 by norm_num, Nat.count_succ]
  rw [show 345 = 344 + 1 by norm_num, Nat.count_succ]
  rw [show 344 = 343 + 1 by norm_num, Nat.count_succ]
  rw [show 343 = 342 + 1 by norm_num, Nat.count_succ]
  rw [show 342 = 341 + 1 by norm_num, Nat.count_succ]
  rw [show 341 = 340 + 1 by norm_num, Nat.count_succ]
  rw [show 340 = 339 + 1 by norm_num, Nat.count_succ]
  rw [show 339 = 338 + 1 by norm_num, Nat.count_succ]
  rw [show 338 = 337 + 1 by norm_num, Nat.count_succ]
  rw [count_337]
  simp [prime_337, not_prime_338, not_prime_339, not_prime_340, not_prime_341, not_prime_342, not_prime_343, not_prime_344, not_prime_345, not_prime_346]

theorem prime_347 : (347 : Nat).Prime := by norm_num

theorem nth_68 : Nat.nth Nat.Prime 68 = 347 := by
  rw [← count_347]
  exact Nat.nth_count prime_347

theorem not_prime_348 : ¬Nat.Prime 348 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 174) (n := 348)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_349 : Nat.count Nat.Prime 349 = 69 := by
  rw [show 349 = 348 + 1 by norm_num, Nat.count_succ]
  rw [show 348 = 347 + 1 by norm_num, Nat.count_succ]
  rw [count_347]
  simp [prime_347, not_prime_348]

theorem prime_349 : (349 : Nat).Prime := by norm_num

theorem nth_69 : Nat.nth Nat.Prime 69 = 349 := by
  rw [← count_349]
  exact Nat.nth_count prime_349

theorem not_prime_350 : ¬Nat.Prime 350 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 175) (n := 350)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_351 : ¬Nat.Prime 351 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 117) (n := 351)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_352 : ¬Nat.Prime 352 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 176) (n := 352)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_353 : Nat.count Nat.Prime 353 = 70 := by
  rw [show 353 = 352 + 1 by norm_num, Nat.count_succ]
  rw [show 352 = 351 + 1 by norm_num, Nat.count_succ]
  rw [show 351 = 350 + 1 by norm_num, Nat.count_succ]
  rw [show 350 = 349 + 1 by norm_num, Nat.count_succ]
  rw [count_349]
  simp [prime_349, not_prime_350, not_prime_351, not_prime_352]

theorem prime_353 : (353 : Nat).Prime := by norm_num

theorem nth_70 : Nat.nth Nat.Prime 70 = 353 := by
  rw [← count_353]
  exact Nat.nth_count prime_353

theorem not_prime_354 : ¬Nat.Prime 354 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 177) (n := 354)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_355 : ¬Nat.Prime 355 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 71) (n := 355)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_356 : ¬Nat.Prime 356 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 178) (n := 356)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_357 : ¬Nat.Prime 357 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 119) (n := 357)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_358 : ¬Nat.Prime 358 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 179) (n := 358)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_359 : Nat.count Nat.Prime 359 = 71 := by
  rw [show 359 = 358 + 1 by norm_num, Nat.count_succ]
  rw [show 358 = 357 + 1 by norm_num, Nat.count_succ]
  rw [show 357 = 356 + 1 by norm_num, Nat.count_succ]
  rw [show 356 = 355 + 1 by norm_num, Nat.count_succ]
  rw [show 355 = 354 + 1 by norm_num, Nat.count_succ]
  rw [show 354 = 353 + 1 by norm_num, Nat.count_succ]
  rw [count_353]
  simp [prime_353, not_prime_354, not_prime_355, not_prime_356, not_prime_357, not_prime_358]

theorem prime_359 : (359 : Nat).Prime := by norm_num

theorem nth_71 : Nat.nth Nat.Prime 71 = 359 := by
  rw [← count_359]
  exact Nat.nth_count prime_359

theorem not_prime_360 : ¬Nat.Prime 360 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 180) (n := 360)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_361 : ¬Nat.Prime 361 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 19) (n := 361)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_362 : ¬Nat.Prime 362 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 181) (n := 362)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_363 : ¬Nat.Prime 363 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 121) (n := 363)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_364 : ¬Nat.Prime 364 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 182) (n := 364)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_365 : ¬Nat.Prime 365 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 73) (n := 365)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_366 : ¬Nat.Prime 366 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 183) (n := 366)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_367 : Nat.count Nat.Prime 367 = 72 := by
  rw [show 367 = 366 + 1 by norm_num, Nat.count_succ]
  rw [show 366 = 365 + 1 by norm_num, Nat.count_succ]
  rw [show 365 = 364 + 1 by norm_num, Nat.count_succ]
  rw [show 364 = 363 + 1 by norm_num, Nat.count_succ]
  rw [show 363 = 362 + 1 by norm_num, Nat.count_succ]
  rw [show 362 = 361 + 1 by norm_num, Nat.count_succ]
  rw [show 361 = 360 + 1 by norm_num, Nat.count_succ]
  rw [show 360 = 359 + 1 by norm_num, Nat.count_succ]
  rw [count_359]
  simp [prime_359, not_prime_360, not_prime_361, not_prime_362, not_prime_363, not_prime_364, not_prime_365, not_prime_366]

theorem prime_367 : (367 : Nat).Prime := by norm_num

theorem nth_72 : Nat.nth Nat.Prime 72 = 367 := by
  rw [← count_367]
  exact Nat.nth_count prime_367

theorem not_prime_368 : ¬Nat.Prime 368 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 184) (n := 368)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_369 : ¬Nat.Prime 369 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 123) (n := 369)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_370 : ¬Nat.Prime 370 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 185) (n := 370)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_371 : ¬Nat.Prime 371 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 53) (n := 371)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_372 : ¬Nat.Prime 372 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 186) (n := 372)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_373 : Nat.count Nat.Prime 373 = 73 := by
  rw [show 373 = 372 + 1 by norm_num, Nat.count_succ]
  rw [show 372 = 371 + 1 by norm_num, Nat.count_succ]
  rw [show 371 = 370 + 1 by norm_num, Nat.count_succ]
  rw [show 370 = 369 + 1 by norm_num, Nat.count_succ]
  rw [show 369 = 368 + 1 by norm_num, Nat.count_succ]
  rw [show 368 = 367 + 1 by norm_num, Nat.count_succ]
  rw [count_367]
  simp [prime_367, not_prime_368, not_prime_369, not_prime_370, not_prime_371, not_prime_372]

theorem prime_373 : (373 : Nat).Prime := by norm_num

theorem nth_73 : Nat.nth Nat.Prime 73 = 373 := by
  rw [← count_373]
  exact Nat.nth_count prime_373

theorem not_prime_374 : ¬Nat.Prime 374 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 187) (n := 374)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_375 : ¬Nat.Prime 375 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 125) (n := 375)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_376 : ¬Nat.Prime 376 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 188) (n := 376)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_377 : ¬Nat.Prime 377 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 29) (n := 377)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_378 : ¬Nat.Prime 378 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 189) (n := 378)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_379 : Nat.count Nat.Prime 379 = 74 := by
  rw [show 379 = 378 + 1 by norm_num, Nat.count_succ]
  rw [show 378 = 377 + 1 by norm_num, Nat.count_succ]
  rw [show 377 = 376 + 1 by norm_num, Nat.count_succ]
  rw [show 376 = 375 + 1 by norm_num, Nat.count_succ]
  rw [show 375 = 374 + 1 by norm_num, Nat.count_succ]
  rw [show 374 = 373 + 1 by norm_num, Nat.count_succ]
  rw [count_373]
  simp [prime_373, not_prime_374, not_prime_375, not_prime_376, not_prime_377, not_prime_378]

theorem prime_379 : (379 : Nat).Prime := by norm_num

theorem nth_74 : Nat.nth Nat.Prime 74 = 379 := by
  rw [← count_379]
  exact Nat.nth_count prime_379

end OeisA100474.PrimeCertificate
