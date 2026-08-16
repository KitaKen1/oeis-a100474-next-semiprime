import OeisA100474PrimeCertificate.Chunk07

/-! Kernel prime/count certificate, chunk 08 (200–224). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace OeisA100474.PrimeCertificate

theorem not_prime_1224 : ¬Nat.Prime 1224 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 612) (n := 1224)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1225 : ¬Nat.Prime 1225 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 245) (n := 1225)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1226 : ¬Nat.Prime 1226 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 613) (n := 1226)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1227 : ¬Nat.Prime 1227 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 409) (n := 1227)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1228 : ¬Nat.Prime 1228 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 614) (n := 1228)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1229 : Nat.count Nat.Prime 1229 = 200 := by
  rw [show 1229 = 1228 + 1 by norm_num, Nat.count_succ]
  rw [show 1228 = 1227 + 1 by norm_num, Nat.count_succ]
  rw [show 1227 = 1226 + 1 by norm_num, Nat.count_succ]
  rw [show 1226 = 1225 + 1 by norm_num, Nat.count_succ]
  rw [show 1225 = 1224 + 1 by norm_num, Nat.count_succ]
  rw [show 1224 = 1223 + 1 by norm_num, Nat.count_succ]
  rw [count_1223]
  simp [prime_1223, not_prime_1224, not_prime_1225, not_prime_1226, not_prime_1227, not_prime_1228]

theorem prime_1229 : (1229 : Nat).Prime := by norm_num

theorem nth_200 : Nat.nth Nat.Prime 200 = 1229 := by
  rw [← count_1229]
  exact Nat.nth_count prime_1229

theorem not_prime_1230 : ¬Nat.Prime 1230 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 615) (n := 1230)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1231 : Nat.count Nat.Prime 1231 = 201 := by
  rw [show 1231 = 1230 + 1 by norm_num, Nat.count_succ]
  rw [show 1230 = 1229 + 1 by norm_num, Nat.count_succ]
  rw [count_1229]
  simp [prime_1229, not_prime_1230]

theorem prime_1231 : (1231 : Nat).Prime := by norm_num

theorem nth_201 : Nat.nth Nat.Prime 201 = 1231 := by
  rw [← count_1231]
  exact Nat.nth_count prime_1231

theorem not_prime_1232 : ¬Nat.Prime 1232 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 616) (n := 1232)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1233 : ¬Nat.Prime 1233 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 411) (n := 1233)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1234 : ¬Nat.Prime 1234 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 617) (n := 1234)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1235 : ¬Nat.Prime 1235 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 247) (n := 1235)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1236 : ¬Nat.Prime 1236 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 618) (n := 1236)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1237 : Nat.count Nat.Prime 1237 = 202 := by
  rw [show 1237 = 1236 + 1 by norm_num, Nat.count_succ]
  rw [show 1236 = 1235 + 1 by norm_num, Nat.count_succ]
  rw [show 1235 = 1234 + 1 by norm_num, Nat.count_succ]
  rw [show 1234 = 1233 + 1 by norm_num, Nat.count_succ]
  rw [show 1233 = 1232 + 1 by norm_num, Nat.count_succ]
  rw [show 1232 = 1231 + 1 by norm_num, Nat.count_succ]
  rw [count_1231]
  simp [prime_1231, not_prime_1232, not_prime_1233, not_prime_1234, not_prime_1235, not_prime_1236]

theorem prime_1237 : (1237 : Nat).Prime := by norm_num

theorem nth_202 : Nat.nth Nat.Prime 202 = 1237 := by
  rw [← count_1237]
  exact Nat.nth_count prime_1237

theorem not_prime_1238 : ¬Nat.Prime 1238 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 619) (n := 1238)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1239 : ¬Nat.Prime 1239 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 413) (n := 1239)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1240 : ¬Nat.Prime 1240 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 620) (n := 1240)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1241 : ¬Nat.Prime 1241 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 73) (n := 1241)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1242 : ¬Nat.Prime 1242 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 621) (n := 1242)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1243 : ¬Nat.Prime 1243 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 113) (n := 1243)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1244 : ¬Nat.Prime 1244 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 622) (n := 1244)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1245 : ¬Nat.Prime 1245 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 415) (n := 1245)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1246 : ¬Nat.Prime 1246 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 623) (n := 1246)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1247 : ¬Nat.Prime 1247 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 43) (n := 1247)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1248 : ¬Nat.Prime 1248 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 624) (n := 1248)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1249 : Nat.count Nat.Prime 1249 = 203 := by
  rw [show 1249 = 1248 + 1 by norm_num, Nat.count_succ]
  rw [show 1248 = 1247 + 1 by norm_num, Nat.count_succ]
  rw [show 1247 = 1246 + 1 by norm_num, Nat.count_succ]
  rw [show 1246 = 1245 + 1 by norm_num, Nat.count_succ]
  rw [show 1245 = 1244 + 1 by norm_num, Nat.count_succ]
  rw [show 1244 = 1243 + 1 by norm_num, Nat.count_succ]
  rw [show 1243 = 1242 + 1 by norm_num, Nat.count_succ]
  rw [show 1242 = 1241 + 1 by norm_num, Nat.count_succ]
  rw [show 1241 = 1240 + 1 by norm_num, Nat.count_succ]
  rw [show 1240 = 1239 + 1 by norm_num, Nat.count_succ]
  rw [show 1239 = 1238 + 1 by norm_num, Nat.count_succ]
  rw [show 1238 = 1237 + 1 by norm_num, Nat.count_succ]
  rw [count_1237]
  simp [prime_1237, not_prime_1238, not_prime_1239, not_prime_1240, not_prime_1241, not_prime_1242, not_prime_1243, not_prime_1244, not_prime_1245, not_prime_1246, not_prime_1247, not_prime_1248]

theorem prime_1249 : (1249 : Nat).Prime := by norm_num

theorem nth_203 : Nat.nth Nat.Prime 203 = 1249 := by
  rw [← count_1249]
  exact Nat.nth_count prime_1249

theorem not_prime_1250 : ¬Nat.Prime 1250 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 625) (n := 1250)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1251 : ¬Nat.Prime 1251 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 417) (n := 1251)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1252 : ¬Nat.Prime 1252 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 626) (n := 1252)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1253 : ¬Nat.Prime 1253 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 179) (n := 1253)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1254 : ¬Nat.Prime 1254 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 627) (n := 1254)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1255 : ¬Nat.Prime 1255 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 251) (n := 1255)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1256 : ¬Nat.Prime 1256 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 628) (n := 1256)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1257 : ¬Nat.Prime 1257 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 419) (n := 1257)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1258 : ¬Nat.Prime 1258 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 629) (n := 1258)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1259 : Nat.count Nat.Prime 1259 = 204 := by
  rw [show 1259 = 1258 + 1 by norm_num, Nat.count_succ]
  rw [show 1258 = 1257 + 1 by norm_num, Nat.count_succ]
  rw [show 1257 = 1256 + 1 by norm_num, Nat.count_succ]
  rw [show 1256 = 1255 + 1 by norm_num, Nat.count_succ]
  rw [show 1255 = 1254 + 1 by norm_num, Nat.count_succ]
  rw [show 1254 = 1253 + 1 by norm_num, Nat.count_succ]
  rw [show 1253 = 1252 + 1 by norm_num, Nat.count_succ]
  rw [show 1252 = 1251 + 1 by norm_num, Nat.count_succ]
  rw [show 1251 = 1250 + 1 by norm_num, Nat.count_succ]
  rw [show 1250 = 1249 + 1 by norm_num, Nat.count_succ]
  rw [count_1249]
  simp [prime_1249, not_prime_1250, not_prime_1251, not_prime_1252, not_prime_1253, not_prime_1254, not_prime_1255, not_prime_1256, not_prime_1257, not_prime_1258]

theorem prime_1259 : (1259 : Nat).Prime := by norm_num

theorem nth_204 : Nat.nth Nat.Prime 204 = 1259 := by
  rw [← count_1259]
  exact Nat.nth_count prime_1259

theorem not_prime_1260 : ¬Nat.Prime 1260 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 630) (n := 1260)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1261 : ¬Nat.Prime 1261 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 97) (n := 1261)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1262 : ¬Nat.Prime 1262 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 631) (n := 1262)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1263 : ¬Nat.Prime 1263 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 421) (n := 1263)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1264 : ¬Nat.Prime 1264 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 632) (n := 1264)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1265 : ¬Nat.Prime 1265 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 253) (n := 1265)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1266 : ¬Nat.Prime 1266 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 633) (n := 1266)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1267 : ¬Nat.Prime 1267 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 181) (n := 1267)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1268 : ¬Nat.Prime 1268 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 634) (n := 1268)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1269 : ¬Nat.Prime 1269 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 423) (n := 1269)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1270 : ¬Nat.Prime 1270 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 635) (n := 1270)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1271 : ¬Nat.Prime 1271 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 41) (n := 1271)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1272 : ¬Nat.Prime 1272 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 636) (n := 1272)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1273 : ¬Nat.Prime 1273 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 67) (n := 1273)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1274 : ¬Nat.Prime 1274 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 637) (n := 1274)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1275 : ¬Nat.Prime 1275 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 425) (n := 1275)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1276 : ¬Nat.Prime 1276 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 638) (n := 1276)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1277 : Nat.count Nat.Prime 1277 = 205 := by
  rw [show 1277 = 1276 + 1 by norm_num, Nat.count_succ]
  rw [show 1276 = 1275 + 1 by norm_num, Nat.count_succ]
  rw [show 1275 = 1274 + 1 by norm_num, Nat.count_succ]
  rw [show 1274 = 1273 + 1 by norm_num, Nat.count_succ]
  rw [show 1273 = 1272 + 1 by norm_num, Nat.count_succ]
  rw [show 1272 = 1271 + 1 by norm_num, Nat.count_succ]
  rw [show 1271 = 1270 + 1 by norm_num, Nat.count_succ]
  rw [show 1270 = 1269 + 1 by norm_num, Nat.count_succ]
  rw [show 1269 = 1268 + 1 by norm_num, Nat.count_succ]
  rw [show 1268 = 1267 + 1 by norm_num, Nat.count_succ]
  rw [show 1267 = 1266 + 1 by norm_num, Nat.count_succ]
  rw [show 1266 = 1265 + 1 by norm_num, Nat.count_succ]
  rw [show 1265 = 1264 + 1 by norm_num, Nat.count_succ]
  rw [show 1264 = 1263 + 1 by norm_num, Nat.count_succ]
  rw [show 1263 = 1262 + 1 by norm_num, Nat.count_succ]
  rw [show 1262 = 1261 + 1 by norm_num, Nat.count_succ]
  rw [show 1261 = 1260 + 1 by norm_num, Nat.count_succ]
  rw [show 1260 = 1259 + 1 by norm_num, Nat.count_succ]
  rw [count_1259]
  simp [prime_1259, not_prime_1260, not_prime_1261, not_prime_1262, not_prime_1263, not_prime_1264, not_prime_1265, not_prime_1266, not_prime_1267, not_prime_1268, not_prime_1269, not_prime_1270, not_prime_1271, not_prime_1272, not_prime_1273, not_prime_1274, not_prime_1275, not_prime_1276]

theorem prime_1277 : (1277 : Nat).Prime := by norm_num

theorem nth_205 : Nat.nth Nat.Prime 205 = 1277 := by
  rw [← count_1277]
  exact Nat.nth_count prime_1277

theorem not_prime_1278 : ¬Nat.Prime 1278 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 639) (n := 1278)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1279 : Nat.count Nat.Prime 1279 = 206 := by
  rw [show 1279 = 1278 + 1 by norm_num, Nat.count_succ]
  rw [show 1278 = 1277 + 1 by norm_num, Nat.count_succ]
  rw [count_1277]
  simp [prime_1277, not_prime_1278]

theorem prime_1279 : (1279 : Nat).Prime := by norm_num

theorem nth_206 : Nat.nth Nat.Prime 206 = 1279 := by
  rw [← count_1279]
  exact Nat.nth_count prime_1279

theorem not_prime_1280 : ¬Nat.Prime 1280 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 640) (n := 1280)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1281 : ¬Nat.Prime 1281 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 427) (n := 1281)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1282 : ¬Nat.Prime 1282 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 641) (n := 1282)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1283 : Nat.count Nat.Prime 1283 = 207 := by
  rw [show 1283 = 1282 + 1 by norm_num, Nat.count_succ]
  rw [show 1282 = 1281 + 1 by norm_num, Nat.count_succ]
  rw [show 1281 = 1280 + 1 by norm_num, Nat.count_succ]
  rw [show 1280 = 1279 + 1 by norm_num, Nat.count_succ]
  rw [count_1279]
  simp [prime_1279, not_prime_1280, not_prime_1281, not_prime_1282]

theorem prime_1283 : (1283 : Nat).Prime := by norm_num

theorem nth_207 : Nat.nth Nat.Prime 207 = 1283 := by
  rw [← count_1283]
  exact Nat.nth_count prime_1283

theorem not_prime_1284 : ¬Nat.Prime 1284 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 642) (n := 1284)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1285 : ¬Nat.Prime 1285 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 257) (n := 1285)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1286 : ¬Nat.Prime 1286 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 643) (n := 1286)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1287 : ¬Nat.Prime 1287 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 429) (n := 1287)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1288 : ¬Nat.Prime 1288 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 644) (n := 1288)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1289 : Nat.count Nat.Prime 1289 = 208 := by
  rw [show 1289 = 1288 + 1 by norm_num, Nat.count_succ]
  rw [show 1288 = 1287 + 1 by norm_num, Nat.count_succ]
  rw [show 1287 = 1286 + 1 by norm_num, Nat.count_succ]
  rw [show 1286 = 1285 + 1 by norm_num, Nat.count_succ]
  rw [show 1285 = 1284 + 1 by norm_num, Nat.count_succ]
  rw [show 1284 = 1283 + 1 by norm_num, Nat.count_succ]
  rw [count_1283]
  simp [prime_1283, not_prime_1284, not_prime_1285, not_prime_1286, not_prime_1287, not_prime_1288]

theorem prime_1289 : (1289 : Nat).Prime := by norm_num

theorem nth_208 : Nat.nth Nat.Prime 208 = 1289 := by
  rw [← count_1289]
  exact Nat.nth_count prime_1289

theorem not_prime_1290 : ¬Nat.Prime 1290 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 645) (n := 1290)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1291 : Nat.count Nat.Prime 1291 = 209 := by
  rw [show 1291 = 1290 + 1 by norm_num, Nat.count_succ]
  rw [show 1290 = 1289 + 1 by norm_num, Nat.count_succ]
  rw [count_1289]
  simp [prime_1289, not_prime_1290]

theorem prime_1291 : (1291 : Nat).Prime := by norm_num

theorem nth_209 : Nat.nth Nat.Prime 209 = 1291 := by
  rw [← count_1291]
  exact Nat.nth_count prime_1291

theorem not_prime_1292 : ¬Nat.Prime 1292 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 646) (n := 1292)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1293 : ¬Nat.Prime 1293 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 431) (n := 1293)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1294 : ¬Nat.Prime 1294 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 647) (n := 1294)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1295 : ¬Nat.Prime 1295 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 259) (n := 1295)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1296 : ¬Nat.Prime 1296 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 648) (n := 1296)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1297 : Nat.count Nat.Prime 1297 = 210 := by
  rw [show 1297 = 1296 + 1 by norm_num, Nat.count_succ]
  rw [show 1296 = 1295 + 1 by norm_num, Nat.count_succ]
  rw [show 1295 = 1294 + 1 by norm_num, Nat.count_succ]
  rw [show 1294 = 1293 + 1 by norm_num, Nat.count_succ]
  rw [show 1293 = 1292 + 1 by norm_num, Nat.count_succ]
  rw [show 1292 = 1291 + 1 by norm_num, Nat.count_succ]
  rw [count_1291]
  simp [prime_1291, not_prime_1292, not_prime_1293, not_prime_1294, not_prime_1295, not_prime_1296]

theorem prime_1297 : (1297 : Nat).Prime := by norm_num

theorem nth_210 : Nat.nth Nat.Prime 210 = 1297 := by
  rw [← count_1297]
  exact Nat.nth_count prime_1297

theorem not_prime_1298 : ¬Nat.Prime 1298 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 649) (n := 1298)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1299 : ¬Nat.Prime 1299 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 433) (n := 1299)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1300 : ¬Nat.Prime 1300 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 650) (n := 1300)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1301 : Nat.count Nat.Prime 1301 = 211 := by
  rw [show 1301 = 1300 + 1 by norm_num, Nat.count_succ]
  rw [show 1300 = 1299 + 1 by norm_num, Nat.count_succ]
  rw [show 1299 = 1298 + 1 by norm_num, Nat.count_succ]
  rw [show 1298 = 1297 + 1 by norm_num, Nat.count_succ]
  rw [count_1297]
  simp [prime_1297, not_prime_1298, not_prime_1299, not_prime_1300]

theorem prime_1301 : (1301 : Nat).Prime := by norm_num

theorem nth_211 : Nat.nth Nat.Prime 211 = 1301 := by
  rw [← count_1301]
  exact Nat.nth_count prime_1301

theorem not_prime_1302 : ¬Nat.Prime 1302 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 651) (n := 1302)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1303 : Nat.count Nat.Prime 1303 = 212 := by
  rw [show 1303 = 1302 + 1 by norm_num, Nat.count_succ]
  rw [show 1302 = 1301 + 1 by norm_num, Nat.count_succ]
  rw [count_1301]
  simp [prime_1301, not_prime_1302]

theorem prime_1303 : (1303 : Nat).Prime := by norm_num

theorem nth_212 : Nat.nth Nat.Prime 212 = 1303 := by
  rw [← count_1303]
  exact Nat.nth_count prime_1303

theorem not_prime_1304 : ¬Nat.Prime 1304 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 652) (n := 1304)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1305 : ¬Nat.Prime 1305 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 435) (n := 1305)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1306 : ¬Nat.Prime 1306 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 653) (n := 1306)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1307 : Nat.count Nat.Prime 1307 = 213 := by
  rw [show 1307 = 1306 + 1 by norm_num, Nat.count_succ]
  rw [show 1306 = 1305 + 1 by norm_num, Nat.count_succ]
  rw [show 1305 = 1304 + 1 by norm_num, Nat.count_succ]
  rw [show 1304 = 1303 + 1 by norm_num, Nat.count_succ]
  rw [count_1303]
  simp [prime_1303, not_prime_1304, not_prime_1305, not_prime_1306]

theorem prime_1307 : (1307 : Nat).Prime := by norm_num

theorem nth_213 : Nat.nth Nat.Prime 213 = 1307 := by
  rw [← count_1307]
  exact Nat.nth_count prime_1307

theorem not_prime_1308 : ¬Nat.Prime 1308 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 654) (n := 1308)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1309 : ¬Nat.Prime 1309 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 187) (n := 1309)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1310 : ¬Nat.Prime 1310 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 655) (n := 1310)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1311 : ¬Nat.Prime 1311 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 437) (n := 1311)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1312 : ¬Nat.Prime 1312 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 656) (n := 1312)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1313 : ¬Nat.Prime 1313 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 101) (n := 1313)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1314 : ¬Nat.Prime 1314 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 657) (n := 1314)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1315 : ¬Nat.Prime 1315 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 263) (n := 1315)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1316 : ¬Nat.Prime 1316 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 658) (n := 1316)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1317 : ¬Nat.Prime 1317 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 439) (n := 1317)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1318 : ¬Nat.Prime 1318 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 659) (n := 1318)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1319 : Nat.count Nat.Prime 1319 = 214 := by
  rw [show 1319 = 1318 + 1 by norm_num, Nat.count_succ]
  rw [show 1318 = 1317 + 1 by norm_num, Nat.count_succ]
  rw [show 1317 = 1316 + 1 by norm_num, Nat.count_succ]
  rw [show 1316 = 1315 + 1 by norm_num, Nat.count_succ]
  rw [show 1315 = 1314 + 1 by norm_num, Nat.count_succ]
  rw [show 1314 = 1313 + 1 by norm_num, Nat.count_succ]
  rw [show 1313 = 1312 + 1 by norm_num, Nat.count_succ]
  rw [show 1312 = 1311 + 1 by norm_num, Nat.count_succ]
  rw [show 1311 = 1310 + 1 by norm_num, Nat.count_succ]
  rw [show 1310 = 1309 + 1 by norm_num, Nat.count_succ]
  rw [show 1309 = 1308 + 1 by norm_num, Nat.count_succ]
  rw [show 1308 = 1307 + 1 by norm_num, Nat.count_succ]
  rw [count_1307]
  simp [prime_1307, not_prime_1308, not_prime_1309, not_prime_1310, not_prime_1311, not_prime_1312, not_prime_1313, not_prime_1314, not_prime_1315, not_prime_1316, not_prime_1317, not_prime_1318]

theorem prime_1319 : (1319 : Nat).Prime := by norm_num

theorem nth_214 : Nat.nth Nat.Prime 214 = 1319 := by
  rw [← count_1319]
  exact Nat.nth_count prime_1319

theorem not_prime_1320 : ¬Nat.Prime 1320 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 660) (n := 1320)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1321 : Nat.count Nat.Prime 1321 = 215 := by
  rw [show 1321 = 1320 + 1 by norm_num, Nat.count_succ]
  rw [show 1320 = 1319 + 1 by norm_num, Nat.count_succ]
  rw [count_1319]
  simp [prime_1319, not_prime_1320]

theorem prime_1321 : (1321 : Nat).Prime := by norm_num

theorem nth_215 : Nat.nth Nat.Prime 215 = 1321 := by
  rw [← count_1321]
  exact Nat.nth_count prime_1321

theorem not_prime_1322 : ¬Nat.Prime 1322 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 661) (n := 1322)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1323 : ¬Nat.Prime 1323 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 441) (n := 1323)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1324 : ¬Nat.Prime 1324 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 662) (n := 1324)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1325 : ¬Nat.Prime 1325 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 265) (n := 1325)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1326 : ¬Nat.Prime 1326 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 663) (n := 1326)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1327 : Nat.count Nat.Prime 1327 = 216 := by
  rw [show 1327 = 1326 + 1 by norm_num, Nat.count_succ]
  rw [show 1326 = 1325 + 1 by norm_num, Nat.count_succ]
  rw [show 1325 = 1324 + 1 by norm_num, Nat.count_succ]
  rw [show 1324 = 1323 + 1 by norm_num, Nat.count_succ]
  rw [show 1323 = 1322 + 1 by norm_num, Nat.count_succ]
  rw [show 1322 = 1321 + 1 by norm_num, Nat.count_succ]
  rw [count_1321]
  simp [prime_1321, not_prime_1322, not_prime_1323, not_prime_1324, not_prime_1325, not_prime_1326]

theorem prime_1327 : (1327 : Nat).Prime := by norm_num

theorem nth_216 : Nat.nth Nat.Prime 216 = 1327 := by
  rw [← count_1327]
  exact Nat.nth_count prime_1327

theorem not_prime_1328 : ¬Nat.Prime 1328 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 664) (n := 1328)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1329 : ¬Nat.Prime 1329 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 443) (n := 1329)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1330 : ¬Nat.Prime 1330 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 665) (n := 1330)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1331 : ¬Nat.Prime 1331 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 121) (n := 1331)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1332 : ¬Nat.Prime 1332 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 666) (n := 1332)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1333 : ¬Nat.Prime 1333 :=
  Nat.not_prime_of_mul_eq (a := 31) (b := 43) (n := 1333)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1334 : ¬Nat.Prime 1334 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 667) (n := 1334)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1335 : ¬Nat.Prime 1335 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 445) (n := 1335)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1336 : ¬Nat.Prime 1336 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 668) (n := 1336)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1337 : ¬Nat.Prime 1337 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 191) (n := 1337)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1338 : ¬Nat.Prime 1338 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 669) (n := 1338)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1339 : ¬Nat.Prime 1339 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 103) (n := 1339)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1340 : ¬Nat.Prime 1340 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 670) (n := 1340)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1341 : ¬Nat.Prime 1341 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 447) (n := 1341)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1342 : ¬Nat.Prime 1342 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 671) (n := 1342)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1343 : ¬Nat.Prime 1343 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 79) (n := 1343)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1344 : ¬Nat.Prime 1344 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 672) (n := 1344)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1345 : ¬Nat.Prime 1345 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 269) (n := 1345)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1346 : ¬Nat.Prime 1346 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 673) (n := 1346)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1347 : ¬Nat.Prime 1347 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 449) (n := 1347)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1348 : ¬Nat.Prime 1348 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 674) (n := 1348)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1349 : ¬Nat.Prime 1349 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 71) (n := 1349)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1350 : ¬Nat.Prime 1350 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 675) (n := 1350)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1351 : ¬Nat.Prime 1351 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 193) (n := 1351)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1352 : ¬Nat.Prime 1352 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 676) (n := 1352)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1353 : ¬Nat.Prime 1353 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 451) (n := 1353)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1354 : ¬Nat.Prime 1354 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 677) (n := 1354)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1355 : ¬Nat.Prime 1355 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 271) (n := 1355)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1356 : ¬Nat.Prime 1356 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 678) (n := 1356)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1357 : ¬Nat.Prime 1357 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 59) (n := 1357)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1358 : ¬Nat.Prime 1358 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 679) (n := 1358)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1359 : ¬Nat.Prime 1359 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 453) (n := 1359)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1360 : ¬Nat.Prime 1360 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 680) (n := 1360)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1361 : Nat.count Nat.Prime 1361 = 217 := by
  rw [show 1361 = 1360 + 1 by norm_num, Nat.count_succ]
  rw [show 1360 = 1359 + 1 by norm_num, Nat.count_succ]
  rw [show 1359 = 1358 + 1 by norm_num, Nat.count_succ]
  rw [show 1358 = 1357 + 1 by norm_num, Nat.count_succ]
  rw [show 1357 = 1356 + 1 by norm_num, Nat.count_succ]
  rw [show 1356 = 1355 + 1 by norm_num, Nat.count_succ]
  rw [show 1355 = 1354 + 1 by norm_num, Nat.count_succ]
  rw [show 1354 = 1353 + 1 by norm_num, Nat.count_succ]
  rw [show 1353 = 1352 + 1 by norm_num, Nat.count_succ]
  rw [show 1352 = 1351 + 1 by norm_num, Nat.count_succ]
  rw [show 1351 = 1350 + 1 by norm_num, Nat.count_succ]
  rw [show 1350 = 1349 + 1 by norm_num, Nat.count_succ]
  rw [show 1349 = 1348 + 1 by norm_num, Nat.count_succ]
  rw [show 1348 = 1347 + 1 by norm_num, Nat.count_succ]
  rw [show 1347 = 1346 + 1 by norm_num, Nat.count_succ]
  rw [show 1346 = 1345 + 1 by norm_num, Nat.count_succ]
  rw [show 1345 = 1344 + 1 by norm_num, Nat.count_succ]
  rw [show 1344 = 1343 + 1 by norm_num, Nat.count_succ]
  rw [show 1343 = 1342 + 1 by norm_num, Nat.count_succ]
  rw [show 1342 = 1341 + 1 by norm_num, Nat.count_succ]
  rw [show 1341 = 1340 + 1 by norm_num, Nat.count_succ]
  rw [show 1340 = 1339 + 1 by norm_num, Nat.count_succ]
  rw [show 1339 = 1338 + 1 by norm_num, Nat.count_succ]
  rw [show 1338 = 1337 + 1 by norm_num, Nat.count_succ]
  rw [show 1337 = 1336 + 1 by norm_num, Nat.count_succ]
  rw [show 1336 = 1335 + 1 by norm_num, Nat.count_succ]
  rw [show 1335 = 1334 + 1 by norm_num, Nat.count_succ]
  rw [show 1334 = 1333 + 1 by norm_num, Nat.count_succ]
  rw [show 1333 = 1332 + 1 by norm_num, Nat.count_succ]
  rw [show 1332 = 1331 + 1 by norm_num, Nat.count_succ]
  rw [show 1331 = 1330 + 1 by norm_num, Nat.count_succ]
  rw [show 1330 = 1329 + 1 by norm_num, Nat.count_succ]
  rw [show 1329 = 1328 + 1 by norm_num, Nat.count_succ]
  rw [show 1328 = 1327 + 1 by norm_num, Nat.count_succ]
  rw [count_1327]
  simp [prime_1327, not_prime_1328, not_prime_1329, not_prime_1330, not_prime_1331, not_prime_1332, not_prime_1333, not_prime_1334, not_prime_1335, not_prime_1336, not_prime_1337, not_prime_1338, not_prime_1339, not_prime_1340, not_prime_1341, not_prime_1342, not_prime_1343, not_prime_1344, not_prime_1345, not_prime_1346, not_prime_1347, not_prime_1348, not_prime_1349, not_prime_1350, not_prime_1351, not_prime_1352, not_prime_1353, not_prime_1354, not_prime_1355, not_prime_1356, not_prime_1357, not_prime_1358, not_prime_1359, not_prime_1360]

theorem prime_1361 : (1361 : Nat).Prime := by norm_num

theorem nth_217 : Nat.nth Nat.Prime 217 = 1361 := by
  rw [← count_1361]
  exact Nat.nth_count prime_1361

theorem not_prime_1362 : ¬Nat.Prime 1362 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 681) (n := 1362)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1363 : ¬Nat.Prime 1363 :=
  Nat.not_prime_of_mul_eq (a := 29) (b := 47) (n := 1363)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1364 : ¬Nat.Prime 1364 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 682) (n := 1364)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1365 : ¬Nat.Prime 1365 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 455) (n := 1365)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1366 : ¬Nat.Prime 1366 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 683) (n := 1366)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1367 : Nat.count Nat.Prime 1367 = 218 := by
  rw [show 1367 = 1366 + 1 by norm_num, Nat.count_succ]
  rw [show 1366 = 1365 + 1 by norm_num, Nat.count_succ]
  rw [show 1365 = 1364 + 1 by norm_num, Nat.count_succ]
  rw [show 1364 = 1363 + 1 by norm_num, Nat.count_succ]
  rw [show 1363 = 1362 + 1 by norm_num, Nat.count_succ]
  rw [show 1362 = 1361 + 1 by norm_num, Nat.count_succ]
  rw [count_1361]
  simp [prime_1361, not_prime_1362, not_prime_1363, not_prime_1364, not_prime_1365, not_prime_1366]

theorem prime_1367 : (1367 : Nat).Prime := by norm_num

theorem nth_218 : Nat.nth Nat.Prime 218 = 1367 := by
  rw [← count_1367]
  exact Nat.nth_count prime_1367

theorem not_prime_1368 : ¬Nat.Prime 1368 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 684) (n := 1368)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1369 : ¬Nat.Prime 1369 :=
  Nat.not_prime_of_mul_eq (a := 37) (b := 37) (n := 1369)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1370 : ¬Nat.Prime 1370 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 685) (n := 1370)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1371 : ¬Nat.Prime 1371 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 457) (n := 1371)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1372 : ¬Nat.Prime 1372 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 686) (n := 1372)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1373 : Nat.count Nat.Prime 1373 = 219 := by
  rw [show 1373 = 1372 + 1 by norm_num, Nat.count_succ]
  rw [show 1372 = 1371 + 1 by norm_num, Nat.count_succ]
  rw [show 1371 = 1370 + 1 by norm_num, Nat.count_succ]
  rw [show 1370 = 1369 + 1 by norm_num, Nat.count_succ]
  rw [show 1369 = 1368 + 1 by norm_num, Nat.count_succ]
  rw [show 1368 = 1367 + 1 by norm_num, Nat.count_succ]
  rw [count_1367]
  simp [prime_1367, not_prime_1368, not_prime_1369, not_prime_1370, not_prime_1371, not_prime_1372]

theorem prime_1373 : (1373 : Nat).Prime := by norm_num

theorem nth_219 : Nat.nth Nat.Prime 219 = 1373 := by
  rw [← count_1373]
  exact Nat.nth_count prime_1373

theorem not_prime_1374 : ¬Nat.Prime 1374 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 687) (n := 1374)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1375 : ¬Nat.Prime 1375 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 275) (n := 1375)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1376 : ¬Nat.Prime 1376 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 688) (n := 1376)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1377 : ¬Nat.Prime 1377 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 459) (n := 1377)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1378 : ¬Nat.Prime 1378 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 689) (n := 1378)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1379 : ¬Nat.Prime 1379 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 197) (n := 1379)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1380 : ¬Nat.Prime 1380 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 690) (n := 1380)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1381 : Nat.count Nat.Prime 1381 = 220 := by
  rw [show 1381 = 1380 + 1 by norm_num, Nat.count_succ]
  rw [show 1380 = 1379 + 1 by norm_num, Nat.count_succ]
  rw [show 1379 = 1378 + 1 by norm_num, Nat.count_succ]
  rw [show 1378 = 1377 + 1 by norm_num, Nat.count_succ]
  rw [show 1377 = 1376 + 1 by norm_num, Nat.count_succ]
  rw [show 1376 = 1375 + 1 by norm_num, Nat.count_succ]
  rw [show 1375 = 1374 + 1 by norm_num, Nat.count_succ]
  rw [show 1374 = 1373 + 1 by norm_num, Nat.count_succ]
  rw [count_1373]
  simp [prime_1373, not_prime_1374, not_prime_1375, not_prime_1376, not_prime_1377, not_prime_1378, not_prime_1379, not_prime_1380]

theorem prime_1381 : (1381 : Nat).Prime := by norm_num

theorem nth_220 : Nat.nth Nat.Prime 220 = 1381 := by
  rw [← count_1381]
  exact Nat.nth_count prime_1381

theorem not_prime_1382 : ¬Nat.Prime 1382 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 691) (n := 1382)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1383 : ¬Nat.Prime 1383 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 461) (n := 1383)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1384 : ¬Nat.Prime 1384 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 692) (n := 1384)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1385 : ¬Nat.Prime 1385 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 277) (n := 1385)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1386 : ¬Nat.Prime 1386 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 693) (n := 1386)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1387 : ¬Nat.Prime 1387 :=
  Nat.not_prime_of_mul_eq (a := 19) (b := 73) (n := 1387)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1388 : ¬Nat.Prime 1388 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 694) (n := 1388)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1389 : ¬Nat.Prime 1389 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 463) (n := 1389)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1390 : ¬Nat.Prime 1390 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 695) (n := 1390)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1391 : ¬Nat.Prime 1391 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 107) (n := 1391)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1392 : ¬Nat.Prime 1392 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 696) (n := 1392)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1393 : ¬Nat.Prime 1393 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 199) (n := 1393)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1394 : ¬Nat.Prime 1394 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 697) (n := 1394)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1395 : ¬Nat.Prime 1395 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 465) (n := 1395)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1396 : ¬Nat.Prime 1396 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 698) (n := 1396)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1397 : ¬Nat.Prime 1397 :=
  Nat.not_prime_of_mul_eq (a := 11) (b := 127) (n := 1397)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1398 : ¬Nat.Prime 1398 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 699) (n := 1398)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1399 : Nat.count Nat.Prime 1399 = 221 := by
  rw [show 1399 = 1398 + 1 by norm_num, Nat.count_succ]
  rw [show 1398 = 1397 + 1 by norm_num, Nat.count_succ]
  rw [show 1397 = 1396 + 1 by norm_num, Nat.count_succ]
  rw [show 1396 = 1395 + 1 by norm_num, Nat.count_succ]
  rw [show 1395 = 1394 + 1 by norm_num, Nat.count_succ]
  rw [show 1394 = 1393 + 1 by norm_num, Nat.count_succ]
  rw [show 1393 = 1392 + 1 by norm_num, Nat.count_succ]
  rw [show 1392 = 1391 + 1 by norm_num, Nat.count_succ]
  rw [show 1391 = 1390 + 1 by norm_num, Nat.count_succ]
  rw [show 1390 = 1389 + 1 by norm_num, Nat.count_succ]
  rw [show 1389 = 1388 + 1 by norm_num, Nat.count_succ]
  rw [show 1388 = 1387 + 1 by norm_num, Nat.count_succ]
  rw [show 1387 = 1386 + 1 by norm_num, Nat.count_succ]
  rw [show 1386 = 1385 + 1 by norm_num, Nat.count_succ]
  rw [show 1385 = 1384 + 1 by norm_num, Nat.count_succ]
  rw [show 1384 = 1383 + 1 by norm_num, Nat.count_succ]
  rw [show 1383 = 1382 + 1 by norm_num, Nat.count_succ]
  rw [show 1382 = 1381 + 1 by norm_num, Nat.count_succ]
  rw [count_1381]
  simp [prime_1381, not_prime_1382, not_prime_1383, not_prime_1384, not_prime_1385, not_prime_1386, not_prime_1387, not_prime_1388, not_prime_1389, not_prime_1390, not_prime_1391, not_prime_1392, not_prime_1393, not_prime_1394, not_prime_1395, not_prime_1396, not_prime_1397, not_prime_1398]

theorem prime_1399 : (1399 : Nat).Prime := by norm_num

theorem nth_221 : Nat.nth Nat.Prime 221 = 1399 := by
  rw [← count_1399]
  exact Nat.nth_count prime_1399

theorem not_prime_1400 : ¬Nat.Prime 1400 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 700) (n := 1400)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1401 : ¬Nat.Prime 1401 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 467) (n := 1401)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1402 : ¬Nat.Prime 1402 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 701) (n := 1402)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1403 : ¬Nat.Prime 1403 :=
  Nat.not_prime_of_mul_eq (a := 23) (b := 61) (n := 1403)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1404 : ¬Nat.Prime 1404 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 702) (n := 1404)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1405 : ¬Nat.Prime 1405 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 281) (n := 1405)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1406 : ¬Nat.Prime 1406 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 703) (n := 1406)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1407 : ¬Nat.Prime 1407 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 469) (n := 1407)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1408 : ¬Nat.Prime 1408 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 704) (n := 1408)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1409 : Nat.count Nat.Prime 1409 = 222 := by
  rw [show 1409 = 1408 + 1 by norm_num, Nat.count_succ]
  rw [show 1408 = 1407 + 1 by norm_num, Nat.count_succ]
  rw [show 1407 = 1406 + 1 by norm_num, Nat.count_succ]
  rw [show 1406 = 1405 + 1 by norm_num, Nat.count_succ]
  rw [show 1405 = 1404 + 1 by norm_num, Nat.count_succ]
  rw [show 1404 = 1403 + 1 by norm_num, Nat.count_succ]
  rw [show 1403 = 1402 + 1 by norm_num, Nat.count_succ]
  rw [show 1402 = 1401 + 1 by norm_num, Nat.count_succ]
  rw [show 1401 = 1400 + 1 by norm_num, Nat.count_succ]
  rw [show 1400 = 1399 + 1 by norm_num, Nat.count_succ]
  rw [count_1399]
  simp [prime_1399, not_prime_1400, not_prime_1401, not_prime_1402, not_prime_1403, not_prime_1404, not_prime_1405, not_prime_1406, not_prime_1407, not_prime_1408]

theorem prime_1409 : (1409 : Nat).Prime := by norm_num

theorem nth_222 : Nat.nth Nat.Prime 222 = 1409 := by
  rw [← count_1409]
  exact Nat.nth_count prime_1409

theorem not_prime_1410 : ¬Nat.Prime 1410 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 705) (n := 1410)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1411 : ¬Nat.Prime 1411 :=
  Nat.not_prime_of_mul_eq (a := 17) (b := 83) (n := 1411)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1412 : ¬Nat.Prime 1412 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 706) (n := 1412)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1413 : ¬Nat.Prime 1413 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 471) (n := 1413)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1414 : ¬Nat.Prime 1414 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 707) (n := 1414)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1415 : ¬Nat.Prime 1415 :=
  Nat.not_prime_of_mul_eq (a := 5) (b := 283) (n := 1415)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1416 : ¬Nat.Prime 1416 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 708) (n := 1416)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1417 : ¬Nat.Prime 1417 :=
  Nat.not_prime_of_mul_eq (a := 13) (b := 109) (n := 1417)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1418 : ¬Nat.Prime 1418 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 709) (n := 1418)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1419 : ¬Nat.Prime 1419 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 473) (n := 1419)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1420 : ¬Nat.Prime 1420 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 710) (n := 1420)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1421 : ¬Nat.Prime 1421 :=
  Nat.not_prime_of_mul_eq (a := 7) (b := 203) (n := 1421)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1422 : ¬Nat.Prime 1422 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 711) (n := 1422)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1423 : Nat.count Nat.Prime 1423 = 223 := by
  rw [show 1423 = 1422 + 1 by norm_num, Nat.count_succ]
  rw [show 1422 = 1421 + 1 by norm_num, Nat.count_succ]
  rw [show 1421 = 1420 + 1 by norm_num, Nat.count_succ]
  rw [show 1420 = 1419 + 1 by norm_num, Nat.count_succ]
  rw [show 1419 = 1418 + 1 by norm_num, Nat.count_succ]
  rw [show 1418 = 1417 + 1 by norm_num, Nat.count_succ]
  rw [show 1417 = 1416 + 1 by norm_num, Nat.count_succ]
  rw [show 1416 = 1415 + 1 by norm_num, Nat.count_succ]
  rw [show 1415 = 1414 + 1 by norm_num, Nat.count_succ]
  rw [show 1414 = 1413 + 1 by norm_num, Nat.count_succ]
  rw [show 1413 = 1412 + 1 by norm_num, Nat.count_succ]
  rw [show 1412 = 1411 + 1 by norm_num, Nat.count_succ]
  rw [show 1411 = 1410 + 1 by norm_num, Nat.count_succ]
  rw [show 1410 = 1409 + 1 by norm_num, Nat.count_succ]
  rw [count_1409]
  simp [prime_1409, not_prime_1410, not_prime_1411, not_prime_1412, not_prime_1413, not_prime_1414, not_prime_1415, not_prime_1416, not_prime_1417, not_prime_1418, not_prime_1419, not_prime_1420, not_prime_1421, not_prime_1422]

theorem prime_1423 : (1423 : Nat).Prime := by norm_num

theorem nth_223 : Nat.nth Nat.Prime 223 = 1423 := by
  rw [← count_1423]
  exact Nat.nth_count prime_1423

theorem not_prime_1424 : ¬Nat.Prime 1424 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 712) (n := 1424)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1425 : ¬Nat.Prime 1425 :=
  Nat.not_prime_of_mul_eq (a := 3) (b := 475) (n := 1425)
    (by norm_num) (by norm_num) (by norm_num)

theorem not_prime_1426 : ¬Nat.Prime 1426 :=
  Nat.not_prime_of_mul_eq (a := 2) (b := 713) (n := 1426)
    (by norm_num) (by norm_num) (by norm_num)

theorem count_1427 : Nat.count Nat.Prime 1427 = 224 := by
  rw [show 1427 = 1426 + 1 by norm_num, Nat.count_succ]
  rw [show 1426 = 1425 + 1 by norm_num, Nat.count_succ]
  rw [show 1425 = 1424 + 1 by norm_num, Nat.count_succ]
  rw [show 1424 = 1423 + 1 by norm_num, Nat.count_succ]
  rw [count_1423]
  simp [prime_1423, not_prime_1424, not_prime_1425, not_prime_1426]

theorem prime_1427 : (1427 : Nat).Prime := by norm_num

theorem nth_224 : Nat.nth Nat.Prime 224 = 1427 := by
  rw [← count_1427]
  exact Nat.nth_count prime_1427

end OeisA100474.PrimeCertificate
