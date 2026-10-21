{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2e_B03 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0127 ; K0134 ; K0135 ; K0137 ; K0145 ; K0147 ; K0157 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0357 ; K0367 ; K0457 ; K0467 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1357 ; K1367 ; K1457 ; K1467 ; K2345 ; K2346 ; K2347 ; K2357 ; K2367 ; K2457 ; K2467 ; K3457 ; K3467 ; M5 ; M6 ; M7 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R094 as R094
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B047 using (module MV01807 ; module MV01809)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B057 using (module MV02195 ; module MV02196 ; module MV02197 ; module MV02198 ; module MV02199 ; module MV02200 ; module MV02201 ; module MV02202 ; module MV02203 ; module MV02204 ; module MV02205 ; module MV02206 ; module MV02207 ; module MV02208 ; module MV02209 ; module MV02210)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B058 using (module MV02211 ; module MV02212 ; module MV02213 ; module MV02214 ; module MV02215 ; module MV02216 ; module MV02217 ; module MV02218 ; module MV02219 ; module MV02220 ; module MV02221 ; module MV02222 ; module MV02223 ; module MV02224 ; module MV02225 ; module MV02226 ; module MV02227 ; module MV02228 ; module MV02229 ; module MV02230 ; module MV02231 ; module MV02232 ; module MV02233 ; module MV02234 ; module MV02235 ; module MV02236 ; module MV02237 ; module MV02238 ; module MV02239 ; module MV02240 ; module MV02241 ; module MV02242 ; module MV02243)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B059 using (module MV02244 ; module MV02245 ; module MV02246 ; module MV02247 ; module MV02248 ; module MV02249 ; module MV02250 ; module MV02251 ; module MV02252 ; module MV02253 ; module MV02254 ; module MV02255 ; module MV02256 ; module MV02257 ; module MV02258 ; module MV02259 ; module MV02260 ; module MV02261 ; module MV02262 ; module MV02263 ; module MV02264 ; module MV02265 ; module MV02266 ; module MV02267 ; module MV02268 ; module MV02269 ; module MV02270 ; module MV02271 ; module MV02272 ; module MV02273 ; module MV02274 ; module MV02275 ; module MV02276 ; module MV02277 ; module MV02278 ; module MV02279 ; module MV02280 ; module MV02281 ; module MV02282 ; module MV02283 ; module MV02284 ; module MV02285 ; module MV02286 ; module MV02287)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B060 using (module MV02288 ; module MV02289 ; module MV02290 ; module MV02291 ; module MV02292 ; module MV02293 ; module MV02294 ; module MV02295 ; module MV02296 ; module MV02297 ; module MV02298 ; module MV02299 ; module MV02300 ; module MV02301 ; module MV02302 ; module MV02303 ; module MV02304 ; module MV02305 ; module MV02306 ; module MV02307 ; module MV02308 ; module MV02309 ; module MV02310 ; module MV02311 ; module MV02312 ; module MV02313 ; module MV02314 ; module MV02315 ; module MV02316)

module r2e_ij50236 where

  proved : M5 • K0236 ≈ K0236 • M5
  proved = GL.•-cancelʳ {g = M5 • K0236} {g' = K0236 • M5} {h = p (s1 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02195.proved (MV02196.proved))) (trans (cong refl R094.proved) (move-product MV02196.proved (MV02195.proved))))

module r2e_ij50237 where

  proved : M5 • K0237 ≈ K0237 • M5
  proved = GL.•-cancelʳ {g = M5 • K0237} {g' = K0237 • M5} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02197.proved (MV02198.proved))) (trans (cong refl R094.proved) (move-product MV02198.proved (MV02197.proved))))

module r2e_ij50246 where

  proved : M5 • K0246 ≈ K0246 • M5
  proved = GL.•-cancelʳ {g = M5 • K0246} {g' = K0246 • M5} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02199.proved (MV02200.proved))) (trans (cong refl R094.proved) (move-product MV02200.proved (MV02199.proved))))

module r2e_ij50247 where

  proved : M5 • K0247 ≈ K0247 • M5
  proved = GL.•-cancelʳ {g = M5 • K0247} {g' = K0247 • M5} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02201.proved (MV02202.proved))) (trans (cong refl R094.proved) (move-product MV02202.proved (MV02201.proved))))

module r2e_ij50267 where

  proved : M5 • K0267 ≈ K0267 • M5
  proved = GL.•-cancelʳ {g = M5 • K0267} {g' = K0267 • M5} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02203.proved (MV02204.proved))) (trans (cong refl R094.proved) (move-product MV02204.proved (MV02203.proved))))

module r2e_ij50346 where

  proved : M5 • K0346 ≈ K0346 • M5
  proved = GL.•-cancelʳ {g = M5 • K0346} {g' = K0346 • M5} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02205.proved (MV02206.proved))) (trans (cong refl R094.proved) (move-product MV02206.proved (MV02205.proved))))

module r2e_ij50347 where

  proved : M5 • K0347 ≈ K0347 • M5
  proved = GL.•-cancelʳ {g = M5 • K0347} {g' = K0347 • M5} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02207.proved (MV02208.proved))) (trans (cong refl R094.proved) (move-product MV02208.proved (MV02207.proved))))

module r2e_ij50367 where

  proved : M5 • K0367 ≈ K0367 • M5
  proved = GL.•-cancelʳ {g = M5 • K0367} {g' = K0367 • M5} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02209.proved (MV02210.proved))) (trans (cong refl R094.proved) (move-product MV02210.proved (MV02209.proved))))

module r2e_ij50467 where

  proved : M5 • K0467 ≈ K0467 • M5
  proved = GL.•-cancelʳ {g = M5 • K0467} {g' = K0467 • M5} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02211.proved (MV02212.proved))) (trans (cong refl R094.proved) (move-product MV02212.proved (MV02211.proved))))

module r2e_ij51234 where

  proved : M5 • K1234 ≈ K1234 • M5
  proved = GL.•-cancelʳ {g = M5 • K1234} {g' = K1234 • M5} {h = p (s0 • s1 • s2 • s3 • s4)}
    (trans (sym (move-product MV02213.proved (MV02214.proved))) (trans (cong refl R094.proved) (move-product MV02214.proved (MV02213.proved))))

module r2e_ij51236 where

  proved : M5 • K1236 ≈ K1236 • M5
  proved = GL.•-cancelʳ {g = M5 • K1236} {g' = K1236 • M5} {h = p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02215.proved (MV02216.proved))) (trans (cong refl R094.proved) (move-product MV02216.proved (MV02215.proved))))

module r2e_ij51237 where

  proved : M5 • K1237 ≈ K1237 • M5
  proved = GL.•-cancelʳ {g = M5 • K1237} {g' = K1237 • M5} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02217.proved (MV02218.proved))) (trans (cong refl R094.proved) (move-product MV02218.proved (MV02217.proved))))

module r2e_ij51246 where

  proved : M5 • K1246 ≈ K1246 • M5
  proved = GL.•-cancelʳ {g = M5 • K1246} {g' = K1246 • M5} {h = p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02219.proved (MV02220.proved))) (trans (cong refl R094.proved) (move-product MV02220.proved (MV02219.proved))))

module r2e_ij51247 where

  proved : M5 • K1247 ≈ K1247 • M5
  proved = GL.•-cancelʳ {g = M5 • K1247} {g' = K1247 • M5} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02221.proved (MV02222.proved))) (trans (cong refl R094.proved) (move-product MV02222.proved (MV02221.proved))))

module r2e_ij51267 where

  proved : M5 • K1267 ≈ K1267 • M5
  proved = GL.•-cancelʳ {g = M5 • K1267} {g' = K1267 • M5} {h = p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02223.proved (MV02224.proved))) (trans (cong refl R094.proved) (move-product MV02224.proved (MV02223.proved))))

module r2e_ij51346 where

  proved : M5 • K1346 ≈ K1346 • M5
  proved = GL.•-cancelʳ {g = M5 • K1346} {g' = K1346 • M5} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02225.proved (MV02226.proved))) (trans (cong refl R094.proved) (move-product MV02226.proved (MV02225.proved))))

module r2e_ij51347 where

  proved : M5 • K1347 ≈ K1347 • M5
  proved = GL.•-cancelʳ {g = M5 • K1347} {g' = K1347 • M5} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02227.proved (MV02228.proved))) (trans (cong refl R094.proved) (move-product MV02228.proved (MV02227.proved))))

module r2e_ij51367 where

  proved : M5 • K1367 ≈ K1367 • M5
  proved = GL.•-cancelʳ {g = M5 • K1367} {g' = K1367 • M5} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02229.proved (MV02230.proved))) (trans (cong refl R094.proved) (move-product MV02230.proved (MV02229.proved))))

module r2e_ij51467 where

  proved : M5 • K1467 ≈ K1467 • M5
  proved = GL.•-cancelʳ {g = M5 • K1467} {g' = K1467 • M5} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02231.proved (MV02232.proved))) (trans (cong refl R094.proved) (move-product MV02232.proved (MV02231.proved))))

module r2e_ij52346 where

  proved : M5 • K2346 ≈ K2346 • M5
  proved = GL.•-cancelʳ {g = M5 • K2346} {g' = K2346 • M5} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02233.proved (MV02234.proved))) (trans (cong refl R094.proved) (move-product MV02234.proved (MV02233.proved))))

module r2e_ij52347 where

  proved : M5 • K2347 ≈ K2347 • M5
  proved = GL.•-cancelʳ {g = M5 • K2347} {g' = K2347 • M5} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02235.proved (MV02236.proved))) (trans (cong refl R094.proved) (move-product MV02236.proved (MV02235.proved))))

module r2e_ij52367 where

  proved : M5 • K2367 ≈ K2367 • M5
  proved = GL.•-cancelʳ {g = M5 • K2367} {g' = K2367 • M5} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02237.proved (MV02238.proved))) (trans (cong refl R094.proved) (move-product MV02238.proved (MV02237.proved))))

module r2e_ij52467 where

  proved : M5 • K2467 ≈ K2467 • M5
  proved = GL.•-cancelʳ {g = M5 • K2467} {g' = K2467 • M5} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02239.proved (MV02240.proved))) (trans (cong refl R094.proved) (move-product MV02240.proved (MV02239.proved))))

module r2e_ij53467 where

  proved : M5 • K3467 ≈ K3467 • M5
  proved = GL.•-cancelʳ {g = M5 • K3467} {g' = K3467 • M5} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02241.proved (MV02242.proved))) (trans (cong refl R094.proved) (move-product MV02242.proved (MV02241.proved))))

module r2e_ij60123 where

  proved : M6 • K0123 ≈ K0123 • M6
  proved = GL.•-cancelʳ {g = M6 • K0123} {g' = K0123 • M6} {h = p (s5 • s4)}
    (trans (sym (move-product MV01807.proved (MV02243.proved))) (trans (cong refl R094.proved) (move-product MV02243.proved (MV01807.proved))))

module r2e_ij60124 where

  proved : M6 • K0124 ≈ K0124 • M6
  proved = GL.•-cancelʳ {g = M6 • K0124} {g' = K0124 • M6} {h = p (s3 • s5 • s4)}
    (trans (sym (move-product MV02244.proved (MV02245.proved))) (trans (cong refl R094.proved) (move-product MV02245.proved (MV02244.proved))))

module r2e_ij60125 where

  proved : M6 • K0125 ≈ K0125 • M6
  proved = GL.•-cancelʳ {g = M6 • K0125} {g' = K0125 • M6} {h = p (s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02246.proved (MV02247.proved))) (trans (cong refl R094.proved) (move-product MV02247.proved (MV02246.proved))))

module r2e_ij60127 where

  proved : M6 • K0127 ≈ K0127 • M6
  proved = GL.•-cancelʳ {g = M6 • K0127} {g' = K0127 • M6} {h = p (s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02248.proved (MV02249.proved))) (trans (cong refl R094.proved) (move-product MV02249.proved (MV02248.proved))))

module r2e_ij60134 where

  proved : M6 • K0134 ≈ K0134 • M6
  proved = GL.•-cancelʳ {g = M6 • K0134} {g' = K0134 • M6} {h = p (s2 • s3 • s5 • s4)}
    (trans (sym (move-product MV02250.proved (MV02251.proved))) (trans (cong refl R094.proved) (move-product MV02251.proved (MV02250.proved))))

module r2e_ij60135 where

  proved : M6 • K0135 ≈ K0135 • M6
  proved = GL.•-cancelʳ {g = M6 • K0135} {g' = K0135 • M6} {h = p (s2 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02252.proved (MV02253.proved))) (trans (cong refl R094.proved) (move-product MV02253.proved (MV02252.proved))))

module r2e_ij60137 where

  proved : M6 • K0137 ≈ K0137 • M6
  proved = GL.•-cancelʳ {g = M6 • K0137} {g' = K0137 • M6} {h = p (s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02254.proved (MV02255.proved))) (trans (cong refl R094.proved) (move-product MV02255.proved (MV02254.proved))))

module r2e_ij60145 where

  proved : M6 • K0145 ≈ K0145 • M6
  proved = GL.•-cancelʳ {g = M6 • K0145} {g' = K0145 • M6} {h = p (s3 • s2 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02256.proved (MV02257.proved))) (trans (cong refl R094.proved) (move-product MV02257.proved (MV02256.proved))))

module r2e_ij60147 where

  proved : M6 • K0147 ≈ K0147 • M6
  proved = GL.•-cancelʳ {g = M6 • K0147} {g' = K0147 • M6} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02258.proved (MV02259.proved))) (trans (cong refl R094.proved) (move-product MV02259.proved (MV02258.proved))))

module r2e_ij60157 where

  proved : M6 • K0157 ≈ K0157 • M6
  proved = GL.•-cancelʳ {g = M6 • K0157} {g' = K0157 • M6} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02260.proved (MV02261.proved))) (trans (cong refl R094.proved) (move-product MV02261.proved (MV02260.proved))))

module r2e_ij60234 where

  proved : M6 • K0234 ≈ K0234 • M6
  proved = GL.•-cancelʳ {g = M6 • K0234} {g' = K0234 • M6} {h = p (s1 • s2 • s3 • s5 • s4)}
    (trans (sym (move-product MV02262.proved (MV02263.proved))) (trans (cong refl R094.proved) (move-product MV02263.proved (MV02262.proved))))

module r2e_ij60235 where

  proved : M6 • K0235 ≈ K0235 • M6
  proved = GL.•-cancelʳ {g = M6 • K0235} {g' = K0235 • M6} {h = p (s1 • s2 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02264.proved (MV02265.proved))) (trans (cong refl R094.proved) (move-product MV02265.proved (MV02264.proved))))

module r2e_ij60237 where

  proved : M6 • K0237 ≈ K0237 • M6
  proved = GL.•-cancelʳ {g = M6 • K0237} {g' = K0237 • M6} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02266.proved (MV02267.proved))) (trans (cong refl R094.proved) (move-product MV02267.proved (MV02266.proved))))

module r2e_ij60245 where

  proved : M6 • K0245 ≈ K0245 • M6
  proved = GL.•-cancelʳ {g = M6 • K0245} {g' = K0245 • M6} {h = p (s1 • s3 • s2 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02268.proved (MV02269.proved))) (trans (cong refl R094.proved) (move-product MV02269.proved (MV02268.proved))))

module r2e_ij60247 where

  proved : M6 • K0247 ≈ K0247 • M6
  proved = GL.•-cancelʳ {g = M6 • K0247} {g' = K0247 • M6} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02270.proved (MV02271.proved))) (trans (cong refl R094.proved) (move-product MV02271.proved (MV02270.proved))))

module r2e_ij60257 where

  proved : M6 • K0257 ≈ K0257 • M6
  proved = GL.•-cancelʳ {g = M6 • K0257} {g' = K0257 • M6} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02272.proved (MV02273.proved))) (trans (cong refl R094.proved) (move-product MV02273.proved (MV02272.proved))))

module r2e_ij60345 where

  proved : M6 • K0345 ≈ K0345 • M6
  proved = GL.•-cancelʳ {g = M6 • K0345} {g' = K0345 • M6} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02274.proved (MV02275.proved))) (trans (cong refl R094.proved) (move-product MV02275.proved (MV02274.proved))))

module r2e_ij60347 where

  proved : M6 • K0347 ≈ K0347 • M6
  proved = GL.•-cancelʳ {g = M6 • K0347} {g' = K0347 • M6} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02276.proved (MV02277.proved))) (trans (cong refl R094.proved) (move-product MV02277.proved (MV02276.proved))))

module r2e_ij60357 where

  proved : M6 • K0357 ≈ K0357 • M6
  proved = GL.•-cancelʳ {g = M6 • K0357} {g' = K0357 • M6} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02278.proved (MV02279.proved))) (trans (cong refl R094.proved) (move-product MV02279.proved (MV02278.proved))))

module r2e_ij60457 where

  proved : M6 • K0457 ≈ K0457 • M6
  proved = GL.•-cancelʳ {g = M6 • K0457} {g' = K0457 • M6} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02280.proved (MV02281.proved))) (trans (cong refl R094.proved) (move-product MV02281.proved (MV02280.proved))))

module r2e_ij61234 where

  proved : M6 • K1234 ≈ K1234 • M6
  proved = GL.•-cancelʳ {g = M6 • K1234} {g' = K1234 • M6} {h = p (s0 • s1 • s2 • s3 • s5 • s4)}
    (trans (sym (move-product MV02282.proved (MV02283.proved))) (trans (cong refl R094.proved) (move-product MV02283.proved (MV02282.proved))))

module r2e_ij61235 where

  proved : M6 • K1235 ≈ K1235 • M6
  proved = GL.•-cancelʳ {g = M6 • K1235} {g' = K1235 • M6} {h = p (s0 • s1 • s2 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02284.proved (MV02285.proved))) (trans (cong refl R094.proved) (move-product MV02285.proved (MV02284.proved))))

module r2e_ij61237 where

  proved : M6 • K1237 ≈ K1237 • M6
  proved = GL.•-cancelʳ {g = M6 • K1237} {g' = K1237 • M6} {h = p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02286.proved (MV02287.proved))) (trans (cong refl R094.proved) (move-product MV02287.proved (MV02286.proved))))

module r2e_ij61245 where

  proved : M6 • K1245 ≈ K1245 • M6
  proved = GL.•-cancelʳ {g = M6 • K1245} {g' = K1245 • M6} {h = p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02288.proved (MV02289.proved))) (trans (cong refl R094.proved) (move-product MV02289.proved (MV02288.proved))))

module r2e_ij61247 where

  proved : M6 • K1247 ≈ K1247 • M6
  proved = GL.•-cancelʳ {g = M6 • K1247} {g' = K1247 • M6} {h = p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02290.proved (MV02291.proved))) (trans (cong refl R094.proved) (move-product MV02291.proved (MV02290.proved))))

module r2e_ij61257 where

  proved : M6 • K1257 ≈ K1257 • M6
  proved = GL.•-cancelʳ {g = M6 • K1257} {g' = K1257 • M6} {h = p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02292.proved (MV02293.proved))) (trans (cong refl R094.proved) (move-product MV02293.proved (MV02292.proved))))

module r2e_ij61345 where

  proved : M6 • K1345 ≈ K1345 • M6
  proved = GL.•-cancelʳ {g = M6 • K1345} {g' = K1345 • M6} {h = p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02294.proved (MV02295.proved))) (trans (cong refl R094.proved) (move-product MV02295.proved (MV02294.proved))))

module r2e_ij61347 where

  proved : M6 • K1347 ≈ K1347 • M6
  proved = GL.•-cancelʳ {g = M6 • K1347} {g' = K1347 • M6} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02296.proved (MV02297.proved))) (trans (cong refl R094.proved) (move-product MV02297.proved (MV02296.proved))))

module r2e_ij61357 where

  proved : M6 • K1357 ≈ K1357 • M6
  proved = GL.•-cancelʳ {g = M6 • K1357} {g' = K1357 • M6} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02298.proved (MV02299.proved))) (trans (cong refl R094.proved) (move-product MV02299.proved (MV02298.proved))))

module r2e_ij61457 where

  proved : M6 • K1457 ≈ K1457 • M6
  proved = GL.•-cancelʳ {g = M6 • K1457} {g' = K1457 • M6} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02300.proved (MV02301.proved))) (trans (cong refl R094.proved) (move-product MV02301.proved (MV02300.proved))))

module r2e_ij62345 where

  proved : M6 • K2345 ≈ K2345 • M6
  proved = GL.•-cancelʳ {g = M6 • K2345} {g' = K2345 • M6} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4)}
    (trans (sym (move-product MV02302.proved (MV02303.proved))) (trans (cong refl R094.proved) (move-product MV02303.proved (MV02302.proved))))

module r2e_ij62347 where

  proved : M6 • K2347 ≈ K2347 • M6
  proved = GL.•-cancelʳ {g = M6 • K2347} {g' = K2347 • M6} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02304.proved (MV02305.proved))) (trans (cong refl R094.proved) (move-product MV02305.proved (MV02304.proved))))

module r2e_ij62357 where

  proved : M6 • K2357 ≈ K2357 • M6
  proved = GL.•-cancelʳ {g = M6 • K2357} {g' = K2357 • M6} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02306.proved (MV02307.proved))) (trans (cong refl R094.proved) (move-product MV02307.proved (MV02306.proved))))

module r2e_ij62457 where

  proved : M6 • K2457 ≈ K2457 • M6
  proved = GL.•-cancelʳ {g = M6 • K2457} {g' = K2457 • M6} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02308.proved (MV02309.proved))) (trans (cong refl R094.proved) (move-product MV02309.proved (MV02308.proved))))

module r2e_ij63457 where

  proved : M6 • K3457 ≈ K3457 • M6
  proved = GL.•-cancelʳ {g = M6 • K3457} {g' = K3457 • M6} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02310.proved (MV02311.proved))) (trans (cong refl R094.proved) (move-product MV02311.proved (MV02310.proved))))

module r2e_ij70123 where

  proved : M7 • K0123 ≈ K0123 • M7
  proved = GL.•-cancelʳ {g = M7 • K0123} {g' = K0123 • M7} {h = p (s6 • s5 • s4)}
    (trans (sym (move-product MV01809.proved (MV02312.proved))) (trans (cong refl R094.proved) (move-product MV02312.proved (MV01809.proved))))

module r2e_ij70124 where

  proved : M7 • K0124 ≈ K0124 • M7
  proved = GL.•-cancelʳ {g = M7 • K0124} {g' = K0124 • M7} {h = p (s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02313.proved (MV02314.proved))) (trans (cong refl R094.proved) (move-product MV02314.proved (MV02313.proved))))

module r2e_ij70125 where

  proved : M7 • K0125 ≈ K0125 • M7
  proved = GL.•-cancelʳ {g = M7 • K0125} {g' = K0125 • M7} {h = p (s4 • s3 • s6 • s5 • s4)}
    (trans (sym (move-product MV02315.proved (MV02316.proved))) (trans (cong refl R094.proved) (move-product MV02316.proved (MV02315.proved))))
