{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_B02 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3457 ; K3467 ; K3567 ; K4567 ; X13 ; X14 ; X15 ; X16 ; X17 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as R091
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00655 ; module MV00656 ; module MV00657 ; module MV00658 ; module MV00660 ; module MV00661 ; module MV00662 ; module MV00663 ; module MV00664)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B032 using (module MV01230 ; module MV01231 ; module MV01232 ; module MV01233 ; module MV01234 ; module MV01235 ; module MV01236 ; module MV01237 ; module MV01238 ; module MV01239 ; module MV01240 ; module MV01241 ; module MV01242 ; module MV01243 ; module MV01244 ; module MV01245 ; module MV01246 ; module MV01247 ; module MV01248 ; module MV01249 ; module MV01250)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B033 using (module MV01251 ; module MV01252 ; module MV01253 ; module MV01254 ; module MV01255 ; module MV01256 ; module MV01257 ; module MV01258 ; module MV01259 ; module MV01260 ; module MV01261 ; module MV01262 ; module MV01263 ; module MV01264 ; module MV01265 ; module MV01266 ; module MV01267 ; module MV01268 ; module MV01269 ; module MV01270 ; module MV01271 ; module MV01272 ; module MV01273 ; module MV01274 ; module MV01275 ; module MV01276 ; module MV01277 ; module MV01278 ; module MV01279 ; module MV01280 ; module MV01281 ; module MV01282 ; module MV01283 ; module MV01284)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B034 using (module MV01285 ; module MV01286 ; module MV01287 ; module MV01288 ; module MV01289 ; module MV01290 ; module MV01291 ; module MV01292 ; module MV01293 ; module MV01294 ; module MV01295 ; module MV01296 ; module MV01297 ; module MV01298 ; module MV01299 ; module MV01300 ; module MV01301 ; module MV01302 ; module MV01303 ; module MV01304 ; module MV01305 ; module MV01306 ; module MV01307 ; module MV01308 ; module MV01309 ; module MV01310 ; module MV01311 ; module MV01312 ; module MV01313 ; module MV01314 ; module MV01315 ; module MV01316 ; module MV01317 ; module MV01318 ; module MV01319 ; module MV01320 ; module MV01321)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B035 using (module MV01322 ; module MV01323 ; module MV01324 ; module MV01325 ; module MV01326 ; module MV01327 ; module MV01328 ; module MV01329 ; module MV01330 ; module MV01331 ; module MV01332 ; module MV01333 ; module MV01334 ; module MV01335 ; module MV01336 ; module MV01337 ; module MV01338 ; module MV01339 ; module MV01340 ; module MV01341 ; module MV01342)

module r2c_ij130246 where

  proved : X13 • K0246 ≈ K0246 • X13
  proved = GL.•-cancelʳ {g = X13 • K0246} {g' = K0246 • X13} {h = p (s1 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01230.proved (MV00660.proved))) (trans (cong refl R091.proved) (move-product MV00660.proved (MV01230.proved))))

module r2c_ij130247 where

  proved : X13 • K0247 ≈ K0247 • X13
  proved = GL.•-cancelʳ {g = X13 • K0247} {g' = K0247 • X13} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01231.proved (MV00661.proved))) (trans (cong refl R091.proved) (move-product MV00661.proved (MV01231.proved))))

module r2c_ij130256 where

  proved : X13 • K0256 ≈ K0256 • X13
  proved = GL.•-cancelʳ {g = X13 • K0256} {g' = K0256 • X13} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01232.proved (MV00662.proved))) (trans (cong refl R091.proved) (move-product MV00662.proved (MV01232.proved))))

module r2c_ij130257 where

  proved : X13 • K0257 ≈ K0257 • X13
  proved = GL.•-cancelʳ {g = X13 • K0257} {g' = K0257 • X13} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01233.proved (MV00663.proved))) (trans (cong refl R091.proved) (move-product MV00663.proved (MV01233.proved))))

module r2c_ij130267 where

  proved : X13 • K0267 ≈ K0267 • X13
  proved = GL.•-cancelʳ {g = X13 • K0267} {g' = K0267 • X13} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01234.proved (MV00664.proved))) (trans (cong refl R091.proved) (move-product MV00664.proved (MV01234.proved))))

module r2c_ij130456 where

  proved : X13 • K0456 ≈ K0456 • X13
  proved = GL.•-cancelʳ {g = X13 • K0456} {g' = K0456 • X13} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01235.proved (MV01236.proved))) (trans (cong refl R091.proved) (move-product MV01236.proved (MV01235.proved))))

module r2c_ij130457 where

  proved : X13 • K0457 ≈ K0457 • X13
  proved = GL.•-cancelʳ {g = X13 • K0457} {g' = K0457 • X13} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01237.proved (MV01238.proved))) (trans (cong refl R091.proved) (move-product MV01238.proved (MV01237.proved))))

module r2c_ij130467 where

  proved : X13 • K0467 ≈ K0467 • X13
  proved = GL.•-cancelʳ {g = X13 • K0467} {g' = K0467 • X13} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01239.proved (MV01240.proved))) (trans (cong refl R091.proved) (move-product MV01240.proved (MV01239.proved))))

module r2c_ij130567 where

  proved : X13 • K0567 ≈ K0567 • X13
  proved = GL.•-cancelʳ {g = X13 • K0567} {g' = K0567 • X13} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01241.proved (MV01242.proved))) (trans (cong refl R091.proved) (move-product MV01242.proved (MV01241.proved))))

module r2c_ij132456 where

  proved : X13 • K2456 ≈ K2456 • X13
  proved = GL.•-cancelʳ {g = X13 • K2456} {g' = K2456 • X13} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01243.proved (MV01244.proved))) (trans (cong refl R091.proved) (move-product MV01244.proved (MV01243.proved))))

module r2c_ij132457 where

  proved : X13 • K2457 ≈ K2457 • X13
  proved = GL.•-cancelʳ {g = X13 • K2457} {g' = K2457 • X13} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01245.proved (MV01246.proved))) (trans (cong refl R091.proved) (move-product MV01246.proved (MV01245.proved))))

module r2c_ij132467 where

  proved : X13 • K2467 ≈ K2467 • X13
  proved = GL.•-cancelʳ {g = X13 • K2467} {g' = K2467 • X13} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01247.proved (MV01248.proved))) (trans (cong refl R091.proved) (move-product MV01248.proved (MV01247.proved))))

module r2c_ij132567 where

  proved : X13 • K2567 ≈ K2567 • X13
  proved = GL.•-cancelʳ {g = X13 • K2567} {g' = K2567 • X13} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01249.proved (MV01250.proved))) (trans (cong refl R091.proved) (move-product MV01250.proved (MV01249.proved))))

module r2c_ij134567 where

  proved : X13 • K4567 ≈ K4567 • X13
  proved = GL.•-cancelʳ {g = X13 • K4567} {g' = K4567 • X13} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01251.proved (MV01252.proved))) (trans (cong refl R091.proved) (move-product MV01252.proved (MV01251.proved))))

module r2c_ij140235 where

  proved : X14 • K0235 ≈ K0235 • X14
  proved = GL.•-cancelʳ {g = X14 • K0235} {g' = K0235 • X14} {h = p (s1 • s2 • s4 • s3)}
    (trans (sym (move-product MV01253.proved (MV00656.proved))) (trans (cong refl R091.proved) (move-product MV00656.proved (MV01253.proved))))

module r2c_ij140236 where

  proved : X14 • K0236 ≈ K0236 • X14
  proved = GL.•-cancelʳ {g = X14 • K0236} {g' = K0236 • X14} {h = p (s1 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01254.proved (MV00657.proved))) (trans (cong refl R091.proved) (move-product MV00657.proved (MV01254.proved))))

module r2c_ij140237 where

  proved : X14 • K0237 ≈ K0237 • X14
  proved = GL.•-cancelʳ {g = X14 • K0237} {g' = K0237 • X14} {h = p (s1 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01255.proved (MV00658.proved))) (trans (cong refl R091.proved) (move-product MV00658.proved (MV01255.proved))))

module r2c_ij140256 where

  proved : X14 • K0256 ≈ K0256 • X14
  proved = GL.•-cancelʳ {g = X14 • K0256} {g' = K0256 • X14} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01256.proved (MV01257.proved))) (trans (cong refl R091.proved) (move-product MV01257.proved (MV01256.proved))))

module r2c_ij140257 where

  proved : X14 • K0257 ≈ K0257 • X14
  proved = GL.•-cancelʳ {g = X14 • K0257} {g' = K0257 • X14} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01258.proved (MV01259.proved))) (trans (cong refl R091.proved) (move-product MV01259.proved (MV01258.proved))))

module r2c_ij140267 where

  proved : X14 • K0267 ≈ K0267 • X14
  proved = GL.•-cancelʳ {g = X14 • K0267} {g' = K0267 • X14} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01260.proved (MV01261.proved))) (trans (cong refl R091.proved) (move-product MV01261.proved (MV01260.proved))))

module r2c_ij140356 where

  proved : X14 • K0356 ≈ K0356 • X14
  proved = GL.•-cancelʳ {g = X14 • K0356} {g' = K0356 • X14} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01262.proved (MV01263.proved))) (trans (cong refl R091.proved) (move-product MV01263.proved (MV01262.proved))))

module r2c_ij140357 where

  proved : X14 • K0357 ≈ K0357 • X14
  proved = GL.•-cancelʳ {g = X14 • K0357} {g' = K0357 • X14} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01264.proved (MV01265.proved))) (trans (cong refl R091.proved) (move-product MV01265.proved (MV01264.proved))))

module r2c_ij140367 where

  proved : X14 • K0367 ≈ K0367 • X14
  proved = GL.•-cancelʳ {g = X14 • K0367} {g' = K0367 • X14} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01266.proved (MV01267.proved))) (trans (cong refl R091.proved) (move-product MV01267.proved (MV01266.proved))))

module r2c_ij140567 where

  proved : X14 • K0567 ≈ K0567 • X14
  proved = GL.•-cancelʳ {g = X14 • K0567} {g' = K0567 • X14} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01268.proved (MV01269.proved))) (trans (cong refl R091.proved) (move-product MV01269.proved (MV01268.proved))))

module r2c_ij142356 where

  proved : X14 • K2356 ≈ K2356 • X14
  proved = GL.•-cancelʳ {g = X14 • K2356} {g' = K2356 • X14} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01270.proved (MV01271.proved))) (trans (cong refl R091.proved) (move-product MV01271.proved (MV01270.proved))))

module r2c_ij142357 where

  proved : X14 • K2357 ≈ K2357 • X14
  proved = GL.•-cancelʳ {g = X14 • K2357} {g' = K2357 • X14} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01272.proved (MV01273.proved))) (trans (cong refl R091.proved) (move-product MV01273.proved (MV01272.proved))))

module r2c_ij142367 where

  proved : X14 • K2367 ≈ K2367 • X14
  proved = GL.•-cancelʳ {g = X14 • K2367} {g' = K2367 • X14} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01274.proved (MV01275.proved))) (trans (cong refl R091.proved) (move-product MV01275.proved (MV01274.proved))))

module r2c_ij142567 where

  proved : X14 • K2567 ≈ K2567 • X14
  proved = GL.•-cancelʳ {g = X14 • K2567} {g' = K2567 • X14} {h = p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01276.proved (MV01277.proved))) (trans (cong refl R091.proved) (move-product MV01277.proved (MV01276.proved))))

module r2c_ij143567 where

  proved : X14 • K3567 ≈ K3567 • X14
  proved = GL.•-cancelʳ {g = X14 • K3567} {g' = K3567 • X14} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01278.proved (MV01279.proved))) (trans (cong refl R091.proved) (move-product MV01279.proved (MV01278.proved))))

module r2c_ij150234 where

  proved : X15 • K0234 ≈ K0234 • X15
  proved = GL.•-cancelʳ {g = X15 • K0234} {g' = K0234 • X15} {h = p (s1 • s2 • s3)}
    (trans (sym (move-product MV01280.proved (MV00655.proved))) (trans (cong refl R091.proved) (move-product MV00655.proved (MV01280.proved))))

module r2c_ij150236 where

  proved : X15 • K0236 ≈ K0236 • X15
  proved = GL.•-cancelʳ {g = X15 • K0236} {g' = K0236 • X15} {h = p (s1 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01281.proved (MV01282.proved))) (trans (cong refl R091.proved) (move-product MV01282.proved (MV01281.proved))))

module r2c_ij150237 where

  proved : X15 • K0237 ≈ K0237 • X15
  proved = GL.•-cancelʳ {g = X15 • K0237} {g' = K0237 • X15} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01283.proved (MV01284.proved))) (trans (cong refl R091.proved) (move-product MV01284.proved (MV01283.proved))))

module r2c_ij150246 where

  proved : X15 • K0246 ≈ K0246 • X15
  proved = GL.•-cancelʳ {g = X15 • K0246} {g' = K0246 • X15} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01285.proved (MV01286.proved))) (trans (cong refl R091.proved) (move-product MV01286.proved (MV01285.proved))))

module r2c_ij150247 where

  proved : X15 • K0247 ≈ K0247 • X15
  proved = GL.•-cancelʳ {g = X15 • K0247} {g' = K0247 • X15} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01287.proved (MV01288.proved))) (trans (cong refl R091.proved) (move-product MV01288.proved (MV01287.proved))))

module r2c_ij150267 where

  proved : X15 • K0267 ≈ K0267 • X15
  proved = GL.•-cancelʳ {g = X15 • K0267} {g' = K0267 • X15} {h = p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01289.proved (MV01290.proved))) (trans (cong refl R091.proved) (move-product MV01290.proved (MV01289.proved))))

module r2c_ij150346 where

  proved : X15 • K0346 ≈ K0346 • X15
  proved = GL.•-cancelʳ {g = X15 • K0346} {g' = K0346 • X15} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01291.proved (MV01292.proved))) (trans (cong refl R091.proved) (move-product MV01292.proved (MV01291.proved))))

module r2c_ij150347 where

  proved : X15 • K0347 ≈ K0347 • X15
  proved = GL.•-cancelʳ {g = X15 • K0347} {g' = K0347 • X15} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01293.proved (MV01294.proved))) (trans (cong refl R091.proved) (move-product MV01294.proved (MV01293.proved))))

module r2c_ij150367 where

  proved : X15 • K0367 ≈ K0367 • X15
  proved = GL.•-cancelʳ {g = X15 • K0367} {g' = K0367 • X15} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01295.proved (MV01296.proved))) (trans (cong refl R091.proved) (move-product MV01296.proved (MV01295.proved))))

module r2c_ij150467 where

  proved : X15 • K0467 ≈ K0467 • X15
  proved = GL.•-cancelʳ {g = X15 • K0467} {g' = K0467 • X15} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01297.proved (MV01298.proved))) (trans (cong refl R091.proved) (move-product MV01298.proved (MV01297.proved))))

module r2c_ij152346 where

  proved : X15 • K2346 ≈ K2346 • X15
  proved = GL.•-cancelʳ {g = X15 • K2346} {g' = K2346 • X15} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01299.proved (MV01300.proved))) (trans (cong refl R091.proved) (move-product MV01300.proved (MV01299.proved))))

module r2c_ij152347 where

  proved : X15 • K2347 ≈ K2347 • X15
  proved = GL.•-cancelʳ {g = X15 • K2347} {g' = K2347 • X15} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01301.proved (MV01302.proved))) (trans (cong refl R091.proved) (move-product MV01302.proved (MV01301.proved))))

module r2c_ij152367 where

  proved : X15 • K2367 ≈ K2367 • X15
  proved = GL.•-cancelʳ {g = X15 • K2367} {g' = K2367 • X15} {h = p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01303.proved (MV01304.proved))) (trans (cong refl R091.proved) (move-product MV01304.proved (MV01303.proved))))

module r2c_ij152467 where

  proved : X15 • K2467 ≈ K2467 • X15
  proved = GL.•-cancelʳ {g = X15 • K2467} {g' = K2467 • X15} {h = p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01305.proved (MV01306.proved))) (trans (cong refl R091.proved) (move-product MV01306.proved (MV01305.proved))))

module r2c_ij153467 where

  proved : X15 • K3467 ≈ K3467 • X15
  proved = GL.•-cancelʳ {g = X15 • K3467} {g' = K3467 • X15} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01307.proved (MV01308.proved))) (trans (cong refl R091.proved) (move-product MV01308.proved (MV01307.proved))))

module r2c_ij160234 where

  proved : X16 • K0234 ≈ K0234 • X16
  proved = GL.•-cancelʳ {g = X16 • K0234} {g' = K0234 • X16} {h = p (s1 • s2 • s3 • s5)}
    (trans (sym (move-product MV01309.proved (MV01310.proved))) (trans (cong refl R091.proved) (move-product MV01310.proved (MV01309.proved))))

module r2c_ij160235 where

  proved : X16 • K0235 ≈ K0235 • X16
  proved = GL.•-cancelʳ {g = X16 • K0235} {g' = K0235 • X16} {h = p (s1 • s2 • s4 • s3 • s5)}
    (trans (sym (move-product MV01311.proved (MV01312.proved))) (trans (cong refl R091.proved) (move-product MV01312.proved (MV01311.proved))))

module r2c_ij160237 where

  proved : X16 • K0237 ≈ K0237 • X16
  proved = GL.•-cancelʳ {g = X16 • K0237} {g' = K0237 • X16} {h = p (s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01313.proved (MV01314.proved))) (trans (cong refl R091.proved) (move-product MV01314.proved (MV01313.proved))))

module r2c_ij160245 where

  proved : X16 • K0245 ≈ K0245 • X16
  proved = GL.•-cancelʳ {g = X16 • K0245} {g' = K0245 • X16} {h = p (s1 • s3 • s2 • s4 • s3 • s5)}
    (trans (sym (move-product MV01315.proved (MV01316.proved))) (trans (cong refl R091.proved) (move-product MV01316.proved (MV01315.proved))))

module r2c_ij160247 where

  proved : X16 • K0247 ≈ K0247 • X16
  proved = GL.•-cancelʳ {g = X16 • K0247} {g' = K0247 • X16} {h = p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01317.proved (MV01318.proved))) (trans (cong refl R091.proved) (move-product MV01318.proved (MV01317.proved))))

module r2c_ij160257 where

  proved : X16 • K0257 ≈ K0257 • X16
  proved = GL.•-cancelʳ {g = X16 • K0257} {g' = K0257 • X16} {h = p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01319.proved (MV01320.proved))) (trans (cong refl R091.proved) (move-product MV01320.proved (MV01319.proved))))

module r2c_ij160345 where

  proved : X16 • K0345 ≈ K0345 • X16
  proved = GL.•-cancelʳ {g = X16 • K0345} {g' = K0345 • X16} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s5)}
    (trans (sym (move-product MV01321.proved (MV01322.proved))) (trans (cong refl R091.proved) (move-product MV01322.proved (MV01321.proved))))

module r2c_ij160347 where

  proved : X16 • K0347 ≈ K0347 • X16
  proved = GL.•-cancelʳ {g = X16 • K0347} {g' = K0347 • X16} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01323.proved (MV01324.proved))) (trans (cong refl R091.proved) (move-product MV01324.proved (MV01323.proved))))

module r2c_ij160357 where

  proved : X16 • K0357 ≈ K0357 • X16
  proved = GL.•-cancelʳ {g = X16 • K0357} {g' = K0357 • X16} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01325.proved (MV01326.proved))) (trans (cong refl R091.proved) (move-product MV01326.proved (MV01325.proved))))

module r2c_ij160457 where

  proved : X16 • K0457 ≈ K0457 • X16
  proved = GL.•-cancelʳ {g = X16 • K0457} {g' = K0457 • X16} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01327.proved (MV01328.proved))) (trans (cong refl R091.proved) (move-product MV01328.proved (MV01327.proved))))

module r2c_ij162345 where

  proved : X16 • K2345 ≈ K2345 • X16
  proved = GL.•-cancelʳ {g = X16 • K2345} {g' = K2345 • X16} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01329.proved (MV01330.proved))) (trans (cong refl R091.proved) (move-product MV01330.proved (MV01329.proved))))

module r2c_ij162347 where

  proved : X16 • K2347 ≈ K2347 • X16
  proved = GL.•-cancelʳ {g = X16 • K2347} {g' = K2347 • X16} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01331.proved (MV01332.proved))) (trans (cong refl R091.proved) (move-product MV01332.proved (MV01331.proved))))

module r2c_ij162357 where

  proved : X16 • K2357 ≈ K2357 • X16
  proved = GL.•-cancelʳ {g = X16 • K2357} {g' = K2357 • X16} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01333.proved (MV01334.proved))) (trans (cong refl R091.proved) (move-product MV01334.proved (MV01333.proved))))

module r2c_ij162457 where

  proved : X16 • K2457 ≈ K2457 • X16
  proved = GL.•-cancelʳ {g = X16 • K2457} {g' = K2457 • X16} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01335.proved (MV01336.proved))) (trans (cong refl R091.proved) (move-product MV01336.proved (MV01335.proved))))

module r2c_ij163457 where

  proved : X16 • K3457 ≈ K3457 • X16
  proved = GL.•-cancelʳ {g = X16 • K3457} {g' = K3457 • X16} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01337.proved (MV01338.proved))) (trans (cong refl R091.proved) (move-product MV01338.proved (MV01337.proved))))

module r2c_ij170234 where

  proved : X17 • K0234 ≈ K0234 • X17
  proved = GL.•-cancelʳ {g = X17 • K0234} {g' = K0234 • X17} {h = p (s1 • s2 • s3 • s6 • s5)}
    (trans (sym (move-product MV01339.proved (MV01340.proved))) (trans (cong refl R091.proved) (move-product MV01340.proved (MV01339.proved))))

module r2c_ij170235 where

  proved : X17 • K0235 ≈ K0235 • X17
  proved = GL.•-cancelʳ {g = X17 • K0235} {g' = K0235 • X17} {h = p (s1 • s2 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01341.proved (MV01342.proved))) (trans (cong refl R091.proved) (move-product MV01342.proved (MV01341.proved))))
