{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.TransportCases.r2c_B03 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0236 ; K0245 ; K0246 ; K0256 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2356 ; K2456 ; K3456 ; K3467 ; K3567 ; K4567 ; X17 ; X23 ; X24 ; X25 ; X26 ; _•_ ; _≈_ ; cong ; module GL ; move-product ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; sym ; trans)
open K
import Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 as R091
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 using (module MV00645 ; module MV00646 ; module MV00647 ; module MV00648 ; module MV00649 ; module MV00650 ; module MV00651 ; module MV00652 ; module MV00653 ; module MV00654)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B035 using (module MV01343 ; module MV01344 ; module MV01345 ; module MV01346 ; module MV01347 ; module MV01348 ; module MV01349 ; module MV01350 ; module MV01351 ; module MV01352 ; module MV01353 ; module MV01354 ; module MV01355 ; module MV01356 ; module MV01357 ; module MV01358)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B036 using (module MV01359 ; module MV01360 ; module MV01361 ; module MV01362 ; module MV01363 ; module MV01364 ; module MV01365 ; module MV01366 ; module MV01367 ; module MV01368 ; module MV01369 ; module MV01370 ; module MV01371 ; module MV01372 ; module MV01373 ; module MV01374 ; module MV01375 ; module MV01376 ; module MV01377 ; module MV01378 ; module MV01379 ; module MV01380 ; module MV01381 ; module MV01382 ; module MV01383 ; module MV01384 ; module MV01385 ; module MV01386 ; module MV01387 ; module MV01388 ; module MV01389 ; module MV01390)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B037 using (module MV01391 ; module MV01392 ; module MV01393 ; module MV01394 ; module MV01395 ; module MV01396 ; module MV01397 ; module MV01398 ; module MV01399 ; module MV01400 ; module MV01401 ; module MV01402 ; module MV01403 ; module MV01404 ; module MV01405 ; module MV01406 ; module MV01407 ; module MV01408 ; module MV01409 ; module MV01410 ; module MV01411 ; module MV01412 ; module MV01413 ; module MV01414 ; module MV01415 ; module MV01416 ; module MV01417 ; module MV01418 ; module MV01419 ; module MV01420 ; module MV01421 ; module MV01422 ; module MV01423 ; module MV01424 ; module MV01425 ; module MV01426)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B038 using (module MV01427 ; module MV01428 ; module MV01429 ; module MV01430 ; module MV01431 ; module MV01432 ; module MV01433 ; module MV01434 ; module MV01435 ; module MV01436 ; module MV01437 ; module MV01438 ; module MV01439 ; module MV01440 ; module MV01441 ; module MV01442 ; module MV01443 ; module MV01444 ; module MV01445 ; module MV01446 ; module MV01447 ; module MV01448 ; module MV01449 ; module MV01450 ; module MV01451 ; module MV01452 ; module MV01453 ; module MV01454)

module r2c_ij170236 where

  proved : X17 • K0236 ≈ K0236 • X17
  proved = GL.•-cancelʳ {g = X17 • K0236} {g' = K0236 • X17} {h = p (s1 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01343.proved (MV01344.proved))) (trans (cong refl R091.proved) (move-product MV01344.proved (MV01343.proved))))

module r2c_ij170245 where

  proved : X17 • K0245 ≈ K0245 • X17
  proved = GL.•-cancelʳ {g = X17 • K0245} {g' = K0245 • X17} {h = p (s1 • s3 • s2 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01345.proved (MV01346.proved))) (trans (cong refl R091.proved) (move-product MV01346.proved (MV01345.proved))))

module r2c_ij170246 where

  proved : X17 • K0246 ≈ K0246 • X17
  proved = GL.•-cancelʳ {g = X17 • K0246} {g' = K0246 • X17} {h = p (s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01347.proved (MV01348.proved))) (trans (cong refl R091.proved) (move-product MV01348.proved (MV01347.proved))))

module r2c_ij170256 where

  proved : X17 • K0256 ≈ K0256 • X17
  proved = GL.•-cancelʳ {g = X17 • K0256} {g' = K0256 • X17} {h = p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01349.proved (MV01350.proved))) (trans (cong refl R091.proved) (move-product MV01350.proved (MV01349.proved))))

module r2c_ij170345 where

  proved : X17 • K0345 ≈ K0345 • X17
  proved = GL.•-cancelʳ {g = X17 • K0345} {g' = K0345 • X17} {h = p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01351.proved (MV01352.proved))) (trans (cong refl R091.proved) (move-product MV01352.proved (MV01351.proved))))

module r2c_ij170346 where

  proved : X17 • K0346 ≈ K0346 • X17
  proved = GL.•-cancelʳ {g = X17 • K0346} {g' = K0346 • X17} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01353.proved (MV01354.proved))) (trans (cong refl R091.proved) (move-product MV01354.proved (MV01353.proved))))

module r2c_ij170356 where

  proved : X17 • K0356 ≈ K0356 • X17
  proved = GL.•-cancelʳ {g = X17 • K0356} {g' = K0356 • X17} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01355.proved (MV01356.proved))) (trans (cong refl R091.proved) (move-product MV01356.proved (MV01355.proved))))

module r2c_ij170456 where

  proved : X17 • K0456 ≈ K0456 • X17
  proved = GL.•-cancelʳ {g = X17 • K0456} {g' = K0456 • X17} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01357.proved (MV01358.proved))) (trans (cong refl R091.proved) (move-product MV01358.proved (MV01357.proved))))

module r2c_ij172345 where

  proved : X17 • K2345 ≈ K2345 • X17
  proved = GL.•-cancelʳ {g = X17 • K2345} {g' = K2345 • X17} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01359.proved (MV01360.proved))) (trans (cong refl R091.proved) (move-product MV01360.proved (MV01359.proved))))

module r2c_ij172346 where

  proved : X17 • K2346 ≈ K2346 • X17
  proved = GL.•-cancelʳ {g = X17 • K2346} {g' = K2346 • X17} {h = p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01361.proved (MV01362.proved))) (trans (cong refl R091.proved) (move-product MV01362.proved (MV01361.proved))))

module r2c_ij172356 where

  proved : X17 • K2356 ≈ K2356 • X17
  proved = GL.•-cancelʳ {g = X17 • K2356} {g' = K2356 • X17} {h = p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01363.proved (MV01364.proved))) (trans (cong refl R091.proved) (move-product MV01364.proved (MV01363.proved))))

module r2c_ij172456 where

  proved : X17 • K2456 ≈ K2456 • X17
  proved = GL.•-cancelʳ {g = X17 • K2456} {g' = K2456 • X17} {h = p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01365.proved (MV01366.proved))) (trans (cong refl R091.proved) (move-product MV01366.proved (MV01365.proved))))

module r2c_ij173456 where

  proved : X17 • K3456 ≈ K3456 • X17
  proved = GL.•-cancelʳ {g = X17 • K3456} {g' = K3456 • X17} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01367.proved (MV01368.proved))) (trans (cong refl R091.proved) (move-product MV01368.proved (MV01367.proved))))

module r2c_ij230145 where

  proved : X23 • K0145 ≈ K0145 • X23
  proved = GL.•-cancelʳ {g = X23 • K0145} {g' = K0145 • X23} {h = p (s3 • s2 • s4 • s3)}
    (trans (sym (move-product MV01369.proved (MV00649.proved))) (trans (cong refl R091.proved) (move-product MV00649.proved (MV01369.proved))))

module r2c_ij230146 where

  proved : X23 • K0146 ≈ K0146 • X23
  proved = GL.•-cancelʳ {g = X23 • K0146} {g' = K0146 • X23} {h = p (s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01370.proved (MV00650.proved))) (trans (cong refl R091.proved) (move-product MV00650.proved (MV01370.proved))))

module r2c_ij230147 where

  proved : X23 • K0147 ≈ K0147 • X23
  proved = GL.•-cancelʳ {g = X23 • K0147} {g' = K0147 • X23} {h = p (s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01371.proved (MV00651.proved))) (trans (cong refl R091.proved) (move-product MV00651.proved (MV01371.proved))))

module r2c_ij230156 where

  proved : X23 • K0156 ≈ K0156 • X23
  proved = GL.•-cancelʳ {g = X23 • K0156} {g' = K0156 • X23} {h = p (s4 • s3 • s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01372.proved (MV00652.proved))) (trans (cong refl R091.proved) (move-product MV00652.proved (MV01372.proved))))

module r2c_ij230157 where

  proved : X23 • K0157 ≈ K0157 • X23
  proved = GL.•-cancelʳ {g = X23 • K0157} {g' = K0157 • X23} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01373.proved (MV00653.proved))) (trans (cong refl R091.proved) (move-product MV00653.proved (MV01373.proved))))

module r2c_ij230167 where

  proved : X23 • K0167 ≈ K0167 • X23
  proved = GL.•-cancelʳ {g = X23 • K0167} {g' = K0167 • X23} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01374.proved (MV00654.proved))) (trans (cong refl R091.proved) (move-product MV00654.proved (MV01374.proved))))

module r2c_ij230456 where

  proved : X23 • K0456 ≈ K0456 • X23
  proved = GL.•-cancelʳ {g = X23 • K0456} {g' = K0456 • X23} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01375.proved (MV01376.proved))) (trans (cong refl R091.proved) (move-product MV01376.proved (MV01375.proved))))

module r2c_ij230457 where

  proved : X23 • K0457 ≈ K0457 • X23
  proved = GL.•-cancelʳ {g = X23 • K0457} {g' = K0457 • X23} {h = p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01377.proved (MV01378.proved))) (trans (cong refl R091.proved) (move-product MV01378.proved (MV01377.proved))))

module r2c_ij230467 where

  proved : X23 • K0467 ≈ K0467 • X23
  proved = GL.•-cancelʳ {g = X23 • K0467} {g' = K0467 • X23} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01379.proved (MV01380.proved))) (trans (cong refl R091.proved) (move-product MV01380.proved (MV01379.proved))))

module r2c_ij230567 where

  proved : X23 • K0567 ≈ K0567 • X23
  proved = GL.•-cancelʳ {g = X23 • K0567} {g' = K0567 • X23} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01381.proved (MV01382.proved))) (trans (cong refl R091.proved) (move-product MV01382.proved (MV01381.proved))))

module r2c_ij231456 where

  proved : X23 • K1456 ≈ K1456 • X23
  proved = GL.•-cancelʳ {g = X23 • K1456} {g' = K1456 • X23} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01383.proved (MV01384.proved))) (trans (cong refl R091.proved) (move-product MV01384.proved (MV01383.proved))))

module r2c_ij231457 where

  proved : X23 • K1457 ≈ K1457 • X23
  proved = GL.•-cancelʳ {g = X23 • K1457} {g' = K1457 • X23} {h = p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01385.proved (MV01386.proved))) (trans (cong refl R091.proved) (move-product MV01386.proved (MV01385.proved))))

module r2c_ij231467 where

  proved : X23 • K1467 ≈ K1467 • X23
  proved = GL.•-cancelʳ {g = X23 • K1467} {g' = K1467 • X23} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01387.proved (MV01388.proved))) (trans (cong refl R091.proved) (move-product MV01388.proved (MV01387.proved))))

module r2c_ij231567 where

  proved : X23 • K1567 ≈ K1567 • X23
  proved = GL.•-cancelʳ {g = X23 • K1567} {g' = K1567 • X23} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01389.proved (MV01390.proved))) (trans (cong refl R091.proved) (move-product MV01390.proved (MV01389.proved))))

module r2c_ij234567 where

  proved : X23 • K4567 ≈ K4567 • X23
  proved = GL.•-cancelʳ {g = X23 • K4567} {g' = K4567 • X23} {h = p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01391.proved (MV01392.proved))) (trans (cong refl R091.proved) (move-product MV01392.proved (MV01391.proved))))

module r2c_ij240135 where

  proved : X24 • K0135 ≈ K0135 • X24
  proved = GL.•-cancelʳ {g = X24 • K0135} {g' = K0135 • X24} {h = p (s2 • s4 • s3)}
    (trans (sym (move-product MV01393.proved (MV00646.proved))) (trans (cong refl R091.proved) (move-product MV00646.proved (MV01393.proved))))

module r2c_ij240136 where

  proved : X24 • K0136 ≈ K0136 • X24
  proved = GL.•-cancelʳ {g = X24 • K0136} {g' = K0136 • X24} {h = p (s2 • s5 • s4 • s3)}
    (trans (sym (move-product MV01394.proved (MV00647.proved))) (trans (cong refl R091.proved) (move-product MV00647.proved (MV01394.proved))))

module r2c_ij240137 where

  proved : X24 • K0137 ≈ K0137 • X24
  proved = GL.•-cancelʳ {g = X24 • K0137} {g' = K0137 • X24} {h = p (s2 • s6 • s5 • s4 • s3)}
    (trans (sym (move-product MV01395.proved (MV00648.proved))) (trans (cong refl R091.proved) (move-product MV00648.proved (MV01395.proved))))

module r2c_ij240156 where

  proved : X24 • K0156 ≈ K0156 • X24
  proved = GL.•-cancelʳ {g = X24 • K0156} {g' = K0156 • X24} {h = p (s4 • s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01396.proved (MV01397.proved))) (trans (cong refl R091.proved) (move-product MV01397.proved (MV01396.proved))))

module r2c_ij240157 where

  proved : X24 • K0157 ≈ K0157 • X24
  proved = GL.•-cancelʳ {g = X24 • K0157} {g' = K0157 • X24} {h = p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01398.proved (MV01399.proved))) (trans (cong refl R091.proved) (move-product MV01399.proved (MV01398.proved))))

module r2c_ij240167 where

  proved : X24 • K0167 ≈ K0167 • X24
  proved = GL.•-cancelʳ {g = X24 • K0167} {g' = K0167 • X24} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01400.proved (MV01401.proved))) (trans (cong refl R091.proved) (move-product MV01401.proved (MV01400.proved))))

module r2c_ij240356 where

  proved : X24 • K0356 ≈ K0356 • X24
  proved = GL.•-cancelʳ {g = X24 • K0356} {g' = K0356 • X24} {h = p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01402.proved (MV01403.proved))) (trans (cong refl R091.proved) (move-product MV01403.proved (MV01402.proved))))

module r2c_ij240357 where

  proved : X24 • K0357 ≈ K0357 • X24
  proved = GL.•-cancelʳ {g = X24 • K0357} {g' = K0357 • X24} {h = p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01404.proved (MV01405.proved))) (trans (cong refl R091.proved) (move-product MV01405.proved (MV01404.proved))))

module r2c_ij240367 where

  proved : X24 • K0367 ≈ K0367 • X24
  proved = GL.•-cancelʳ {g = X24 • K0367} {g' = K0367 • X24} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01406.proved (MV01407.proved))) (trans (cong refl R091.proved) (move-product MV01407.proved (MV01406.proved))))

module r2c_ij240567 where

  proved : X24 • K0567 ≈ K0567 • X24
  proved = GL.•-cancelʳ {g = X24 • K0567} {g' = K0567 • X24} {h = p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01408.proved (MV01409.proved))) (trans (cong refl R091.proved) (move-product MV01409.proved (MV01408.proved))))

module r2c_ij241356 where

  proved : X24 • K1356 ≈ K1356 • X24
  proved = GL.•-cancelʳ {g = X24 • K1356} {g' = K1356 • X24} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01410.proved (MV01411.proved))) (trans (cong refl R091.proved) (move-product MV01411.proved (MV01410.proved))))

module r2c_ij241357 where

  proved : X24 • K1357 ≈ K1357 • X24
  proved = GL.•-cancelʳ {g = X24 • K1357} {g' = K1357 • X24} {h = p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01412.proved (MV01413.proved))) (trans (cong refl R091.proved) (move-product MV01413.proved (MV01412.proved))))

module r2c_ij241367 where

  proved : X24 • K1367 ≈ K1367 • X24
  proved = GL.•-cancelʳ {g = X24 • K1367} {g' = K1367 • X24} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01414.proved (MV01415.proved))) (trans (cong refl R091.proved) (move-product MV01415.proved (MV01414.proved))))

module r2c_ij241567 where

  proved : X24 • K1567 ≈ K1567 • X24
  proved = GL.•-cancelʳ {g = X24 • K1567} {g' = K1567 • X24} {h = p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01416.proved (MV01417.proved))) (trans (cong refl R091.proved) (move-product MV01417.proved (MV01416.proved))))

module r2c_ij243567 where

  proved : X24 • K3567 ≈ K3567 • X24
  proved = GL.•-cancelʳ {g = X24 • K3567} {g' = K3567 • X24} {h = p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01418.proved (MV01419.proved))) (trans (cong refl R091.proved) (move-product MV01419.proved (MV01418.proved))))

module r2c_ij250134 where

  proved : X25 • K0134 ≈ K0134 • X25
  proved = GL.•-cancelʳ {g = X25 • K0134} {g' = K0134 • X25} {h = p (s2 • s3)}
    (trans (sym (move-product MV01420.proved (MV00645.proved))) (trans (cong refl R091.proved) (move-product MV00645.proved (MV01420.proved))))

module r2c_ij250136 where

  proved : X25 • K0136 ≈ K0136 • X25
  proved = GL.•-cancelʳ {g = X25 • K0136} {g' = K0136 • X25} {h = p (s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01421.proved (MV01422.proved))) (trans (cong refl R091.proved) (move-product MV01422.proved (MV01421.proved))))

module r2c_ij250137 where

  proved : X25 • K0137 ≈ K0137 • X25
  proved = GL.•-cancelʳ {g = X25 • K0137} {g' = K0137 • X25} {h = p (s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01423.proved (MV01424.proved))) (trans (cong refl R091.proved) (move-product MV01424.proved (MV01423.proved))))

module r2c_ij250146 where

  proved : X25 • K0146 ≈ K0146 • X25
  proved = GL.•-cancelʳ {g = X25 • K0146} {g' = K0146 • X25} {h = p (s3 • s2 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01425.proved (MV01426.proved))) (trans (cong refl R091.proved) (move-product MV01426.proved (MV01425.proved))))

module r2c_ij250147 where

  proved : X25 • K0147 ≈ K0147 • X25
  proved = GL.•-cancelʳ {g = X25 • K0147} {g' = K0147 • X25} {h = p (s3 • s2 • s6 • s5 • s4 • s3 • s5)}
    (trans (sym (move-product MV01427.proved (MV01428.proved))) (trans (cong refl R091.proved) (move-product MV01428.proved (MV01427.proved))))

module r2c_ij250167 where

  proved : X25 • K0167 ≈ K0167 • X25
  proved = GL.•-cancelʳ {g = X25 • K0167} {g' = K0167 • X25} {h = p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01429.proved (MV01430.proved))) (trans (cong refl R091.proved) (move-product MV01430.proved (MV01429.proved))))

module r2c_ij250346 where

  proved : X25 • K0346 ≈ K0346 • X25
  proved = GL.•-cancelʳ {g = X25 • K0346} {g' = K0346 • X25} {h = p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01431.proved (MV01432.proved))) (trans (cong refl R091.proved) (move-product MV01432.proved (MV01431.proved))))

module r2c_ij250347 where

  proved : X25 • K0347 ≈ K0347 • X25
  proved = GL.•-cancelʳ {g = X25 • K0347} {g' = K0347 • X25} {h = p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01433.proved (MV01434.proved))) (trans (cong refl R091.proved) (move-product MV01434.proved (MV01433.proved))))

module r2c_ij250367 where

  proved : X25 • K0367 ≈ K0367 • X25
  proved = GL.•-cancelʳ {g = X25 • K0367} {g' = K0367 • X25} {h = p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01435.proved (MV01436.proved))) (trans (cong refl R091.proved) (move-product MV01436.proved (MV01435.proved))))

module r2c_ij250467 where

  proved : X25 • K0467 ≈ K0467 • X25
  proved = GL.•-cancelʳ {g = X25 • K0467} {g' = K0467 • X25} {h = p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01437.proved (MV01438.proved))) (trans (cong refl R091.proved) (move-product MV01438.proved (MV01437.proved))))

module r2c_ij251346 where

  proved : X25 • K1346 ≈ K1346 • X25
  proved = GL.•-cancelʳ {g = X25 • K1346} {g' = K1346 • X25} {h = p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01439.proved (MV01440.proved))) (trans (cong refl R091.proved) (move-product MV01440.proved (MV01439.proved))))

module r2c_ij251347 where

  proved : X25 • K1347 ≈ K1347 • X25
  proved = GL.•-cancelʳ {g = X25 • K1347} {g' = K1347 • X25} {h = p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)}
    (trans (sym (move-product MV01441.proved (MV01442.proved))) (trans (cong refl R091.proved) (move-product MV01442.proved (MV01441.proved))))

module r2c_ij251367 where

  proved : X25 • K1367 ≈ K1367 • X25
  proved = GL.•-cancelʳ {g = X25 • K1367} {g' = K1367 • X25} {h = p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01443.proved (MV01444.proved))) (trans (cong refl R091.proved) (move-product MV01444.proved (MV01443.proved))))

module r2c_ij251467 where

  proved : X25 • K1467 ≈ K1467 • X25
  proved = GL.•-cancelʳ {g = X25 • K1467} {g' = K1467 • X25} {h = p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)}
    (trans (sym (move-product MV01445.proved (MV01446.proved))) (trans (cong refl R091.proved) (move-product MV01446.proved (MV01445.proved))))

module r2c_ij253467 where

  proved : X25 • K3467 ≈ K3467 • X25
  proved = GL.•-cancelʳ {g = X25 • K3467} {g' = K3467 • X25} {h = p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)}
    (trans (sym (move-product MV01447.proved (MV01448.proved))) (trans (cong refl R091.proved) (move-product MV01448.proved (MV01447.proved))))

module r2c_ij260134 where

  proved : X26 • K0134 ≈ K0134 • X26
  proved = GL.•-cancelʳ {g = X26 • K0134} {g' = K0134 • X26} {h = p (s2 • s3 • s5)}
    (trans (sym (move-product MV01449.proved (MV01450.proved))) (trans (cong refl R091.proved) (move-product MV01450.proved (MV01449.proved))))

module r2c_ij260135 where

  proved : X26 • K0135 ≈ K0135 • X26
  proved = GL.•-cancelʳ {g = X26 • K0135} {g' = K0135 • X26} {h = p (s2 • s4 • s3 • s5)}
    (trans (sym (move-product MV01451.proved (MV01452.proved))) (trans (cong refl R091.proved) (move-product MV01452.proved (MV01451.proved))))

module r2c_ij260137 where

  proved : X26 • K0137 ≈ K0137 • X26
  proved = GL.•-cancelʳ {g = X26 • K0137} {g' = K0137 • X26} {h = p (s2 • s6 • s5 • s4 • s3 • s6 • s5)}
    (trans (sym (move-product MV01453.proved (MV01454.proved))) (trans (cong refl R091.proved) (move-product MV01454.proved (MV01453.proved))))
