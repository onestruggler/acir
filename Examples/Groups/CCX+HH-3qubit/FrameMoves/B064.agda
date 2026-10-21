{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B064 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0134 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00292 ; module MV00320 ; module MV00350 ; module MV00383 ; module MV00387 ; module MV00388 ; module MV00440 ; module MV00498 ; module MV00551 ; module MV00555 ; module MV00604 ; module MV00624)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00007 ; module MV00014 ; module MV00015 ; module MV00021 ; module MV00022 ; module MV00023 ; module MV00028 ; module MV00029 ; module MV00030 ; module MV00031 ; module MV00035 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00039)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00042 ; module MV00043 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00047 ; module MV00049 ; module MV00050 ; module MV00051 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00055)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00250 ; module MV00270 ; module MV00275 ; module MV00281 ; module MV00287)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00303 ; module MV00309 ; module MV00314 ; module MV00326 ; module MV00331)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00337 ; module MV00343 ; module MV00356 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00376 ; module MV00392 ; module MV00393 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00399 ; module MV00404 ; module MV00405 ; module MV00407 ; module MV00410 ; module MV00411 ; module MV00417 ; module MV00418 ; module MV00423 ; module MV00424 ; module MV00425)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428 ; module MV00434 ; module MV00445 ; module MV00449 ; module MV00451 ; module MV00454)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B010 using (module MV00459 ; module MV00466 ; module MV00471 ; module MV00477)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00499 ; module MV00503 ; module MV00504 ; module MV00509 ; module MV00510)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00515 ; module MV00521 ; module MV00528 ; module MV00534 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545 ; module MV00556 ; module MV00559 ; module MV00560 ; module MV00562 ; module MV00564 ; module MV00565)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00569 ; module MV00572 ; module MV00574 ; module MV00577 ; module MV00580 ; module MV00585 ; module MV00587 ; module MV00588)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00590 ; module MV00592 ; module MV00593 ; module MV00596 ; module MV00598 ; module MV00602 ; module MV00607 ; module MV00608 ; module MV00609 ; module MV00611)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00612 ; module MV00613 ; module MV00615 ; module MV00616 ; module MV00617 ; module MV00620 ; module MV00621 ; module MV00622 ; module MV00625 ; module MV00626 ; module MV00627 ; module MV00628 ; module MV00629)

module MV02444 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0134 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00326.proved (move-compose MV00445.proved (move-compose MV00451.proved (move-compose MV00466.proved (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))))))) Eq.refl Eq.refl

module MV02445 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K0127 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00287.proved (move-compose MV00343.proved (move-compose MV00459.proved (move-compose MV00477.proved (move-compose MV00510.proved (move-compose MV00565.proved (move-compose MV00577.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))))) Eq.refl Eq.refl

module MV02446 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0126 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00281.proved (move-compose MV00337.proved (move-compose MV00454.proved (move-compose MV00471.proved (move-compose MV00504.proved (move-compose MV00560.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))))))) Eq.refl Eq.refl

module MV02447 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0125 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00275.proved (move-compose MV00331.proved (move-compose MV00449.proved (move-compose MV00466.proved (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))))))) Eq.refl Eq.refl

module MV02448 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0124 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00270.proved (move-compose MV00326.proved (move-compose MV00445.proved (move-compose MV00451.proved (move-compose MV00466.proved (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))))))))) Eq.refl Eq.refl

module MV02449 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0123 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00250.proved (move-compose MV00270.proved (move-compose MV00326.proved (move-compose MV00445.proved (move-compose MV00451.proved (move-compose MV00466.proved (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))))))))) Eq.refl Eq.refl

module MV02450 where

  proved : p (s0 • s1 • s0) • M2 ≈ M0 • p (s0 • s1 • s0)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (MV00014.proved))) Eq.refl Eq.refl

module MV02451 where

  proved : p (s0 • s1 • s2 • s1 • s0) • M3 ≈ M0 • p (s0 • s1 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00022.proved (MV00021.proved))))) Eq.refl Eq.refl

module MV02452 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • M4 ≈ M0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (MV00028.proved))))))) Eq.refl Eq.refl

module MV02453 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • M5 ≈ M0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00031.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (MV00035.proved))))))))) Eq.refl Eq.refl

module MV02454 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • M6 ≈ M0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00031.proved (move-compose MV00039.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00043.proved (MV00042.proved))))))))))) Eq.refl Eq.refl

module MV02455 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • M7 ≈ M0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00031.proved (move-compose MV00039.proved (move-compose MV00047.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (MV00049.proved))))))))))))) Eq.refl Eq.refl

module MV02456 where

  proved : p (s1 • s2 • s1) • M3 ≈ M1 • p (s1 • s2 • s1)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00023.proved (MV00022.proved))) Eq.refl Eq.refl

module MV02457 where

  proved : p (s1 • s2 • s3 • s2 • s1) • M4 ≈ M1 • p (s1 • s2 • s3 • s2 • s1)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00031.proved (move-compose MV00030.proved (MV00029.proved))))) Eq.refl Eq.refl

module MV02458 where

  proved : p (s1 • s2 • s3 • s4 • s3 • s2 • s1) • M5 ≈ M1 • p (s1 • s2 • s3 • s4 • s3 • s2 • s1)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00031.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (MV00036.proved))))))) Eq.refl Eq.refl

module MV02459 where

  proved : p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) • M6 ≈ M1 • p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00031.proved (move-compose MV00039.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (MV00043.proved))))))))) Eq.refl Eq.refl

module MV02460 where

  proved : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) • M7 ≈ M1 • p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00023.proved (move-compose MV00031.proved (move-compose MV00039.proved (move-compose MV00047.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (MV00050.proved))))))))))) Eq.refl Eq.refl

module MV02461 where

  proved : p (s2 • s3 • s2) • M4 ≈ M2 • p (s2 • s3 • s2)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00031.proved (MV00030.proved))) Eq.refl Eq.refl

module MV02462 where

  proved : p (s2 • s3 • s4 • s3 • s2) • M5 ≈ M2 • p (s2 • s3 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00031.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00037.proved))))) Eq.refl Eq.refl

module MV02463 where

  proved : p (s2 • s3 • s4 • s5 • s4 • s3 • s2) • M6 ≈ M2 • p (s2 • s3 • s4 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00031.proved (move-compose MV00039.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (MV00044.proved))))))) Eq.refl Eq.refl

module MV02464 where

  proved : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) • M7 ≈ M2 • p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00031.proved (move-compose MV00039.proved (move-compose MV00047.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (MV00051.proved))))))))) Eq.refl Eq.refl

module MV02465 where

  proved : p (s3 • s4 • s3) • M5 ≈ M3 • p (s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00031.proved (move-compose MV00039.proved (MV00038.proved))) Eq.refl Eq.refl

module MV02466 where

  proved : p (s3 • s4 • s5 • s4 • s3) • M6 ≈ M3 • p (s3 • s4 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00031.proved (move-compose MV00039.proved (move-compose MV00047.proved (move-compose MV00046.proved (MV00045.proved))))) Eq.refl Eq.refl

module MV02467 where

  proved : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • M7 ≈ M3 • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00031.proved (move-compose MV00039.proved (move-compose MV00047.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (MV00052.proved))))))) Eq.refl Eq.refl

module MV02468 where

  proved : p (s4 • s5 • s4) • M6 ≈ M4 • p (s4 • s5 • s4)
  proved = by-assoc-and (move-compose MV00039.proved (move-compose MV00047.proved (MV00046.proved))) Eq.refl Eq.refl

module MV02469 where

  proved : p (s4 • s5 • s6 • s5 • s4) • M7 ≈ M4 • p (s4 • s5 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00039.proved (move-compose MV00047.proved (move-compose MV00055.proved (move-compose MV00054.proved (MV00053.proved))))) Eq.refl Eq.refl

module MV02470 where

  proved : p (s5 • s6 • s5) • M7 ≈ M5 • p (s5 • s6 • s5)
  proved = by-assoc-and (move-compose MV00047.proved (move-compose MV00055.proved (MV00054.proved))) Eq.refl Eq.refl

module MV02471 where

  proved : p (s0 • s1 • s0) • K0345 ≈ K2345 • p (s0 • s1 • s0)
  proved = by-assoc-and (move-compose MV00555.proved (move-compose MV00498.proved (MV00387.proved))) Eq.refl Eq.refl

module MV02472 where

  proved : p (s0 • s1 • s0) • K0346 ≈ K2346 • p (s0 • s1 • s0)
  proved = by-assoc-and (move-compose MV00559.proved (move-compose MV00503.proved (MV00392.proved))) Eq.refl Eq.refl

module MV02473 where

  proved : p (s0 • s1 • s0) • K0347 ≈ K2347 • p (s0 • s1 • s0)
  proved = by-assoc-and (move-compose MV00564.proved (move-compose MV00509.proved (MV00398.proved))) Eq.refl Eq.refl

module MV02474 where

  proved : p (s0 • s1 • s0) • K0356 ≈ K2356 • p (s0 • s1 • s0)
  proved = by-assoc-and (move-compose MV00569.proved (move-compose MV00515.proved (MV00404.proved))) Eq.refl Eq.refl

module MV02475 where

  proved : p (s0 • s1 • s0) • K0357 ≈ K2357 • p (s0 • s1 • s0)
  proved = by-assoc-and (move-compose MV00574.proved (move-compose MV00521.proved (MV00410.proved))) Eq.refl Eq.refl

module MV02476 where

  proved : p (s0 • s1 • s0) • K0367 ≈ K2367 • p (s0 • s1 • s0)
  proved = by-assoc-and (move-compose MV00580.proved (move-compose MV00528.proved (MV00417.proved))) Eq.refl Eq.refl

module MV02477 where

  proved : p (s0 • s1 • s0) • K0456 ≈ K2456 • p (s0 • s1 • s0)
  proved = by-assoc-and (move-compose MV00585.proved (move-compose MV00534.proved (MV00423.proved))) Eq.refl Eq.refl

module MV02478 where

  proved : p (s0 • s1 • s0) • K0457 ≈ K2457 • p (s0 • s1 • s0)
  proved = by-assoc-and (move-compose MV00590.proved (move-compose MV00539.proved (MV00428.proved))) Eq.refl Eq.refl

module MV02479 where

  proved : p (s0 • s1 • s0) • K0467 ≈ K2467 • p (s0 • s1 • s0)
  proved = by-assoc-and (move-compose MV00596.proved (move-compose MV00545.proved (MV00434.proved))) Eq.refl Eq.refl

module MV02480 where

  proved : p (s0 • s1 • s0) • K0567 ≈ K2567 • p (s0 • s1 • s0)
  proved = by-assoc-and (move-compose MV00602.proved (move-compose MV00551.proved (MV00440.proved))) Eq.refl Eq.refl

module MV02481 where

  proved : p (s0 • s1 • s2 • s1 • s0) • K0456 ≈ K3456 • p (s0 • s1 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00607.proved (move-compose MV00608.proved (move-compose MV00587.proved (move-compose MV00534.proved (MV00423.proved))))) Eq.refl Eq.refl

module MV02482 where

  proved : p (s0 • s1 • s2 • s1 • s0) • K0457 ≈ K3457 • p (s0 • s1 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00611.proved (move-compose MV00612.proved (move-compose MV00592.proved (move-compose MV00539.proved (MV00428.proved))))) Eq.refl Eq.refl

module MV02483 where

  proved : p (s0 • s1 • s2 • s1 • s0) • K0467 ≈ K3467 • p (s0 • s1 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00616.proved (move-compose MV00617.proved (move-compose MV00598.proved (move-compose MV00545.proved (MV00434.proved))))) Eq.refl Eq.refl

module MV02484 where

  proved : p (s0 • s1 • s2 • s1 • s0) • K0567 ≈ K3567 • p (s0 • s1 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00621.proved (move-compose MV00622.proved (move-compose MV00604.proved (move-compose MV00551.proved (MV00440.proved))))) Eq.refl Eq.refl

module MV02485 where

  proved : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • K0567 ≈ K4567 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00626.proved (move-compose MV00627.proved (move-compose MV00628.proved (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00551.proved (MV00440.proved))))))) Eq.refl Eq.refl

module MV02486 where

  proved : p (s1 • s2 • s1) • K1456 ≈ K3456 • p (s1 • s2 • s1)
  proved = by-assoc-and (move-compose MV00608.proved (move-compose MV00587.proved (MV00534.proved))) Eq.refl Eq.refl

module MV02487 where

  proved : p (s1 • s2 • s1) • K1457 ≈ K3457 • p (s1 • s2 • s1)
  proved = by-assoc-and (move-compose MV00612.proved (move-compose MV00592.proved (MV00539.proved))) Eq.refl Eq.refl

module MV02488 where

  proved : p (s1 • s2 • s1) • K1467 ≈ K3467 • p (s1 • s2 • s1)
  proved = by-assoc-and (move-compose MV00617.proved (move-compose MV00598.proved (MV00545.proved))) Eq.refl Eq.refl

module MV02489 where

  proved : p (s1 • s2 • s1) • K1567 ≈ K3567 • p (s1 • s2 • s1)
  proved = by-assoc-and (move-compose MV00622.proved (move-compose MV00604.proved (MV00551.proved))) Eq.refl Eq.refl

module MV02490 where

  proved : p (s1 • s2 • s3 • s2 • s1) • K1567 ≈ K4567 • p (s1 • s2 • s3 • s2 • s1)
  proved = by-assoc-and (move-compose MV00627.proved (move-compose MV00628.proved (move-compose MV00624.proved (move-compose MV00604.proved (MV00551.proved))))) Eq.refl Eq.refl

module MV02491 where

  proved : p (s2 • s3 • s2) • K2567 ≈ K4567 • p (s2 • s3 • s2)
  proved = by-assoc-and (move-compose MV00628.proved (move-compose MV00624.proved (MV00604.proved))) Eq.refl Eq.refl

module MV02492 where

  proved : p (s1 • s2 • s1) • K0145 ≈ K0345 • p (s1 • s2 • s1)
  proved = by-assoc-and (move-compose MV00388.proved (move-compose MV00350.proved (MV00292.proved))) Eq.refl Eq.refl

module MV02493 where

  proved : p (s1 • s2 • s1) • K0146 ≈ K0346 • p (s1 • s2 • s1)
  proved = by-assoc-and (move-compose MV00393.proved (move-compose MV00356.proved (MV00297.proved))) Eq.refl Eq.refl

module MV02494 where

  proved : p (s1 • s2 • s1) • K0147 ≈ K0347 • p (s1 • s2 • s1)
  proved = by-assoc-and (move-compose MV00399.proved (move-compose MV00363.proved (MV00303.proved))) Eq.refl Eq.refl

module MV02495 where

  proved : p (s1 • s2 • s1) • K0156 ≈ K0356 • p (s1 • s2 • s1)
  proved = by-assoc-and (move-compose MV00405.proved (move-compose MV00370.proved (MV00309.proved))) Eq.refl Eq.refl

module MV02496 where

  proved : p (s1 • s2 • s1) • K0157 ≈ K0357 • p (s1 • s2 • s1)
  proved = by-assoc-and (move-compose MV00411.proved (move-compose MV00376.proved (MV00314.proved))) Eq.refl Eq.refl

module MV02497 where

  proved : p (s1 • s2 • s1) • K0167 ≈ K0367 • p (s1 • s2 • s1)
  proved = by-assoc-and (move-compose MV00418.proved (move-compose MV00383.proved (MV00320.proved))) Eq.refl Eq.refl

module MV02498 where

  proved : p (s1 • s2 • s3 • s2 • s1) • K0156 ≈ K0456 • p (s1 • s2 • s3 • s2 • s1)
  proved = by-assoc-and (move-compose MV00424.proved (move-compose MV00425.proved (move-compose MV00407.proved (move-compose MV00370.proved (MV00309.proved))))) Eq.refl Eq.refl
