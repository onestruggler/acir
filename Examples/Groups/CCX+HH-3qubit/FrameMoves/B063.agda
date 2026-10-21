{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B063 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K4567 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00331)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00337 ; module MV00343 ; module MV00349 ; module MV00355 ; module MV00362)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00369 ; module MV00375 ; module MV00382)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00445 ; module MV00449 ; module MV00451 ; module MV00454)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B010 using (module MV00459 ; module MV00464 ; module MV00466 ; module MV00469 ; module MV00471 ; module MV00475 ; module MV00477 ; module MV00481 ; module MV00486)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00492 ; module MV00497 ; module MV00499 ; module MV00502 ; module MV00504 ; module MV00508 ; module MV00510 ; module MV00514)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00516 ; module MV00520 ; module MV00522 ; module MV00527 ; module MV00529 ; module MV00533 ; module MV00538)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00544 ; module MV00550 ; module MV00556 ; module MV00560 ; module MV00562 ; module MV00565)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00570 ; module MV00572 ; module MV00575 ; module MV00577 ; module MV00581 ; module MV00586 ; module MV00588)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00591 ; module MV00593 ; module MV00597 ; module MV00599 ; module MV00603 ; module MV00609)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00613 ; module MV00615 ; module MV00618 ; module MV00620 ; module MV00623 ; module MV00625 ; module MV00629)

module MV02406 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K1257 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00522.proved (move-compose MV00575.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))) Eq.refl Eq.refl

module MV02407 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K1256 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00516.proved (move-compose MV00570.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))) Eq.refl Eq.refl

module MV02408 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K1247 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00510.proved (move-compose MV00565.proved (move-compose MV00577.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))) Eq.refl Eq.refl

module MV02409 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K1246 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00504.proved (move-compose MV00560.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))) Eq.refl Eq.refl

module MV02410 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K1245 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))) Eq.refl Eq.refl

module MV02411 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K1237 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00477.proved (move-compose MV00510.proved (move-compose MV00565.proved (move-compose MV00577.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))) Eq.refl Eq.refl

module MV02412 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K1236 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00471.proved (move-compose MV00504.proved (move-compose MV00560.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))) Eq.refl Eq.refl

module MV02413 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K1235 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00466.proved (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))))) Eq.refl Eq.refl

module MV02414 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K1234 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00451.proved (move-compose MV00466.proved (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))))) Eq.refl Eq.refl

module MV02415 where

  proved : p (s0 • s1 • s2 • s3) • K4567 ≈ K0567 • p (s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00550.proved (move-compose MV00603.proved (move-compose MV00623.proved (MV00629.proved)))) Eq.refl Eq.refl

module MV02416 where

  proved : p (s0 • s1 • s2 • s4 • s3) • K4567 ≈ K0467 • p (s0 • s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00544.proved (move-compose MV00597.proved (move-compose MV00618.proved (move-compose MV00625.proved (MV00629.proved))))) Eq.refl Eq.refl

module MV02417 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3) • K4567 ≈ K0457 • p (s0 • s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00538.proved (move-compose MV00591.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))) Eq.refl Eq.refl

module MV02418 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0456 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00533.proved (move-compose MV00586.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))) Eq.refl Eq.refl

module MV02419 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3) • K4567 ≈ K0367 • p (s0 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00527.proved (move-compose MV00581.proved (move-compose MV00599.proved (move-compose MV00618.proved (move-compose MV00625.proved (MV00629.proved)))))) Eq.refl Eq.refl

module MV02420 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K0357 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00520.proved (move-compose MV00575.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))) Eq.refl Eq.refl

module MV02421 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0356 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00514.proved (move-compose MV00570.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))) Eq.refl Eq.refl

module MV02422 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K0347 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00508.proved (move-compose MV00565.proved (move-compose MV00577.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))) Eq.refl Eq.refl

module MV02423 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0346 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00502.proved (move-compose MV00560.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))) Eq.refl Eq.refl

module MV02424 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0345 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00497.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))) Eq.refl Eq.refl

module MV02425 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • K4567 ≈ K0267 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00492.proved (move-compose MV00529.proved (move-compose MV00581.proved (move-compose MV00599.proved (move-compose MV00618.proved (move-compose MV00625.proved (MV00629.proved))))))) Eq.refl Eq.refl

module MV02426 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K0257 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00486.proved (move-compose MV00522.proved (move-compose MV00575.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))) Eq.refl Eq.refl

module MV02427 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0256 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00481.proved (move-compose MV00516.proved (move-compose MV00570.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))) Eq.refl Eq.refl

module MV02428 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K0247 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00475.proved (move-compose MV00510.proved (move-compose MV00565.proved (move-compose MV00577.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))) Eq.refl Eq.refl

module MV02429 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0246 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00469.proved (move-compose MV00504.proved (move-compose MV00560.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))) Eq.refl Eq.refl

module MV02430 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0245 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00464.proved (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))))) Eq.refl Eq.refl

module MV02431 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K0237 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00459.proved (move-compose MV00477.proved (move-compose MV00510.proved (move-compose MV00565.proved (move-compose MV00577.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))) Eq.refl Eq.refl

module MV02432 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0236 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00454.proved (move-compose MV00471.proved (move-compose MV00504.proved (move-compose MV00560.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))))) Eq.refl Eq.refl

module MV02433 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0235 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00449.proved (move-compose MV00466.proved (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))))) Eq.refl Eq.refl

module MV02434 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0234 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00445.proved (move-compose MV00451.proved (move-compose MV00466.proved (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))))))) Eq.refl Eq.refl

module MV02435 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • K4567 ≈ K0167 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00382.proved (move-compose MV00492.proved (move-compose MV00529.proved (move-compose MV00581.proved (move-compose MV00599.proved (move-compose MV00618.proved (move-compose MV00625.proved (MV00629.proved)))))))) Eq.refl Eq.refl

module MV02436 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K0157 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00375.proved (move-compose MV00486.proved (move-compose MV00522.proved (move-compose MV00575.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))) Eq.refl Eq.refl

module MV02437 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0156 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00369.proved (move-compose MV00481.proved (move-compose MV00516.proved (move-compose MV00570.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))) Eq.refl Eq.refl

module MV02438 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K0147 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00362.proved (move-compose MV00475.proved (move-compose MV00510.proved (move-compose MV00565.proved (move-compose MV00577.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))) Eq.refl Eq.refl

module MV02439 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0146 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00355.proved (move-compose MV00469.proved (move-compose MV00504.proved (move-compose MV00560.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))))) Eq.refl Eq.refl

module MV02440 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0145 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00349.proved (move-compose MV00464.proved (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))))) Eq.refl Eq.refl

module MV02441 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K0137 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00343.proved (move-compose MV00459.proved (move-compose MV00477.proved (move-compose MV00510.proved (move-compose MV00565.proved (move-compose MV00577.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))))) Eq.refl Eq.refl

module MV02442 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0136 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00337.proved (move-compose MV00454.proved (move-compose MV00471.proved (move-compose MV00504.proved (move-compose MV00560.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))))))) Eq.refl Eq.refl

module MV02443 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K0135 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00331.proved (move-compose MV00449.proved (move-compose MV00466.proved (move-compose MV00499.proved (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))))))) Eq.refl Eq.refl
