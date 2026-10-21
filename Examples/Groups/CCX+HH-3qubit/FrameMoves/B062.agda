{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B062 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K4567 ; M4 ; M7 ; NK ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00012)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00276 ; module MV00292 ; module MV00350 ; module MV00387 ; module MV00498)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00048 ; module MV00049 ; module MV00050 ; module MV00051 ; module MV00052 ; module MV00053 ; module MV00054)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00309)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00356)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00392)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00404 ; module MV00407 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00503)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00515 ; module MV00529 ; module MV00534)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00556 ; module MV00560 ; module MV00562 ; module MV00565)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00570 ; module MV00572 ; module MV00575 ; module MV00577 ; module MV00581 ; module MV00586 ; module MV00587 ; module MV00588)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00591 ; module MV00593 ; module MV00597 ; module MV00599 ; module MV00603 ; module MV00609)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B016 using (module MV00613 ; module MV00615 ; module MV00618 ; module MV00620 ; module MV00623 ; module MV00625 ; module MV00629)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B018 using (module PE01299 ; module PE01300)

module MV02365 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02366 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1346 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02367 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV02368 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1356 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV02369 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV02370 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1456 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV02371 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02372 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K2345 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00498.proved (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02373 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV02374 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K2346 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00503.proved (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV02375 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV02376 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K2356 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00515.proved (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV02377 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))) Eq.refl Eq.refl

module MV02378 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K2456 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))) Eq.refl Eq.refl

module MV02379 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))))))) Eq.refl Eq.refl

module MV02380 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K3456 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00587.proved (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))))))) Eq.refl Eq.refl

module MV02381 where

  step0 : p (ε) • K4567 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)) PE01299.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ K4567 • p (ε)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE01300.proved) Eq.refl Eq.refl

  proved : p (ε) • K4567 ≈ K4567 • p (ε)
  proved = trans step0 (trans step1 step2)

module MV02382 where

  proved : p (s4 • s3) • K4567 ≈ K3467 • p (s4 • s3)
  proved = by-assoc-and (move-compose MV00625.proved (MV00629.proved)) Eq.refl Eq.refl

module MV02383 where

  proved : p (s5 • s4 • s3) • K4567 ≈ K3457 • p (s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))) Eq.refl Eq.refl

module MV02384 where

  proved : p (s6 • s5 • s4 • s3) • K4567 ≈ K3456 • p (s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))) Eq.refl Eq.refl

module MV02385 where

  proved : p (s2 • s3) • K4567 ≈ K2567 • p (s2 • s3)
  proved = by-assoc-and (move-compose MV00623.proved (MV00629.proved)) Eq.refl Eq.refl

module MV02386 where

  proved : p (s2 • s4 • s3) • K4567 ≈ K2467 • p (s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00618.proved (move-compose MV00625.proved (MV00629.proved))) Eq.refl Eq.refl

module MV02387 where

  proved : p (s2 • s5 • s4 • s3) • K4567 ≈ K2457 • p (s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))) Eq.refl Eq.refl

module MV02388 where

  proved : p (s2 • s6 • s5 • s4 • s3) • K4567 ≈ K2456 • p (s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))) Eq.refl Eq.refl

module MV02389 where

  proved : p (s3 • s2 • s4 • s3) • K4567 ≈ K2367 • p (s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00599.proved (move-compose MV00618.proved (move-compose MV00625.proved (MV00629.proved)))) Eq.refl Eq.refl

module MV02390 where

  proved : p (s3 • s2 • s5 • s4 • s3) • K4567 ≈ K2357 • p (s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))) Eq.refl Eq.refl

module MV02391 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K2356 • p (s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))) Eq.refl Eq.refl

module MV02392 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K2347 • p (s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00577.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))) Eq.refl Eq.refl

module MV02393 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K2346 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))) Eq.refl Eq.refl

module MV02394 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K2345 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))) Eq.refl Eq.refl

module MV02395 where

  proved : p (s1 • s2 • s3) • K4567 ≈ K1567 • p (s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00603.proved (move-compose MV00623.proved (MV00629.proved))) Eq.refl Eq.refl

module MV02396 where

  proved : p (s1 • s2 • s4 • s3) • K4567 ≈ K1467 • p (s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00597.proved (move-compose MV00618.proved (move-compose MV00625.proved (MV00629.proved)))) Eq.refl Eq.refl

module MV02397 where

  proved : p (s1 • s2 • s5 • s4 • s3) • K4567 ≈ K1457 • p (s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00591.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))) Eq.refl Eq.refl

module MV02398 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K1456 • p (s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00586.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))) Eq.refl Eq.refl

module MV02399 where

  proved : p (s1 • s3 • s2 • s4 • s3) • K4567 ≈ K1367 • p (s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00581.proved (move-compose MV00599.proved (move-compose MV00618.proved (move-compose MV00625.proved (MV00629.proved))))) Eq.refl Eq.refl

module MV02400 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K1357 • p (s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00575.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))) Eq.refl Eq.refl

module MV02401 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K1356 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00570.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))) Eq.refl Eq.refl

module MV02402 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • K4567 ≈ K1347 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00565.proved (move-compose MV00577.proved (move-compose MV00593.proved (move-compose MV00613.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))) Eq.refl Eq.refl

module MV02403 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K1346 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00560.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved)))))))) Eq.refl Eq.refl

module MV02404 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K4567 ≈ K1345 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00556.proved (move-compose MV00562.proved (move-compose MV00572.proved (move-compose MV00588.proved (move-compose MV00609.proved (move-compose MV00615.proved (move-compose MV00620.proved (move-compose MV00625.proved (MV00629.proved))))))))) Eq.refl Eq.refl

module MV02405 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3) • K4567 ≈ K1267 • p (s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00529.proved (move-compose MV00581.proved (move-compose MV00599.proved (move-compose MV00618.proved (move-compose MV00625.proved (MV00629.proved)))))) Eq.refl Eq.refl
