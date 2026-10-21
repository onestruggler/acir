{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B017 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0267 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00350 ; module MV00383 ; module MV00387 ; module MV00420 ; module MV00438)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00249 ; module MV00259 ; module MV00269 ; module MV00274 ; module MV00280 ; module MV00282 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00303 ; module MV00309 ; module MV00314 ; module MV00325 ; module MV00330)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00336 ; module MV00342 ; module MV00348 ; module MV00354 ; module MV00356 ; module MV00361 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00368 ; module MV00370 ; module MV00374 ; module MV00376 ; module MV00381 ; module MV00392 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00404 ; module MV00407 ; module MV00410 ; module MV00413 ; module MV00417)

module MV00644 where

  proved : p (s6 • s5 • s4 • s3) • K0123 ≈ K0127 • p (s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))) Eq.refl Eq.refl

module MV00645 where

  proved : p (s2 • s3) • K0123 ≈ K0134 • p (s2 • s3)
  proved = by-assoc-and (move-compose MV00249.proved (MV00245.proved)) Eq.refl Eq.refl

module MV00646 where

  proved : p (s2 • s4 • s3) • K0123 ≈ K0135 • p (s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00254.proved (move-compose MV00251.proved (MV00245.proved))) Eq.refl Eq.refl

module MV00647 where

  proved : p (s2 • s5 • s4 • s3) • K0123 ≈ K0136 • p (s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))) Eq.refl Eq.refl

module MV00648 where

  proved : p (s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0137 • p (s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))) Eq.refl Eq.refl

module MV00649 where

  proved : p (s3 • s2 • s4 • s3) • K0123 ≈ K0145 • p (s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (MV00245.proved)))) Eq.refl Eq.refl

module MV00650 where

  proved : p (s3 • s2 • s5 • s4 • s3) • K0123 ≈ K0146 • p (s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))) Eq.refl Eq.refl

module MV00651 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0147 • p (s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))) Eq.refl Eq.refl

module MV00652 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K0156 • p (s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))) Eq.refl Eq.refl

module MV00653 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0157 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))) Eq.refl Eq.refl

module MV00654 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0167 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))) Eq.refl Eq.refl

module MV00655 where

  proved : p (s1 • s2 • s3) • K0123 ≈ K0234 • p (s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00269.proved (move-compose MV00249.proved (MV00245.proved))) Eq.refl Eq.refl

module MV00656 where

  proved : p (s1 • s2 • s4 • s3) • K0123 ≈ K0235 • p (s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (MV00245.proved)))) Eq.refl Eq.refl

module MV00657 where

  proved : p (s1 • s2 • s5 • s4 • s3) • K0123 ≈ K0236 • p (s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))) Eq.refl Eq.refl

module MV00658 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0237 • p (s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))) Eq.refl Eq.refl

module MV00659 where

  proved : p (s1 • s3 • s2 • s4 • s3) • K0123 ≈ K0245 • p (s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (MV00245.proved))))) Eq.refl Eq.refl

module MV00660 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K0246 • p (s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))) Eq.refl Eq.refl

module MV00661 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0247 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))) Eq.refl Eq.refl

module MV00662 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K0256 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))) Eq.refl Eq.refl

module MV00663 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0257 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))) Eq.refl Eq.refl

module MV00664 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0267 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))) Eq.refl Eq.refl

module MV00665 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3) • K0123 ≈ K0345 • p (s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (MV00245.proved)))))) Eq.refl Eq.refl

module MV00666 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K0346 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))) Eq.refl Eq.refl

module MV00667 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0347 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))) Eq.refl Eq.refl

module MV00668 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K0356 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))) Eq.refl Eq.refl

module MV00669 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0357 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))) Eq.refl Eq.refl

module MV00670 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0367 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))) Eq.refl Eq.refl

module MV00671 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K0456 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))) Eq.refl Eq.refl

module MV00672 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0457 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))) Eq.refl Eq.refl

module MV00673 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0467 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))))) Eq.refl Eq.refl

module MV00674 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K0567 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))))) Eq.refl Eq.refl

module MV00675 where

  proved : p (s0 • s1 • s2 • s3) • K0123 ≈ K1234 • p (s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00325.proved (move-compose MV00269.proved (move-compose MV00249.proved (MV00245.proved)))) Eq.refl Eq.refl

module MV00676 where

  proved : p (s0 • s1 • s2 • s4 • s3) • K0123 ≈ K1235 • p (s0 • s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00330.proved (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (MV00245.proved))))) Eq.refl Eq.refl

module MV00677 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3) • K0123 ≈ K1236 • p (s0 • s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00336.proved (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))) Eq.refl Eq.refl

module MV00678 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K1237 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00342.proved (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))) Eq.refl Eq.refl

module MV00679 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3) • K0123 ≈ K1245 • p (s0 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00348.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (MV00245.proved)))))) Eq.refl Eq.refl

module MV00680 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K1246 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00354.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))) Eq.refl Eq.refl

module MV00681 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K1247 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00361.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))) Eq.refl Eq.refl

module MV00682 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K1256 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00368.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))) Eq.refl Eq.refl

module MV00683 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K1257 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00374.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))) Eq.refl Eq.refl

module MV00684 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K1267 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00381.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))) Eq.refl Eq.refl

module MV00685 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • K0123 ≈ K1345 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (MV00245.proved))))))) Eq.refl Eq.refl

module MV00686 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K1346 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))) Eq.refl Eq.refl

module MV00687 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K1347 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))) Eq.refl Eq.refl

module MV00688 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K1356 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))) Eq.refl Eq.refl

module MV00689 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K1357 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))) Eq.refl Eq.refl

module MV00690 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K1367 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))))) Eq.refl Eq.refl
