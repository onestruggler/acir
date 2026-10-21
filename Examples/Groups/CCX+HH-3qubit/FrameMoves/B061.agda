{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B061 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0145 ; K0146 ; K0156 ; K0234 ; K0235 ; K0236 ; K0245 ; K0246 ; K0256 ; K0345 ; K0346 ; K0356 ; K0456 ; K1234 ; K1235 ; K1236 ; K1245 ; K1246 ; K1256 ; K1345 ; M4 ; M7 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00276 ; module MV00292 ; module MV00350 ; module MV00387)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00048 ; module MV00049 ; module MV00050 ; module MV00051 ; module MV00052 ; module MV00053 ; module MV00054)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00249 ; module MV00259 ; module MV00269 ; module MV00274 ; module MV00280 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00309 ; module MV00325 ; module MV00330)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00336 ; module MV00348 ; module MV00354 ; module MV00356)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00368 ; module MV00370)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00407)

module MV02325 where

  proved : p (s3 • s2 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02326 where

  proved : p (s3 • s2 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0145 • p (s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02327 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02328 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0146 • p (s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02329 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02330 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0156 • p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02331 where

  proved : p (s1 • s2 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s1 • s2 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00051.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV02332 where

  proved : p (s1 • s2 • s3 • s6 • s5 • s4) • K0123 ≈ K0234 • p (s1 • s2 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))) Eq.refl Eq.refl

module MV02333 where

  proved : p (s1 • s2 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s1 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00051.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02334 where

  proved : p (s1 • s2 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0235 • p (s1 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02335 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s1 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02336 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0236 • p (s1 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02337 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02338 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0245 • p (s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02339 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02340 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0246 • p (s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02341 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02342 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0256 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02343 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02344 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0345 • p (s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02345 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02346 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0346 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02347 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02348 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0356 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02349 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV02350 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0456 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV02351 where

  proved : p (s0 • s1 • s2 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s0 • s1 • s2 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00050.proved (move-compose MV00051.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02352 where

  proved : p (s0 • s1 • s2 • s3 • s6 • s5 • s4) • K0123 ≈ K1234 • p (s0 • s1 • s2 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00325.proved (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02353 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s0 • s1 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00050.proved (move-compose MV00051.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02354 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1235 • p (s0 • s1 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00330.proved (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02355 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s0 • s1 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00050.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02356 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1236 • p (s0 • s1 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00336.proved (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02357 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02358 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1245 • p (s0 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00348.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02359 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02360 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1246 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00354.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02361 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02362 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1256 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00368.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02363 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M7 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02364 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1345 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl
