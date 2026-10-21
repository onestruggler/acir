{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B058 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0467 ; K1234 ; K1236 ; K1237 ; K1246 ; K1247 ; K1267 ; K1346 ; K1347 ; K1367 ; K1467 ; K2346 ; K2347 ; K2367 ; K2467 ; K3467 ; M4 ; M5 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00288 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00032 ; module MV00035 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00041 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00047 ; module MV00048 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00055)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00249 ; module MV00259 ; module MV00269 ; module MV00280 ; module MV00282 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00303 ; module MV00325)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00336 ; module MV00342 ; module MV00354 ; module MV00356 ; module MV00361 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00381 ; module MV00392 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00417)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00434)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00503 ; module MV00509)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00528)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00598)

module MV02211 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M5 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))) Eq.refl Eq.refl

module MV02212 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0467 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))) Eq.refl Eq.refl

module MV02213 where

  proved : p (s0 • s1 • s2 • s3 • s4) • M4 ≈ M5 • p (s0 • s1 • s2 • s3 • s4)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00036.proved (move-compose MV00037.proved (move-compose MV00038.proved (MV00032.proved))))) Eq.refl Eq.refl

module MV02214 where

  proved : p (s0 • s1 • s2 • s3 • s4) • K0123 ≈ K1234 • p (s0 • s1 • s2 • s3 • s4)
  proved = by-assoc-and (move-compose MV00325.proved (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (MV00246.proved))))) Eq.refl Eq.refl

module MV02215 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00036.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02216 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K1236 • p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00336.proved (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02217 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00036.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02218 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K1237 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00342.proved (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02219 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02220 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K1246 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00354.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02221 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02222 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K1247 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00361.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02223 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M5 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV02224 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1267 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00381.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV02225 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02226 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K1346 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02227 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02228 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K1347 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02229 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M5 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))) Eq.refl Eq.refl

module MV02230 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1367 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))) Eq.refl Eq.refl

module MV02231 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M5 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))))))) Eq.refl Eq.refl

module MV02232 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1467 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))))))) Eq.refl Eq.refl

module MV02233 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00035.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02234 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K2346 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00503.proved (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02235 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00035.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV02236 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K2347 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00509.proved (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV02237 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M5 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00035.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))))))) Eq.refl Eq.refl

module MV02238 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K2367 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00528.proved (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))))))) Eq.refl Eq.refl

module MV02239 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M5 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00035.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))))) Eq.refl Eq.refl

module MV02240 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K2467 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))))) Eq.refl Eq.refl

module MV02241 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M5 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00035.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))))))))) Eq.refl Eq.refl

module MV02242 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K3467 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00598.proved (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))))))))) Eq.refl Eq.refl

module MV02243 where

  proved : p (s5 • s4) • K0123 ≈ K0123 • p (s5 • s4)
  proved = by-assoc-and (move-compose MV00247.proved (MV00246.proved)) Eq.refl Eq.refl
