{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B059 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0127 ; K0134 ; K0135 ; K0137 ; K0145 ; K0147 ; K0157 ; K0234 ; K0235 ; K0237 ; K0245 ; K0247 ; K0257 ; K0345 ; K0347 ; K0357 ; K0457 ; K1234 ; K1235 ; K1237 ; M4 ; M6 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306 ; module MV00350)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00042 ; module MV00043 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00048 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00055)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00249 ; module MV00269 ; module MV00274 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00303 ; module MV00314 ; module MV00325 ; module MV00330)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00342 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00376)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00413)

module MV02244 where

  proved : p (s3 • s5 • s4) • M4 ≈ M6 • p (s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))) Eq.refl Eq.refl

module MV02245 where

  proved : p (s3 • s5 • s4) • K0123 ≈ K0124 • p (s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))) Eq.refl Eq.refl

module MV02246 where

  proved : p (s4 • s3 • s5 • s4) • M4 ≈ M6 • p (s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))) Eq.refl Eq.refl

module MV02247 where

  proved : p (s4 • s3 • s5 • s4) • K0123 ≈ K0125 • p (s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))) Eq.refl Eq.refl

module MV02248 where

  proved : p (s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02249 where

  proved : p (s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0127 • p (s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02250 where

  proved : p (s2 • s3 • s5 • s4) • M4 ≈ M6 • p (s2 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00044.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))) Eq.refl Eq.refl

module MV02251 where

  proved : p (s2 • s3 • s5 • s4) • K0123 ≈ K0134 • p (s2 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))) Eq.refl Eq.refl

module MV02252 where

  proved : p (s2 • s4 • s3 • s5 • s4) • M4 ≈ M6 • p (s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00044.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))) Eq.refl Eq.refl

module MV02253 where

  proved : p (s2 • s4 • s3 • s5 • s4) • K0123 ≈ K0135 • p (s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))) Eq.refl Eq.refl

module MV02254 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02255 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0137 • p (s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02256 where

  proved : p (s3 • s2 • s4 • s3 • s5 • s4) • M4 ≈ M6 • p (s3 • s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV02257 where

  proved : p (s3 • s2 • s4 • s3 • s5 • s4) • K0123 ≈ K0145 • p (s3 • s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))) Eq.refl Eq.refl

module MV02258 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02259 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0147 • p (s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02260 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02261 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0157 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02262 where

  proved : p (s1 • s2 • s3 • s5 • s4) • M4 ≈ M6 • p (s1 • s2 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00044.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))) Eq.refl Eq.refl

module MV02263 where

  proved : p (s1 • s2 • s3 • s5 • s4) • K0123 ≈ K0234 • p (s1 • s2 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))) Eq.refl Eq.refl

module MV02264 where

  proved : p (s1 • s2 • s4 • s3 • s5 • s4) • M4 ≈ M6 • p (s1 • s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00044.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV02265 where

  proved : p (s1 • s2 • s4 • s3 • s5 • s4) • K0123 ≈ K0235 • p (s1 • s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))) Eq.refl Eq.refl

module MV02266 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02267 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0237 • p (s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02268 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s5 • s4) • M4 ≈ M6 • p (s1 • s3 • s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02269 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s5 • s4) • K0123 ≈ K0245 • p (s1 • s3 • s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02270 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02271 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0247 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02272 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02273 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0257 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02274 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4) • M4 ≈ M6 • p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02275 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4) • K0123 ≈ K0345 • p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02276 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02277 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0347 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02278 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV02279 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0357 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV02280 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV02281 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0457 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV02282 where

  proved : p (s0 • s1 • s2 • s3 • s5 • s4) • M4 ≈ M6 • p (s0 • s1 • s2 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00042.proved (move-compose MV00043.proved (move-compose MV00044.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV02283 where

  proved : p (s0 • s1 • s2 • s3 • s5 • s4) • K0123 ≈ K1234 • p (s0 • s1 • s2 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00325.proved (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))) Eq.refl Eq.refl

module MV02284 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s5 • s4) • M4 ≈ M6 • p (s0 • s1 • s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00042.proved (move-compose MV00043.proved (move-compose MV00044.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02285 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s5 • s4) • K0123 ≈ K1235 • p (s0 • s1 • s2 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00330.proved (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02286 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M6 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00042.proved (move-compose MV00043.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02287 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K1237 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00342.proved (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl
