{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B057 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0126 ; K0127 ; K0134 ; K0136 ; K0137 ; K0146 ; K0147 ; K0167 ; K0234 ; K0236 ; K0237 ; K0246 ; K0247 ; K0267 ; K0346 ; K0347 ; K0367 ; K2367 ; K2567 ; K3567 ; M4 ; M5 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00288 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420 ; module MV00438 ; module MV00440 ; module MV00551 ; module MV00604)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00028 ; module MV00029 ; module MV00030 ; module MV00032 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00039 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00041 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00047 ; module MV00048 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00055)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00249 ; module MV00259 ; module MV00269 ; module MV00280 ; module MV00282 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00303)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00356 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00417)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00528)

module MV02170 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K2367 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00528.proved (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))) Eq.refl Eq.refl

module MV02171 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M4 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00029.proved (move-compose MV00028.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))))))))) Eq.refl Eq.refl

module MV02172 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K2567 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))))))))) Eq.refl Eq.refl

module MV02173 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M4 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00028.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))))))) Eq.refl Eq.refl

module MV02174 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K3567 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))))))) Eq.refl Eq.refl

module MV02175 where

  proved : p (s3 • s4) • M4 ≈ M5 • p (s3 • s4)
  proved = by-assoc-and (move-compose MV00038.proved (MV00032.proved)) Eq.refl Eq.refl

module MV02176 where

  proved : p (s3 • s4) • K0123 ≈ K0124 • p (s3 • s4)
  proved = by-assoc-and (move-compose MV00245.proved (MV00246.proved)) Eq.refl Eq.refl

module MV02177 where

  proved : p (s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))) Eq.refl Eq.refl

module MV02178 where

  proved : p (s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0126 • p (s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))) Eq.refl Eq.refl

module MV02179 where

  proved : p (s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV02180 where

  proved : p (s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0127 • p (s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))) Eq.refl Eq.refl

module MV02181 where

  proved : p (s2 • s3 • s4) • M4 ≈ M5 • p (s2 • s3 • s4)
  proved = by-assoc-and (move-compose MV00037.proved (move-compose MV00038.proved (MV00032.proved))) Eq.refl Eq.refl

module MV02182 where

  proved : p (s2 • s3 • s4) • K0123 ≈ K0134 • p (s2 • s3 • s4)
  proved = by-assoc-and (move-compose MV00249.proved (move-compose MV00245.proved (MV00246.proved))) Eq.refl Eq.refl

module MV02183 where

  proved : p (s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV02184 where

  proved : p (s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0136 • p (s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))) Eq.refl Eq.refl

module MV02185 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02186 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0137 • p (s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02187 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02188 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0146 • p (s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02189 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02190 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0147 • p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02191 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M5 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02192 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0167 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02193 where

  proved : p (s1 • s2 • s3 • s4) • M4 ≈ M5 • p (s1 • s2 • s3 • s4)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00037.proved (move-compose MV00038.proved (MV00032.proved)))) Eq.refl Eq.refl

module MV02194 where

  proved : p (s1 • s2 • s3 • s4) • K0123 ≈ K0234 • p (s1 • s2 • s3 • s4)
  proved = by-assoc-and (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (MV00246.proved)))) Eq.refl Eq.refl

module MV02195 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s1 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02196 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0236 • p (s1 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02197 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02198 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0237 • p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02199 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02200 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0246 • p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02201 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02202 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0247 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02203 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M5 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV02204 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0267 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV02205 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02206 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0346 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02207 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M5 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02208 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0347 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02209 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M5 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV02210 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K0367 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl
