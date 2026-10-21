{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B054 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0256 ; K0257 ; K0267 ; K0456 ; K0457 ; K0467 ; K0567 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1267 ; K1456 ; K1457 ; K1467 ; K1567 ; M3 ; M4 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420 ; module MV00438 ; module MV00440)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00021 ; module MV00022 ; module MV00025 ; module MV00026 ; module MV00029 ; module MV00030 ; module MV00031 ; module MV00032 ; module MV00033 ; module MV00034 ; module MV00037 ; module MV00038 ; module MV00039 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00041 ; module MV00045 ; module MV00046 ; module MV00047)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00303 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00348 ; module MV00354 ; module MV00361)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00368 ; module MV00370 ; module MV00374 ; module MV00376 ; module MV00381)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00407 ; module MV00413 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428 ; module MV00434)

module MV02063 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02064 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K0256 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02065 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02066 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0257 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02067 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02068 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0267 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02069 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02070 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0456 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02071 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV02072 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0457 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV02073 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV02074 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0467 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV02075 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))) Eq.refl Eq.refl

module MV02076 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0567 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))) Eq.refl Eq.refl

module MV02077 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s4) • M4 ≈ M3 • p (s0 • s1 • s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02078 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s4) • K0123 ≈ K1245 • p (s0 • s1 • s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00348.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02079 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02080 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K1246 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00354.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02081 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02082 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K1247 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00361.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02083 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02084 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K1256 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00368.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02085 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02086 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K1257 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00374.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02087 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02088 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K1267 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00381.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02089 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV02090 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K1456 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV02091 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV02092 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K1457 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV02093 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))) Eq.refl Eq.refl

module MV02094 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K1467 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))) Eq.refl Eq.refl

module MV02095 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))))))))) Eq.refl Eq.refl

module MV02096 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K1567 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))))))))) Eq.refl Eq.refl
