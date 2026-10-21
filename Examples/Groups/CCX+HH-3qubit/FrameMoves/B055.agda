{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B055 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0125 ; K0126 ; K0127 ; K0135 ; K0136 ; K0137 ; K0156 ; K0157 ; K0167 ; K0235 ; K0236 ; K0237 ; K0256 ; K0257 ; K0267 ; K2456 ; K2457 ; K2467 ; K2567 ; K4567 ; M3 ; M4 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00288 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420 ; module MV00438 ; module MV00440 ; module MV00551 ; module MV00604 ; module MV00624)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00021 ; module MV00022 ; module MV00025 ; module MV00028 ; module MV00029 ; module MV00030 ; module MV00031 ; module MV00032 ; module MV00033 ; module MV00034 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00039 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00041 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00047 ; module MV00048 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00055)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00259 ; module MV00274 ; module MV00280 ; module MV00282 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00300 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00376)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00407 ; module MV00413 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428 ; module MV00434)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00534 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545)

module MV02097 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV02098 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K2456 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV02099 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))) Eq.refl Eq.refl

module MV02100 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K2457 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))) Eq.refl Eq.refl

module MV02101 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))))))))) Eq.refl Eq.refl

module MV02102 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K2467 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))))))))) Eq.refl Eq.refl

module MV02103 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M3 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))))) Eq.refl Eq.refl

module MV02104 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K2567 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))))) Eq.refl Eq.refl

module MV02105 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • M4 ≈ M3 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00028.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00055.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))))))))))))))))))) Eq.refl Eq.refl

module MV02106 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4) • K0123 ≈ K4567 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (move-compose MV00247.proved (MV00246.proved))))))))))))))))))) Eq.refl Eq.refl

module MV02107 where

  proved : p (s4 • s3 • s4) • M4 ≈ M4 • p (s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))) Eq.refl Eq.refl

module MV02108 where

  proved : p (s4 • s3 • s4) • K0123 ≈ K0125 • p (s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))) Eq.refl Eq.refl

module MV02109 where

  proved : p (s5 • s4 • s3 • s4) • M4 ≈ M4 • p (s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))) Eq.refl Eq.refl

module MV02110 where

  proved : p (s5 • s4 • s3 • s4) • K0123 ≈ K0126 • p (s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))) Eq.refl Eq.refl

module MV02111 where

  proved : p (s6 • s5 • s4 • s3 • s4) • M4 ≈ M4 • p (s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))) Eq.refl Eq.refl

module MV02112 where

  proved : p (s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0127 • p (s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))) Eq.refl Eq.refl

module MV02113 where

  proved : p (s2 • s4 • s3 • s4) • M4 ≈ M4 • p (s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00030.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))) Eq.refl Eq.refl

module MV02114 where

  proved : p (s2 • s4 • s3 • s4) • K0123 ≈ K0135 • p (s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))) Eq.refl Eq.refl

module MV02115 where

  proved : p (s2 • s5 • s4 • s3 • s4) • M4 ≈ M4 • p (s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))) Eq.refl Eq.refl

module MV02116 where

  proved : p (s2 • s5 • s4 • s3 • s4) • K0123 ≈ K0136 • p (s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))) Eq.refl Eq.refl

module MV02117 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M4 • p (s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV02118 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0137 • p (s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))) Eq.refl Eq.refl

module MV02119 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M4 • p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02120 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0156 • p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02121 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M4 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02122 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0157 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02123 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M4 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02124 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0167 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02125 where

  proved : p (s1 • s2 • s4 • s3 • s4) • M4 ≈ M4 • p (s1 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00029.proved (move-compose MV00030.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))) Eq.refl Eq.refl

module MV02126 where

  proved : p (s1 • s2 • s4 • s3 • s4) • K0123 ≈ K0235 • p (s1 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))) Eq.refl Eq.refl

module MV02127 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M4 • p (s1 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00029.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV02128 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K0236 • p (s1 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))) Eq.refl Eq.refl

module MV02129 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M4 • p (s1 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00029.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02130 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0237 • p (s1 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02131 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M4 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00029.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02132 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0256 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02133 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M4 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00029.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02134 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0257 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02135 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M4 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00029.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02136 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K0267 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))))) Eq.refl Eq.refl
