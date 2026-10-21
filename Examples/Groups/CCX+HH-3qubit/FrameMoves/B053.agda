{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B053 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0245 ; K0246 ; K0247 ; K1457 ; K1467 ; K1567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; M2 ; M3 ; M4 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420 ; module MV00438 ; module MV00440 ; module MV00551 ; module MV00604 ; module MV00624)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00014 ; module MV00017 ; module MV00018 ; module MV00021 ; module MV00022 ; module MV00023 ; module MV00025 ; module MV00026 ; module MV00027 ; module MV00029 ; module MV00030 ; module MV00031 ; module MV00032 ; module MV00033 ; module MV00034 ; module MV00037 ; module MV00038 ; module MV00039 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00041 ; module MV00045 ; module MV00046 ; module MV00047)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00303 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00376)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00407 ; module MV00413 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428 ; module MV00434)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00534 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00587)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00592 ; module MV00598)

module MV02026 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV02027 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K1457 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV02028 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV02029 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K1467 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV02030 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))))))) Eq.refl Eq.refl

module MV02031 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K1567 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))))))) Eq.refl Eq.refl

module MV02032 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M2 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))) Eq.refl Eq.refl

module MV02033 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K3456 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00587.proved (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))) Eq.refl Eq.refl

module MV02034 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M2 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))))))))) Eq.refl Eq.refl

module MV02035 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K3457 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00592.proved (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))))))))) Eq.refl Eq.refl

module MV02036 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M2 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))))) Eq.refl Eq.refl

module MV02037 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K3467 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00598.proved (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))))) Eq.refl Eq.refl

module MV02038 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M2 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved))))))))))))))))) Eq.refl Eq.refl

module MV02039 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K3567 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved))))))))))))))))) Eq.refl Eq.refl

module MV02040 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • M4 ≈ M2 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00029.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00041.proved (move-compose MV00047.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00040.proved (MV00032.proved)))))))))))))))))) Eq.refl Eq.refl

module MV02041 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4) • K0123 ≈ K4567 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4)
  proved = by-assoc-and (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (MV00246.proved)))))))))))))))))) Eq.refl Eq.refl

module MV02042 where

  proved : p (s4 • s3) • M4 ≈ M3 • p (s4 • s3)
  proved = by-assoc-and (move-compose MV00025.proved (MV00031.proved)) Eq.refl Eq.refl

module MV02043 where

  proved : p (s5 • s4 • s3) • M4 ≈ M3 • p (s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))) Eq.refl Eq.refl

module MV02044 where

  proved : p (s6 • s5 • s4 • s3) • M4 ≈ M3 • p (s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))) Eq.refl Eq.refl

module MV02045 where

  proved : p (s3 • s2 • s4 • s3 • s4) • M4 ≈ M3 • p (s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))) Eq.refl Eq.refl

module MV02046 where

  proved : p (s3 • s2 • s4 • s3 • s4) • K0123 ≈ K0145 • p (s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))) Eq.refl Eq.refl

module MV02047 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV02048 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K0146 • p (s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))) Eq.refl Eq.refl

module MV02049 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02050 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0147 • p (s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02051 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02052 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K0156 • p (s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02053 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02054 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0157 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02055 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02056 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0167 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02057 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s4) • M4 ≈ M3 • p (s1 • s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))) Eq.refl Eq.refl

module MV02058 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s4) • K0123 ≈ K0245 • p (s1 • s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))) Eq.refl Eq.refl

module MV02059 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s1 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV02060 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K0246 • p (s1 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV02061 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M3 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02062 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0247 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))) Eq.refl Eq.refl
