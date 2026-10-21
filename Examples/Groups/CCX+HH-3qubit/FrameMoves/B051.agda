{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B051 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; K4567 ; M1 ; M2 ; M4 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00288 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420 ; module MV00438 ; module MV00440 ; module MV00551 ; module MV00604 ; module MV00624)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00009 ; module MV00010 ; module MV00014 ; module MV00015 ; module MV00017 ; module MV00018 ; module MV00022 ; module MV00023 ; module MV00025 ; module MV00026 ; module MV00027 ; module MV00030 ; module MV00031 ; module MV00032 ; module MV00033 ; module MV00034 ; module MV00038 ; module MV00039)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00300 ; module MV00303 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00376 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00404 ; module MV00407 ; module MV00410 ; module MV00413 ; module MV00417 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428 ; module MV00434)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00509)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00515 ; module MV00521 ; module MV00528 ; module MV00534 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00587)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00592 ; module MV00598)

module MV01957 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV01958 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K2347 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00509.proved (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV01959 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV01960 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K2356 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00515.proved (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV01961 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV01962 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K2357 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00521.proved (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV01963 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV01964 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K2367 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00528.proved (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV01965 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV01966 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K2456 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV01967 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV01968 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K2457 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV01969 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))))))) Eq.refl Eq.refl

module MV01970 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K2467 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))))))) Eq.refl Eq.refl

module MV01971 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))))))) Eq.refl Eq.refl

module MV01972 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K2567 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))))))) Eq.refl Eq.refl

module MV01973 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV01974 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K3456 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00587.proved (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV01975 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))))))) Eq.refl Eq.refl

module MV01976 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K3457 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00592.proved (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))))))) Eq.refl Eq.refl

module MV01977 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))))))) Eq.refl Eq.refl

module MV01978 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K3467 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00598.proved (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))))))) Eq.refl Eq.refl

module MV01979 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))))))))) Eq.refl Eq.refl

module MV01980 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K3567 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))))))))) Eq.refl Eq.refl

module MV01981 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M1 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00015.proved (move-compose MV00014.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))))))))) Eq.refl Eq.refl

module MV01982 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K4567 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))))))))) Eq.refl Eq.refl

module MV01983 where

  proved : p (s2 • s4 • s3) • M4 ≈ M2 • p (s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00025.proved (MV00031.proved))) Eq.refl Eq.refl

module MV01984 where

  proved : p (s2 • s5 • s4 • s3) • M4 ≈ M2 • p (s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))) Eq.refl Eq.refl

module MV01985 where

  proved : p (s2 • s6 • s5 • s4 • s3) • M4 ≈ M2 • p (s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))) Eq.refl Eq.refl

module MV01986 where

  proved : p (s3 • s2 • s4 • s3) • M4 ≈ M2 • p (s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00025.proved (MV00031.proved)))) Eq.refl Eq.refl

module MV01987 where

  proved : p (s3 • s2 • s5 • s4 • s3) • M4 ≈ M2 • p (s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))) Eq.refl Eq.refl

module MV01988 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M2 • p (s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))) Eq.refl Eq.refl
