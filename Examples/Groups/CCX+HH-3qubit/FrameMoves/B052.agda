{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B052 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1345 ; K1346 ; K1347 ; K1356 ; K1357 ; K1367 ; K1456 ; M2 ; M4 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00350 ; module MV00383 ; module MV00387 ; module MV00420 ; module MV00438)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00014 ; module MV00017 ; module MV00018 ; module MV00019 ; module MV00022 ; module MV00023 ; module MV00025 ; module MV00026 ; module MV00027 ; module MV00030 ; module MV00031 ; module MV00032 ; module MV00033 ; module MV00034 ; module MV00038 ; module MV00039)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00303 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00356 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00376 ; module MV00392 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00404 ; module MV00407 ; module MV00410 ; module MV00413 ; module MV00417 ; module MV00423)

module MV01989 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3) • M4 ≈ M2 • p (s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))) Eq.refl Eq.refl

module MV01990 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M2 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved))))))) Eq.refl Eq.refl

module MV01991 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M4 ≈ M2 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00019.proved (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00027.proved (move-compose MV00026.proved (move-compose MV00025.proved (MV00031.proved)))))))) Eq.refl Eq.refl

module MV01992 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s4) • M4 ≈ M2 • p (s2 • s1 • s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))) Eq.refl Eq.refl

module MV01993 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s4) • K0123 ≈ K0345 • p (s2 • s1 • s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))) Eq.refl Eq.refl

module MV01994 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV01995 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K0346 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV01996 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV01997 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0347 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV01998 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV01999 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K0356 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02000 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02001 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0357 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02002 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02003 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0367 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02004 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02005 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K0456 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02006 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02007 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0457 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02008 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV02009 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0467 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV02010 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00018.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))))) Eq.refl Eq.refl

module MV02011 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K0567 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))))) Eq.refl Eq.refl

module MV02012 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4) • M4 ≈ M2 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))) Eq.refl Eq.refl

module MV02013 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4) • K0123 ≈ K1345 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))) Eq.refl Eq.refl

module MV02014 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))) Eq.refl Eq.refl

module MV02015 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K1346 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))) Eq.refl Eq.refl

module MV02016 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02017 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K1347 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02018 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))) Eq.refl Eq.refl

module MV02019 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K1356 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))) Eq.refl Eq.refl

module MV02020 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02021 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K1357 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))) Eq.refl Eq.refl

module MV02022 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00026.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00034.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved)))))))))))) Eq.refl Eq.refl

module MV02023 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4) • K0123 ≈ K1367 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved)))))))))))) Eq.refl Eq.refl

module MV02024 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • M4 ≈ M2 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00017.proved (move-compose MV00023.proved (move-compose MV00022.proved (move-compose MV00025.proved (move-compose MV00031.proved (move-compose MV00030.proved (move-compose MV00033.proved (move-compose MV00039.proved (move-compose MV00038.proved (MV00032.proved))))))))))) Eq.refl Eq.refl

module MV02025 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4) • K0123 ≈ K1456 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4)
  proved = by-assoc-and (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00246.proved))))))))))) Eq.refl Eq.refl
