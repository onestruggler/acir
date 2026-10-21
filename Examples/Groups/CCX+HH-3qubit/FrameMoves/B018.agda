{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B018 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K3456 ; K3457 ; K3467 ; K3567 ; M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X01 ; X02 ; X03 ; X12 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008 ; module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00350 ; module MV00383 ; module MV00387 ; module MV00420 ; module MV00438 ; module MV00440 ; module MV00498 ; module MV00551 ; module MV00604)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00002 ; module MV00003 ; module MV00016 ; module MV00024 ; module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00048 ; module MV00057 ; module MV00058 ; module MV00059 ; module MV00060 ; module MV00061 ; module MV00063 ; module MV00065 ; module MV00066 ; module MV00067 ; module MV00068 ; module MV00070 ; module MV00071 ; module MV00073 ; module MV00074 ; module MV00077 ; module MV00078 ; module MV00079 ; module MV00104 ; module MV00105 ; module MV00110 ; module MV00113 ; module MV00117)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00303 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00356 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00376 ; module MV00392 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00404 ; module MV00407 ; module MV00410 ; module MV00413 ; module MV00417 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428 ; module MV00434)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00503 ; module MV00509)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00515 ; module MV00521 ; module MV00528 ; module MV00534 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B014 using (module MV00587)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00592 ; module MV00598)

module MV00691 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K1456 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))) Eq.refl Eq.refl

module MV00692 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K1457 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))))) Eq.refl Eq.refl

module MV00693 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K1467 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))))) Eq.refl Eq.refl

module MV00694 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K1567 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))))))) Eq.refl Eq.refl

module MV00695 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • K0123 ≈ K2345 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00498.proved (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (MV00245.proved)))))))) Eq.refl Eq.refl

module MV00696 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K2346 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00503.proved (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))) Eq.refl Eq.refl

module MV00697 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K2347 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00509.proved (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))) Eq.refl Eq.refl

module MV00698 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K2356 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00515.proved (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))) Eq.refl Eq.refl

module MV00699 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K2357 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00521.proved (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))))) Eq.refl Eq.refl

module MV00700 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K2367 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00528.proved (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))))) Eq.refl Eq.refl

module MV00701 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K2456 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))))) Eq.refl Eq.refl

module MV00702 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K2457 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))))) Eq.refl Eq.refl

module MV00703 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K2467 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))))))) Eq.refl Eq.refl

module MV00704 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K2567 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))))))) Eq.refl Eq.refl

module MV00705 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • K0123 ≈ K3456 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00587.proved (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))))) Eq.refl Eq.refl

module MV00706 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K3457 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00592.proved (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))))))) Eq.refl Eq.refl

module MV00707 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K3467 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00598.proved (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))))))) Eq.refl Eq.refl

module MV00708 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K3567 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved))))))))))))))) Eq.refl Eq.refl

module MV00709 where

  proved : p (s1 • s0) • X12 ≈ X01 • p (s1 • s0)
  proved = by-assoc-and (move-compose MV00063.proved (MV00104.proved)) Eq.refl Eq.refl

module MV00710 where

  proved : p (s2 • s1 • s0) • X12 ≈ X01 • p (s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00057.proved (move-compose MV00063.proved (MV00104.proved))) Eq.refl Eq.refl

module MV00711 where

  proved : p (s3 • s2 • s1 • s0) • X12 ≈ X01 • p (s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00063.proved (MV00104.proved)))) Eq.refl Eq.refl

module MV00712 where

  proved : p (s4 • s3 • s2 • s1 • s0) • X12 ≈ X01 • p (s4 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00063.proved (MV00104.proved))))) Eq.refl Eq.refl

module MV00713 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0) • X12 ≈ X01 • p (s5 • s4 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00063.proved (MV00104.proved)))))) Eq.refl Eq.refl

module MV00714 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0) • X12 ≈ X01 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00063.proved (MV00104.proved))))))) Eq.refl Eq.refl

module MV00715 where

  proved : p (s2 • s1 • s0 • s2) • X12 ≈ X02 • p (s2 • s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00071.proved (move-compose MV00070.proved (move-compose MV00110.proved (MV00105.proved)))) Eq.refl Eq.refl

module MV00716 where

  proved : p (s2 • s1 • s0 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00002.proved)))) Eq.refl Eq.refl

module MV00717 where

  proved : p (s3 • s2 • s1 • s0 • s2) • X12 ≈ X02 • p (s3 • s2 • s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00065.proved (move-compose MV00071.proved (move-compose MV00070.proved (move-compose MV00110.proved (MV00105.proved))))) Eq.refl Eq.refl

module MV00718 where

  proved : p (s3 • s2 • s1 • s0 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00002.proved))))) Eq.refl Eq.refl

module MV00719 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2) • X12 ≈ X02 • p (s4 • s3 • s2 • s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00066.proved (move-compose MV00065.proved (move-compose MV00071.proved (move-compose MV00070.proved (move-compose MV00110.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00720 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00721 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2) • X12 ≈ X02 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00067.proved (move-compose MV00066.proved (move-compose MV00065.proved (move-compose MV00071.proved (move-compose MV00070.proved (move-compose MV00110.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00722 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00723 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2) • X12 ≈ X02 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00068.proved (move-compose MV00067.proved (move-compose MV00066.proved (move-compose MV00065.proved (move-compose MV00071.proved (move-compose MV00070.proved (move-compose MV00110.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00724 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00725 where

  proved : p (s0 • s2) • X12 ≈ X03 • p (s0 • s2)
  proved = by-assoc-and (move-compose MV00110.proved (MV00105.proved)) Eq.refl Eq.refl

module MV00726 where

  proved : p (s0 • s2) • M0 ≈ M1 • p (s0 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (MV00002.proved)) Eq.refl Eq.refl

module MV00727 where

  proved : p (s1 • s0 • s2) • X12 ≈ X03 • p (s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00070.proved (move-compose MV00110.proved (MV00105.proved))) Eq.refl Eq.refl

module MV00728 where

  proved : p (s1 • s0 • s2) • M0 ≈ M2 • p (s1 • s0 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (MV00002.proved))) Eq.refl Eq.refl

module MV00729 where

  proved : p (s3 • s2 • s1 • s0 • s3 • s2) • X12 ≈ X03 • p (s3 • s2 • s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00079.proved (move-compose MV00078.proved (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00730 where

  proved : p (s3 • s2 • s1 • s0 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00731 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s3 • s2) • X12 ≈ X03 • p (s4 • s3 • s2 • s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00073.proved (move-compose MV00079.proved (move-compose MV00078.proved (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00732 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00733 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2) • X12 ≈ X03 • p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00074.proved (move-compose MV00073.proved (move-compose MV00079.proved (move-compose MV00078.proved (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00734 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl
