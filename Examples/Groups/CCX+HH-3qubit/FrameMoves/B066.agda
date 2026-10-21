{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B066 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X01 ; X02 ; X13 ; X14 ; X15 ; X16 ; X17 ; X24 ; X25 ; X26 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00009 ; module MV00010 ; module MV00011 ; module MV00012 ; module MV00013 ; module MV00024 ; module MV00029 ; module MV00030 ; module MV00032 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00043 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00048 ; module MV00050 ; module MV00051 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00056 ; module MV00057 ; module MV00058 ; module MV00059 ; module MV00060 ; module MV00061 ; module MV00113 ; module MV00118)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00119 ; module MV00121 ; module MV00125 ; module MV00126 ; module MV00127 ; module MV00129 ; module MV00132 ; module MV00133 ; module MV00134 ; module MV00135 ; module MV00137 ; module MV00139 ; module MV00140 ; module MV00141 ; module MV00142 ; module MV00143)

module MV02572 where

  proved : p (s2 • s3) • X13 ≈ X14 • p (s2 • s3)
  proved = by-assoc-and (move-compose MV00119.proved (MV00113.proved)) Eq.refl Eq.refl

module MV02573 where

  proved : p (s2 • s3) • M1 ≈ M1 • p (s2 • s3)
  proved = by-assoc-and (move-compose MV00009.proved (MV00010.proved)) Eq.refl Eq.refl

module MV02574 where

  proved : p (s2 • s3) • M3 ≈ M4 • p (s2 • s3)
  proved = by-assoc-and (move-compose MV00030.proved (MV00024.proved)) Eq.refl Eq.refl

module MV02575 where

  proved : p (s2 • s4 • s3) • X01 ≈ X01 • p (s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00057.proved (move-compose MV00059.proved (MV00058.proved))) Eq.refl Eq.refl

module MV02576 where

  proved : p (s2 • s4 • s3) • X13 ≈ X15 • p (s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00126.proved (move-compose MV00121.proved (MV00113.proved))) Eq.refl Eq.refl

module MV02577 where

  proved : p (s2 • s4 • s3) • M1 ≈ M1 • p (s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00011.proved (MV00010.proved))) Eq.refl Eq.refl

module MV02578 where

  proved : p (s2 • s4 • s3) • M3 ≈ M5 • p (s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00037.proved (move-compose MV00032.proved (MV00024.proved))) Eq.refl Eq.refl

module MV02579 where

  proved : p (s2 • s5 • s4 • s3) • X01 ≈ X01 • p (s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))) Eq.refl Eq.refl

module MV02580 where

  proved : p (s2 • s5 • s4 • s3) • X13 ≈ X16 • p (s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))) Eq.refl Eq.refl

module MV02581 where

  proved : p (s2 • s5 • s4 • s3) • M1 ≈ M1 • p (s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))) Eq.refl Eq.refl

module MV02582 where

  proved : p (s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))) Eq.refl Eq.refl

module MV02583 where

  proved : p (s2 • s6 • s5 • s4 • s3) • X01 ≈ X01 • p (s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))) Eq.refl Eq.refl

module MV02584 where

  proved : p (s2 • s6 • s5 • s4 • s3) • X13 ≈ X17 • p (s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))) Eq.refl Eq.refl

module MV02585 where

  proved : p (s2 • s6 • s5 • s4 • s3) • M1 ≈ M1 • p (s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))) Eq.refl Eq.refl

module MV02586 where

  proved : p (s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))) Eq.refl Eq.refl

module MV02587 where

  proved : p (s3 • s2 • s4 • s3) • X01 ≈ X01 • p (s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00059.proved (MV00058.proved)))) Eq.refl Eq.refl

module MV02588 where

  proved : p (s3 • s2 • s4 • s3) • X13 ≈ X15 • p (s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00121.proved (MV00113.proved)))) Eq.refl Eq.refl

module MV02589 where

  proved : p (s3 • s2 • s4 • s3) • M1 ≈ M1 • p (s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00011.proved (MV00010.proved)))) Eq.refl Eq.refl

module MV02590 where

  proved : p (s3 • s2 • s4 • s3) • M3 ≈ M5 • p (s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00032.proved (MV00024.proved)))) Eq.refl Eq.refl

module MV02591 where

  proved : p (s3 • s2 • s5 • s4 • s3) • X01 ≈ X01 • p (s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))) Eq.refl Eq.refl

module MV02592 where

  proved : p (s3 • s2 • s5 • s4 • s3) • X13 ≈ X16 • p (s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))) Eq.refl Eq.refl

module MV02593 where

  proved : p (s3 • s2 • s5 • s4 • s3) • M1 ≈ M1 • p (s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))) Eq.refl Eq.refl

module MV02594 where

  proved : p (s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))) Eq.refl Eq.refl

module MV02595 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X01 • p (s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))) Eq.refl Eq.refl

module MV02596 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X17 • p (s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))) Eq.refl Eq.refl

module MV02597 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M1 • p (s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))) Eq.refl Eq.refl

module MV02598 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))) Eq.refl Eq.refl

module MV02599 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X01 • p (s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))) Eq.refl Eq.refl

module MV02600 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X16 • p (s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00135.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))) Eq.refl Eq.refl

module MV02601 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M1 • p (s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))) Eq.refl Eq.refl

module MV02602 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))) Eq.refl Eq.refl

module MV02603 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X01 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))) Eq.refl Eq.refl

module MV02604 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X17 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))) Eq.refl Eq.refl

module MV02605 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M1 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))) Eq.refl Eq.refl

module MV02606 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))) Eq.refl Eq.refl

module MV02607 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X01 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))) Eq.refl Eq.refl

module MV02608 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X17 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))) Eq.refl Eq.refl

module MV02609 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M1 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))) Eq.refl Eq.refl

module MV02610 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))) Eq.refl Eq.refl

module MV02611 where

  proved : p (s1 • s2 • s3) • X01 ≈ X02 • p (s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00056.proved (move-compose MV00057.proved (MV00058.proved))) Eq.refl Eq.refl

module MV02612 where

  proved : p (s1 • s2 • s3) • X13 ≈ X24 • p (s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00118.proved (move-compose MV00119.proved (MV00113.proved))) Eq.refl Eq.refl

module MV02613 where

  proved : p (s1 • s2 • s3) • M1 ≈ M2 • p (s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00009.proved (MV00010.proved))) Eq.refl Eq.refl

module MV02614 where

  proved : p (s1 • s2 • s3) • M3 ≈ M4 • p (s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00029.proved (move-compose MV00030.proved (MV00024.proved))) Eq.refl Eq.refl

module MV02615 where

  proved : p (s1 • s2 • s4 • s3) • X01 ≈ X02 • p (s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00056.proved (move-compose MV00057.proved (move-compose MV00059.proved (MV00058.proved)))) Eq.refl Eq.refl

module MV02616 where

  proved : p (s1 • s2 • s4 • s3) • X13 ≈ X25 • p (s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00125.proved (move-compose MV00126.proved (move-compose MV00121.proved (MV00113.proved)))) Eq.refl Eq.refl

module MV02617 where

  proved : p (s1 • s2 • s4 • s3) • M1 ≈ M2 • p (s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00009.proved (move-compose MV00011.proved (MV00010.proved)))) Eq.refl Eq.refl

module MV02618 where

  proved : p (s1 • s2 • s4 • s3) • M3 ≈ M5 • p (s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00037.proved (move-compose MV00032.proved (MV00024.proved)))) Eq.refl Eq.refl

module MV02619 where

  proved : p (s1 • s2 • s5 • s4 • s3) • X01 ≈ X02 • p (s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00056.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))) Eq.refl Eq.refl

module MV02620 where

  proved : p (s1 • s2 • s5 • s4 • s3) • X13 ≈ X26 • p (s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00132.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))) Eq.refl Eq.refl

module MV02621 where

  proved : p (s1 • s2 • s5 • s4 • s3) • M1 ≈ M2 • p (s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))) Eq.refl Eq.refl

module MV02622 where

  proved : p (s1 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))) Eq.refl Eq.refl

module MV02623 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X02 • p (s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00056.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))) Eq.refl Eq.refl

module MV02624 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X27 • p (s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00139.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))) Eq.refl Eq.refl

module MV02625 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M2 • p (s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))) Eq.refl Eq.refl

module MV02626 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))) Eq.refl Eq.refl

module MV02627 where

  proved : p (s1 • s3 • s2 • s4 • s3) • X01 ≈ X02 • p (s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00059.proved (MV00058.proved))))) Eq.refl Eq.refl

module MV02628 where

  proved : p (s1 • s3 • s2 • s4 • s3) • X13 ≈ X25 • p (s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00125.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00121.proved (MV00113.proved))))) Eq.refl Eq.refl

module MV02629 where

  proved : p (s1 • s3 • s2 • s4 • s3) • M1 ≈ M2 • p (s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00011.proved (MV00010.proved))))) Eq.refl Eq.refl

module MV02630 where

  proved : p (s1 • s3 • s2 • s4 • s3) • M3 ≈ M5 • p (s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00032.proved (MV00024.proved))))) Eq.refl Eq.refl

module MV02631 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X02 • p (s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))) Eq.refl Eq.refl

module MV02632 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X26 • p (s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00132.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))) Eq.refl Eq.refl
