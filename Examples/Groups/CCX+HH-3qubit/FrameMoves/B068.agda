{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B068 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X01 ; X04 ; X05 ; X12 ; X13 ; X24 ; X25 ; X26 ; X27 ; X47 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00009 ; module MV00010 ; module MV00011 ; module MV00012 ; module MV00013 ; module MV00014 ; module MV00016 ; module MV00024 ; module MV00028 ; module MV00029 ; module MV00030 ; module MV00032 ; module MV00035 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00042 ; module MV00043 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00048 ; module MV00049 ; module MV00050 ; module MV00051 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00056 ; module MV00057 ; module MV00058 ; module MV00059 ; module MV00060 ; module MV00061 ; module MV00062 ; module MV00064 ; module MV00072 ; module MV00080 ; module MV00113 ; module MV00118)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00119 ; module MV00121 ; module MV00125 ; module MV00126 ; module MV00127 ; module MV00129 ; module MV00132 ; module MV00133 ; module MV00134 ; module MV00135 ; module MV00137 ; module MV00139 ; module MV00140 ; module MV00141 ; module MV00142 ; module MV00143 ; module MV00151 ; module MV00158 ; module MV00165 ; module MV00172 ; module MV00174 ; module MV00202 ; module MV00223)

module MV02677 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M4 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))) Eq.refl Eq.refl

module MV02678 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))) Eq.refl Eq.refl

module MV02679 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X04 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00072.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))))) Eq.refl Eq.refl

module MV02680 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X47 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))))) Eq.refl Eq.refl

module MV02681 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M4 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))))) Eq.refl Eq.refl

module MV02682 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))))) Eq.refl Eq.refl

module MV02683 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X04 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00072.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))))) Eq.refl Eq.refl

module MV02684 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X47 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))))) Eq.refl Eq.refl

module MV02685 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M4 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))))) Eq.refl Eq.refl

module MV02686 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))))) Eq.refl Eq.refl

module MV02687 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X05 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00080.proved (move-compose MV00072.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))))))) Eq.refl Eq.refl

module MV02688 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X57 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))))))) Eq.refl Eq.refl

module MV02689 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M5 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))))))) Eq.refl Eq.refl

module MV02690 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))))))) Eq.refl Eq.refl

module MV02691 where

  proved : p (s0 • s1 • s2 • s3) • X01 ≈ X12 • p (s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00062.proved (move-compose MV00056.proved (move-compose MV00057.proved (MV00058.proved)))) Eq.refl Eq.refl

module MV02692 where

  proved : p (s0 • s1 • s2 • s3) • X13 ≈ X24 • p (s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00151.proved (move-compose MV00118.proved (move-compose MV00119.proved (MV00113.proved)))) Eq.refl Eq.refl

module MV02693 where

  proved : p (s0 • s1 • s2 • s3) • M1 ≈ M2 • p (s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00008.proved (move-compose MV00009.proved (MV00010.proved)))) Eq.refl Eq.refl

module MV02694 where

  proved : p (s0 • s1 • s2 • s3) • M3 ≈ M4 • p (s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00028.proved (move-compose MV00029.proved (move-compose MV00030.proved (MV00024.proved)))) Eq.refl Eq.refl

module MV02695 where

  proved : p (s0 • s1 • s2 • s4 • s3) • X01 ≈ X12 • p (s0 • s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00062.proved (move-compose MV00056.proved (move-compose MV00057.proved (move-compose MV00059.proved (MV00058.proved))))) Eq.refl Eq.refl

module MV02696 where

  proved : p (s0 • s1 • s2 • s4 • s3) • X13 ≈ X25 • p (s0 • s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00158.proved (move-compose MV00125.proved (move-compose MV00126.proved (move-compose MV00121.proved (MV00113.proved))))) Eq.refl Eq.refl

module MV02697 where

  proved : p (s0 • s1 • s2 • s4 • s3) • M1 ≈ M2 • p (s0 • s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00008.proved (move-compose MV00009.proved (move-compose MV00011.proved (MV00010.proved))))) Eq.refl Eq.refl

module MV02698 where

  proved : p (s0 • s1 • s2 • s4 • s3) • M3 ≈ M5 • p (s0 • s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00036.proved (move-compose MV00037.proved (move-compose MV00032.proved (MV00024.proved))))) Eq.refl Eq.refl

module MV02699 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3) • X01 ≈ X12 • p (s0 • s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00062.proved (move-compose MV00056.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))) Eq.refl Eq.refl

module MV02700 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3) • X13 ≈ X26 • p (s0 • s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00165.proved (move-compose MV00132.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))) Eq.refl Eq.refl

module MV02701 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3) • M1 ≈ M2 • p (s0 • s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00008.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))) Eq.refl Eq.refl

module MV02702 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s0 • s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00042.proved (move-compose MV00043.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))) Eq.refl Eq.refl

module MV02703 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X12 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00062.proved (move-compose MV00056.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))) Eq.refl Eq.refl

module MV02704 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X27 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00172.proved (move-compose MV00139.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))) Eq.refl Eq.refl

module MV02705 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M2 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00008.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))) Eq.refl Eq.refl

module MV02706 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00050.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))) Eq.refl Eq.refl

module MV02707 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3) • X01 ≈ X12 • p (s0 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00062.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00059.proved (MV00058.proved)))))) Eq.refl Eq.refl

module MV02708 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3) • X13 ≈ X25 • p (s0 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00158.proved (move-compose MV00125.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00121.proved (MV00113.proved)))))) Eq.refl Eq.refl

module MV02709 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3) • M1 ≈ M2 • p (s0 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00011.proved (MV00010.proved)))))) Eq.refl Eq.refl

module MV02710 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3) • M3 ≈ M5 • p (s0 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00032.proved (MV00024.proved)))))) Eq.refl Eq.refl

module MV02711 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X12 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00062.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))) Eq.refl Eq.refl

module MV02712 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X26 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00165.proved (move-compose MV00132.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))) Eq.refl Eq.refl

module MV02713 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M2 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))) Eq.refl Eq.refl

module MV02714 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00042.proved (move-compose MV00043.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))) Eq.refl Eq.refl

module MV02715 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X12 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00062.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))) Eq.refl Eq.refl

module MV02716 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X27 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00172.proved (move-compose MV00139.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))) Eq.refl Eq.refl

module MV02717 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M2 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))) Eq.refl Eq.refl

module MV02718 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))) Eq.refl Eq.refl

module MV02719 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X12 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00062.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))) Eq.refl Eq.refl

module MV02720 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X26 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00165.proved (move-compose MV00132.proved (move-compose MV00135.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))) Eq.refl Eq.refl

module MV02721 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M2 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))) Eq.refl Eq.refl
