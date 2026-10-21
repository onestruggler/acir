{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B067 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M2 ; M3 ; M5 ; M6 ; M7 ; X01 ; X02 ; X03 ; X04 ; X13 ; X26 ; X27 ; X35 ; X36 ; X37 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00009 ; module MV00010 ; module MV00011 ; module MV00012 ; module MV00013 ; module MV00016 ; module MV00024 ; module MV00032 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00043 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00048 ; module MV00050 ; module MV00051 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00056 ; module MV00057 ; module MV00058 ; module MV00059 ; module MV00060 ; module MV00061 ; module MV00064 ; module MV00072 ; module MV00113)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00125 ; module MV00126 ; module MV00127 ; module MV00129 ; module MV00132 ; module MV00133 ; module MV00134 ; module MV00135 ; module MV00137 ; module MV00139 ; module MV00140 ; module MV00141 ; module MV00142 ; module MV00143 ; module MV00160 ; module MV00167 ; module MV00174 ; module MV00195)

module MV02633 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M2 • p (s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))) Eq.refl Eq.refl

module MV02634 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))) Eq.refl Eq.refl

module MV02635 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X02 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))) Eq.refl Eq.refl

module MV02636 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X27 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00139.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))) Eq.refl Eq.refl

module MV02637 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M2 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))) Eq.refl Eq.refl

module MV02638 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))) Eq.refl Eq.refl

module MV02639 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X02 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))) Eq.refl Eq.refl

module MV02640 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X26 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00132.proved (move-compose MV00135.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))) Eq.refl Eq.refl

module MV02641 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M2 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))) Eq.refl Eq.refl

module MV02642 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))) Eq.refl Eq.refl

module MV02643 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X02 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))) Eq.refl Eq.refl

module MV02644 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X27 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00139.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))) Eq.refl Eq.refl

module MV02645 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M2 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))) Eq.refl Eq.refl

module MV02646 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))) Eq.refl Eq.refl

module MV02647 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X02 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00056.proved (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))) Eq.refl Eq.refl

module MV02648 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X27 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00139.proved (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))) Eq.refl Eq.refl

module MV02649 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M2 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))) Eq.refl Eq.refl

module MV02650 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))) Eq.refl Eq.refl

module MV02651 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3) • X01 ≈ X03 • p (s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00059.proved (MV00058.proved)))))) Eq.refl Eq.refl

module MV02652 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3) • X13 ≈ X35 • p (s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00121.proved (MV00113.proved)))))) Eq.refl Eq.refl

module MV02653 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3) • M1 ≈ M3 • p (s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00011.proved (MV00010.proved)))))) Eq.refl Eq.refl

module MV02654 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3) • M3 ≈ M5 • p (s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00032.proved (MV00024.proved)))))) Eq.refl Eq.refl

module MV02655 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X03 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))) Eq.refl Eq.refl

module MV02656 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X36 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))) Eq.refl Eq.refl

module MV02657 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M3 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))) Eq.refl Eq.refl

module MV02658 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))) Eq.refl Eq.refl

module MV02659 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X03 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))) Eq.refl Eq.refl

module MV02660 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X37 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))) Eq.refl Eq.refl

module MV02661 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M3 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))) Eq.refl Eq.refl

module MV02662 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))) Eq.refl Eq.refl

module MV02663 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X03 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))) Eq.refl Eq.refl

module MV02664 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X36 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00135.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))) Eq.refl Eq.refl

module MV02665 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M3 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))) Eq.refl Eq.refl

module MV02666 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))) Eq.refl Eq.refl

module MV02667 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X03 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))) Eq.refl Eq.refl

module MV02668 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X37 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))) Eq.refl Eq.refl

module MV02669 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M3 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))) Eq.refl Eq.refl

module MV02670 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))) Eq.refl Eq.refl

module MV02671 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X03 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))))) Eq.refl Eq.refl

module MV02672 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X37 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))))) Eq.refl Eq.refl

module MV02673 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M3 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))))) Eq.refl Eq.refl

module MV02674 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))))) Eq.refl Eq.refl

module MV02675 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X04 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00072.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))) Eq.refl Eq.refl

module MV02676 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X46 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00135.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))) Eq.refl Eq.refl
