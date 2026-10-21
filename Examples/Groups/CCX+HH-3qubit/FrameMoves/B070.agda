{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B070 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M3 ; M4 ; M5 ; M6 ; M7 ; X01 ; X13 ; X14 ; X15 ; X23 ; X24 ; X35 ; X36 ; X37 ; X47 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00009 ; module MV00010 ; module MV00011 ; module MV00012 ; module MV00013 ; module MV00016 ; module MV00021 ; module MV00022 ; module MV00024 ; module MV00028 ; module MV00032 ; module MV00035 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00042 ; module MV00043 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00048 ; module MV00049 ; module MV00050 ; module MV00051 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00056 ; module MV00057 ; module MV00058 ; module MV00059 ; module MV00060 ; module MV00061 ; module MV00064 ; module MV00069 ; module MV00072 ; module MV00076 ; module MV00080 ; module MV00083 ; module MV00111 ; module MV00113 ; module MV00118)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00125 ; module MV00126 ; module MV00127 ; module MV00129 ; module MV00132 ; module MV00133 ; module MV00134 ; module MV00135 ; module MV00137 ; module MV00139 ; module MV00140 ; module MV00141 ; module MV00142 ; module MV00143 ; module MV00160 ; module MV00167 ; module MV00174 ; module MV00185 ; module MV00186 ; module MV00192 ; module MV00193 ; module MV00199 ; module MV00200 ; module MV00202 ; module MV00219 ; module MV00223 ; module MV00232)

module MV02761 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M4 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00028.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))))) Eq.refl Eq.refl

module MV02762 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))))) Eq.refl Eq.refl

module MV02763 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X14 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00076.proved (move-compose MV00072.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))))))) Eq.refl Eq.refl

module MV02764 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X47 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00219.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))))))) Eq.refl Eq.refl

module MV02765 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M4 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00028.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))))))) Eq.refl Eq.refl

module MV02766 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))))))) Eq.refl Eq.refl

module MV02767 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X15 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00083.proved (move-compose MV00080.proved (move-compose MV00072.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))))))) Eq.refl Eq.refl

module MV02768 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X57 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00232.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))))))) Eq.refl Eq.refl

module MV02769 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M5 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))))))) Eq.refl Eq.refl

module MV02770 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))))))) Eq.refl Eq.refl

module MV02771 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • X01 ≈ X23 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00111.proved (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00059.proved (MV00058.proved)))))))) Eq.refl Eq.refl

module MV02772 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • X13 ≈ X35 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00186.proved (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00121.proved (MV00113.proved)))))))) Eq.refl Eq.refl

module MV02773 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • M1 ≈ M3 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00011.proved (MV00010.proved)))))))) Eq.refl Eq.refl

module MV02774 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • M3 ≈ M5 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00036.proved (move-compose MV00035.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00032.proved (MV00024.proved)))))))) Eq.refl Eq.refl

module MV02775 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X23 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00111.proved (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))) Eq.refl Eq.refl

module MV02776 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X36 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00193.proved (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))) Eq.refl Eq.refl

module MV02777 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M3 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))) Eq.refl Eq.refl

module MV02778 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00042.proved (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))) Eq.refl Eq.refl

module MV02779 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X23 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00111.proved (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))))) Eq.refl Eq.refl

module MV02780 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X37 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00200.proved (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))))) Eq.refl Eq.refl

module MV02781 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M3 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))))) Eq.refl Eq.refl

module MV02782 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))))) Eq.refl Eq.refl

module MV02783 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X23 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00111.proved (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))))) Eq.refl Eq.refl

module MV02784 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X36 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00193.proved (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00135.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))))) Eq.refl Eq.refl

module MV02785 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M3 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))))) Eq.refl Eq.refl

module MV02786 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00043.proved (move-compose MV00042.proved (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))))) Eq.refl Eq.refl

module MV02787 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X23 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00111.proved (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))))) Eq.refl Eq.refl

module MV02788 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X37 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00200.proved (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))))) Eq.refl Eq.refl

module MV02789 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M3 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))))) Eq.refl Eq.refl

module MV02790 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))))) Eq.refl Eq.refl

module MV02791 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X23 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00111.proved (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))))))) Eq.refl Eq.refl

module MV02792 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X37 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00200.proved (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))))))) Eq.refl Eq.refl

module MV02793 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M3 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00022.proved (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))))))) Eq.refl Eq.refl

module MV02794 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))))))) Eq.refl Eq.refl

module MV02795 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X24 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00118.proved (move-compose MV00076.proved (move-compose MV00072.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))))) Eq.refl Eq.refl
