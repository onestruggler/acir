{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B069 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X01 ; X12 ; X13 ; X14 ; X27 ; X35 ; X36 ; X37 ; X46 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00009 ; module MV00010 ; module MV00011 ; module MV00012 ; module MV00013 ; module MV00014 ; module MV00016 ; module MV00021 ; module MV00024 ; module MV00028 ; module MV00032 ; module MV00035 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00042 ; module MV00043 ; module MV00044 ; module MV00045 ; module MV00046 ; module MV00048 ; module MV00049 ; module MV00050 ; module MV00051 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00056 ; module MV00057 ; module MV00058 ; module MV00059 ; module MV00060 ; module MV00061 ; module MV00062 ; module MV00064 ; module MV00069 ; module MV00072 ; module MV00076 ; module MV00113)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00125 ; module MV00126 ; module MV00127 ; module MV00129 ; module MV00132 ; module MV00133 ; module MV00134 ; module MV00135 ; module MV00137 ; module MV00139 ; module MV00140 ; module MV00141 ; module MV00142 ; module MV00143 ; module MV00160 ; module MV00167 ; module MV00172 ; module MV00174 ; module MV00185 ; module MV00192 ; module MV00195 ; module MV00199 ; module MV00202 ; module MV00212 ; module MV00219)

module MV02722 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00042.proved (move-compose MV00043.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))) Eq.refl Eq.refl

module MV02723 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X12 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00062.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))) Eq.refl Eq.refl

module MV02724 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X27 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00172.proved (move-compose MV00139.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))) Eq.refl Eq.refl

module MV02725 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M2 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))) Eq.refl Eq.refl

module MV02726 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))) Eq.refl Eq.refl

module MV02727 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X12 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00062.proved (move-compose MV00056.proved (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))))) Eq.refl Eq.refl

module MV02728 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X27 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00172.proved (move-compose MV00139.proved (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))))) Eq.refl Eq.refl

module MV02729 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M2 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00008.proved (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))))) Eq.refl Eq.refl

module MV02730 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00050.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))))) Eq.refl Eq.refl

module MV02731 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • X01 ≈ X13 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00059.proved (MV00058.proved))))))) Eq.refl Eq.refl

module MV02732 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • X13 ≈ X35 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00121.proved (MV00113.proved))))))) Eq.refl Eq.refl

module MV02733 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • M1 ≈ M3 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00011.proved (MV00010.proved))))))) Eq.refl Eq.refl

module MV02734 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3) • M3 ≈ M5 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00035.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00032.proved (MV00024.proved))))))) Eq.refl Eq.refl

module MV02735 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X13 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))) Eq.refl Eq.refl

module MV02736 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X36 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))) Eq.refl Eq.refl

module MV02737 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M3 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))) Eq.refl Eq.refl

module MV02738 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00042.proved (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))) Eq.refl Eq.refl

module MV02739 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X13 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))) Eq.refl Eq.refl

module MV02740 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X37 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))) Eq.refl Eq.refl

module MV02741 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M3 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))) Eq.refl Eq.refl

module MV02742 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))) Eq.refl Eq.refl

module MV02743 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X13 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))) Eq.refl Eq.refl

module MV02744 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X36 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00135.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))) Eq.refl Eq.refl

module MV02745 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M3 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))) Eq.refl Eq.refl

module MV02746 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00042.proved (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))) Eq.refl Eq.refl

module MV02747 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X13 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))))) Eq.refl Eq.refl

module MV02748 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X37 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))))) Eq.refl Eq.refl

module MV02749 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M3 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))))) Eq.refl Eq.refl

module MV02750 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))))) Eq.refl Eq.refl

module MV02751 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X13 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00069.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))))) Eq.refl Eq.refl

module MV02752 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X37 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))))) Eq.refl Eq.refl

module MV02753 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M3 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00021.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved))))))))))) Eq.refl Eq.refl

module MV02754 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00049.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))))) Eq.refl Eq.refl

module MV02755 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X01 ≈ X14 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00076.proved (move-compose MV00072.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))))) Eq.refl Eq.refl

module MV02756 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X13 ≈ X46 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00212.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00135.proved (move-compose MV00134.proved (move-compose MV00133.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))))) Eq.refl Eq.refl

module MV02757 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M1 ≈ M4 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00028.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))))) Eq.refl Eq.refl

module MV02758 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M3 ≈ M6 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00042.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00043.proved (move-compose MV00046.proved (move-compose MV00045.proved (move-compose MV00044.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))))) Eq.refl Eq.refl

module MV02759 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X14 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00076.proved (move-compose MV00072.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved))))))))))) Eq.refl Eq.refl

module MV02760 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X47 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00219.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved))))))))))) Eq.refl Eq.refl
