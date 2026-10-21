{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B072 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M3 ; M5 ; M7 ; X01 ; X12 ; X13 ; X14 ; X15 ; X16 ; X23 ; X24 ; X25 ; X26 ; X34 ; X45 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00009 ; module MV00010 ; module MV00011 ; module MV00012 ; module MV00013 ; module MV00016 ; module MV00024 ; module MV00032 ; module MV00035 ; module MV00036 ; module MV00037 ; module MV00038 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00048 ; module MV00049 ; module MV00050 ; module MV00051 ; module MV00052 ; module MV00053 ; module MV00054 ; module MV00056 ; module MV00057 ; module MV00058 ; module MV00059 ; module MV00060 ; module MV00061 ; module MV00064 ; module MV00072 ; module MV00080 ; module MV00083 ; module MV00105 ; module MV00106 ; module MV00107 ; module MV00108 ; module MV00109 ; module MV00111 ; module MV00113 ; module MV00118)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00125 ; module MV00129 ; module MV00132 ; module MV00137 ; module MV00139 ; module MV00140 ; module MV00141 ; module MV00142 ; module MV00143 ; module MV00153 ; module MV00160 ; module MV00174 ; module MV00188 ; module MV00202 ; module MV00223 ; module MV00232 ; module MV00233 ; module MV00234 ; module MV00235)

module MV02826 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved))))))))))))))) Eq.refl Eq.refl

module MV02827 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X01 ≈ X45 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00083.proved (move-compose MV00080.proved (move-compose MV00072.proved (move-compose MV00064.proved (move-compose MV00056.proved (move-compose MV00060.proved (move-compose MV00059.proved (move-compose MV00058.proved (move-compose MV00057.proved (move-compose MV00061.proved (move-compose MV00060.proved (move-compose MV00059.proved (MV00058.proved)))))))))))))))) Eq.refl Eq.refl

module MV02828 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X13 ≈ X57 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00232.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00143.proved (move-compose MV00142.proved (move-compose MV00141.proved (move-compose MV00140.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (MV00113.proved)))))))))))))))) Eq.refl Eq.refl

module MV02829 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M1 ≈ M5 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00038.proved (move-compose MV00037.proved (move-compose MV00036.proved (move-compose MV00035.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00012.proved (move-compose MV00011.proved (move-compose MV00010.proved (move-compose MV00009.proved (move-compose MV00013.proved (move-compose MV00012.proved (move-compose MV00011.proved (MV00010.proved)))))))))))))))) Eq.refl Eq.refl

module MV02830 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M3 ≈ M7 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00049.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00050.proved (move-compose MV00054.proved (move-compose MV00053.proved (move-compose MV00052.proved (move-compose MV00051.proved (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (MV00024.proved)))))))))))))))) Eq.refl Eq.refl

module MV02831 where

  proved : p (s4 • s3) • X12 ≈ X12 • p (s4 • s3)
  proved = by-assoc-and (move-compose MV00107.proved (MV00106.proved)) Eq.refl Eq.refl

module MV02832 where

  proved : p (s4 • s3) • M0 ≈ M0 • p (s4 • s3)
  proved = by-assoc-and (move-compose MV00004.proved (MV00003.proved)) Eq.refl Eq.refl

module MV02833 where

  proved : p (s5 • s4 • s3) • X12 ≈ X12 • p (s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))) Eq.refl Eq.refl

module MV02834 where

  proved : p (s5 • s4 • s3) • M0 ≈ M0 • p (s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))) Eq.refl Eq.refl

module MV02835 where

  proved : p (s6 • s5 • s4 • s3) • X12 ≈ X12 • p (s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))) Eq.refl Eq.refl

module MV02836 where

  proved : p (s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))) Eq.refl Eq.refl

module MV02837 where

  proved : p (s2 • s3) • X12 ≈ X13 • p (s2 • s3)
  proved = by-assoc-and (move-compose MV00105.proved (MV00106.proved)) Eq.refl Eq.refl

module MV02838 where

  proved : p (s2 • s4 • s3) • X12 ≈ X13 • p (s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00105.proved (move-compose MV00107.proved (MV00106.proved))) Eq.refl Eq.refl

module MV02839 where

  proved : p (s2 • s4 • s3) • M0 ≈ M0 • p (s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00004.proved (MV00003.proved))) Eq.refl Eq.refl

module MV02840 where

  proved : p (s2 • s5 • s4 • s3) • X12 ≈ X13 • p (s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))) Eq.refl Eq.refl

module MV02841 where

  proved : p (s2 • s5 • s4 • s3) • M0 ≈ M0 • p (s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))) Eq.refl Eq.refl

module MV02842 where

  proved : p (s2 • s6 • s5 • s4 • s3) • X12 ≈ X13 • p (s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))) Eq.refl Eq.refl

module MV02843 where

  proved : p (s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))) Eq.refl Eq.refl

module MV02844 where

  proved : p (s3 • s2 • s4 • s3) • X12 ≈ X14 • p (s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00107.proved (MV00106.proved)))) Eq.refl Eq.refl

module MV02845 where

  proved : p (s3 • s2 • s4 • s3) • M0 ≈ M0 • p (s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00004.proved (MV00003.proved)))) Eq.refl Eq.refl

module MV02846 where

  proved : p (s3 • s2 • s5 • s4 • s3) • X12 ≈ X14 • p (s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))) Eq.refl Eq.refl

module MV02847 where

  proved : p (s3 • s2 • s5 • s4 • s3) • M0 ≈ M0 • p (s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))) Eq.refl Eq.refl

module MV02848 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X14 • p (s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))) Eq.refl Eq.refl

module MV02849 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))) Eq.refl Eq.refl

module MV02850 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X15 • p (s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))) Eq.refl Eq.refl

module MV02851 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M0 • p (s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))) Eq.refl Eq.refl

module MV02852 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X15 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))) Eq.refl Eq.refl

module MV02853 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))) Eq.refl Eq.refl

module MV02854 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X16 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))) Eq.refl Eq.refl

module MV02855 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))) Eq.refl Eq.refl

module MV02856 where

  proved : p (s1 • s2 • s3) • X12 ≈ X23 • p (s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00111.proved (move-compose MV00105.proved (MV00106.proved))) Eq.refl Eq.refl

module MV02857 where

  proved : p (s1 • s2 • s4 • s3) • X12 ≈ X23 • p (s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00111.proved (move-compose MV00105.proved (move-compose MV00107.proved (MV00106.proved)))) Eq.refl Eq.refl

module MV02858 where

  proved : p (s1 • s2 • s4 • s3) • M0 ≈ M0 • p (s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00002.proved (move-compose MV00004.proved (MV00003.proved)))) Eq.refl Eq.refl

module MV02859 where

  proved : p (s1 • s2 • s5 • s4 • s3) • X12 ≈ X23 • p (s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00111.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))) Eq.refl Eq.refl

module MV02860 where

  proved : p (s1 • s2 • s5 • s4 • s3) • M0 ≈ M0 • p (s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))) Eq.refl Eq.refl

module MV02861 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X23 • p (s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00111.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))) Eq.refl Eq.refl

module MV02862 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))) Eq.refl Eq.refl

module MV02863 where

  proved : p (s1 • s3 • s2 • s4 • s3) • X12 ≈ X24 • p (s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00107.proved (MV00106.proved))))) Eq.refl Eq.refl

module MV02864 where

  proved : p (s1 • s3 • s2 • s4 • s3) • M0 ≈ M0 • p (s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00004.proved (MV00003.proved))))) Eq.refl Eq.refl

module MV02865 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X24 • p (s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))) Eq.refl Eq.refl

module MV02866 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M0 • p (s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))) Eq.refl Eq.refl

module MV02867 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X24 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))) Eq.refl Eq.refl

module MV02868 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))) Eq.refl Eq.refl

module MV02869 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X25 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))) Eq.refl Eq.refl

module MV02870 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M0 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))) Eq.refl Eq.refl

module MV02871 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X25 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))) Eq.refl Eq.refl

module MV02872 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))) Eq.refl Eq.refl

module MV02873 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X26 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))) Eq.refl Eq.refl

module MV02874 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M0 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))) Eq.refl Eq.refl

module MV02875 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3) • X12 ≈ X34 • p (s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00107.proved (MV00106.proved)))))) Eq.refl Eq.refl

module MV02876 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3) • M0 ≈ M0 • p (s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00004.proved (MV00003.proved)))))) Eq.refl Eq.refl
