{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B022 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M3 ; M4 ; M5 ; M6 ; M7 ; X12 ; X24 ; X25 ; X26 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00016 ; module MV00024 ; module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00048 ; module MV00105 ; module MV00113)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00125 ; module MV00129 ; module MV00132 ; module MV00137 ; module MV00139 ; module MV00156 ; module MV00157 ; module MV00158 ; module MV00160 ; module MV00161 ; module MV00162 ; module MV00164 ; module MV00165 ; module MV00167 ; module MV00168 ; module MV00169 ; module MV00170 ; module MV00172 ; module MV00174 ; module MV00175 ; module MV00176 ; module MV00177 ; module MV00178 ; module MV00185 ; module MV00186 ; module MV00187 ; module MV00192 ; module MV00193 ; module MV00194 ; module MV00199 ; module MV00200 ; module MV00201)

module MV00872 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X24 • p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00873 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00874 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X24 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00156.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV00875 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl

module MV00876 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X24 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00157.proved (move-compose MV00156.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))) Eq.refl Eq.refl

module MV00877 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))) Eq.refl Eq.refl

module MV00878 where

  proved : p (s1 • s4 • s3 • s2) • X12 ≈ X25 • p (s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))) Eq.refl Eq.refl

module MV00879 where

  proved : p (s1 • s4 • s3 • s2) • M0 ≈ M0 • p (s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))) Eq.refl Eq.refl

module MV00880 where

  proved : p (s0 • s1 • s4 • s3 • s2) • X12 ≈ X25 • p (s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00158.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))) Eq.refl Eq.refl

module MV00881 where

  proved : p (s0 • s1 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))) Eq.refl Eq.refl

module MV00882 where

  proved : p (s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X25 • p (s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00883 where

  proved : p (s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00884 where

  proved : p (s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X25 • p (s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00186.proved (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00885 where

  proved : p (s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00886 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X25 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))) Eq.refl Eq.refl

module MV00887 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))) Eq.refl Eq.refl

module MV00888 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X25 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00164.proved (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))))) Eq.refl Eq.refl

module MV00889 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))))) Eq.refl Eq.refl

module MV00890 where

  proved : p (s1 • s5 • s4 • s3 • s2) • X12 ≈ X26 • p (s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))) Eq.refl Eq.refl

module MV00891 where

  proved : p (s1 • s5 • s4 • s3 • s2) • M0 ≈ M0 • p (s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))) Eq.refl Eq.refl

module MV00892 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X26 • p (s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00165.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00893 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00894 where

  proved : p (s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X26 • p (s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00895 where

  proved : p (s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00896 where

  proved : p (s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X26 • p (s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00897 where

  proved : p (s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00898 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X26 • p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV00899 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl

module MV00900 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X26 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00178.proved (move-compose MV00177.proved (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))))) Eq.refl Eq.refl

module MV00901 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))))) Eq.refl Eq.refl

module MV00902 where

  proved : p (s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X27 • p (s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00903 where

  proved : p (s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M0 • p (s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00904 where

  proved : p (s0 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X27 • p (s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00172.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00905 where

  proved : p (s0 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00906 where

  proved : p (s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X27 • p (s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00907 where

  proved : p (s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00908 where

  proved : p (s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X27 • p (s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV00909 where

  proved : p (s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl

module MV00910 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X27 • p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))) Eq.refl Eq.refl
