{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B023 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M4 ; M5 ; M6 ; M7 ; X12 ; X27 ; X34 ; X35 ; X36 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00016 ; module MV00024 ; module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00048 ; module MV00105 ; module MV00113 ; module MV00118)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00125 ; module MV00129 ; module MV00132 ; module MV00137 ; module MV00139 ; module MV00153 ; module MV00160 ; module MV00167 ; module MV00174 ; module MV00175 ; module MV00176 ; module MV00177 ; module MV00179 ; module MV00180 ; module MV00183 ; module MV00184 ; module MV00185 ; module MV00186 ; module MV00188 ; module MV00189 ; module MV00191 ; module MV00192 ; module MV00193 ; module MV00195 ; module MV00196 ; module MV00197 ; module MV00199 ; module MV00200 ; module MV00201 ; module MV00202 ; module MV00203 ; module MV00204 ; module MV00205 ; module MV00206 ; module MV00207 ; module MV00208 ; module MV00209 ; module MV00212 ; module MV00213 ; module MV00214 ; module MV00215 ; module MV00219 ; module MV00220 ; module MV00221 ; module MV00222)

module MV00911 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))) Eq.refl Eq.refl

module MV00912 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X27 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00177.proved (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))))) Eq.refl Eq.refl

module MV00913 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))))) Eq.refl Eq.refl

module MV00914 where

  proved : p (s2 • s1 • s3 • s2) • X12 ≈ X34 • p (s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved)))) Eq.refl Eq.refl

module MV00915 where

  proved : p (s2 • s1 • s3 • s2) • M0 ≈ M0 • p (s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved)))) Eq.refl Eq.refl

module MV00916 where

  proved : p (s0 • s2 • s1 • s3 • s2) • X12 ≈ X34 • p (s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved))))) Eq.refl Eq.refl

module MV00917 where

  proved : p (s0 • s2 • s1 • s3 • s2) • M0 ≈ M1 • p (s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved))))) Eq.refl Eq.refl

module MV00918 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2) • X12 ≈ X34 • p (s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00180.proved (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00919 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s2 • s1 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00920 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X34 • p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV00921 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl

module MV00922 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X34 • p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00183.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))) Eq.refl Eq.refl

module MV00923 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))) Eq.refl Eq.refl

module MV00924 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X34 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))))) Eq.refl Eq.refl

module MV00925 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))))) Eq.refl Eq.refl

module MV00926 where

  proved : p (s2 • s1 • s4 • s3 • s2) • X12 ≈ X35 • p (s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))) Eq.refl Eq.refl

module MV00927 where

  proved : p (s2 • s1 • s4 • s3 • s2) • M0 ≈ M0 • p (s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))) Eq.refl Eq.refl

module MV00928 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X35 • p (s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00929 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00930 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X35 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00186.proved (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00931 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00932 where

  proved : p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X35 • p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00933 where

  proved : p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00934 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X35 • p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00212.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))))) Eq.refl Eq.refl

module MV00935 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))))) Eq.refl Eq.refl

module MV00936 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X35 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00212.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))))) Eq.refl Eq.refl

module MV00937 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))))) Eq.refl Eq.refl

module MV00938 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X36 • p (s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00939 where

  proved : p (s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M0 • p (s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00940 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X36 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00941 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00942 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X36 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00193.proved (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00943 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00944 where

  proved : p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X36 • p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00212.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))) Eq.refl Eq.refl

module MV00945 where

  proved : p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))) Eq.refl Eq.refl

module MV00946 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X36 • p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00212.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))) Eq.refl Eq.refl

module MV00947 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))) Eq.refl Eq.refl

module MV00948 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X36 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00219.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))))))) Eq.refl Eq.refl

module MV00949 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))))))) Eq.refl Eq.refl
