{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B024 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X12 ; X37 ; X45 ; X46 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00016 ; module MV00024 ; module MV00032 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00048 ; module MV00105 ; module MV00113)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00125 ; module MV00129 ; module MV00132 ; module MV00137 ; module MV00139 ; module MV00160 ; module MV00167 ; module MV00174 ; module MV00188 ; module MV00195 ; module MV00199 ; module MV00200 ; module MV00202 ; module MV00203 ; module MV00204 ; module MV00206 ; module MV00207 ; module MV00208 ; module MV00211 ; module MV00212 ; module MV00213 ; module MV00214 ; module MV00216 ; module MV00217 ; module MV00219 ; module MV00220 ; module MV00221 ; module MV00222 ; module MV00223 ; module MV00224 ; module MV00225 ; module MV00226 ; module MV00227 ; module MV00228 ; module MV00229 ; module MV00230 ; module MV00232 ; module MV00233 ; module MV00234 ; module MV00235 ; module MV00236)

module MV00950 where

  proved : p (s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X37 • p (s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00951 where

  proved : p (s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M0 • p (s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00952 where

  proved : p (s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X37 • p (s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00953 where

  proved : p (s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00954 where

  proved : p (s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X37 • p (s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00200.proved (move-compose MV00199.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00955 where

  proved : p (s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00956 where

  proved : p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X37 • p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00219.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))) Eq.refl Eq.refl

module MV00957 where

  proved : p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))) Eq.refl Eq.refl

module MV00958 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X37 • p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00219.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))))) Eq.refl Eq.refl

module MV00959 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))))) Eq.refl Eq.refl

module MV00960 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X37 • p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00219.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))))) Eq.refl Eq.refl

module MV00961 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))))) Eq.refl Eq.refl

module MV00962 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X45 • p (s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))) Eq.refl Eq.refl

module MV00963 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M0 • p (s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))) Eq.refl Eq.refl

module MV00964 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X45 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00965 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00966 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X45 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00967 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00968 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • X12 ≈ X45 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00969 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00970 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X45 • p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00226.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))))) Eq.refl Eq.refl

module MV00971 where

  proved : p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M6 • p (s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))))) Eq.refl Eq.refl

module MV00972 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X45 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00226.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))))))) Eq.refl Eq.refl

module MV00973 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))))))) Eq.refl Eq.refl

module MV00974 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X46 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))) Eq.refl Eq.refl

module MV00975 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M0 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))) Eq.refl Eq.refl

module MV00976 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X46 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00212.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))) Eq.refl Eq.refl

module MV00977 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M1 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))) Eq.refl Eq.refl

module MV00978 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X46 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00213.proved (move-compose MV00212.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))) Eq.refl Eq.refl

module MV00979 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M2 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))) Eq.refl Eq.refl

module MV00980 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X46 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00212.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))) Eq.refl Eq.refl

module MV00981 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M3 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))) Eq.refl Eq.refl

module MV00982 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • X12 ≈ X46 • p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00226.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved))))))))))))) Eq.refl Eq.refl

module MV00983 where

  proved : p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2) • M0 ≈ M5 • p (s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved))))))))))))) Eq.refl Eq.refl

module MV00984 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • X12 ≈ X46 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00232.proved (move-compose MV00223.proved (move-compose MV00202.proved (move-compose MV00174.proved (move-compose MV00139.proved (move-compose MV00137.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (MV00105.proved)))))))))))))))) Eq.refl Eq.refl

module MV00985 where

  proved : p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2) • M0 ≈ M7 • p (s6 • s5 • s4 • s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s6 • s5 • s4 • s3 • s2)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (move-compose MV00032.proved (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (MV00002.proved)))))))))))))))) Eq.refl Eq.refl
