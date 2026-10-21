{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B074 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; X12 ; X34 ; X35 ; X36 ; X45 ; X46 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00105 ; module MV00106 ; module MV00107 ; module MV00108 ; module MV00109 ; module MV00113 ; module MV00118)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00121 ; module MV00125 ; module MV00129 ; module MV00132 ; module MV00153 ; module MV00160 ; module MV00167 ; module MV00179 ; module MV00180 ; module MV00185 ; module MV00186 ; module MV00188 ; module MV00192 ; module MV00193 ; module MV00195 ; module MV00206 ; module MV00207 ; module MV00212 ; module MV00213 ; module MV00216 ; module MV00226 ; module MV00227)

module MV02920 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X35 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))) Eq.refl Eq.refl

module MV02921 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))) Eq.refl Eq.refl

module MV02922 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X35 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))) Eq.refl Eq.refl

module MV02923 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))) Eq.refl Eq.refl

module MV02924 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X36 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))))) Eq.refl Eq.refl

module MV02925 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))))) Eq.refl Eq.refl

module MV02926 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X45 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))) Eq.refl Eq.refl

module MV02927 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))) Eq.refl Eq.refl

module MV02928 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X45 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))))) Eq.refl Eq.refl

module MV02929 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))))) Eq.refl Eq.refl

module MV02930 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X46 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00212.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))))) Eq.refl Eq.refl

module MV02931 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))))) Eq.refl Eq.refl

module MV02932 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X56 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00226.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))))))) Eq.refl Eq.refl

module MV02933 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M1 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))))))) Eq.refl Eq.refl

module MV02934 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • X12 ≈ X34 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00180.proved (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00107.proved (MV00106.proved)))))))) Eq.refl Eq.refl

module MV02935 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3) • M0 ≈ M2 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00004.proved (MV00003.proved)))))))) Eq.refl Eq.refl

module MV02936 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X34 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00180.proved (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))) Eq.refl Eq.refl

module MV02937 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M2 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))) Eq.refl Eq.refl

module MV02938 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X34 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00180.proved (move-compose MV00179.proved (move-compose MV00153.proved (move-compose MV00118.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))) Eq.refl Eq.refl

module MV02939 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M2 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))) Eq.refl Eq.refl

module MV02940 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X35 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00186.proved (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))) Eq.refl Eq.refl

module MV02941 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M2 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))) Eq.refl Eq.refl

module MV02942 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X35 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00186.proved (move-compose MV00185.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))))) Eq.refl Eq.refl

module MV02943 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M2 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))))) Eq.refl Eq.refl

module MV02944 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X36 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00193.proved (move-compose MV00192.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))))) Eq.refl Eq.refl

module MV02945 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M2 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))))) Eq.refl Eq.refl

module MV02946 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • X12 ≈ X45 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))))) Eq.refl Eq.refl

module MV02947 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3) • M0 ≈ M2 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))))) Eq.refl Eq.refl

module MV02948 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X45 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00188.proved (move-compose MV00160.proved (move-compose MV00125.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))))) Eq.refl Eq.refl

module MV02949 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M2 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))))) Eq.refl Eq.refl

module MV02950 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X46 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00213.proved (move-compose MV00212.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved))))))))))))) Eq.refl Eq.refl

module MV02951 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M2 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved))))))))))))) Eq.refl Eq.refl

module MV02952 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X12 ≈ X56 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00227.proved (move-compose MV00226.proved (move-compose MV00216.proved (move-compose MV00195.proved (move-compose MV00167.proved (move-compose MV00132.proved (move-compose MV00129.proved (move-compose MV00121.proved (move-compose MV00113.proved (move-compose MV00105.proved (move-compose MV00109.proved (move-compose MV00108.proved (move-compose MV00107.proved (MV00106.proved)))))))))))))) Eq.refl Eq.refl

module MV02953 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M2 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))))))) Eq.refl Eq.refl
