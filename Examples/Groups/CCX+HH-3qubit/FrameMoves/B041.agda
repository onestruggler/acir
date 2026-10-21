{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B041 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0145 ; K0146 ; K0147 ; K0167 ; K0246 ; K0247 ; K0267 ; K0467 ; K1246 ; K1247 ; K1267 ; K1467 ; K2467 ; K2567 ; X35 ; X36 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420 ; module MV00438 ; module MV00440 ; module MV00551)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00185 ; module MV00186 ; module MV00191 ; module MV00196 ; module MV00197 ; module MV00203 ; module MV00204 ; module MV00205 ; module MV00207 ; module MV00208 ; module MV00209 ; module MV00210 ; module MV00211 ; module MV00214 ; module MV00215 ; module MV00216 ; module MV00217 ; module MV00218 ; module MV00222 ; module MV00223 ; module MV00224 ; module MV00225 ; module MV00228 ; module MV00229 ; module MV00230 ; module MV00235 ; module MV00236 ; module MV00237 ; module MV00238 ; module MV00242 ; module MV00243 ; module MV00244 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00303)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00354 ; module MV00361)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00381)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00434)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545)

module MV01535 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K2567 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))))))) Eq.refl Eq.refl

module MV01536 where

  proved : p (s5 • s4 • s3 • s5) • X45 ≈ X35 • p (s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))) Eq.refl Eq.refl

module MV01537 where

  proved : p (s5 • s4 • s3 • s5) • K0123 ≈ K0126 • p (s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))) Eq.refl Eq.refl

module MV01538 where

  proved : p (s6 • s5 • s4 • s3 • s5) • X45 ≈ X35 • p (s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01539 where

  proved : p (s6 • s5 • s4 • s3 • s5) • K0123 ≈ K0127 • p (s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01540 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X35 • p (s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01541 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0146 • p (s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01542 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X35 • p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01543 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0147 • p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01544 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X35 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01545 where

  proved : p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0167 • p (s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01546 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X35 • p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00186.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01547 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0246 • p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01548 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X35 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00186.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01549 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K0247 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01550 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X35 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00186.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01551 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0267 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01552 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X35 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01553 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0467 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01554 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X35 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00185.proved (move-compose MV00186.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01555 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K1246 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00354.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01556 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X35 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00185.proved (move-compose MV00186.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01557 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K1247 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00361.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01558 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X35 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00185.proved (move-compose MV00186.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01559 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1267 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00381.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01560 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X35 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00185.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))))) Eq.refl Eq.refl

module MV01561 where

  proved : p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1467 • p (s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))))) Eq.refl Eq.refl

module MV01562 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X35 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00186.proved (move-compose MV00185.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))))) Eq.refl Eq.refl

module MV01563 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K2467 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))))) Eq.refl Eq.refl

module MV01564 where

  proved : p (s3 • s5) • X45 ≈ X36 • p (s3 • s5)
  proved = by-assoc-and (move-compose MV00215.proved (MV00210.proved)) Eq.refl Eq.refl

module MV01565 where

  proved : p (s3 • s5) • K0123 ≈ K0124 • p (s3 • s5)
  proved = by-assoc-and (move-compose MV00245.proved (MV00247.proved)) Eq.refl Eq.refl

module MV01566 where

  proved : p (s4 • s3 • s5) • X45 ≈ X36 • p (s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))) Eq.refl Eq.refl

module MV01567 where

  proved : p (s4 • s3 • s5) • K0123 ≈ K0125 • p (s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))) Eq.refl Eq.refl

module MV01568 where

  proved : p (s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X36 • p (s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01569 where

  proved : p (s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0127 • p (s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01570 where

  proved : p (s3 • s2 • s4 • s3 • s4 • s5) • X45 ≈ X36 • p (s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01571 where

  proved : p (s3 • s2 • s4 • s3 • s4 • s5) • K0123 ≈ K0145 • p (s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01572 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X36 • p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01573 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0147 • p (s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl
