{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B032 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0456 ; K0457 ; K0467 ; K0567 ; K2456 ; K2457 ; K2467 ; K2567 ; K3457 ; K3467 ; K3567 ; K4567 ; X12 ; X13 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00288 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420 ; module MV00438 ; module MV00440 ; module MV00551 ; module MV00604 ; module MV00624)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00106 ; module MV00112 ; module MV00114)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00119 ; module MV00120 ; module MV00145 ; module MV00146 ; module MV00148 ; module MV00149 ; module MV00152 ; module MV00154 ; module MV00156 ; module MV00161 ; module MV00162 ; module MV00180 ; module MV00181 ; module MV00183 ; module MV00184 ; module MV00187 ; module MV00189 ; module MV00191 ; module MV00196 ; module MV00197 ; module MV00208 ; module MV00209 ; module MV00210 ; module MV00211 ; module MV00215 ; module MV00216 ; module MV00217 ; module MV00229 ; module MV00230 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00300 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00376)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00407 ; module MV00413 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428 ; module MV00434)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00534 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00592 ; module MV00598)

module MV01221 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X12 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01222 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K3457 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00592.proved (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01223 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X12 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00183.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))))))))) Eq.refl Eq.refl

module MV01224 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K3467 • p (s2 • s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00598.proved (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))))))))) Eq.refl Eq.refl

module MV01225 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X12 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00183.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))))))))))) Eq.refl Eq.refl

module MV01226 where

  proved : p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K3567 • p (s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))))))))))) Eq.refl Eq.refl

module MV01227 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X12 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00106.proved (move-compose MV00112.proved (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00183.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))))))))))) Eq.refl Eq.refl

module MV01228 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K4567 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))))))))))) Eq.refl Eq.refl

module MV01229 where

  proved : p (s1 • s3 • s2 • s4 • s3) • X45 ≈ X13 • p (s1 • s3 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00189.proved (MV00209.proved))))) Eq.refl Eq.refl

module MV01230 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3) • X45 ≈ X13 • p (s1 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))) Eq.refl Eq.refl

module MV01231 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X13 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00146.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))) Eq.refl Eq.refl

module MV01232 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3) • X45 ≈ X13 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))) Eq.refl Eq.refl

module MV01233 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X13 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00146.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))))) Eq.refl Eq.refl

module MV01234 where

  proved : p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X13 • p (s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00146.proved (move-compose MV00149.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))))) Eq.refl Eq.refl

module MV01235 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5) • X45 ≈ X13 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00120.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01236 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5) • K0123 ≈ K0456 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01237 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X13 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00120.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01238 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K0457 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01239 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X13 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00120.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00156.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01240 where

  proved : p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K0467 • p (s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01241 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X13 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00114.proved (move-compose MV00120.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00156.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01242 where

  proved : p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K0567 • p (s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01243 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X13 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01244 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K2456 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01245 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X13 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01246 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K2457 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01247 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X13 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00183.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01248 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K2467 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01249 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • X45 ≈ X13 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00146.proved (move-compose MV00145.proved (move-compose MV00148.proved (move-compose MV00154.proved (move-compose MV00181.proved (move-compose MV00180.proved (move-compose MV00183.proved (move-compose MV00189.proved (move-compose MV00209.proved (move-compose MV00208.proved (move-compose MV00211.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))))))))))) Eq.refl Eq.refl

module MV01250 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5) • K0123 ≈ K2567 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))))))))))) Eq.refl Eq.refl
