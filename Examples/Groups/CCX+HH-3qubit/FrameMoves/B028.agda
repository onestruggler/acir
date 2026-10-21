{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B028 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K1256 ; K1257 ; K1267 ; K1356 ; K1357 ; K1367 ; K1567 ; K2356 ; K2357 ; K2367 ; K2456 ; K2457 ; K2467 ; K2567 ; K4567 ; X03 ; X04 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00288 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383 ; module MV00420 ; module MV00438 ; module MV00440 ; module MV00551 ; module MV00604 ; module MV00624)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00070 ; module MV00077 ; module MV00078 ; module MV00079 ; module MV00110 ; module MV00114 ; module MV00117)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00119 ; module MV00120 ; module MV00126 ; module MV00127 ; module MV00128 ; module MV00152 ; module MV00156 ; module MV00159 ; module MV00161 ; module MV00162 ; module MV00168 ; module MV00169 ; module MV00170 ; module MV00181 ; module MV00183 ; module MV00184 ; module MV00187 ; module MV00189 ; module MV00191 ; module MV00194 ; module MV00196 ; module MV00197 ; module MV00203 ; module MV00204 ; module MV00205 ; module MV00209 ; module MV00210 ; module MV00215 ; module MV00218 ; module MV00222)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00300 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00368 ; module MV00370 ; module MV00374 ; module MV00376 ; module MV00381)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00404 ; module MV00407 ; module MV00410 ; module MV00413 ; module MV00417 ; module MV00423)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428 ; module MV00434)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00515 ; module MV00521 ; module MV00528 ; module MV00534 ; module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 using (module MV00545)

module MV01084 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5) • K0123 ≈ K2456 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00534.proved (move-compose MV00423.proved (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01085 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X03 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00070.proved (move-compose MV00110.proved (move-compose MV00120.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01086 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K2457 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01087 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X03 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00070.proved (move-compose MV00110.proved (move-compose MV00120.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00156.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01088 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K2467 • p (s1 • s0 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00545.proved (move-compose MV00434.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01089 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X03 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00070.proved (move-compose MV00110.proved (move-compose MV00114.proved (move-compose MV00120.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00156.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01090 where

  proved : p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K2567 • p (s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01091 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X03 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00079.proved (move-compose MV00078.proved (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00128.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))))))) Eq.refl Eq.refl

module MV01092 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K4567 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))))))) Eq.refl Eq.refl

module MV01093 where

  proved : p (s0 • s1 • s2 • s4 • s3) • X45 ≈ X04 • p (s0 • s1 • s2 • s4 • s3)
  proved = by-assoc-and (move-compose MV00117.proved (move-compose MV00152.proved (move-compose MV00181.proved (move-compose MV00189.proved (MV00209.proved))))) Eq.refl Eq.refl

module MV01094 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3) • X45 ≈ X04 • p (s0 • s1 • s2 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00117.proved (move-compose MV00152.proved (move-compose MV00181.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved)))))) Eq.refl Eq.refl

module MV01095 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3) • X45 ≈ X04 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00117.proved (move-compose MV00152.proved (move-compose MV00181.proved (move-compose MV00184.proved (move-compose MV00183.proved (move-compose MV00189.proved (MV00209.proved))))))) Eq.refl Eq.refl

module MV01096 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5) • X45 ≈ X04 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00117.proved (move-compose MV00152.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01097 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5) • K0123 ≈ K1256 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00368.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01098 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X04 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00117.proved (move-compose MV00152.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01099 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K1257 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00374.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01100 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X04 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00117.proved (move-compose MV00152.proved (move-compose MV00156.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01101 where

  proved : p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K1267 • p (s0 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00381.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01102 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5) • X45 ≈ X04 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00117.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01103 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5) • K0123 ≈ K1356 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01104 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X04 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00117.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01105 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K1357 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01106 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X04 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00117.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00156.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01107 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K1367 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01108 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X04 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00117.proved (move-compose MV00128.proved (move-compose MV00127.proved (move-compose MV00126.proved (move-compose MV00159.proved (move-compose MV00170.proved (move-compose MV00169.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00205.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01109 where

  proved : p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K1567 • p (s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01110 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5) • X45 ≈ X04 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01111 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5) • K0123 ≈ K2356 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00515.proved (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01112 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X04 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01113 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K2357 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00521.proved (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01114 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • X45 ≈ X04 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00077.proved (move-compose MV00117.proved (move-compose MV00119.proved (move-compose MV00152.proved (move-compose MV00156.proved (move-compose MV00162.proved (move-compose MV00161.proved (move-compose MV00187.proved (move-compose MV00191.proved (move-compose MV00197.proved (move-compose MV00196.proved (move-compose MV00215.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01115 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5) • K0123 ≈ K2367 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5)
  proved = by-assoc-and (move-compose MV00528.proved (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl
