{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B042 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0145 ; K0146 ; K0156 ; K0157 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0457 ; K1245 ; K1247 ; K1257 ; K1457 ; K2457 ; X36 ; X37 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00192 ; module MV00193 ; module MV00196 ; module MV00200 ; module MV00203 ; module MV00204 ; module MV00210 ; module MV00213 ; module MV00214 ; module MV00215 ; module MV00216 ; module MV00218 ; module MV00221 ; module MV00222 ; module MV00223 ; module MV00224 ; module MV00225 ; module MV00228 ; module MV00229 ; module MV00230 ; module MV00235 ; module MV00236 ; module MV00237 ; module MV00238 ; module MV00242 ; module MV00243 ; module MV00244 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00303 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00348 ; module MV00361)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00374 ; module MV00376)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00413)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00539)

module MV01574 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X36 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01575 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0157 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01576 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s4 • s5) • X45 ≈ X36 • p (s1 • s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00193.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01577 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s4 • s5) • K0123 ≈ K0245 • p (s1 • s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01578 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X36 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00193.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01579 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0247 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01580 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X36 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00193.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01581 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0257 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01582 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X36 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01583 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0457 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01584 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s5) • X45 ≈ X36 • p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00192.proved (move-compose MV00193.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01585 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s5) • K0123 ≈ K1245 • p (s0 • s1 • s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00348.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01586 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X36 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00192.proved (move-compose MV00193.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01587 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1247 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00361.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01588 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X36 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00192.proved (move-compose MV00193.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01589 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1257 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00374.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01590 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X36 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00192.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01591 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1457 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01592 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X36 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00193.proved (move-compose MV00192.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))))) Eq.refl Eq.refl

module MV01593 where

  proved : p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K2457 • p (s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))))) Eq.refl Eq.refl

module MV01594 where

  proved : p (s3 • s6 • s5) • X45 ≈ X37 • p (s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))) Eq.refl Eq.refl

module MV01595 where

  proved : p (s3 • s6 • s5) • K0123 ≈ K0124 • p (s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))) Eq.refl Eq.refl

module MV01596 where

  proved : p (s4 • s3 • s6 • s5) • X45 ≈ X37 • p (s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))) Eq.refl Eq.refl

module MV01597 where

  proved : p (s4 • s3 • s6 • s5) • K0123 ≈ K0125 • p (s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))) Eq.refl Eq.refl

module MV01598 where

  proved : p (s5 • s4 • s3 • s6 • s5) • X45 ≈ X37 • p (s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01599 where

  proved : p (s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0126 • p (s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01600 where

  proved : p (s3 • s2 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X37 • p (s3 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01601 where

  proved : p (s3 • s2 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0145 • p (s3 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01602 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X37 • p (s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01603 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0146 • p (s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01604 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X37 • p (s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01605 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0156 • p (s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01606 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X37 • p (s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00200.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01607 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0245 • p (s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01608 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X37 • p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00200.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01609 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0246 • p (s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01610 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X37 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00200.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01611 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0256 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl
