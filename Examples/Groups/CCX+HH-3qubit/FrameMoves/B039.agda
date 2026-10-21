{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B039 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0134 ; K0135 ; K0136 ; K0145 ; K0146 ; K0156 ; K0345 ; K0346 ; K0347 ; K0356 ; K0357 ; K0456 ; K0457 ; K1345 ; K1347 ; K1357 ; K1457 ; K3457 ; X26 ; X27 ; X45 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00276 ; module MV00288 ; module MV00292 ; module MV00306 ; module MV00350 ; module MV00387)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00165 ; module MV00168 ; module MV00172 ; module MV00175 ; module MV00176 ; module MV00192 ; module MV00193 ; module MV00194 ; module MV00196 ; module MV00200 ; module MV00201 ; module MV00203 ; module MV00204 ; module MV00210 ; module MV00213 ; module MV00214 ; module MV00215 ; module MV00216 ; module MV00218 ; module MV00221 ; module MV00222 ; module MV00223 ; module MV00224 ; module MV00225 ; module MV00228 ; module MV00229 ; module MV00230 ; module MV00235 ; module MV00236 ; module MV00237 ; module MV00238 ; module MV00242 ; module MV00243 ; module MV00244 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00249 ; module MV00259 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00300 ; module MV00303 ; module MV00309 ; module MV00314)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00356 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00370 ; module MV00376 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00407 ; module MV00410 ; module MV00413)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 using (module MV00428)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00539)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B015 using (module MV00592)

module MV01464 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0347 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01465 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X26 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01466 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0357 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01467 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X26 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01468 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0457 • p (s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01469 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5) • X45 ≈ X26 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00165.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01470 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5) • K0123 ≈ K1345 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01471 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X26 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00165.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01472 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1347 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01473 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X26 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00165.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01474 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1357 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01475 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X26 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00165.proved (move-compose MV00168.proved (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00196.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01476 where

  proved : p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1457 • p (s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01477 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X26 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00194.proved (move-compose MV00193.proved (move-compose MV00192.proved (move-compose MV00215.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))))) Eq.refl Eq.refl

module MV01478 where

  proved : p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K3457 • p (s2 • s1 • s0 • s3 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00592.proved (move-compose MV00539.proved (move-compose MV00428.proved (move-compose MV00413.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))))) Eq.refl Eq.refl

module MV01479 where

  proved : p (s2 • s3 • s6 • s5) • X45 ≈ X27 • p (s2 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00201.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))) Eq.refl Eq.refl

module MV01480 where

  proved : p (s2 • s3 • s6 • s5) • K0123 ≈ K0134 • p (s2 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))) Eq.refl Eq.refl

module MV01481 where

  proved : p (s2 • s4 • s3 • s6 • s5) • X45 ≈ X27 • p (s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00201.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01482 where

  proved : p (s2 • s4 • s3 • s6 • s5) • K0123 ≈ K0135 • p (s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01483 where

  proved : p (s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X27 • p (s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01484 where

  proved : p (s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0136 • p (s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01485 where

  proved : p (s3 • s2 • s4 • s3 • s6 • s5) • X45 ≈ X27 • p (s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01486 where

  proved : p (s3 • s2 • s4 • s3 • s6 • s5) • K0123 ≈ K0145 • p (s3 • s2 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01487 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X27 • p (s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01488 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0146 • p (s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01489 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • X45 ≈ X27 • p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00176.proved (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00204.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01490 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5) • K0123 ≈ K0156 • p (s4 • s3 • s2 • s5 • s4 • s3 • s6 • s5)
  proved = by-assoc-and (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01491 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X27 • p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01492 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0345 • p (s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01493 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X27 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01494 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0346 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01495 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X27 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01496 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0356 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01497 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X27 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00175.proved (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00203.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01498 where

  proved : p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0456 • p (s3 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00407.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01499 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X27 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00172.proved (move-compose MV00201.proved (move-compose MV00200.proved (move-compose MV00222.proved (move-compose MV00221.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01500 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1345 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl
