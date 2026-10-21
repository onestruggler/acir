{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B044 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0125 ; K0126 ; K0127 ; K0135 ; K0137 ; K0157 ; K0235 ; K0237 ; K0257 ; K0357 ; K1235 ; K1237 ; K1257 ; K1357 ; K1367 ; K2357 ; K2367 ; X45 ; X46 ; X47 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00288 ; module MV00306 ; module MV00318 ; module MV00320 ; module MV00383)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00206 ; module MV00207 ; module MV00208 ; module MV00210 ; module MV00212 ; module MV00213 ; module MV00214 ; module MV00216 ; module MV00217 ; module MV00218 ; module MV00221 ; module MV00223 ; module MV00224 ; module MV00225 ; module MV00228 ; module MV00229 ; module MV00230 ; module MV00235 ; module MV00236 ; module MV00237 ; module MV00238 ; module MV00242 ; module MV00243 ; module MV00244 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00274 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00314 ; module MV00330)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00342)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00374 ; module MV00376)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00410 ; module MV00417)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00521 ; module MV00528)

module MV01649 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X45 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00206.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01650 where

  proved : p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1367 • p (s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01651 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X45 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00207.proved (move-compose MV00206.proved (move-compose MV00208.proved (move-compose MV00207.proved (move-compose MV00217.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))))) Eq.refl Eq.refl

module MV01652 where

  proved : p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K2367 • p (s1 • s0 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00528.proved (move-compose MV00417.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))))) Eq.refl Eq.refl

module MV01653 where

  proved : p (s4 • s3 • s4 • s5) • X45 ≈ X46 • p (s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))) Eq.refl Eq.refl

module MV01654 where

  proved : p (s4 • s3 • s4 • s5) • K0123 ≈ K0125 • p (s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))) Eq.refl Eq.refl

module MV01655 where

  proved : p (s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X46 • p (s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01656 where

  proved : p (s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0127 • p (s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01657 where

  proved : p (s2 • s4 • s3 • s4 • s5) • X45 ≈ X46 • p (s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00214.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01658 where

  proved : p (s2 • s4 • s3 • s4 • s5) • K0123 ≈ K0135 • p (s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01659 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X46 • p (s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01660 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0137 • p (s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01661 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X46 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01662 where

  proved : p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0157 • p (s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01663 where

  proved : p (s1 • s2 • s4 • s3 • s4 • s5) • X45 ≈ X46 • p (s1 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00213.proved (move-compose MV00214.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01664 where

  proved : p (s1 • s2 • s4 • s3 • s4 • s5) • K0123 ≈ K0235 • p (s1 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01665 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X46 • p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00213.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01666 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0237 • p (s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01667 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X46 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00213.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01668 where

  proved : p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0257 • p (s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01669 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X46 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01670 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0357 • p (s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01671 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s4 • s5) • X45 ≈ X46 • p (s0 • s1 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00212.proved (move-compose MV00213.proved (move-compose MV00214.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01672 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s4 • s5) • K0123 ≈ K1235 • p (s0 • s1 • s2 • s4 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00330.proved (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01673 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X46 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00212.proved (move-compose MV00213.proved (move-compose MV00214.proved (move-compose MV00225.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01674 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1237 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00342.proved (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01675 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X46 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00212.proved (move-compose MV00213.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01676 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1257 • p (s0 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00374.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01677 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X46 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00212.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01678 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1357 • p (s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01679 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X46 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00213.proved (move-compose MV00212.proved (move-compose MV00214.proved (move-compose MV00213.proved (move-compose MV00230.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))))) Eq.refl Eq.refl

module MV01680 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K2357 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00521.proved (move-compose MV00410.proved (move-compose MV00376.proved (move-compose MV00314.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))))) Eq.refl Eq.refl

module MV01681 where

  proved : p (s6 • s5) • X45 ≈ X47 • p (s6 • s5)
  proved = by-assoc-and (move-compose MV00218.proved (MV00210.proved)) Eq.refl Eq.refl

module MV01682 where

  proved : p (s6 • s5) • K0123 ≈ K0123 • p (s6 • s5)
  proved = by-assoc-and (move-compose MV00248.proved (MV00247.proved)) Eq.refl Eq.refl

module MV01683 where

  proved : p (s4 • s3 • s4 • s6 • s5) • X45 ≈ X47 • p (s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01684 where

  proved : p (s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0125 • p (s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01685 where

  proved : p (s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X47 • p (s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01686 where

  proved : p (s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0126 • p (s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01687 where

  proved : p (s2 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X47 • p (s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00221.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))) Eq.refl Eq.refl
