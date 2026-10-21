{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B045 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0127 ; K0134 ; K0135 ; K0136 ; K0137 ; K0147 ; K0156 ; K0234 ; K0235 ; K0236 ; K0237 ; K0247 ; K0256 ; K0356 ; K1235 ; K1236 ; K1256 ; K1356 ; K2356 ; X45 ; X47 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00288)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00210 ; module MV00216 ; module MV00218 ; module MV00219 ; module MV00220 ; module MV00221 ; module MV00223 ; module MV00224 ; module MV00227 ; module MV00228 ; module MV00229 ; module MV00234 ; module MV00235 ; module MV00236 ; module MV00237 ; module MV00238 ; module MV00242 ; module MV00243 ; module MV00244 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00249 ; module MV00259 ; module MV00269 ; module MV00274 ; module MV00280 ; module MV00282 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00300 ; module MV00303 ; module MV00309 ; module MV00330)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00336)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00368 ; module MV00370)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B008 using (module MV00404)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B012 using (module MV00515)

module MV01688 where

  proved : p (s2 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0135 • p (s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01689 where

  proved : p (s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X47 • p (s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01690 where

  proved : p (s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0136 • p (s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01691 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X47 • p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01692 where

  proved : p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0156 • p (s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01693 where

  proved : p (s1 • s2 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X47 • p (s1 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00220.proved (move-compose MV00221.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01694 where

  proved : p (s1 • s2 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0235 • p (s1 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01695 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X47 • p (s1 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00220.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01696 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K0236 • p (s1 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01697 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X47 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00220.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01698 where

  proved : p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0256 • p (s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01699 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X47 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01700 where

  proved : p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0356 • p (s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01701 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X47 • p (s0 • s1 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00219.proved (move-compose MV00220.proved (move-compose MV00221.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01702 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1235 • p (s0 • s1 • s2 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00330.proved (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01703 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • X45 ≈ X47 • p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00219.proved (move-compose MV00220.proved (move-compose MV00221.proved (move-compose MV00224.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01704 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s6 • s5) • K0123 ≈ K1236 • p (s0 • s1 • s2 • s5 • s4 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00336.proved (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01705 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X47 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00219.proved (move-compose MV00220.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01706 where

  proved : p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1256 • p (s0 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00368.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01707 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X47 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00219.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01708 where

  proved : p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1356 • p (s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01709 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X47 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00220.proved (move-compose MV00219.proved (move-compose MV00221.proved (move-compose MV00220.proved (move-compose MV00236.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01710 where

  proved : p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K2356 • p (s1 • s0 • s2 • s1 • s4 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00515.proved (move-compose MV00404.proved (move-compose MV00370.proved (move-compose MV00309.proved (move-compose MV00300.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01711 where

  proved : p (s4 • s5) • X45 ≈ X56 • p (s4 • s5)
  proved = by-assoc-and (move-compose MV00216.proved (MV00210.proved)) Eq.refl Eq.refl

module MV01712 where

  proved : p (s4 • s5) • K0123 ≈ K0123 • p (s4 • s5)
  proved = by-assoc-and (move-compose MV00246.proved (MV00247.proved)) Eq.refl Eq.refl

module MV01713 where

  proved : p (s3 • s4 • s5) • X45 ≈ X56 • p (s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))) Eq.refl Eq.refl

module MV01714 where

  proved : p (s3 • s4 • s5) • K0123 ≈ K0124 • p (s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))) Eq.refl Eq.refl

module MV01715 where

  proved : p (s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X56 • p (s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01716 where

  proved : p (s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0127 • p (s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01717 where

  proved : p (s2 • s3 • s4 • s5) • X45 ≈ X56 • p (s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00228.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))) Eq.refl Eq.refl

module MV01718 where

  proved : p (s2 • s3 • s4 • s5) • K0123 ≈ K0134 • p (s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))) Eq.refl Eq.refl

module MV01719 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X56 • p (s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01720 where

  proved : p (s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0137 • p (s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01721 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X56 • p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01722 where

  proved : p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0147 • p (s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01723 where

  proved : p (s1 • s2 • s3 • s4 • s5) • X45 ≈ X56 • p (s1 • s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00227.proved (move-compose MV00228.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01724 where

  proved : p (s1 • s2 • s3 • s4 • s5) • K0123 ≈ K0234 • p (s1 • s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01725 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X56 • p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00227.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01726 where

  proved : p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0237 • p (s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01727 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X56 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00227.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01728 where

  proved : p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0247 • p (s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl
