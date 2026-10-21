{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B046 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0126 ; K0134 ; K0136 ; K0146 ; K0234 ; K0236 ; K0246 ; K0346 ; K0347 ; K1234 ; K1236 ; K1237 ; K1246 ; K1247 ; K1346 ; K1347 ; K2347 ; X45 ; X56 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00245 ; module MV00251 ; module MV00257 ; module MV00263 ; module MV00264 ; module MV00288)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00210 ; module MV00216 ; module MV00218 ; module MV00223 ; module MV00226 ; module MV00227 ; module MV00228 ; module MV00229 ; module MV00232 ; module MV00233 ; module MV00234 ; module MV00235 ; module MV00237 ; module MV00238 ; module MV00242 ; module MV00243 ; module MV00244 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00249 ; module MV00259 ; module MV00269 ; module MV00280 ; module MV00282 ; module MV00286)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00303 ; module MV00325)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00336 ; module MV00342 ; module MV00354 ; module MV00356 ; module MV00361 ; module MV00363)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00392 ; module MV00398)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00509)

module MV01729 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X56 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01730 where

  proved : p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0347 • p (s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01731 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5) • X45 ≈ X56 • p (s0 • s1 • s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00226.proved (move-compose MV00227.proved (move-compose MV00228.proved (move-compose MV00229.proved (move-compose MV00216.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01732 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s5) • K0123 ≈ K1234 • p (s0 • s1 • s2 • s3 • s4 • s5)
  proved = by-assoc-and (move-compose MV00325.proved (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00246.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01733 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X56 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00226.proved (move-compose MV00227.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01734 where

  proved : p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1237 • p (s0 • s1 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00342.proved (move-compose MV00286.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01735 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X56 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00226.proved (move-compose MV00227.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01736 where

  proved : p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1247 • p (s0 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00361.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01737 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X56 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00226.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01738 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1347 • p (s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01739 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X56 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00227.proved (move-compose MV00226.proved (move-compose MV00228.proved (move-compose MV00227.proved (move-compose MV00229.proved (move-compose MV00228.proved (move-compose MV00238.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))))) Eq.refl Eq.refl

module MV01740 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K2347 • p (s1 • s0 • s2 • s1 • s3 • s2 • s6 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00509.proved (move-compose MV00398.proved (move-compose MV00363.proved (move-compose MV00303.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))))) Eq.refl Eq.refl

module MV01741 where

  proved : p (s4 • s6 • s5) • X45 ≈ X57 • p (s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))) Eq.refl Eq.refl

module MV01742 where

  proved : p (s4 • s6 • s5) • K0123 ≈ K0123 • p (s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))) Eq.refl Eq.refl

module MV01743 where

  proved : p (s3 • s4 • s6 • s5) • X45 ≈ X57 • p (s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))) Eq.refl Eq.refl

module MV01744 where

  proved : p (s3 • s4 • s6 • s5) • K0123 ≈ K0124 • p (s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))) Eq.refl Eq.refl

module MV01745 where

  proved : p (s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X57 • p (s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01746 where

  proved : p (s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0126 • p (s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01747 where

  proved : p (s2 • s3 • s4 • s6 • s5) • X45 ≈ X57 • p (s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00234.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01748 where

  proved : p (s2 • s3 • s4 • s6 • s5) • K0123 ≈ K0134 • p (s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01749 where

  proved : p (s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X57 • p (s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01750 where

  proved : p (s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0136 • p (s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01751 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X57 • p (s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01752 where

  proved : p (s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0146 • p (s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01753 where

  proved : p (s1 • s2 • s3 • s4 • s6 • s5) • X45 ≈ X57 • p (s1 • s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00233.proved (move-compose MV00234.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01754 where

  proved : p (s1 • s2 • s3 • s4 • s6 • s5) • K0123 ≈ K0234 • p (s1 • s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01755 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X57 • p (s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00233.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01756 where

  proved : p (s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0236 • p (s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01757 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X57 • p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00233.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01758 where

  proved : p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0246 • p (s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01759 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X57 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01760 where

  proved : p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0346 • p (s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01761 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s6 • s5) • X45 ≈ X57 • p (s0 • s1 • s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00232.proved (move-compose MV00233.proved (move-compose MV00234.proved (move-compose MV00235.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01762 where

  proved : p (s0 • s1 • s2 • s3 • s4 • s6 • s5) • K0123 ≈ K1234 • p (s0 • s1 • s2 • s3 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00325.proved (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01763 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X57 • p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00232.proved (move-compose MV00233.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01764 where

  proved : p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1236 • p (s0 • s1 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00336.proved (move-compose MV00280.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01765 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X57 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00232.proved (move-compose MV00233.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01766 where

  proved : p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1246 • p (s0 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00354.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01767 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X57 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00232.proved (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01768 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1346 • p (s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl
