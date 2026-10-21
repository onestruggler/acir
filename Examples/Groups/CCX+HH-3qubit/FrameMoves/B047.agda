{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B047 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0134 ; K0135 ; K0145 ; K0234 ; K0235 ; K0245 ; K0345 ; K1234 ; K1235 ; K1245 ; K1345 ; K2345 ; K2346 ; M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; M7 ; X45 ; X57 ; X67 ; _•_ ; _≈_ ; by-assoc-and ; m0 ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00000)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00245 ; module MV00251 ; module MV00254 ; module MV00257 ; module MV00276 ; module MV00292 ; module MV00350 ; module MV00387 ; module MV00498)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00001 ; module MV00002 ; module MV00003 ; module MV00004 ; module MV00005 ; module MV00006 ; module MV00007 ; module MV00014 ; module MV00015 ; module MV00021 ; module MV00023 ; module MV00031 ; module MV00032 ; module MV00035 ; module MV00040)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 using (module MV00042 ; module MV00048)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B003 using (module MV00210 ; module MV00218 ; module MV00223 ; module MV00232 ; module MV00233 ; module MV00234 ; module MV00235 ; module MV00237 ; module MV00239 ; module MV00240 ; module MV00241 ; module MV00242 ; module MV00243 ; module MV00244 ; module MV00246)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B004 using (module MV00247 ; module MV00248 ; module MV00249 ; module MV00259 ; module MV00269 ; module MV00274 ; module MV00282)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 using (module MV00297 ; module MV00325 ; module MV00330)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 using (module MV00348 ; module MV00356)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B007 using (module MV00392)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B011 using (module MV00503)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00955)

module MV01769 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X57 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00233.proved (move-compose MV00232.proved (move-compose MV00234.proved (move-compose MV00233.proved (move-compose MV00235.proved (move-compose MV00234.proved (move-compose MV00244.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))))) Eq.refl Eq.refl

module MV01770 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K2346 • p (s1 • s0 • s2 • s1 • s3 • s2 • s5 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00503.proved (move-compose MV00392.proved (move-compose MV00356.proved (move-compose MV00297.proved (move-compose MV00282.proved (move-compose MV00259.proved (move-compose MV00257.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))))) Eq.refl Eq.refl

module MV01771 where

  proved : p (s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))) Eq.refl Eq.refl

module MV01772 where

  proved : p (s5 • s4 • s6 • s5) • K0123 ≈ K0123 • p (s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))) Eq.refl Eq.refl

module MV01773 where

  proved : p (s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))) Eq.refl Eq.refl

module MV01774 where

  proved : p (s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0124 • p (s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))) Eq.refl Eq.refl

module MV01775 where

  proved : p (s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01776 where

  proved : p (s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0125 • p (s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01777 where

  proved : p (s2 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00241.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))) Eq.refl Eq.refl

module MV01778 where

  proved : p (s2 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0134 • p (s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))) Eq.refl Eq.refl

module MV01779 where

  proved : p (s2 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00241.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01780 where

  proved : p (s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0135 • p (s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01781 where

  proved : p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01782 where

  proved : p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0145 • p (s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01783 where

  proved : p (s1 • s2 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s1 • s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00240.proved (move-compose MV00241.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))) Eq.refl Eq.refl

module MV01784 where

  proved : p (s1 • s2 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0234 • p (s1 • s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))) Eq.refl Eq.refl

module MV01785 where

  proved : p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00240.proved (move-compose MV00241.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01786 where

  proved : p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0235 • p (s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01787 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00240.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01788 where

  proved : p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0245 • p (s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01789 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01790 where

  proved : p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K0345 • p (s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01791 where

  proved : p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00239.proved (move-compose MV00240.proved (move-compose MV00241.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))) Eq.refl Eq.refl

module MV01792 where

  proved : p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1234 • p (s0 • s1 • s2 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00325.proved (move-compose MV00269.proved (move-compose MV00249.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))) Eq.refl Eq.refl

module MV01793 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00239.proved (move-compose MV00240.proved (move-compose MV00241.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))) Eq.refl Eq.refl

module MV01794 where

  proved : p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1235 • p (s0 • s1 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00330.proved (move-compose MV00274.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))) Eq.refl Eq.refl

module MV01795 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00239.proved (move-compose MV00240.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))) Eq.refl Eq.refl

module MV01796 where

  proved : p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1245 • p (s0 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00348.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))) Eq.refl Eq.refl

module MV01797 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00239.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved))))))))))) Eq.refl Eq.refl

module MV01798 where

  proved : p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K1345 • p (s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved))))))))))) Eq.refl Eq.refl

module MV01799 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • X45 ≈ X67 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00240.proved (move-compose MV00239.proved (move-compose MV00241.proved (move-compose MV00240.proved (move-compose MV00242.proved (move-compose MV00241.proved (move-compose MV00243.proved (move-compose MV00242.proved (move-compose MV00237.proved (move-compose MV00223.proved (move-compose MV00218.proved (MV00210.proved)))))))))))) Eq.refl Eq.refl

module MV01800 where

  proved : p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5) • K0123 ≈ K2345 • p (s1 • s0 • s2 • s1 • s3 • s2 • s4 • s3 • s5 • s4 • s6 • s5)
  proved = by-assoc-and (move-compose MV00498.proved (move-compose MV00387.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00251.proved (move-compose MV00245.proved (move-compose MV00247.proved (move-compose MV00246.proved (move-compose MV00248.proved (MV00247.proved)))))))))))) Eq.refl Eq.refl

module MV01801 where

  proved : p (s1 • s2 • s3) • M0 ≈ M0 • p (s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00001.proved (move-compose MV00002.proved (MV00003.proved))) Eq.refl Eq.refl

module MV01802 where

  proved : p (s1 • s2 • s3) • M4 ≈ M1 • p (s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00015.proved (move-compose MV00023.proved (MV00031.proved))) Eq.refl Eq.refl

module MV01803 where

  proved : p (s2 • s3) • M0 ≈ M0 • p (s2 • s3)
  proved = by-assoc-and (move-compose MV00002.proved (MV00003.proved)) Eq.refl Eq.refl

module MV01804 where

  proved : p (s2 • s3) • M4 ≈ M2 • p (s2 • s3)
  proved = by-assoc-and (move-compose MV00023.proved (MV00031.proved)) Eq.refl Eq.refl

module MV01805 where

  step0 : p (ε) • M4 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (ε) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) PE00955.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (ε) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (ε) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) CM00000.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (ε) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ M4 • p (ε)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0) (ε) PE00955.proved) Eq.refl Eq.refl

  proved : p (ε) • M4 ≈ M4 • p (ε)
  proved = trans step0 (trans step1 step2)

module MV01806 where

  proved : p (s5 • s4) • M0 ≈ M0 • p (s5 • s4)
  proved = by-assoc-and (move-compose MV00005.proved (MV00004.proved)) Eq.refl Eq.refl

module MV01807 where

  proved : p (s5 • s4) • M4 ≈ M6 • p (s5 • s4)
  proved = by-assoc-and (move-compose MV00040.proved (MV00032.proved)) Eq.refl Eq.refl

module MV01808 where

  proved : p (s6 • s5 • s4) • M0 ≈ M0 • p (s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00006.proved (move-compose MV00005.proved (MV00004.proved))) Eq.refl Eq.refl

module MV01809 where

  proved : p (s6 • s5 • s4) • M4 ≈ M7 • p (s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00048.proved (move-compose MV00040.proved (MV00032.proved))) Eq.refl Eq.refl

module MV01810 where

  proved : p (s0 • s1 • s2 • s3) • M0 ≈ M1 • p (s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00001.proved (move-compose MV00002.proved (MV00003.proved)))) Eq.refl Eq.refl

module MV01811 where

  proved : p (s0 • s1 • s2 • s3) • M4 ≈ M0 • p (s0 • s1 • s2 • s3)
  proved = by-assoc-and (move-compose MV00007.proved (move-compose MV00015.proved (move-compose MV00023.proved (MV00031.proved)))) Eq.refl Eq.refl

module MV01812 where

  proved : p (s0 • s2 • s3) • M0 ≈ M1 • p (s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00002.proved (MV00003.proved))) Eq.refl Eq.refl

module MV01813 where

  proved : p (s0 • s2 • s3) • M4 ≈ M2 • p (s0 • s2 • s3)
  proved = by-assoc-and (move-compose MV00014.proved (move-compose MV00023.proved (MV00031.proved))) Eq.refl Eq.refl

module MV01814 where

  proved : p (s0 • s3) • M0 ≈ M1 • p (s0 • s3)
  proved = by-assoc-and (move-compose MV00000.proved (MV00003.proved)) Eq.refl Eq.refl

module MV01815 where

  proved : p (s0 • s3) • M4 ≈ M3 • p (s0 • s3)
  proved = by-assoc-and (move-compose MV00021.proved (MV00031.proved)) Eq.refl Eq.refl

module MV01816 where

  proved : p (s0 • s4) • M0 ≈ M1 • p (s0 • s4)
  proved = by-assoc-and (move-compose MV00000.proved (MV00004.proved)) Eq.refl Eq.refl

module MV01817 where

  proved : p (s0 • s4) • M4 ≈ M5 • p (s0 • s4)
  proved = by-assoc-and (move-compose MV00035.proved (MV00032.proved)) Eq.refl Eq.refl

module MV01818 where

  proved : p (s0 • s5 • s4) • M0 ≈ M1 • p (s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00005.proved (MV00004.proved))) Eq.refl Eq.refl

module MV01819 where

  proved : p (s0 • s5 • s4) • M4 ≈ M6 • p (s0 • s5 • s4)
  proved = by-assoc-and (move-compose MV00042.proved (move-compose MV00040.proved (MV00032.proved))) Eq.refl Eq.refl

module MV01820 where

  proved : p (s0 • s6 • s5 • s4) • M0 ≈ M1 • p (s0 • s6 • s5 • s4)
  proved = by-assoc-and (move-compose MV00000.proved (move-compose MV00006.proved (move-compose MV00005.proved (MV00004.proved)))) Eq.refl Eq.refl
