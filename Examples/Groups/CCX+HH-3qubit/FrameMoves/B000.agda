{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K0125 ; K0126 ; K0127 ; K0135 ; K0137 ; K0145 ; K0147 ; K0157 ; K0167 ; K0245 ; K0267 ; K0345 ; K0367 ; K0467 ; K0567 ; K1345 ; K1567 ; K2345 ; K2567 ; K3567 ; K4567 ; M0 ; M1 ; M2 ; NK ; _•_ ; _≈_ ; by-assoc-and ; m0 ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00000 ; module CM00001 ; module CM00012 ; module CM00013 ; module CM00014 ; module CM00015 ; module CM00017)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B000 using (module PE00004 ; module PE00147 ; module PE00155 ; module PE00163 ; module PE00210 ; module PE00214 ; module PE00215 ; module PE00216 ; module PE00217 ; module PE00222 ; module PE00223 ; module PE00240 ; module PE00241 ; module PE00264 ; module PE00265 ; module PE00272 ; module PE00273 ; module PE00274 ; module PE00275 ; module PE00300 ; module PE00301 ; module PE00324 ; module PE00325 ; module PE00328 ; module PE00329 ; module PE00388 ; module PE00389 ; module PE00454 ; module PE00455 ; module PE00462 ; module PE00463 ; module PE00464 ; module PE00465 ; module PE00528 ; module PE00529 ; module PE00564 ; module PE00565 ; module PE00568 ; module PE00569 ; module PE00684 ; module PE00685 ; module PE00790 ; module PE00791 ; module PE00798 ; module PE00799 ; module PE00896 ; module PE00897 ; module PE00936)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00000 ; module PE00001 ; module PE00009 ; module PE00937)

module MV00245 where

  step0 : p (s3) • K0123 ≈ p (s3) • p (ε) • NK • p (ε)
  step0 = by-assoc-and (under (ε) (NK • p (ε)) PE00004.proved) Eq.refl Eq.refl

  step1 : p (s3) • p (ε) • NK • p (ε) ≈ p (s3) • NK • p (ε) • p (ε)
  step1 = by-assoc-and (under (p (s3)) (p (ε)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s3) • NK • p (ε) • p (ε) ≈ K0124 • p (s3)
  step2 = by-assoc-and (under (p (s3) • NK) (ε) PE00210.proved) Eq.refl Eq.refl

  proved : p (s3) • K0123 ≈ K0124 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00251 where

  step0 : p (s4) • K0124 ≈ p (s3 • s4 • s3) • p (s4) • NK • p (s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3)) PE00147.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s3) • p (s4) • NK • p (s3) ≈ p (s3 • s4 • s3) • NK • p (s4) • p (s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s3)) (p (s3)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s3) • NK • p (s4) • p (s3) ≈ K0125 • p (s4)
  step2 = by-assoc-and (under (p (s3 • s4 • s3) • NK) (ε) PE00147.proved) Eq.refl Eq.refl

  proved : p (s4) • K0124 ≈ K0125 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00254 where

  step0 : p (s2) • K0125 ≈ p (s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3)) PE00214.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3) ≈ p (s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3)) (p (s3 • s4 • s3)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3) ≈ K0135 • p (s2)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3) • NK) (ε) PE00215.proved) Eq.refl Eq.refl

  proved : p (s2) • K0125 ≈ K0135 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00255 where

  step0 : p (s3) • K0125 ≈ p (s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3)) PE00216.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3) ≈ p (s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s3)) (p (s3 • s4 • s3)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3) ≈ K0125 • p (s3)
  step2 = by-assoc-and (under (p (s3 • s4 • s3) • NK) (ε) PE00217.proved) Eq.refl Eq.refl

  proved : p (s3) • K0125 ≈ K0125 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00276 where

  step0 : p (s3) • K0135 ≈ p (s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2)) PE00240.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2) ≈ K0145 • p (s3)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00241.proved) Eq.refl Eq.refl

  proved : p (s3) • K0135 ≈ K0145 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00292 where

  step0 : p (s1) • K0145 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2)) PE00272.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2) ≈ K0245 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00273.proved) Eq.refl Eq.refl

  proved : p (s1) • K0145 ≈ K0245 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00293 where

  step0 : p (s2) • K0145 ≈ p (s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2)) PE00274.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2) ≈ K0145 • p (s2)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00275.proved) Eq.refl Eq.refl

  proved : p (s2) • K0145 ≈ K0145 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00350 where

  step0 : p (s2) • K0245 ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) PE00388.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0345 • p (s2)
  step2 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00389.proved) Eq.refl Eq.refl

  proved : p (s2) • K0245 ≈ K0345 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00387 where

  step0 : p (s0) • K0345 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1)) PE00462.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1) ≈ K1345 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00463.proved) Eq.refl Eq.refl

  proved : p (s0) • K0345 ≈ K1345 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00388 where

  step0 : p (s1) • K0345 ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1)) PE00464.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1) ≈ K0345 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00465.proved) Eq.refl Eq.refl

  proved : p (s1) • K0345 ≈ K0345 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00633 where

  proved : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • K0123 ≈ K1345 • p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00387.proved (move-compose MV00388.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00293.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00255.proved (move-compose MV00251.proved (MV00245.proved)))))))))) Eq.refl Eq.refl

module MV00498 where

  step0 : p (s1) • K1345 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)) PE00684.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ K2345 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00685.proved) Eq.refl Eq.refl

  proved : p (s1) • K1345 ≈ K2345 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00555 where

  step0 : p (s0) • K2345 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE00798.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K2345 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00799.proved) Eq.refl Eq.refl

  proved : p (s0) • K2345 ≈ K2345 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00634 where

  proved : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • K0123 ≈ K2345 • p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)
  proved = by-assoc-and (move-compose MV00555.proved (move-compose MV00498.proved (move-compose MV00387.proved (move-compose MV00388.proved (move-compose MV00350.proved (move-compose MV00292.proved (move-compose MV00293.proved (move-compose MV00276.proved (move-compose MV00254.proved (move-compose MV00255.proved (move-compose MV00251.proved (MV00245.proved)))))))))))) Eq.refl Eq.refl

module MV00257 where

  step0 : p (s5) • K0125 ≈ p (s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3)) PE00155.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3) ≈ p (s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s3)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3) ≈ K0126 • p (s5)
  step2 = by-assoc-and (under (p (s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00155.proved) Eq.refl Eq.refl

  proved : p (s5) • K0125 ≈ K0126 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00263 where

  step0 : p (s6) • K0126 ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3)) PE00163.proved) Eq.refl Eq.refl

  step1 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3) ≈ p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3)
  step1 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3) ≈ K0127 • p (s6)
  step2 = by-assoc-and (under (p (s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00163.proved) Eq.refl Eq.refl

  proved : p (s6) • K0126 ≈ K0127 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00264 where

  step0 : p (s2) • K0127 ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) PE00222.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3) ≈ K0137 • p (s2)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00223.proved) Eq.refl Eq.refl

  proved : p (s2) • K0127 ≈ K0137 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00288 where

  step0 : p (s3) • K0137 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) PE00264.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2) ≈ K0147 • p (s3)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00265.proved) Eq.refl Eq.refl

  proved : p (s3) • K0137 ≈ K0147 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00306 where

  step0 : p (s4) • K0147 ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) PE00300.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0157 • p (s4)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00301.proved) Eq.refl Eq.refl

  proved : p (s4) • K0147 ≈ K0157 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00318 where

  step0 : p (s5) • K0157 ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) PE00324.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0167 • p (s5)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00325.proved) Eq.refl Eq.refl

  proved : p (s5) • K0157 ≈ K0167 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00320 where

  step0 : p (s1) • K0167 ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) PE00328.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ K0267 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00329.proved) Eq.refl Eq.refl

  proved : p (s1) • K0167 ≈ K0267 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00383 where

  step0 : p (s2) • K0267 ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1)) PE00454.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ K0367 • p (s2)
  step2 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00455.proved) Eq.refl Eq.refl

  proved : p (s2) • K0267 ≈ K0367 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00420 where

  step0 : p (s3) • K0367 ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1)) PE00528.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s1) ≈ K0467 • p (s3)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00529.proved) Eq.refl Eq.refl

  proved : p (s3) • K0367 ≈ K0467 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00438 where

  step0 : p (s4) • K0467 ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00564.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0567 • p (s4)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00565.proved) Eq.refl Eq.refl

  proved : p (s4) • K0467 ≈ K0567 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00440 where

  step0 : p (s0) • K0567 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) PE00568.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ K1567 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00569.proved) Eq.refl Eq.refl

  proved : p (s0) • K0567 ≈ K1567 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00551 where

  step0 : p (s1) • K1567 ≈ p (s0 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00790.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ K2567 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00791.proved) Eq.refl Eq.refl

  proved : p (s1) • K1567 ≈ K2567 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00604 where

  step0 : p (s2) • K2567 ≈ p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s0)) PE00896.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s0) ≈ K3567 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00897.proved) Eq.refl Eq.refl

  proved : p (s2) • K2567 ≈ K3567 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00624 where

  step0 : p (s3) • K3567 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)) PE00936.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0 • s1 • s2 • s1 • s0) ≈ K4567 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00937.proved) Eq.refl Eq.refl

  proved : p (s3) • K3567 ≈ K4567 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00632 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • K0123 ≈ K4567 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00624.proved (move-compose MV00604.proved (move-compose MV00551.proved (move-compose MV00440.proved (move-compose MV00438.proved (move-compose MV00420.proved (move-compose MV00383.proved (move-compose MV00320.proved (move-compose MV00318.proved (move-compose MV00306.proved (move-compose MV00288.proved (move-compose MV00264.proved (move-compose MV00263.proved (move-compose MV00257.proved (move-compose MV00251.proved (MV00245.proved)))))))))))))))) Eq.refl Eq.refl

module MV00000 where

  step0 : p (s0) • M0 ≈ p (s0) • p (ε) • m0 • p (ε)
  step0 = by-assoc-and (under (ε) (m0 • p (ε)) PE00000.proved) Eq.refl Eq.refl

  step1 : p (s0) • p (ε) • m0 • p (ε) ≈ p (s0) • m0 • p (ε) • p (ε)
  step1 = by-assoc-and (under (p (s0)) (p (ε)) CM00000.proved) Eq.refl Eq.refl

  step2 : p (s0) • m0 • p (ε) • p (ε) ≈ M1 • p (s0)
  step2 = by-assoc-and (under (p (s0) • m0) (ε) PE00001.proved) Eq.refl Eq.refl

  proved : p (s0) • M0 ≈ M1 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00008 where

  step0 : p (s1) • M1 ≈ p (s0 • s1 • s0) • p (s1) • m0 • p (s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0)) PE00009.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0) • p (s1) • m0 • p (s0) ≈ p (s0 • s1 • s0) • m0 • p (s1) • p (s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0)) (p (s0)) CM00001.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0) • m0 • p (s1) • p (s0) ≈ M2 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s0) • m0) (ε) PE00009.proved) Eq.refl Eq.refl

  proved : p (s1) • M1 ≈ M2 • p (s1)
  proved = trans step0 (trans step1 step2)
