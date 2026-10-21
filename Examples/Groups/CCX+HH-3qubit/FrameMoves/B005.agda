{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B005 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0134 ; K0135 ; K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0156 ; K0157 ; K0167 ; K0234 ; K0235 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K1234 ; K1235 ; NK ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00012 ; module CM00013 ; module CM00014 ; module CM00015 ; module CM00016 ; module CM00017 ; module CM00018)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B005 using (module PE00282 ; module PE00283 ; module PE00284 ; module PE00285 ; module PE00286 ; module PE00287 ; module PE00288 ; module PE00289 ; module PE00290 ; module PE00291 ; module PE00292 ; module PE00293 ; module PE00294 ; module PE00295 ; module PE00296 ; module PE00297 ; module PE00298 ; module PE00299 ; module PE00302 ; module PE00303 ; module PE00304 ; module PE00305 ; module PE00306 ; module PE00307 ; module PE00308 ; module PE00309 ; module PE00310 ; module PE00311 ; module PE00312 ; module PE00313 ; module PE00314 ; module PE00315 ; module PE00316)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B006 using (module PE00317 ; module PE00318 ; module PE00319 ; module PE00320 ; module PE00321 ; module PE00322 ; module PE00323 ; module PE00326 ; module PE00327 ; module PE00330 ; module PE00331 ; module PE00332 ; module PE00333 ; module PE00334 ; module PE00335 ; module PE00336 ; module PE00337 ; module PE00338 ; module PE00339 ; module PE00340 ; module PE00341 ; module PE00342 ; module PE00343 ; module PE00344 ; module PE00345 ; module PE00346 ; module PE00347 ; module PE00348 ; module PE00349 ; module PE00350 ; module PE00351 ; module PE00352 ; module PE00353)

module MV00297 where

  step0 : p (s1) • K0146 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) PE00282.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0246 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00283.proved) Eq.refl Eq.refl

  proved : p (s1) • K0146 ≈ K0246 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00298 where

  step0 : p (s2) • K0146 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) PE00284.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0146 • p (s2)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00285.proved) Eq.refl Eq.refl

  proved : p (s2) • K0146 ≈ K0146 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00299 where

  step0 : p (s3) • K0146 ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) PE00286.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0136 • p (s3)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00287.proved) Eq.refl Eq.refl

  proved : p (s3) • K0146 ≈ K0136 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00300 where

  step0 : p (s4) • K0146 ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) PE00288.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0156 • p (s4)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00289.proved) Eq.refl Eq.refl

  proved : p (s4) • K0146 ≈ K0156 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00301 where

  step0 : p (s5) • K0146 ≈ p (s2 • s3 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) PE00290.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0145 • p (s5)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00291.proved) Eq.refl Eq.refl

  proved : p (s5) • K0146 ≈ K0145 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00302 where

  step0 : p (s6) • K0146 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) PE00292.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0147 • p (s6)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00293.proved) Eq.refl Eq.refl

  proved : p (s6) • K0146 ≈ K0147 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00303 where

  step0 : p (s1) • K0147 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) PE00294.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0247 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00295.proved) Eq.refl Eq.refl

  proved : p (s1) • K0147 ≈ K0247 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00304 where

  step0 : p (s2) • K0147 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) PE00296.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0147 • p (s2)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00297.proved) Eq.refl Eq.refl

  proved : p (s2) • K0147 ≈ K0147 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00305 where

  step0 : p (s3) • K0147 ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) PE00298.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0137 • p (s3)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00299.proved) Eq.refl Eq.refl

  proved : p (s3) • K0147 ≈ K0137 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00307 where

  step0 : p (s5) • K0147 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) PE00302.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0147 • p (s5)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00303.proved) Eq.refl Eq.refl

  proved : p (s5) • K0147 ≈ K0147 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00308 where

  step0 : p (s6) • K0147 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) PE00304.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2) ≈ K0146 • p (s6)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00305.proved) Eq.refl Eq.refl

  proved : p (s6) • K0147 ≈ K0146 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00309 where

  step0 : p (s1) • K0156 ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) PE00306.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0256 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00307.proved) Eq.refl Eq.refl

  proved : p (s1) • K0156 ≈ K0256 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00310 where

  step0 : p (s2) • K0156 ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) PE00308.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0156 • p (s2)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00309.proved) Eq.refl Eq.refl

  proved : p (s2) • K0156 ≈ K0156 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00311 where

  step0 : p (s3) • K0156 ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) PE00310.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0156 • p (s3)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00311.proved) Eq.refl Eq.refl

  proved : p (s3) • K0156 ≈ K0156 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00312 where

  step0 : p (s4) • K0156 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) PE00312.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0146 • p (s4)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00313.proved) Eq.refl Eq.refl

  proved : p (s4) • K0156 ≈ K0146 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00313 where

  step0 : p (s6) • K0156 ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) PE00314.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0157 • p (s6)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00315.proved) Eq.refl Eq.refl

  proved : p (s6) • K0156 ≈ K0157 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00314 where

  step0 : p (s1) • K0157 ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) PE00316.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0257 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00317.proved) Eq.refl Eq.refl

  proved : p (s1) • K0157 ≈ K0257 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00315 where

  step0 : p (s2) • K0157 ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) PE00318.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) CM00018.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0157 • p (s2)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00319.proved) Eq.refl Eq.refl

  proved : p (s2) • K0157 ≈ K0157 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00316 where

  step0 : p (s3) • K0157 ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) PE00320.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0157 • p (s3)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00321.proved) Eq.refl Eq.refl

  proved : p (s3) • K0157 ≈ K0157 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00317 where

  step0 : p (s4) • K0157 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) PE00322.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0147 • p (s4)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00323.proved) Eq.refl Eq.refl

  proved : p (s4) • K0157 ≈ K0147 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00319 where

  step0 : p (s6) • K0157 ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) PE00326.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2) ≈ K0156 • p (s6)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00327.proved) Eq.refl Eq.refl

  proved : p (s6) • K0157 ≈ K0156 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00321 where

  step0 : p (s2) • K0167 ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) PE00330.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ K0167 • p (s2)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00331.proved) Eq.refl Eq.refl

  proved : p (s2) • K0167 ≈ K0167 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00322 where

  step0 : p (s3) • K0167 ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) PE00332.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ K0167 • p (s3)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00333.proved) Eq.refl Eq.refl

  proved : p (s3) • K0167 ≈ K0167 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00323 where

  step0 : p (s4) • K0167 ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) PE00334.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ K0167 • p (s4)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00335.proved) Eq.refl Eq.refl

  proved : p (s4) • K0167 ≈ K0167 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00324 where

  step0 : p (s5) • K0167 ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) PE00336.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2) ≈ K0157 • p (s5)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00337.proved) Eq.refl Eq.refl

  proved : p (s5) • K0167 ≈ K0157 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00325 where

  step0 : p (s0) • K0234 ≈ p (s0 • s1 • s2 • s3) • p (ε) • NK • p (s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2 • s1)) PE00338.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3) • p (ε) • NK • p (s3 • s2 • s1) ≈ p (s0 • s1 • s2 • s3) • NK • p (ε) • p (s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3)) (p (s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3) • NK • p (ε) • p (s3 • s2 • s1) ≈ K1234 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3) • NK) (ε) PE00339.proved) Eq.refl Eq.refl

  proved : p (s0) • K0234 ≈ K1234 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00326 where

  step0 : p (s1) • K0234 ≈ p (s2 • s3) • p (ε) • NK • p (s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2 • s1)) PE00340.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3) • p (ε) • NK • p (s3 • s2 • s1) ≈ p (s2 • s3) • NK • p (ε) • p (s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s2 • s3)) (p (s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3) • NK • p (ε) • p (s3 • s2 • s1) ≈ K0134 • p (s1)
  step2 = by-assoc-and (under (p (s2 • s3) • NK) (ε) PE00341.proved) Eq.refl Eq.refl

  proved : p (s1) • K0234 ≈ K0134 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00327 where

  step0 : p (s4) • K0234 ≈ p (s1 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2 • s1)) PE00342.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3)) (p (s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s2 • s1) ≈ K0235 • p (s4)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3) • NK) (ε) PE00343.proved) Eq.refl Eq.refl

  proved : p (s4) • K0234 ≈ K0235 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00328 where

  step0 : p (s5) • K0234 ≈ p (s1 • s2 • s3) • p (s5) • NK • p (s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2 • s1)) PE00344.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3) • p (s5) • NK • p (s3 • s2 • s1) ≈ p (s1 • s2 • s3) • NK • p (s5) • p (s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3)) (p (s3 • s2 • s1)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3) • NK • p (s5) • p (s3 • s2 • s1) ≈ K0234 • p (s5)
  step2 = by-assoc-and (under (p (s1 • s2 • s3) • NK) (ε) PE00345.proved) Eq.refl Eq.refl

  proved : p (s5) • K0234 ≈ K0234 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00329 where

  step0 : p (s6) • K0234 ≈ p (s1 • s2 • s3) • p (s6) • NK • p (s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2 • s1)) PE00346.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3) • p (s6) • NK • p (s3 • s2 • s1) ≈ p (s1 • s2 • s3) • NK • p (s6) • p (s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3)) (p (s3 • s2 • s1)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3) • NK • p (s6) • p (s3 • s2 • s1) ≈ K0234 • p (s6)
  step2 = by-assoc-and (under (p (s1 • s2 • s3) • NK) (ε) PE00347.proved) Eq.refl Eq.refl

  proved : p (s6) • K0234 ≈ K0234 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00330 where

  step0 : p (s0) • K0235 ≈ p (s0 • s1 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1)) PE00348.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s1) ≈ p (s0 • s1 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s1) ≈ K1235 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3) • NK) (ε) PE00349.proved) Eq.refl Eq.refl

  proved : p (s0) • K0235 ≈ K1235 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00331 where

  step0 : p (s1) • K0235 ≈ p (s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1)) PE00350.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s1) ≈ p (s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s1) ≈ K0135 • p (s1)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s3) • NK) (ε) PE00351.proved) Eq.refl Eq.refl

  proved : p (s1) • K0235 ≈ K0135 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00332 where

  step0 : p (s3) • K0235 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1)) PE00352.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1) ≈ K0245 • p (s3)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00353.proved) Eq.refl Eq.refl

  proved : p (s3) • K0235 ≈ K0245 • p (s3)
  proved = trans step0 (trans step1 step2)
