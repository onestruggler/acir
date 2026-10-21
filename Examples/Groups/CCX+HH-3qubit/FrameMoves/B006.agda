{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B006 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0136 ; K0137 ; K0145 ; K0146 ; K0147 ; K0234 ; K0235 ; K0236 ; K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K0346 ; K0347 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; NK ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00012 ; module CM00013 ; module CM00014 ; module CM00015 ; module CM00016 ; module CM00017)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B006 using (module PE00354 ; module PE00355 ; module PE00356 ; module PE00357 ; module PE00358 ; module PE00359 ; module PE00360 ; module PE00361 ; module PE00362 ; module PE00363 ; module PE00364 ; module PE00365 ; module PE00366 ; module PE00367 ; module PE00368 ; module PE00369 ; module PE00370 ; module PE00371 ; module PE00372 ; module PE00373 ; module PE00374 ; module PE00375 ; module PE00376 ; module PE00377)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B007 using (module PE00378 ; module PE00379 ; module PE00380 ; module PE00381 ; module PE00382 ; module PE00383 ; module PE00384 ; module PE00385 ; module PE00386 ; module PE00387 ; module PE00390 ; module PE00391 ; module PE00392 ; module PE00393 ; module PE00394 ; module PE00395 ; module PE00396 ; module PE00397 ; module PE00398 ; module PE00399 ; module PE00400 ; module PE00401 ; module PE00402 ; module PE00403 ; module PE00404 ; module PE00405 ; module PE00406 ; module PE00407 ; module PE00408 ; module PE00409 ; module PE00410 ; module PE00411 ; module PE00412 ; module PE00413 ; module PE00414 ; module PE00415 ; module PE00416 ; module PE00417 ; module PE00418 ; module PE00419 ; module PE00420 ; module PE00421)

module MV00333 where

  step0 : p (s4) • K0235 ≈ p (s1 • s2 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1)) PE00354.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3)) (p (s3 • s4 • s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1) ≈ K0234 • p (s4)
  step2 = by-assoc-and (under (p (s1 • s2 • s3) • NK) (ε) PE00355.proved) Eq.refl Eq.refl

  proved : p (s4) • K0235 ≈ K0234 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00334 where

  step0 : p (s5) • K0235 ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1)) PE00356.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s1)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s1) ≈ K0236 • p (s5)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00357.proved) Eq.refl Eq.refl

  proved : p (s5) • K0235 ≈ K0236 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00335 where

  step0 : p (s6) • K0235 ≈ p (s1 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1)) PE00358.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s1)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s1) ≈ K0235 • p (s6)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3) • NK) (ε) PE00359.proved) Eq.refl Eq.refl

  proved : p (s6) • K0235 ≈ K0235 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00336 where

  step0 : p (s0) • K0236 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) PE00360.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ K1236 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00361.proved) Eq.refl Eq.refl

  proved : p (s0) • K0236 ≈ K1236 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00337 where

  step0 : p (s1) • K0236 ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) PE00362.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ K0136 • p (s1)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00363.proved) Eq.refl Eq.refl

  proved : p (s1) • K0236 ≈ K0136 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00338 where

  step0 : p (s3) • K0236 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) PE00364.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ K0246 • p (s3)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00365.proved) Eq.refl Eq.refl

  proved : p (s3) • K0236 ≈ K0246 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00339 where

  step0 : p (s4) • K0236 ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) PE00366.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ K0236 • p (s4)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00367.proved) Eq.refl Eq.refl

  proved : p (s4) • K0236 ≈ K0236 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00340 where

  step0 : p (s5) • K0236 ≈ p (s1 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) PE00368.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ K0235 • p (s5)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3) • NK) (ε) PE00369.proved) Eq.refl Eq.refl

  proved : p (s5) • K0236 ≈ K0235 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00341 where

  step0 : p (s6) • K0236 ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) PE00370.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1) ≈ K0237 • p (s6)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00371.proved) Eq.refl Eq.refl

  proved : p (s6) • K0236 ≈ K0237 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00342 where

  step0 : p (s0) • K0237 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) PE00372.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ K1237 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00373.proved) Eq.refl Eq.refl

  proved : p (s0) • K0237 ≈ K1237 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00343 where

  step0 : p (s1) • K0237 ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) PE00374.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ K0137 • p (s1)
  step2 = by-assoc-and (under (p (s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00375.proved) Eq.refl Eq.refl

  proved : p (s1) • K0237 ≈ K0137 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00344 where

  step0 : p (s3) • K0237 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) PE00376.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ K0247 • p (s3)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00377.proved) Eq.refl Eq.refl

  proved : p (s3) • K0237 ≈ K0247 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00345 where

  step0 : p (s4) • K0237 ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) PE00378.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ K0237 • p (s4)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00379.proved) Eq.refl Eq.refl

  proved : p (s4) • K0237 ≈ K0237 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00346 where

  step0 : p (s5) • K0237 ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) PE00380.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ K0237 • p (s5)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00381.proved) Eq.refl Eq.refl

  proved : p (s5) • K0237 ≈ K0237 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00347 where

  step0 : p (s6) • K0237 ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) PE00382.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1) ≈ K0236 • p (s6)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00383.proved) Eq.refl Eq.refl

  proved : p (s6) • K0237 ≈ K0236 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00348 where

  step0 : p (s0) • K0245 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) PE00384.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K1245 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00385.proved) Eq.refl Eq.refl

  proved : p (s0) • K0245 ≈ K1245 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00349 where

  step0 : p (s1) • K0245 ≈ p (s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) PE00386.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0145 • p (s1)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00387.proved) Eq.refl Eq.refl

  proved : p (s1) • K0245 ≈ K0145 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00351 where

  step0 : p (s3) • K0245 ≈ p (s1 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) PE00390.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0235 • p (s3)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3) • NK) (ε) PE00391.proved) Eq.refl Eq.refl

  proved : p (s3) • K0245 ≈ K0235 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00352 where

  step0 : p (s5) • K0245 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) PE00392.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0246 • p (s5)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00393.proved) Eq.refl Eq.refl

  proved : p (s5) • K0245 ≈ K0246 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00353 where

  step0 : p (s6) • K0245 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) PE00394.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0245 • p (s6)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00395.proved) Eq.refl Eq.refl

  proved : p (s6) • K0245 ≈ K0245 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00354 where

  step0 : p (s0) • K0246 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00396.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K1246 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00397.proved) Eq.refl Eq.refl

  proved : p (s0) • K0246 ≈ K1246 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00355 where

  step0 : p (s1) • K0246 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00398.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0146 • p (s1)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00399.proved) Eq.refl Eq.refl

  proved : p (s1) • K0246 ≈ K0146 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00356 where

  step0 : p (s2) • K0246 ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00400.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0346 • p (s2)
  step2 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00401.proved) Eq.refl Eq.refl

  proved : p (s2) • K0246 ≈ K0346 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00357 where

  step0 : p (s3) • K0246 ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00402.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0236 • p (s3)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00403.proved) Eq.refl Eq.refl

  proved : p (s3) • K0246 ≈ K0236 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00358 where

  step0 : p (s4) • K0246 ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00404.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0256 • p (s4)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00405.proved) Eq.refl Eq.refl

  proved : p (s4) • K0246 ≈ K0256 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00359 where

  step0 : p (s5) • K0246 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00406.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0245 • p (s5)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00407.proved) Eq.refl Eq.refl

  proved : p (s5) • K0246 ≈ K0245 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00360 where

  step0 : p (s6) • K0246 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00408.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0247 • p (s6)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00409.proved) Eq.refl Eq.refl

  proved : p (s6) • K0246 ≈ K0247 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00361 where

  step0 : p (s0) • K0247 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00410.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K1247 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00411.proved) Eq.refl Eq.refl

  proved : p (s0) • K0247 ≈ K1247 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00362 where

  step0 : p (s1) • K0247 ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00412.proved) Eq.refl Eq.refl

  step1 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0147 • p (s1)
  step2 = by-assoc-and (under (p (s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00413.proved) Eq.refl Eq.refl

  proved : p (s1) • K0247 ≈ K0147 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00363 where

  step0 : p (s2) • K0247 ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00414.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0347 • p (s2)
  step2 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00415.proved) Eq.refl Eq.refl

  proved : p (s2) • K0247 ≈ K0347 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00364 where

  step0 : p (s3) • K0247 ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00416.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0237 • p (s3)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00417.proved) Eq.refl Eq.refl

  proved : p (s3) • K0247 ≈ K0237 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00365 where

  step0 : p (s4) • K0247 ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00418.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0257 • p (s4)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00419.proved) Eq.refl Eq.refl

  proved : p (s4) • K0247 ≈ K0257 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00366 where

  step0 : p (s5) • K0247 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) PE00420.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1) ≈ K0247 • p (s5)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00421.proved) Eq.refl Eq.refl

  proved : p (s5) • K0247 ≈ K0247 • p (s5)
  proved = trans step0 (trans step1 step2)
