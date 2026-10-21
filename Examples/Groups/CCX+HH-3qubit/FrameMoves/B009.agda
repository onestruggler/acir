{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B009 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0234 ; K0235 ; K0236 ; K0356 ; K0357 ; K0367 ; K0456 ; K0457 ; K0467 ; K0567 ; K1234 ; K1235 ; K1236 ; K1245 ; K1246 ; K1457 ; K1467 ; NK ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00012 ; module CM00013 ; module CM00014 ; module CM00015 ; module CM00016 ; module CM00017 ; module CM00018)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B009 using (module PE00540 ; module PE00541)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B010 using (module PE00542 ; module PE00543 ; module PE00544 ; module PE00545 ; module PE00546 ; module PE00547 ; module PE00548 ; module PE00549 ; module PE00550 ; module PE00551 ; module PE00552 ; module PE00553 ; module PE00554 ; module PE00555 ; module PE00556 ; module PE00557 ; module PE00558 ; module PE00559 ; module PE00560 ; module PE00561 ; module PE00562 ; module PE00563 ; module PE00566 ; module PE00567 ; module PE00570 ; module PE00571 ; module PE00572 ; module PE00573 ; module PE00574 ; module PE00575 ; module PE00576 ; module PE00577 ; module PE00578 ; module PE00579 ; module PE00580 ; module PE00581 ; module PE00582 ; module PE00583 ; module PE00584 ; module PE00585 ; module PE00586 ; module PE00587 ; module PE00588 ; module PE00589 ; module PE00590 ; module PE00591 ; module PE00592 ; module PE00593 ; module PE00594)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B011 using (module PE00595 ; module PE00596 ; module PE00597 ; module PE00598 ; module PE00599)

module MV00426 where

  step0 : p (s3) • K0456 ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00540.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0356 • p (s3)
  step2 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00541.proved) Eq.refl Eq.refl

  proved : p (s3) • K0456 ≈ K0356 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00427 where

  step0 : p (s6) • K0456 ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00542.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0457 • p (s6)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00543.proved) Eq.refl Eq.refl

  proved : p (s6) • K0456 ≈ K0457 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00428 where

  step0 : p (s0) • K0457 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00544.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K1457 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00545.proved) Eq.refl Eq.refl

  proved : p (s0) • K0457 ≈ K1457 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00429 where

  step0 : p (s1) • K0457 ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00546.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0457 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00547.proved) Eq.refl Eq.refl

  proved : p (s1) • K0457 ≈ K0457 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00430 where

  step0 : p (s2) • K0457 ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00548.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00018.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0457 • p (s2)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00549.proved) Eq.refl Eq.refl

  proved : p (s2) • K0457 ≈ K0457 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00431 where

  step0 : p (s3) • K0457 ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00550.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0357 • p (s3)
  step2 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00551.proved) Eq.refl Eq.refl

  proved : p (s3) • K0457 ≈ K0357 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00432 where

  step0 : p (s5) • K0457 ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00552.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0467 • p (s5)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00553.proved) Eq.refl Eq.refl

  proved : p (s5) • K0457 ≈ K0467 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00433 where

  step0 : p (s6) • K0457 ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00554.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0456 • p (s6)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00555.proved) Eq.refl Eq.refl

  proved : p (s6) • K0457 ≈ K0456 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00434 where

  step0 : p (s0) • K0467 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00556.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K1467 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00557.proved) Eq.refl Eq.refl

  proved : p (s0) • K0467 ≈ K1467 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00435 where

  step0 : p (s1) • K0467 ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00558.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0467 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00559.proved) Eq.refl Eq.refl

  proved : p (s1) • K0467 ≈ K0467 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00436 where

  step0 : p (s2) • K0467 ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00560.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0467 • p (s2)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00561.proved) Eq.refl Eq.refl

  proved : p (s2) • K0467 ≈ K0467 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00437 where

  step0 : p (s3) • K0467 ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00562.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0367 • p (s3)
  step2 = by-assoc-and (under (p (s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00563.proved) Eq.refl Eq.refl

  proved : p (s3) • K0467 ≈ K0367 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00439 where

  step0 : p (s5) • K0467 ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) PE00566.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1) ≈ K0457 • p (s5)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00567.proved) Eq.refl Eq.refl

  proved : p (s5) • K0467 ≈ K0457 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00441 where

  step0 : p (s1) • K0567 ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) PE00570.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ K0567 • p (s1)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00571.proved) Eq.refl Eq.refl

  proved : p (s1) • K0567 ≈ K0567 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00442 where

  step0 : p (s2) • K0567 ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) PE00572.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ K0567 • p (s2)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00573.proved) Eq.refl Eq.refl

  proved : p (s2) • K0567 ≈ K0567 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00443 where

  step0 : p (s3) • K0567 ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) PE00574.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ K0567 • p (s3)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00575.proved) Eq.refl Eq.refl

  proved : p (s3) • K0567 ≈ K0567 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00444 where

  step0 : p (s4) • K0567 ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) PE00576.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1) ≈ K0467 • p (s4)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00577.proved) Eq.refl Eq.refl

  proved : p (s4) • K0567 ≈ K0467 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00445 where

  step0 : p (s0) • K1234 ≈ p (s1 • s2 • s3) • p (ε) • NK • p (s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2 • s1 • s0)) PE00578.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3) • p (ε) • NK • p (s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3) • NK • p (ε) • p (s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s1 • s2 • s3)) (p (s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3) • NK • p (ε) • p (s3 • s2 • s1 • s0) ≈ K0234 • p (s0)
  step2 = by-assoc-and (under (p (s1 • s2 • s3) • NK) (ε) PE00579.proved) Eq.refl Eq.refl

  proved : p (s0) • K1234 ≈ K0234 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00446 where

  step0 : p (s4) • K1234 ≈ p (s0 • s1 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2 • s1 • s0)) PE00580.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3)) (p (s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s2 • s1 • s0) ≈ K1235 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3) • NK) (ε) PE00581.proved) Eq.refl Eq.refl

  proved : p (s4) • K1234 ≈ K1235 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00447 where

  step0 : p (s5) • K1234 ≈ p (s0 • s1 • s2 • s3) • p (s5) • NK • p (s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2 • s1 • s0)) PE00582.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3) • p (s5) • NK • p (s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3) • NK • p (s5) • p (s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3)) (p (s3 • s2 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3) • NK • p (s5) • p (s3 • s2 • s1 • s0) ≈ K1234 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3) • NK) (ε) PE00583.proved) Eq.refl Eq.refl

  proved : p (s5) • K1234 ≈ K1234 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00448 where

  step0 : p (s6) • K1234 ≈ p (s0 • s1 • s2 • s3) • p (s6) • NK • p (s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s2 • s1 • s0)) PE00584.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3) • p (s6) • NK • p (s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3) • NK • p (s6) • p (s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3)) (p (s3 • s2 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3) • NK • p (s6) • p (s3 • s2 • s1 • s0) ≈ K1234 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3) • NK) (ε) PE00585.proved) Eq.refl Eq.refl

  proved : p (s6) • K1234 ≈ K1234 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00449 where

  step0 : p (s0) • K1235 ≈ p (s1 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1 • s0)) PE00586.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ K0235 • p (s0)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3) • NK) (ε) PE00587.proved) Eq.refl Eq.refl

  proved : p (s0) • K1235 ≈ K0235 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00450 where

  step0 : p (s3) • K1235 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1 • s0)) PE00588.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ K1245 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00589.proved) Eq.refl Eq.refl

  proved : p (s3) • K1235 ≈ K1245 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00451 where

  step0 : p (s4) • K1235 ≈ p (s0 • s1 • s2 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1 • s0)) PE00590.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3)) (p (s3 • s4 • s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ K1234 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3) • NK) (ε) PE00591.proved) Eq.refl Eq.refl

  proved : p (s4) • K1235 ≈ K1234 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00452 where

  step0 : p (s5) • K1235 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1 • s0)) PE00592.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ K1236 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00593.proved) Eq.refl Eq.refl

  proved : p (s5) • K1235 ≈ K1236 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00453 where

  step0 : p (s6) • K1235 ≈ p (s0 • s1 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s1 • s0)) PE00594.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s1 • s0) ≈ K1235 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3) • NK) (ε) PE00595.proved) Eq.refl Eq.refl

  proved : p (s6) • K1235 ≈ K1235 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00454 where

  step0 : p (s0) • K1236 ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00596.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ K0236 • p (s0)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00597.proved) Eq.refl Eq.refl

  proved : p (s0) • K1236 ≈ K0236 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00455 where

  step0 : p (s3) • K1236 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00598.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ K1246 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00599.proved) Eq.refl Eq.refl

  proved : p (s3) • K1236 ≈ K1246 • p (s3)
  proved = trans step0 (trans step1 step2)
