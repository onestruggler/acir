{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B010 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0237 ; K0245 ; K0246 ; K0247 ; K0256 ; K0257 ; K1235 ; K1236 ; K1237 ; K1245 ; K1246 ; K1247 ; K1256 ; K1257 ; K1345 ; K1346 ; K1347 ; K1356 ; NK ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00012 ; module CM00013 ; module CM00014 ; module CM00015 ; module CM00016 ; module CM00017)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B011 using (module PE00600 ; module PE00601 ; module PE00602 ; module PE00603 ; module PE00604 ; module PE00605 ; module PE00606 ; module PE00607 ; module PE00608 ; module PE00609 ; module PE00610 ; module PE00611 ; module PE00612 ; module PE00613 ; module PE00614 ; module PE00615 ; module PE00616 ; module PE00617 ; module PE00618 ; module PE00619 ; module PE00620 ; module PE00621 ; module PE00622 ; module PE00623 ; module PE00624 ; module PE00625 ; module PE00626 ; module PE00627 ; module PE00628 ; module PE00629 ; module PE00630 ; module PE00631 ; module PE00632 ; module PE00633 ; module PE00634 ; module PE00635 ; module PE00636 ; module PE00637 ; module PE00638 ; module PE00639 ; module PE00640 ; module PE00641 ; module PE00642 ; module PE00643 ; module PE00644 ; module PE00645 ; module PE00646 ; module PE00647 ; module PE00648)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B012 using (module PE00649 ; module PE00650 ; module PE00651 ; module PE00652 ; module PE00653 ; module PE00654 ; module PE00655 ; module PE00656 ; module PE00657 ; module PE00658 ; module PE00659 ; module PE00660 ; module PE00661)

module MV00456 where

  step0 : p (s4) • K1236 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00600.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ K1236 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00601.proved) Eq.refl Eq.refl

  proved : p (s4) • K1236 ≈ K1236 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00457 where

  step0 : p (s5) • K1236 ≈ p (s0 • s1 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00602.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ K1235 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3) • NK) (ε) PE00603.proved) Eq.refl Eq.refl

  proved : p (s5) • K1236 ≈ K1235 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00458 where

  step0 : p (s6) • K1236 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00604.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ K1237 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00605.proved) Eq.refl Eq.refl

  proved : p (s6) • K1236 ≈ K1237 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00459 where

  step0 : p (s0) • K1237 ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00606.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ K0237 • p (s0)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00607.proved) Eq.refl Eq.refl

  proved : p (s0) • K1237 ≈ K0237 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00460 where

  step0 : p (s3) • K1237 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00608.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ K1247 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00609.proved) Eq.refl Eq.refl

  proved : p (s3) • K1237 ≈ K1247 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00461 where

  step0 : p (s4) • K1237 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00610.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ K1237 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00611.proved) Eq.refl Eq.refl

  proved : p (s4) • K1237 ≈ K1237 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00462 where

  step0 : p (s5) • K1237 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00612.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ K1237 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00613.proved) Eq.refl Eq.refl

  proved : p (s5) • K1237 ≈ K1237 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00463 where

  step0 : p (s6) • K1237 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00614.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ K1236 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00615.proved) Eq.refl Eq.refl

  proved : p (s6) • K1237 ≈ K1236 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00464 where

  step0 : p (s0) • K1245 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00616.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K0245 • p (s0)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00617.proved) Eq.refl Eq.refl

  proved : p (s0) • K1245 ≈ K0245 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00465 where

  step0 : p (s2) • K1245 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00618.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1345 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00619.proved) Eq.refl Eq.refl

  proved : p (s2) • K1245 ≈ K1345 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00466 where

  step0 : p (s3) • K1245 ≈ p (s0 • s1 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00620.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1235 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3) • NK) (ε) PE00621.proved) Eq.refl Eq.refl

  proved : p (s3) • K1245 ≈ K1235 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00467 where

  step0 : p (s5) • K1245 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00622.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1246 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00623.proved) Eq.refl Eq.refl

  proved : p (s5) • K1245 ≈ K1246 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00468 where

  step0 : p (s6) • K1245 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00624.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1245 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00625.proved) Eq.refl Eq.refl

  proved : p (s6) • K1245 ≈ K1245 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00469 where

  step0 : p (s0) • K1246 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00626.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K0246 • p (s0)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00627.proved) Eq.refl Eq.refl

  proved : p (s0) • K1246 ≈ K0246 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00470 where

  step0 : p (s2) • K1246 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00628.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1346 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00629.proved) Eq.refl Eq.refl

  proved : p (s2) • K1246 ≈ K1346 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00471 where

  step0 : p (s3) • K1246 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00630.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1236 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00631.proved) Eq.refl Eq.refl

  proved : p (s3) • K1246 ≈ K1236 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00472 where

  step0 : p (s4) • K1246 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00632.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1256 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00633.proved) Eq.refl Eq.refl

  proved : p (s4) • K1246 ≈ K1256 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00473 where

  step0 : p (s5) • K1246 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00634.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1245 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00635.proved) Eq.refl Eq.refl

  proved : p (s5) • K1246 ≈ K1245 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00474 where

  step0 : p (s6) • K1246 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00636.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1247 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00637.proved) Eq.refl Eq.refl

  proved : p (s6) • K1246 ≈ K1247 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00475 where

  step0 : p (s0) • K1247 ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00638.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K0247 • p (s0)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00639.proved) Eq.refl Eq.refl

  proved : p (s0) • K1247 ≈ K0247 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00476 where

  step0 : p (s2) • K1247 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00640.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1347 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00641.proved) Eq.refl Eq.refl

  proved : p (s2) • K1247 ≈ K1347 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00477 where

  step0 : p (s3) • K1247 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00642.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1237 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00643.proved) Eq.refl Eq.refl

  proved : p (s3) • K1247 ≈ K1237 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00478 where

  step0 : p (s4) • K1247 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00644.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1257 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00645.proved) Eq.refl Eq.refl

  proved : p (s4) • K1247 ≈ K1257 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00479 where

  step0 : p (s5) • K1247 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00646.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1247 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00647.proved) Eq.refl Eq.refl

  proved : p (s5) • K1247 ≈ K1247 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00480 where

  step0 : p (s6) • K1247 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) PE00648.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s0) ≈ K1246 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00649.proved) Eq.refl Eq.refl

  proved : p (s6) • K1247 ≈ K1246 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00481 where

  step0 : p (s0) • K1256 ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00650.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ K0256 • p (s0)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00651.proved) Eq.refl Eq.refl

  proved : p (s0) • K1256 ≈ K0256 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00482 where

  step0 : p (s2) • K1256 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00652.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ K1356 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00653.proved) Eq.refl Eq.refl

  proved : p (s2) • K1256 ≈ K1356 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00483 where

  step0 : p (s3) • K1256 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00654.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ K1256 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00655.proved) Eq.refl Eq.refl

  proved : p (s3) • K1256 ≈ K1256 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00484 where

  step0 : p (s4) • K1256 ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00656.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ K1246 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00657.proved) Eq.refl Eq.refl

  proved : p (s4) • K1256 ≈ K1246 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00485 where

  step0 : p (s6) • K1256 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00658.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ K1257 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00659.proved) Eq.refl Eq.refl

  proved : p (s6) • K1256 ≈ K1257 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00486 where

  step0 : p (s0) • K1257 ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00660.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ K0257 • p (s0)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00661.proved) Eq.refl Eq.refl

  proved : p (s0) • K1257 ≈ K0257 • p (s0)
  proved = trans step0 (trans step1 step2)
