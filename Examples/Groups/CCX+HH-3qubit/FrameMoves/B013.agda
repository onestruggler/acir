{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B013 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0467 ; K0567 ; K1345 ; K1346 ; K1347 ; K1357 ; K1367 ; K1456 ; K1457 ; K1467 ; K1567 ; K2345 ; K2346 ; K2347 ; K2356 ; K2467 ; NK ; _•_ ; _≈_ ; by-assoc-and ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00012 ; module CM00013 ; module CM00014 ; module CM00015 ; module CM00016 ; module CM00017 ; module CM00018)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B014 using (module PE00768 ; module PE00769 ; module PE00770 ; module PE00771 ; module PE00772 ; module PE00773 ; module PE00774 ; module PE00775 ; module PE00776 ; module PE00777 ; module PE00778 ; module PE00779 ; module PE00780 ; module PE00781 ; module PE00782 ; module PE00783 ; module PE00784 ; module PE00785 ; module PE00786 ; module PE00787 ; module PE00788 ; module PE00789 ; module PE00792 ; module PE00793 ; module PE00794)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B015 using (module PE00795 ; module PE00796 ; module PE00797 ; module PE00800 ; module PE00801 ; module PE00802 ; module PE00803 ; module PE00804 ; module PE00805 ; module PE00806 ; module PE00807 ; module PE00808 ; module PE00809 ; module PE00810 ; module PE00811 ; module PE00812 ; module PE00813 ; module PE00814 ; module PE00815 ; module PE00816 ; module PE00817 ; module PE00818 ; module PE00819)

module MV00540 where

  step0 : p (s2) • K1457 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) PE00768.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) CM00018.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ K1457 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00769.proved) Eq.refl Eq.refl

  proved : p (s2) • K1457 ≈ K1457 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00541 where

  step0 : p (s3) • K1457 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) PE00770.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ K1357 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00771.proved) Eq.refl Eq.refl

  proved : p (s3) • K1457 ≈ K1357 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00542 where

  step0 : p (s5) • K1457 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) PE00772.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ K1467 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00773.proved) Eq.refl Eq.refl

  proved : p (s5) • K1457 ≈ K1467 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00543 where

  step0 : p (s6) • K1457 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) PE00774.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ K1456 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00775.proved) Eq.refl Eq.refl

  proved : p (s6) • K1457 ≈ K1456 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00544 where

  step0 : p (s0) • K1467 ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) PE00776.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ K0467 • p (s0)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00777.proved) Eq.refl Eq.refl

  proved : p (s0) • K1467 ≈ K0467 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00545 where

  step0 : p (s1) • K1467 ≈ p (s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) PE00778.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ K2467 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00779.proved) Eq.refl Eq.refl

  proved : p (s1) • K1467 ≈ K2467 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00546 where

  step0 : p (s2) • K1467 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) PE00780.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ K1467 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00781.proved) Eq.refl Eq.refl

  proved : p (s2) • K1467 ≈ K1467 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00547 where

  step0 : p (s3) • K1467 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) PE00782.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ K1367 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00783.proved) Eq.refl Eq.refl

  proved : p (s3) • K1467 ≈ K1367 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00548 where

  step0 : p (s4) • K1467 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) PE00784.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ K1567 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00785.proved) Eq.refl Eq.refl

  proved : p (s4) • K1467 ≈ K1567 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00549 where

  step0 : p (s5) • K1467 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) PE00786.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s2 • s1 • s0) ≈ K1457 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00787.proved) Eq.refl Eq.refl

  proved : p (s5) • K1467 ≈ K1457 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00550 where

  step0 : p (s0) • K1567 ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00788.proved) Eq.refl Eq.refl

  step1 : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (ε) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00012.proved) Eq.refl Eq.refl

  step2 : p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (ε) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ K0567 • p (s0)
  step2 = by-assoc-and (under (p (s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00789.proved) Eq.refl Eq.refl

  proved : p (s0) • K1567 ≈ K0567 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00552 where

  step0 : p (s2) • K1567 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00792.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ K1567 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00793.proved) Eq.refl Eq.refl

  proved : p (s2) • K1567 ≈ K1567 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00553 where

  step0 : p (s3) • K1567 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00794.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ K1567 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00795.proved) Eq.refl Eq.refl

  proved : p (s3) • K1567 ≈ K1567 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00554 where

  step0 : p (s4) • K1567 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00796.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ K1467 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00797.proved) Eq.refl Eq.refl

  proved : p (s4) • K1567 ≈ K1467 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00556 where

  step0 : p (s1) • K2345 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE00800.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K1345 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00801.proved) Eq.refl Eq.refl

  proved : p (s1) • K2345 ≈ K1345 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00557 where

  step0 : p (s5) • K2345 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE00802.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K2346 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00803.proved) Eq.refl Eq.refl

  proved : p (s5) • K2345 ≈ K2346 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00558 where

  step0 : p (s6) • K2345 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE00804.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K2345 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00805.proved) Eq.refl Eq.refl

  proved : p (s6) • K2345 ≈ K2345 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00559 where

  step0 : p (s0) • K2346 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE00806.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K2346 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00807.proved) Eq.refl Eq.refl

  proved : p (s0) • K2346 ≈ K2346 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00560 where

  step0 : p (s1) • K2346 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE00808.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s5 • s4 • s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00016.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s5 • s4 • s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K1346 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00809.proved) Eq.refl Eq.refl

  proved : p (s1) • K2346 ≈ K1346 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00561 where

  step0 : p (s4) • K2346 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE00810.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • p (s4) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00013.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK • p (s4) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K2356 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s4 • s3 • s2 • s3 • s4 • s5 • s4 • s3) • NK) (ε) PE00811.proved) Eq.refl Eq.refl

  proved : p (s4) • K2346 ≈ K2356 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00562 where

  step0 : p (s5) • K2346 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE00812.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • p (s5) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00014.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s5) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K2345 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK) (ε) PE00813.proved) Eq.refl Eq.refl

  proved : p (s5) • K2346 ≈ K2345 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00563 where

  step0 : p (s6) • K2346 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE00814.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6) • NK • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00015.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6) • p (s3 • s4 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K2347 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00815.proved) Eq.refl Eq.refl

  proved : p (s6) • K2346 ≈ K2347 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00564 where

  step0 : p (s0) • K2347 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE00816.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K2347 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00817.proved) Eq.refl Eq.refl

  proved : p (s0) • K2347 ≈ K2347 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00565 where

  step0 : p (s1) • K2347 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) PE00818.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • p (s6 • s5 • s4 • s5 • s6) • NK • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3)) (p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)) CM00017.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK • p (s6 • s5 • s4 • s5 • s6) • p (s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K1347 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3) • NK) (ε) PE00819.proved) Eq.refl Eq.refl

  proved : p (s1) • K2347 ≈ K1347 • p (s1)
  proved = trans step0 (trans step1 step2)
