{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B002 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M5 ; M6 ; M7 ; X01 ; X02 ; X03 ; X04 ; X05 ; X06 ; X07 ; X12 ; X13 ; X14 ; X15 ; X16 ; X17 ; X23 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; m0 ; module Eq ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00001 ; module CM00002 ; module CM00003 ; module CM00004 ; module CM00005 ; module CM00006 ; module CM00010 ; module CM00011)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00009 ; module PE00010 ; module PE00011 ; module PE00012 ; module PE00013 ; module PE00014 ; module PE00017 ; module PE00018 ; module PE00019 ; module PE00020 ; module PE00021 ; module PE00022 ; module PE00025 ; module PE00026 ; module PE00027 ; module PE00028 ; module PE00029 ; module PE00030 ; module PE00033 ; module PE00034 ; module PE00035 ; module PE00036 ; module PE00037 ; module PE00038 ; module PE00041 ; module PE00042 ; module PE00043 ; module PE00044 ; module PE00045 ; module PE00046 ; module PE00047 ; module PE00048 ; module PE00049 ; module PE00050 ; module PE00051 ; module PE00052 ; module PE00053)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B002 using (module PE00054 ; module PE00055 ; module PE00056 ; module PE00057 ; module PE00058 ; module PE00059 ; module PE00060 ; module PE00061 ; module PE00062 ; module PE00063 ; module PE00064 ; module PE00065 ; module PE00066 ; module PE00067 ; module PE00068 ; module PE00069 ; module PE00070 ; module PE00071 ; module PE00072 ; module PE00073 ; module PE00074 ; module PE00075 ; module PE00076 ; module PE00077 ; module PE00078 ; module PE00079 ; module PE00080 ; module PE00081 ; module PE00082 ; module PE00083)

module MV00041 where

  step0 : p (s6) • M5 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00046.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00006.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ M5 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00046.proved) Eq.refl Eq.refl

  proved : p (s6) • M5 ≈ M5 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00042 where

  step0 : p (s0) • M6 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00047.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00010.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M6 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00048.proved) Eq.refl Eq.refl

  proved : p (s0) • M6 ≈ M6 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00043 where

  step0 : p (s1) • M6 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00049.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00001.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M6 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00049.proved) Eq.refl Eq.refl

  proved : p (s1) • M6 ≈ M6 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00044 where

  step0 : p (s2) • M6 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00050.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00002.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M6 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00050.proved) Eq.refl Eq.refl

  proved : p (s2) • M6 ≈ M6 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00045 where

  step0 : p (s3) • M6 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00051.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00003.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M6 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00051.proved) Eq.refl Eq.refl

  proved : p (s3) • M6 ≈ M6 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00046 where

  step0 : p (s4) • M6 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00052.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00004.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M6 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00052.proved) Eq.refl Eq.refl

  proved : p (s4) • M6 ≈ M6 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00047 where

  step0 : p (s5) • M6 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00053.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00005.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M5 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00053.proved) Eq.refl Eq.refl

  proved : p (s5) • M6 ≈ M5 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00048 where

  step0 : p (s6) • M6 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) PE00054.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) CM00006.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M7 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00054.proved) Eq.refl Eq.refl

  proved : p (s6) • M6 ≈ M7 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00049 where

  step0 : p (s0) • M7 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00055.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00011.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s6 • s5 • s4 • s3 • s2 • s1 • s2 • s3 • s4 • s5 • s6) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M7 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00056.proved) Eq.refl Eq.refl

  proved : p (s0) • M7 ≈ M7 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00050 where

  step0 : p (s1) • M7 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00057.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00001.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M7 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00057.proved) Eq.refl Eq.refl

  proved : p (s1) • M7 ≈ M7 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00051 where

  step0 : p (s2) • M7 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00058.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00002.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M7 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00058.proved) Eq.refl Eq.refl

  proved : p (s2) • M7 ≈ M7 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00052 where

  step0 : p (s3) • M7 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00059.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00003.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M7 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00059.proved) Eq.refl Eq.refl

  proved : p (s3) • M7 ≈ M7 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00053 where

  step0 : p (s4) • M7 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00060.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00004.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M7 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00060.proved) Eq.refl Eq.refl

  proved : p (s4) • M7 ≈ M7 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00054 where

  step0 : p (s5) • M7 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00061.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00005.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M7 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00061.proved) Eq.refl Eq.refl

  proved : p (s5) • M7 ≈ M7 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00055 where

  step0 : p (s6) • M7 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) PE00062.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0)) CM00006.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s2 • s3 • s4 • s5 • s6 • s5 • s4 • s3 • s2 • s1 • s0) ≈ M6 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00062.proved) Eq.refl Eq.refl

  proved : p (s6) • M7 ≈ M6 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00056 where

  proved : p (s1) • X01 ≈ X02 • p (s1)
  proved = by-assoc-and PE00009.proved Eq.refl Eq.refl

module MV00057 where

  proved : p (s2) • X01 ≈ X01 • p (s2)
  proved = by-assoc-and PE00010.proved Eq.refl Eq.refl

module MV00058 where

  proved : p (s3) • X01 ≈ X01 • p (s3)
  proved = by-assoc-and PE00011.proved Eq.refl Eq.refl

module MV00059 where

  proved : p (s4) • X01 ≈ X01 • p (s4)
  proved = by-assoc-and PE00012.proved Eq.refl Eq.refl

module MV00060 where

  proved : p (s5) • X01 ≈ X01 • p (s5)
  proved = by-assoc-and PE00013.proved Eq.refl Eq.refl

module MV00061 where

  proved : p (s6) • X01 ≈ X01 • p (s6)
  proved = by-assoc-and PE00014.proved Eq.refl Eq.refl

module MV00062 where

  proved : p (s0) • X02 ≈ X12 • p (s0)
  proved = by-assoc-and PE00063.proved Eq.refl Eq.refl

module MV00063 where

  proved : p (s1) • X02 ≈ X01 • p (s1)
  proved = by-assoc-and PE00017.proved Eq.refl Eq.refl

module MV00064 where

  proved : p (s2) • X02 ≈ X03 • p (s2)
  proved = by-assoc-and PE00018.proved Eq.refl Eq.refl

module MV00065 where

  proved : p (s3) • X02 ≈ X02 • p (s3)
  proved = by-assoc-and PE00019.proved Eq.refl Eq.refl

module MV00066 where

  proved : p (s4) • X02 ≈ X02 • p (s4)
  proved = by-assoc-and PE00020.proved Eq.refl Eq.refl

module MV00067 where

  proved : p (s5) • X02 ≈ X02 • p (s5)
  proved = by-assoc-and PE00021.proved Eq.refl Eq.refl

module MV00068 where

  proved : p (s6) • X02 ≈ X02 • p (s6)
  proved = by-assoc-and PE00022.proved Eq.refl Eq.refl

module MV00069 where

  proved : p (s0) • X03 ≈ X13 • p (s0)
  proved = by-assoc-and PE00064.proved Eq.refl Eq.refl

module MV00070 where

  proved : p (s1) • X03 ≈ X03 • p (s1)
  proved = by-assoc-and PE00025.proved Eq.refl Eq.refl

module MV00071 where

  proved : p (s2) • X03 ≈ X02 • p (s2)
  proved = by-assoc-and PE00026.proved Eq.refl Eq.refl

module MV00072 where

  proved : p (s3) • X03 ≈ X04 • p (s3)
  proved = by-assoc-and PE00027.proved Eq.refl Eq.refl

module MV00073 where

  proved : p (s4) • X03 ≈ X03 • p (s4)
  proved = by-assoc-and PE00028.proved Eq.refl Eq.refl

module MV00074 where

  proved : p (s5) • X03 ≈ X03 • p (s5)
  proved = by-assoc-and PE00029.proved Eq.refl Eq.refl

module MV00075 where

  proved : p (s6) • X03 ≈ X03 • p (s6)
  proved = by-assoc-and PE00030.proved Eq.refl Eq.refl

module MV00076 where

  proved : p (s0) • X04 ≈ X14 • p (s0)
  proved = by-assoc-and PE00065.proved Eq.refl Eq.refl

module MV00077 where

  proved : p (s1) • X04 ≈ X04 • p (s1)
  proved = by-assoc-and PE00033.proved Eq.refl Eq.refl

module MV00078 where

  proved : p (s2) • X04 ≈ X04 • p (s2)
  proved = by-assoc-and PE00034.proved Eq.refl Eq.refl

module MV00079 where

  proved : p (s3) • X04 ≈ X03 • p (s3)
  proved = by-assoc-and PE00035.proved Eq.refl Eq.refl

module MV00080 where

  proved : p (s4) • X04 ≈ X05 • p (s4)
  proved = by-assoc-and PE00036.proved Eq.refl Eq.refl

module MV00081 where

  proved : p (s5) • X04 ≈ X04 • p (s5)
  proved = by-assoc-and PE00037.proved Eq.refl Eq.refl

module MV00082 where

  proved : p (s6) • X04 ≈ X04 • p (s6)
  proved = by-assoc-and PE00038.proved Eq.refl Eq.refl

module MV00083 where

  proved : p (s0) • X05 ≈ X15 • p (s0)
  proved = by-assoc-and PE00066.proved Eq.refl Eq.refl

module MV00084 where

  proved : p (s1) • X05 ≈ X05 • p (s1)
  proved = by-assoc-and PE00041.proved Eq.refl Eq.refl

module MV00085 where

  proved : p (s2) • X05 ≈ X05 • p (s2)
  proved = by-assoc-and PE00042.proved Eq.refl Eq.refl

module MV00086 where

  proved : p (s3) • X05 ≈ X05 • p (s3)
  proved = by-assoc-and PE00043.proved Eq.refl Eq.refl

module MV00087 where

  proved : p (s4) • X05 ≈ X04 • p (s4)
  proved = by-assoc-and PE00044.proved Eq.refl Eq.refl

module MV00088 where

  proved : p (s5) • X05 ≈ X06 • p (s5)
  proved = by-assoc-and PE00045.proved Eq.refl Eq.refl

module MV00089 where

  proved : p (s6) • X05 ≈ X05 • p (s6)
  proved = by-assoc-and PE00046.proved Eq.refl Eq.refl

module MV00090 where

  proved : p (s0) • X06 ≈ X16 • p (s0)
  proved = by-assoc-and PE00067.proved Eq.refl Eq.refl

module MV00091 where

  proved : p (s1) • X06 ≈ X06 • p (s1)
  proved = by-assoc-and PE00049.proved Eq.refl Eq.refl

module MV00092 where

  proved : p (s2) • X06 ≈ X06 • p (s2)
  proved = by-assoc-and PE00050.proved Eq.refl Eq.refl

module MV00093 where

  proved : p (s3) • X06 ≈ X06 • p (s3)
  proved = by-assoc-and PE00051.proved Eq.refl Eq.refl

module MV00094 where

  proved : p (s4) • X06 ≈ X06 • p (s4)
  proved = by-assoc-and PE00052.proved Eq.refl Eq.refl

module MV00095 where

  proved : p (s5) • X06 ≈ X05 • p (s5)
  proved = by-assoc-and PE00053.proved Eq.refl Eq.refl

module MV00096 where

  proved : p (s6) • X06 ≈ X07 • p (s6)
  proved = by-assoc-and PE00054.proved Eq.refl Eq.refl

module MV00097 where

  proved : p (s0) • X07 ≈ X17 • p (s0)
  proved = by-assoc-and PE00068.proved Eq.refl Eq.refl

module MV00098 where

  proved : p (s1) • X07 ≈ X07 • p (s1)
  proved = by-assoc-and PE00057.proved Eq.refl Eq.refl

module MV00099 where

  proved : p (s2) • X07 ≈ X07 • p (s2)
  proved = by-assoc-and PE00058.proved Eq.refl Eq.refl

module MV00100 where

  proved : p (s3) • X07 ≈ X07 • p (s3)
  proved = by-assoc-and PE00059.proved Eq.refl Eq.refl

module MV00101 where

  proved : p (s4) • X07 ≈ X07 • p (s4)
  proved = by-assoc-and PE00060.proved Eq.refl Eq.refl

module MV00102 where

  proved : p (s5) • X07 ≈ X07 • p (s5)
  proved = by-assoc-and PE00061.proved Eq.refl Eq.refl

module MV00103 where

  proved : p (s6) • X07 ≈ X06 • p (s6)
  proved = by-assoc-and PE00062.proved Eq.refl Eq.refl

module MV00104 where

  proved : p (s0) • X12 ≈ X02 • p (s0)
  proved = by-assoc-and PE00069.proved Eq.refl Eq.refl

module MV00105 where

  proved : p (s2) • X12 ≈ X13 • p (s2)
  proved = by-assoc-and PE00070.proved Eq.refl Eq.refl

module MV00106 where

  proved : p (s3) • X12 ≈ X12 • p (s3)
  proved = by-assoc-and PE00071.proved Eq.refl Eq.refl

module MV00107 where

  proved : p (s4) • X12 ≈ X12 • p (s4)
  proved = by-assoc-and PE00072.proved Eq.refl Eq.refl

module MV00108 where

  proved : p (s5) • X12 ≈ X12 • p (s5)
  proved = by-assoc-and PE00073.proved Eq.refl Eq.refl

module MV00109 where

  proved : p (s6) • X12 ≈ X12 • p (s6)
  proved = by-assoc-and PE00074.proved Eq.refl Eq.refl

module MV00110 where

  proved : p (s0) • X13 ≈ X03 • p (s0)
  proved = by-assoc-and PE00075.proved Eq.refl Eq.refl

module MV00111 where

  proved : p (s1) • X13 ≈ X23 • p (s1)
  proved = by-assoc-and PE00076.proved Eq.refl Eq.refl

module MV00112 where

  proved : p (s2) • X13 ≈ X12 • p (s2)
  proved = by-assoc-and PE00077.proved Eq.refl Eq.refl

module MV00113 where

  proved : p (s3) • X13 ≈ X14 • p (s3)
  proved = by-assoc-and PE00078.proved Eq.refl Eq.refl

module MV00114 where

  proved : p (s4) • X13 ≈ X13 • p (s4)
  proved = by-assoc-and PE00079.proved Eq.refl Eq.refl

module MV00115 where

  proved : p (s5) • X13 ≈ X13 • p (s5)
  proved = by-assoc-and PE00080.proved Eq.refl Eq.refl

module MV00116 where

  proved : p (s6) • X13 ≈ X13 • p (s6)
  proved = by-assoc-and PE00081.proved Eq.refl Eq.refl

module MV00117 where

  proved : p (s0) • X14 ≈ X04 • p (s0)
  proved = by-assoc-and PE00082.proved Eq.refl Eq.refl

module MV00118 where

  proved : p (s1) • X14 ≈ X24 • p (s1)
  proved = by-assoc-and PE00083.proved Eq.refl Eq.refl
