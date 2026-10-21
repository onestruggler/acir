{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M1 ; M2 ; M3 ; M4 ; M5 ; M6 ; _•_ ; _≈_ ; by-assoc-and ; m0 ; module Eq ; move-compose ; p ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; trans ; under ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameCommutations.B000 using (module CM00000 ; module CM00001 ; module CM00002 ; module CM00003 ; module CM00004 ; module CM00005 ; module CM00006 ; module CM00007 ; module CM00008 ; module CM00009)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00008)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B000 using (module PE00004)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00000 ; module PE00002 ; module PE00003 ; module PE00005 ; module PE00006 ; module PE00007 ; module PE00008 ; module PE00010 ; module PE00011 ; module PE00012 ; module PE00013 ; module PE00014 ; module PE00015 ; module PE00016 ; module PE00017 ; module PE00018 ; module PE00019 ; module PE00020 ; module PE00021 ; module PE00022 ; module PE00023 ; module PE00024 ; module PE00025 ; module PE00026 ; module PE00027 ; module PE00028 ; module PE00029 ; module PE00030 ; module PE00031 ; module PE00032 ; module PE00033 ; module PE00034 ; module PE00035 ; module PE00036 ; module PE00037 ; module PE00038 ; module PE00039 ; module PE00040 ; module PE00041 ; module PE00042 ; module PE00043 ; module PE00044 ; module PE00045)

module MV00016 where

  step0 : p (s2) • M2 ≈ p (s0 • s1 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s0)) PE00018.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0)) (p (s0 • s1 • s0)) CM00002.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s0) ≈ M3 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0) • m0) (ε) PE00018.proved) Eq.refl Eq.refl

  proved : p (s2) • M2 ≈ M3 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00630 where

  proved : p (s2 • s1 • s0) • M0 ≈ M3 • p (s2 • s1 • s0)
  proved = by-assoc-and (move-compose MV00016.proved (move-compose MV00008.proved (MV00000.proved))) Eq.refl Eq.refl

module MV00001 where

  step0 : p (s1) • M0 ≈ p (ε) • p (s1) • m0 • p (ε)
  step0 = by-assoc-and (under (ε) (m0 • p (ε)) PE00002.proved) Eq.refl Eq.refl

  step1 : p (ε) • p (s1) • m0 • p (ε) ≈ p (ε) • m0 • p (s1) • p (ε)
  step1 = by-assoc-and (under (p (ε)) (p (ε)) CM00001.proved) Eq.refl Eq.refl

  step2 : p (ε) • m0 • p (s1) • p (ε) ≈ M0 • p (s1)
  step2 = by-assoc-and (under (p (ε) • m0) (ε) PE00002.proved) Eq.refl Eq.refl

  proved : p (s1) • M0 ≈ M0 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00002 where

  step0 : p (s2) • M0 ≈ p (ε) • p (s2) • m0 • p (ε)
  step0 = by-assoc-and (under (ε) (m0 • p (ε)) PE00003.proved) Eq.refl Eq.refl

  step1 : p (ε) • p (s2) • m0 • p (ε) ≈ p (ε) • m0 • p (s2) • p (ε)
  step1 = by-assoc-and (under (p (ε)) (p (ε)) CM00002.proved) Eq.refl Eq.refl

  step2 : p (ε) • m0 • p (s2) • p (ε) ≈ M0 • p (s2)
  step2 = by-assoc-and (under (p (ε) • m0) (ε) PE00003.proved) Eq.refl Eq.refl

  proved : p (s2) • M0 ≈ M0 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00003 where

  step0 : p (s3) • M0 ≈ p (ε) • p (s3) • m0 • p (ε)
  step0 = by-assoc-and (under (ε) (m0 • p (ε)) PE00004.proved) Eq.refl Eq.refl

  step1 : p (ε) • p (s3) • m0 • p (ε) ≈ p (ε) • m0 • p (s3) • p (ε)
  step1 = by-assoc-and (under (p (ε)) (p (ε)) CM00003.proved) Eq.refl Eq.refl

  step2 : p (ε) • m0 • p (s3) • p (ε) ≈ M0 • p (s3)
  step2 = by-assoc-and (under (p (ε) • m0) (ε) PE00004.proved) Eq.refl Eq.refl

  proved : p (s3) • M0 ≈ M0 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00004 where

  step0 : p (s4) • M0 ≈ p (ε) • p (s4) • m0 • p (ε)
  step0 = by-assoc-and (under (ε) (m0 • p (ε)) PE00005.proved) Eq.refl Eq.refl

  step1 : p (ε) • p (s4) • m0 • p (ε) ≈ p (ε) • m0 • p (s4) • p (ε)
  step1 = by-assoc-and (under (p (ε)) (p (ε)) CM00004.proved) Eq.refl Eq.refl

  step2 : p (ε) • m0 • p (s4) • p (ε) ≈ M0 • p (s4)
  step2 = by-assoc-and (under (p (ε) • m0) (ε) PE00005.proved) Eq.refl Eq.refl

  proved : p (s4) • M0 ≈ M0 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00005 where

  step0 : p (s5) • M0 ≈ p (ε) • p (s5) • m0 • p (ε)
  step0 = by-assoc-and (under (ε) (m0 • p (ε)) PE00006.proved) Eq.refl Eq.refl

  step1 : p (ε) • p (s5) • m0 • p (ε) ≈ p (ε) • m0 • p (s5) • p (ε)
  step1 = by-assoc-and (under (p (ε)) (p (ε)) CM00005.proved) Eq.refl Eq.refl

  step2 : p (ε) • m0 • p (s5) • p (ε) ≈ M0 • p (s5)
  step2 = by-assoc-and (under (p (ε) • m0) (ε) PE00006.proved) Eq.refl Eq.refl

  proved : p (s5) • M0 ≈ M0 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00006 where

  step0 : p (s6) • M0 ≈ p (ε) • p (s6) • m0 • p (ε)
  step0 = by-assoc-and (under (ε) (m0 • p (ε)) PE00007.proved) Eq.refl Eq.refl

  step1 : p (ε) • p (s6) • m0 • p (ε) ≈ p (ε) • m0 • p (s6) • p (ε)
  step1 = by-assoc-and (under (p (ε)) (p (ε)) CM00006.proved) Eq.refl Eq.refl

  step2 : p (ε) • m0 • p (s6) • p (ε) ≈ M0 • p (s6)
  step2 = by-assoc-and (under (p (ε) • m0) (ε) PE00007.proved) Eq.refl Eq.refl

  proved : p (s6) • M0 ≈ M0 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00024 where

  step0 : p (s3) • M3 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s1 • s0)) PE00027.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s1 • s0)) CM00003.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s2 • s1 • s0) ≈ M4 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0) (ε) PE00027.proved) Eq.refl Eq.refl

  proved : p (s3) • M3 ≈ M4 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00631 where

  proved : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • M0 ≈ M4 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  proved = by-assoc-and (move-compose MV00024.proved (move-compose MV00016.proved (move-compose MV00008.proved (move-compose MV00000.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00001.proved (move-compose MV00005.proved (move-compose MV00004.proved (move-compose MV00003.proved (move-compose MV00002.proved (move-compose MV00006.proved (move-compose MV00005.proved (move-compose MV00004.proved (MV00003.proved)))))))))))))))) Eq.refl Eq.refl

module MV00007 where

  step0 : p (s0) • M1 ≈ p (ε) • p (ε) • m0 • p (s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0)) PE00008.proved) Eq.refl Eq.refl

  step1 : p (ε) • p (ε) • m0 • p (s0) ≈ p (ε) • m0 • p (ε) • p (s0)
  step1 = by-assoc-and (under (p (ε)) (p (s0)) CM00000.proved) Eq.refl Eq.refl

  step2 : p (ε) • m0 • p (ε) • p (s0) ≈ M0 • p (s0)
  step2 = by-assoc-and (under (p (ε) • m0) (ε) PE00000.proved) Eq.refl Eq.refl

  proved : p (s0) • M1 ≈ M0 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00009 where

  step0 : p (s2) • M1 ≈ p (s0) • p (s2) • m0 • p (s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0)) PE00010.proved) Eq.refl Eq.refl

  step1 : p (s0) • p (s2) • m0 • p (s0) ≈ p (s0) • m0 • p (s2) • p (s0)
  step1 = by-assoc-and (under (p (s0)) (p (s0)) CM00002.proved) Eq.refl Eq.refl

  step2 : p (s0) • m0 • p (s2) • p (s0) ≈ M1 • p (s2)
  step2 = by-assoc-and (under (p (s0) • m0) (ε) PE00010.proved) Eq.refl Eq.refl

  proved : p (s2) • M1 ≈ M1 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00010 where

  step0 : p (s3) • M1 ≈ p (s0) • p (s3) • m0 • p (s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0)) PE00011.proved) Eq.refl Eq.refl

  step1 : p (s0) • p (s3) • m0 • p (s0) ≈ p (s0) • m0 • p (s3) • p (s0)
  step1 = by-assoc-and (under (p (s0)) (p (s0)) CM00003.proved) Eq.refl Eq.refl

  step2 : p (s0) • m0 • p (s3) • p (s0) ≈ M1 • p (s3)
  step2 = by-assoc-and (under (p (s0) • m0) (ε) PE00011.proved) Eq.refl Eq.refl

  proved : p (s3) • M1 ≈ M1 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00011 where

  step0 : p (s4) • M1 ≈ p (s0) • p (s4) • m0 • p (s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0)) PE00012.proved) Eq.refl Eq.refl

  step1 : p (s0) • p (s4) • m0 • p (s0) ≈ p (s0) • m0 • p (s4) • p (s0)
  step1 = by-assoc-and (under (p (s0)) (p (s0)) CM00004.proved) Eq.refl Eq.refl

  step2 : p (s0) • m0 • p (s4) • p (s0) ≈ M1 • p (s4)
  step2 = by-assoc-and (under (p (s0) • m0) (ε) PE00012.proved) Eq.refl Eq.refl

  proved : p (s4) • M1 ≈ M1 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00012 where

  step0 : p (s5) • M1 ≈ p (s0) • p (s5) • m0 • p (s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0)) PE00013.proved) Eq.refl Eq.refl

  step1 : p (s0) • p (s5) • m0 • p (s0) ≈ p (s0) • m0 • p (s5) • p (s0)
  step1 = by-assoc-and (under (p (s0)) (p (s0)) CM00005.proved) Eq.refl Eq.refl

  step2 : p (s0) • m0 • p (s5) • p (s0) ≈ M1 • p (s5)
  step2 = by-assoc-and (under (p (s0) • m0) (ε) PE00013.proved) Eq.refl Eq.refl

  proved : p (s5) • M1 ≈ M1 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00013 where

  step0 : p (s6) • M1 ≈ p (s0) • p (s6) • m0 • p (s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0)) PE00014.proved) Eq.refl Eq.refl

  step1 : p (s0) • p (s6) • m0 • p (s0) ≈ p (s0) • m0 • p (s6) • p (s0)
  step1 = by-assoc-and (under (p (s0)) (p (s0)) CM00006.proved) Eq.refl Eq.refl

  step2 : p (s0) • m0 • p (s6) • p (s0) ≈ M1 • p (s6)
  step2 = by-assoc-and (under (p (s0) • m0) (ε) PE00014.proved) Eq.refl Eq.refl

  proved : p (s6) • M1 ≈ M1 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00014 where

  step0 : p (s0) • M2 ≈ p (s0 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s0)) PE00015.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s0) ≈ p (s0 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0)) (p (s0 • s1 • s0)) CM00001.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s0) ≈ M2 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s0) • m0) (ε) PE00016.proved) Eq.refl Eq.refl

  proved : p (s0) • M2 ≈ M2 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00015 where

  step0 : p (s1) • M2 ≈ p (s0) • p (s1) • m0 • p (s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s0)) PE00017.proved) Eq.refl Eq.refl

  step1 : p (s0) • p (s1) • m0 • p (s0 • s1 • s0) ≈ p (s0) • m0 • p (s1) • p (s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0)) (p (s0 • s1 • s0)) CM00001.proved) Eq.refl Eq.refl

  step2 : p (s0) • m0 • p (s1) • p (s0 • s1 • s0) ≈ M1 • p (s1)
  step2 = by-assoc-and (under (p (s0) • m0) (ε) PE00017.proved) Eq.refl Eq.refl

  proved : p (s1) • M2 ≈ M1 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00017 where

  step0 : p (s3) • M2 ≈ p (s0 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s0)) PE00019.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s0) ≈ p (s0 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0)) (p (s0 • s1 • s0)) CM00003.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s0) ≈ M2 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s0) • m0) (ε) PE00019.proved) Eq.refl Eq.refl

  proved : p (s3) • M2 ≈ M2 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00018 where

  step0 : p (s4) • M2 ≈ p (s0 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s0)) PE00020.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s0) ≈ p (s0 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0)) (p (s0 • s1 • s0)) CM00004.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s0) ≈ M2 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s0) • m0) (ε) PE00020.proved) Eq.refl Eq.refl

  proved : p (s4) • M2 ≈ M2 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00019 where

  step0 : p (s5) • M2 ≈ p (s0 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s0)) PE00021.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s0) ≈ p (s0 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0)) (p (s0 • s1 • s0)) CM00005.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s0) ≈ M2 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s0) • m0) (ε) PE00021.proved) Eq.refl Eq.refl

  proved : p (s5) • M2 ≈ M2 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00020 where

  step0 : p (s6) • M2 ≈ p (s0 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s0)) PE00022.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s0) ≈ p (s0 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0)) (p (s0 • s1 • s0)) CM00006.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s0) ≈ M2 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s0) • m0) (ε) PE00022.proved) Eq.refl Eq.refl

  proved : p (s6) • M2 ≈ M2 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00021 where

  step0 : p (s0) • M3 ≈ p (s0 • s1 • s2 • s1 • s0) • p (s2 • s1 • s2) • m0 • p (s0 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s1 • s0)) PE00023.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s0) • p (s2 • s1 • s2) • m0 • p (s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0) • m0 • p (s2 • s1 • s2) • p (s0 • s1 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s1 • s0)) CM00007.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s0) • m0 • p (s2 • s1 • s2) • p (s0 • s1 • s2 • s1 • s0) ≈ M3 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0) • m0) (ε) PE00024.proved) Eq.refl Eq.refl

  proved : p (s0) • M3 ≈ M3 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00022 where

  step0 : p (s1) • M3 ≈ p (s0 • s1 • s2 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s1 • s0)) PE00025.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s1 • s0)) CM00001.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s2 • s1 • s0) ≈ M3 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0) • m0) (ε) PE00025.proved) Eq.refl Eq.refl

  proved : p (s1) • M3 ≈ M3 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00023 where

  step0 : p (s2) • M3 ≈ p (s0 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s1 • s0)) PE00026.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s0)) (p (s0 • s1 • s2 • s1 • s0)) CM00002.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s2 • s1 • s0) ≈ M2 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s0) • m0) (ε) PE00026.proved) Eq.refl Eq.refl

  proved : p (s2) • M3 ≈ M2 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00025 where

  step0 : p (s4) • M3 ≈ p (s0 • s1 • s2 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s1 • s0)) PE00028.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s1 • s0)) CM00004.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s2 • s1 • s0) ≈ M3 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0) • m0) (ε) PE00028.proved) Eq.refl Eq.refl

  proved : p (s4) • M3 ≈ M3 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00026 where

  step0 : p (s5) • M3 ≈ p (s0 • s1 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s1 • s0)) PE00029.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s1 • s0)) CM00005.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s1 • s0) ≈ M3 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0) • m0) (ε) PE00029.proved) Eq.refl Eq.refl

  proved : p (s5) • M3 ≈ M3 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00027 where

  step0 : p (s6) • M3 ≈ p (s0 • s1 • s2 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s1 • s0)) PE00030.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s1 • s0)) CM00006.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s2 • s1 • s0) ≈ M3 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0) • m0) (ε) PE00030.proved) Eq.refl Eq.refl

  proved : p (s6) • M3 ≈ M3 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00028 where

  step0 : p (s0) • M4 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s3 • s2 • s1 • s2 • s3) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) PE00031.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s3 • s2 • s1 • s2 • s3) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s3 • s2 • s1 • s2 • s3) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) CM00008.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s3 • s2 • s1 • s2 • s3) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ M4 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0) (ε) PE00032.proved) Eq.refl Eq.refl

  proved : p (s0) • M4 ≈ M4 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00029 where

  step0 : p (s1) • M4 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) PE00033.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) CM00001.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ M4 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0) (ε) PE00033.proved) Eq.refl Eq.refl

  proved : p (s1) • M4 ≈ M4 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00030 where

  step0 : p (s2) • M4 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) PE00034.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) CM00002.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ M4 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0) (ε) PE00034.proved) Eq.refl Eq.refl

  proved : p (s2) • M4 ≈ M4 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00031 where

  step0 : p (s3) • M4 ≈ p (s0 • s1 • s2 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) PE00035.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) CM00003.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ M3 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s1 • s0) • m0) (ε) PE00035.proved) Eq.refl Eq.refl

  proved : p (s3) • M4 ≈ M3 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00032 where

  step0 : p (s4) • M4 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) PE00036.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) CM00004.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ M5 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00036.proved) Eq.refl Eq.refl

  proved : p (s4) • M4 ≈ M5 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00033 where

  step0 : p (s5) • M4 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) PE00037.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) CM00005.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ M4 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0) (ε) PE00037.proved) Eq.refl Eq.refl

  proved : p (s5) • M4 ≈ M4 • p (s5)
  proved = trans step0 (trans step1 step2)

module MV00034 where

  step0 : p (s6) • M4 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) PE00038.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s6) • m0 • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) CM00006.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s6) • p (s0 • s1 • s2 • s3 • s2 • s1 • s0) ≈ M4 • p (s6)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0) (ε) PE00038.proved) Eq.refl Eq.refl

  proved : p (s6) • M4 ≈ M4 • p (s6)
  proved = trans step0 (trans step1 step2)

module MV00035 where

  step0 : p (s0) • M5 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s4 • s3 • s2 • s1 • s2 • s3 • s4) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00039.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s4 • s3 • s2 • s1 • s2 • s3 • s4) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s4 • s3 • s2 • s1 • s2 • s3 • s4) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00009.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s4 • s3 • s2 • s1 • s2 • s3 • s4) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ M5 • p (s0)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00040.proved) Eq.refl Eq.refl

  proved : p (s0) • M5 ≈ M5 • p (s0)
  proved = trans step0 (trans step1 step2)

module MV00036 where

  step0 : p (s1) • M5 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00041.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s1) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00001.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s1) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ M5 • p (s1)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00041.proved) Eq.refl Eq.refl

  proved : p (s1) • M5 ≈ M5 • p (s1)
  proved = trans step0 (trans step1 step2)

module MV00037 where

  step0 : p (s2) • M5 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00042.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s2) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00002.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s2) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ M5 • p (s2)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00042.proved) Eq.refl Eq.refl

  proved : p (s2) • M5 ≈ M5 • p (s2)
  proved = trans step0 (trans step1 step2)

module MV00038 where

  step0 : p (s3) • M5 ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00043.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • p (s3) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00003.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0 • p (s3) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ M5 • p (s3)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00043.proved) Eq.refl Eq.refl

  proved : p (s3) • M5 ≈ M5 • p (s3)
  proved = trans step0 (trans step1 step2)

module MV00039 where

  step0 : p (s4) • M5 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00044.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • p (s4) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00004.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0 • p (s4) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ M4 • p (s4)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s2 • s1 • s0) • m0) (ε) PE00044.proved) Eq.refl Eq.refl

  proved : p (s4) • M5 ≈ M4 • p (s4)
  proved = trans step0 (trans step1 step2)

module MV00040 where

  step0 : p (s5) • M5 ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (under (ε) (m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) PE00045.proved) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • p (s5) • m0 • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)
  step1 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0)) (p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0)) CM00005.proved) Eq.refl Eq.refl

  step2 : p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0 • p (s5) • p (s0 • s1 • s2 • s3 • s4 • s3 • s2 • s1 • s0) ≈ M6 • p (s5)
  step2 = by-assoc-and (under (p (s0 • s1 • s2 • s3 • s4 • s5 • s4 • s3 • s2 • s1 • s0) • m0) (ε) PE00045.proved) Eq.refl Eq.refl

  proved : p (s5) • M5 ≈ M6 • p (s5)
  proved = trans step0 (trans step1 step2)
