{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameAliases.B000 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K1345 ; K2345 ; K4567 ; M0 ; M1 ; M3 ; M4 ; NK ; X01 ; X04 ; X12 ; X13 ; X23 ; X34 ; X45 ; X56 ; X67 ; _•_ ; _≈_ ; by-assoc ; by-assoc-and ; cong ; forget-frame ; k0124 ; k1345 ; k2345 ; k4567 ; m0 ; m1 ; m3 ; m4 ; module Eq ; p ; refl ; s0 ; s1 ; s2 ; s3 ; s4 ; s5 ; s6 ; t01 ; t04 ; t12 ; t13 ; t23 ; t34 ; t45 ; t56 ; t67 ; trans)
open K
import Examples.Groups.CCX+HH-3qubit.GatePermutations as GatePermutations
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B000 using (module MV00000 ; module MV00245 ; module MV00632 ; module MV00633 ; module MV00634)
open import Examples.Groups.CCX+HH-3qubit.FrameMoves.B001 using (module MV00630 ; module MV00631)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B000 using (module PE00004 ; module PE00213 ; module PE00683 ; module PE00952 ; module PE00953 ; module PE00954)
open import Examples.Groups.CCX+HH-3qubit.FramePermutations.B001 using (module PE00000 ; module PE00002 ; module PE00003 ; module PE00005 ; module PE00006 ; module PE00007 ; module PE00008 ; module PE00948 ; module PE00949 ; module PE00950 ; module PE00951 ; module PE00955 ; module PE00956)

module ANK where

  proved : NK ≈ K0123
  proved = by-assoc Eq.refl

module Ak0124 where

  step0 : k0124 ≈ p (s3) • NK • p (s3)
  step0 = by-assoc-and (cong (GatePermutations.gatet34) (cong (refl {w = NK}) (GatePermutations.gatet34))) Eq.refl Eq.refl

  step1 : p (s3) • NK • p (s3) ≈ p (s3) • NK • p (s3)
  step1 = cong refl (cong refl PE00004.proved)

  step2 : p (s3) • NK • p (s3) ≈ K0124
  step2 = forget-frame (by-assoc-and MV00245.proved Eq.refl Eq.refl) (by-assoc-and PE00213.proved Eq.refl Eq.refl)

  proved : k0124 ≈ K0124
  proved = trans step0 (trans step1 step2)

module Ak1345 where

  step0 : k1345 ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)
  step0 = by-assoc-and (cong (cong (GatePermutations.gatet01) (cong (cong (GatePermutations.gatet12) (cong (GatePermutations.gatet23) (GatePermutations.gatet12))) (cong (cong (GatePermutations.gatet23) (cong (GatePermutations.gatet34) (GatePermutations.gatet23))) (cong (GatePermutations.gatet34) (cong (GatePermutations.gatet45) (GatePermutations.gatet34)))))) (cong (refl {w = NK}) (cong (cong (GatePermutations.gatet34) (cong (GatePermutations.gatet45) (GatePermutations.gatet34))) (cong (cong (GatePermutations.gatet23) (cong (GatePermutations.gatet34) (GatePermutations.gatet23))) (cong (cong (GatePermutations.gatet12) (cong (GatePermutations.gatet23) (GatePermutations.gatet12))) (GatePermutations.gatet01)))))) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0)
  step1 = cong refl (cong refl PE00683.proved)

  step2 : p (s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0) ≈ K1345
  step2 = forget-frame (by-assoc-and MV00633.proved Eq.refl Eq.refl) (by-assoc-and PE00952.proved Eq.refl Eq.refl)

  proved : k1345 ≈ K1345
  proved = trans step0 (trans step1 step2)

module Ak2345 where

  step0 : k2345 ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step0 = by-assoc-and (cong (cong (cong (GatePermutations.gatet01) (cong (GatePermutations.gatet12) (GatePermutations.gatet01))) (cong (cong (GatePermutations.gatet12) (cong (GatePermutations.gatet23) (GatePermutations.gatet12))) (cong (cong (GatePermutations.gatet23) (cong (GatePermutations.gatet34) (GatePermutations.gatet23))) (cong (GatePermutations.gatet34) (cong (GatePermutations.gatet45) (GatePermutations.gatet34)))))) (cong (refl {w = NK}) (cong (cong (GatePermutations.gatet34) (cong (GatePermutations.gatet45) (GatePermutations.gatet34))) (cong (cong (GatePermutations.gatet23) (cong (GatePermutations.gatet34) (GatePermutations.gatet23))) (cong (cong (GatePermutations.gatet12) (cong (GatePermutations.gatet23) (GatePermutations.gatet12))) (cong (GatePermutations.gatet01) (cong (GatePermutations.gatet12) (GatePermutations.gatet01)))))))) Eq.refl Eq.refl

  step1 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0)
  step1 = cong refl (cong refl PE00953.proved)

  step2 : p (s0 • s1 • s0 • s1 • s2 • s1 • s2 • s3 • s2 • s3 • s4 • s3) • NK • p (s3 • s4 • s3 • s2 • s3 • s2 • s1 • s2 • s1 • s0 • s1 • s0) ≈ K2345
  step2 = forget-frame (by-assoc-and MV00634.proved Eq.refl Eq.refl) (by-assoc-and PE00954.proved Eq.refl Eq.refl)

  proved : k2345 ≈ K2345
  proved = trans step0 (trans step1 step2)

module Ak4567 where

  step0 : k4567 ≈ p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • NK • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  step0 = by-assoc-and (cong (GatePermutations.gateX0) (cong (refl {w = NK}) (GatePermutations.gateX0))) Eq.refl Eq.refl

  step1 : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • NK • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) ≈ p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s2 • s3 • s4 • s5 • s1 • s2 • s3 • s4 • s0 • s1 • s2 • s3)
  step1 = cong refl (cong refl PE00950.proved)

  step2 : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • NK • p (s3 • s4 • s5 • s6 • s2 • s3 • s4 • s5 • s1 • s2 • s3 • s4 • s0 • s1 • s2 • s3) ≈ K4567
  step2 = forget-frame (by-assoc-and MV00632.proved Eq.refl Eq.refl) (by-assoc-and PE00951.proved Eq.refl Eq.refl)

  proved : k4567 ≈ K4567
  proved = trans step0 (trans step1 step2)

module Am0 where

  proved : m0 ≈ M0
  proved = by-assoc Eq.refl

module Am1 where

  step0 : m1 ≈ p (s0) • m0 • p (s0)
  step0 = by-assoc-and (cong (GatePermutations.gatet01) (cong (refl {w = m0}) (GatePermutations.gatet01))) Eq.refl Eq.refl

  step1 : p (s0) • m0 • p (s0) ≈ p (s0) • m0 • p (s0)
  step1 = cong refl (cong refl PE00000.proved)

  step2 : p (s0) • m0 • p (s0) ≈ M1
  step2 = forget-frame (by-assoc-and MV00000.proved Eq.refl Eq.refl) (by-assoc-and PE00008.proved Eq.refl Eq.refl)

  proved : m1 ≈ M1
  proved = trans step0 (trans step1 step2)

module Am3 where

  step0 : m3 ≈ p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2)
  step0 = by-assoc-and (cong (cong (GatePermutations.gatet23) (cong (GatePermutations.gatet12) (GatePermutations.gatet01))) (cong (refl {w = m0}) (cong (GatePermutations.gatet01) (cong (GatePermutations.gatet12) (GatePermutations.gatet23))))) Eq.refl Eq.refl

  step1 : p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2) ≈ p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2)
  step1 = cong refl (cong refl PE00948.proved)

  step2 : p (s2 • s1 • s0) • m0 • p (s0 • s1 • s2) ≈ M3
  step2 = forget-frame (by-assoc-and MV00630.proved Eq.refl Eq.refl) (by-assoc-and PE00949.proved Eq.refl Eq.refl)

  proved : m3 ≈ M3
  proved = trans step0 (trans step1 step2)

module Am4 where

  step0 : m4 ≈ p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • m0 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3)
  step0 = by-assoc-and (cong (GatePermutations.gateX0) (cong (refl {w = m0}) (GatePermutations.gateX0))) Eq.refl Eq.refl

  step1 : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • m0 • p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) ≈ p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • m0 • p (s3 • s4 • s5 • s6 • s2 • s3 • s4 • s5 • s1 • s2 • s3 • s4 • s0 • s1 • s2 • s3)
  step1 = cong refl (cong refl PE00950.proved)

  step2 : p (s3 • s2 • s1 • s0 • s4 • s3 • s2 • s1 • s5 • s4 • s3 • s2 • s6 • s5 • s4 • s3) • m0 • p (s3 • s4 • s5 • s6 • s2 • s3 • s4 • s5 • s1 • s2 • s3 • s4 • s0 • s1 • s2 • s3) ≈ M4
  step2 = forget-frame (by-assoc-and MV00631.proved Eq.refl Eq.refl) (by-assoc-and PE00951.proved Eq.refl Eq.refl)

  proved : m4 ≈ M4
  proved = trans step0 (trans step1 step2)

module At01 where

  step0 : t01 ≈ p (s0)
  step0 = by-assoc-and (GatePermutations.gatet01) Eq.refl Eq.refl

  proved : t01 ≈ X01
  proved = trans step0 (by-assoc-and PE00000.proved Eq.refl Eq.refl)

module At04 where

  step0 : t04 ≈ p (s0 • s1 • s2 • s3 • s2 • s1 • s0)
  step0 = by-assoc-and (cong (GatePermutations.gatet01) (cong (GatePermutations.gatet12) (cong (GatePermutations.gatet23) (cong (GatePermutations.gatet34) (cong (GatePermutations.gatet23) (cong (GatePermutations.gatet12) (GatePermutations.gatet01))))))) Eq.refl Eq.refl

  proved : t04 ≈ X04
  proved = trans step0 (by-assoc-and PE00955.proved Eq.refl Eq.refl)

module At12 where

  step0 : t12 ≈ p (s1)
  step0 = by-assoc-and (GatePermutations.gatet12) Eq.refl Eq.refl

  proved : t12 ≈ X12
  proved = trans step0 (by-assoc-and PE00002.proved Eq.refl Eq.refl)

module At13 where

  step0 : t13 ≈ p (s1 • s2 • s1)
  step0 = by-assoc-and (cong (GatePermutations.gatet12) (cong (GatePermutations.gatet23) (GatePermutations.gatet12))) Eq.refl Eq.refl

  proved : t13 ≈ X13
  proved = trans step0 (by-assoc-and PE00956.proved Eq.refl Eq.refl)

module At23 where

  step0 : t23 ≈ p (s2)
  step0 = by-assoc-and (GatePermutations.gatet23) Eq.refl Eq.refl

  proved : t23 ≈ X23
  proved = trans step0 (by-assoc-and PE00003.proved Eq.refl Eq.refl)

module At34 where

  step0 : t34 ≈ p (s3)
  step0 = by-assoc-and (GatePermutations.gatet34) Eq.refl Eq.refl

  proved : t34 ≈ X34
  proved = trans step0 (by-assoc-and PE00004.proved Eq.refl Eq.refl)

module At45 where

  step0 : t45 ≈ p (s4)
  step0 = by-assoc-and (GatePermutations.gatet45) Eq.refl Eq.refl

  proved : t45 ≈ X45
  proved = trans step0 (by-assoc-and PE00005.proved Eq.refl Eq.refl)

module At56 where

  step0 : t56 ≈ p (s5)
  step0 = by-assoc-and (GatePermutations.gatet56) Eq.refl Eq.refl

  proved : t56 ≈ X56
  proved = trans step0 (by-assoc-and PE00006.proved Eq.refl Eq.refl)

module At67 where

  step0 : t67 ≈ p (s6)
  step0 = by-assoc-and (GatePermutations.gatet67) Eq.refl Eq.refl

  proved : t67 ≈ X67
  proved = trans step0 (by-assoc-and PE00007.proved Eq.refl Eq.refl)
