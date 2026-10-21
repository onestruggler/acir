{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.B000 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K1345 ; K2345 ; K4567 ; M0 ; M1 ; M3 ; M4 ; NK ; X01 ; X04 ; X12 ; X13 ; X23 ; X34 ; X45 ; X56 ; X67 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; k0124 ; k1345 ; k2345 ; k4567 ; m0 ; m1 ; m3 ; m4 ; module Eq ; r083 ; r084 ; r085 ; r086 ; r087 ; r088 ; r089 ; r090 ; r091 ; r092 ; r093 ; r094 ; r095 ; r096 ; r097 ; r098 ; r099 ; r100 ; r101 ; refl ; rho ; sym ; t01 ; t04 ; t12 ; t13 ; t23 ; t34 ; t45 ; t56 ; t67 ; trans ; ε)
open K
open import Examples.Groups.CCX+HH-3qubit.FrameAliases.B000 using (module ANK ; module Ak0124 ; module Ak1345 ; module Ak2345 ; module Ak4567 ; module Am0 ; module Am1 ; module Am3 ; module Am4 ; module At01 ; module At04 ; module At12 ; module At13 ; module At23 ; module At34 ; module At45 ; module At56 ; module At67)

module R083 where

  step0 : m0 • m0 ≈ M0 • M0
  step0 = by-assoc-and (cong (Am0.proved) (Am0.proved)) Eq.refl Eq.refl

  step1 : ε ≈ ε
  step1 = by-assoc-and (refl {w = ε}) Eq.refl Eq.refl

  proved : M0 • M0 ≈ ε
  proved = trans (sym (step0)) (trans (axiom r083) (step1))

module R084 where

  step0 : NK • NK ≈ K0123 • K0123
  step0 = by-assoc-and (cong (ANK.proved) (ANK.proved)) Eq.refl Eq.refl

  step1 : ε ≈ ε
  step1 = by-assoc-and (refl {w = ε}) Eq.refl Eq.refl

  proved : K0123 • K0123 ≈ ε
  proved = trans (sym (step0)) (trans (axiom r084) (step1))

module R085 where

  step0 : t12 • m0 ≈ X12 • M0
  step0 = by-assoc-and (cong (At12.proved) (Am0.proved)) Eq.refl Eq.refl

  step1 : m0 • t12 ≈ M0 • X12
  step1 = by-assoc-and (cong (Am0.proved) (At12.proved)) Eq.refl Eq.refl

  proved : X12 • M0 ≈ M0 • X12
  proved = trans (sym (step0)) (trans (axiom r085) (step1))

module R086 where

  step0 : t23 • m0 ≈ X23 • M0
  step0 = by-assoc-and (cong (At23.proved) (Am0.proved)) Eq.refl Eq.refl

  step1 : m0 • t23 ≈ M0 • X23
  step1 = by-assoc-and (cong (Am0.proved) (At23.proved)) Eq.refl Eq.refl

  proved : X23 • M0 ≈ M0 • X23
  proved = trans (sym (step0)) (trans (axiom r086) (step1))

module R087 where

  step0 : t34 • m0 ≈ X34 • M0
  step0 = by-assoc-and (cong (At34.proved) (Am0.proved)) Eq.refl Eq.refl

  step1 : m0 • t34 ≈ M0 • X34
  step1 = by-assoc-and (cong (Am0.proved) (At34.proved)) Eq.refl Eq.refl

  proved : X34 • M0 ≈ M0 • X34
  proved = trans (sym (step0)) (trans (axiom r087) (step1))

module R088 where

  step0 : t45 • m0 ≈ X45 • M0
  step0 = by-assoc-and (cong (At45.proved) (Am0.proved)) Eq.refl Eq.refl

  step1 : m0 • t45 ≈ M0 • X45
  step1 = by-assoc-and (cong (Am0.proved) (At45.proved)) Eq.refl Eq.refl

  proved : X45 • M0 ≈ M0 • X45
  proved = trans (sym (step0)) (trans (axiom r088) (step1))

module R089 where

  step0 : t56 • m0 ≈ X56 • M0
  step0 = by-assoc-and (cong (At56.proved) (Am0.proved)) Eq.refl Eq.refl

  step1 : m0 • t56 ≈ M0 • X56
  step1 = by-assoc-and (cong (Am0.proved) (At56.proved)) Eq.refl Eq.refl

  proved : X56 • M0 ≈ M0 • X56
  proved = trans (sym (step0)) (trans (axiom r089) (step1))

module R090 where

  step0 : t67 • m0 ≈ X67 • M0
  step0 = by-assoc-and (cong (At67.proved) (Am0.proved)) Eq.refl Eq.refl

  step1 : m0 • t67 ≈ M0 • X67
  step1 = by-assoc-and (cong (Am0.proved) (At67.proved)) Eq.refl Eq.refl

  proved : X67 • M0 ≈ M0 • X67
  proved = trans (sym (step0)) (trans (axiom r090) (step1))

module R091 where

  step0 : t45 • NK ≈ X45 • K0123
  step0 = by-assoc-and (cong (At45.proved) (ANK.proved)) Eq.refl Eq.refl

  step1 : NK • t45 ≈ K0123 • X45
  step1 = by-assoc-and (cong (ANK.proved) (At45.proved)) Eq.refl Eq.refl

  proved : X45 • K0123 ≈ K0123 • X45
  proved = trans (sym (step0)) (trans (axiom r091) (step1))

module R092 where

  step0 : t56 • NK ≈ X56 • K0123
  step0 = by-assoc-and (cong (At56.proved) (ANK.proved)) Eq.refl Eq.refl

  step1 : NK • t56 ≈ K0123 • X56
  step1 = by-assoc-and (cong (ANK.proved) (At56.proved)) Eq.refl Eq.refl

  proved : X56 • K0123 ≈ K0123 • X56
  proved = trans (sym (step0)) (trans (axiom r092) (step1))

module R093 where

  step0 : t67 • NK ≈ X67 • K0123
  step0 = by-assoc-and (cong (At67.proved) (ANK.proved)) Eq.refl Eq.refl

  step1 : NK • t67 ≈ K0123 • X67
  step1 = by-assoc-and (cong (ANK.proved) (At67.proved)) Eq.refl Eq.refl

  proved : X67 • K0123 ≈ K0123 • X67
  proved = trans (sym (step0)) (trans (axiom r093) (step1))

module R094 where

  step0 : m4 • NK ≈ M4 • K0123
  step0 = by-assoc-and (cong (Am4.proved) (ANK.proved)) Eq.refl Eq.refl

  step1 : NK • m4 ≈ K0123 • M4
  step1 = by-assoc-and (cong (ANK.proved) (Am4.proved)) Eq.refl Eq.refl

  proved : M4 • K0123 ≈ K0123 • M4
  proved = trans (sym (step0)) (trans (axiom r094) (step1))

module R095 where

  step0 : m0 • m4 ≈ M0 • M4
  step0 = by-assoc-and (cong (Am0.proved) (Am4.proved)) Eq.refl Eq.refl

  step1 : m4 • m0 ≈ M4 • M0
  step1 = by-assoc-and (cong (Am4.proved) (Am0.proved)) Eq.refl Eq.refl

  proved : M0 • M4 ≈ M4 • M0
  proved = trans (sym (step0)) (trans (axiom r095) (step1))

module R096 where

  step0 : NK • k4567 ≈ K0123 • K4567
  step0 = by-assoc-and (cong (ANK.proved) (Ak4567.proved)) Eq.refl Eq.refl

  step1 : k4567 • NK ≈ K4567 • K0123
  step1 = by-assoc-and (cong (Ak4567.proved) (ANK.proved)) Eq.refl Eq.refl

  proved : K0123 • K4567 ≈ K4567 • K0123
  proved = trans (sym (step0)) (trans (axiom r096) (step1))

module R097 where

  step0 : t01 • NK ≈ X01 • K0123
  step0 = by-assoc-and (cong (At01.proved) (ANK.proved)) Eq.refl Eq.refl

  step1 : NK • t13 • m1 • m3 ≈ K0123 • X13 • M1 • M3
  step1 = by-assoc-and (cong (ANK.proved) (cong (At13.proved) (cong (Am1.proved) (Am3.proved)))) Eq.refl Eq.refl

  proved : X01 • K0123 ≈ K0123 • X13 • M1 • M3
  proved = trans (sym (step0)) (trans (axiom r097) (step1))

module R098 where

  step0 : t12 • NK ≈ X12 • K0123
  step0 = by-assoc-and (cong (At12.proved) (ANK.proved)) Eq.refl Eq.refl

  step1 : m0 • NK • m0 • NK • m0 ≈ M0 • K0123 • M0 • K0123 • M0
  step1 = by-assoc-and (cong (Am0.proved) (cong (ANK.proved) (cong (Am0.proved) (cong (ANK.proved) (Am0.proved))))) Eq.refl Eq.refl

  proved : X12 • K0123 ≈ M0 • K0123 • M0 • K0123 • M0
  proved = trans (sym (step0)) (trans (axiom r098) (step1))

module R099 where

  step0 : t23 • NK ≈ X23 • K0123
  step0 = by-assoc-and (cong (At23.proved) (ANK.proved)) Eq.refl Eq.refl

  step1 : NK • t13 ≈ K0123 • X13
  step1 = by-assoc-and (cong (ANK.proved) (At13.proved)) Eq.refl Eq.refl

  proved : X23 • K0123 ≈ K0123 • X13
  proved = trans (sym (step0)) (trans (axiom r099) (step1))

module R100 where

  step0 : NK • k1345 ≈ K0123 • K1345
  step0 = by-assoc-and (cong (ANK.proved) (Ak1345.proved)) Eq.refl Eq.refl

  step1 : k2345 • k0124 ≈ K2345 • K0124
  step1 = by-assoc-and (cong (Ak2345.proved) (Ak0124.proved)) Eq.refl Eq.refl

  proved : K0123 • K1345 ≈ K2345 • K0124
  proved = trans (sym (step0)) (trans (axiom r100) (step1))

module R101 where

  step0 : m0 • m4 • t04 • rho ≈ M0 • M4 • X04 • K4567 • K0123 • X34 • K0123 • K4567
  step0 = by-assoc-and (cong (Am0.proved) (cong (Am4.proved) (cong (At04.proved) (cong (Ak4567.proved) (cong (ANK.proved) (cong (At34.proved) (cong (ANK.proved) (Ak4567.proved)))))))) Eq.refl Eq.refl

  step1 : rho • t04 • m4 • m0 ≈ K4567 • K0123 • X34 • K0123 • K4567 • X04 • M4 • M0
  step1 = by-assoc-and (cong (cong (Ak4567.proved) (cong (ANK.proved) (cong (At34.proved) (cong (ANK.proved) (Ak4567.proved))))) (cong (At04.proved) (cong (Am4.proved) (Am0.proved)))) Eq.refl Eq.refl

  proved : M0 • M4 • X04 • K4567 • K0123 • X34 • K0123 • K4567 ≈ K4567 • K0123 • X34 • K0123 • K4567 • X04 • M4 • M0
  proved = trans (sym (step0)) (trans (axiom r101) (step1))
