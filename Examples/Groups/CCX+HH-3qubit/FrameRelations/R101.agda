{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R101 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K4567 ; M0 ; M4 ; X04 ; X34 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; m0 ; m4 ; r101 ; rho ; sym ; t04 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Ak4567 as Ak4567
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am4 as Am4
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At04 as At04
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At34 as At34

step0 : m0 • m4 • t04 • rho ≈ M0 • M4 • X04 • K4567 • K0123 • X34 • K0123 • K4567
step0 = by-assoc-and (cong (Am0.proved) (cong (Am4.proved) (cong (At04.proved) (cong (Ak4567.proved) (cong (ANK.proved) (cong (At34.proved) (cong (ANK.proved) (Ak4567.proved)))))))) Eq.refl Eq.refl

step1 : rho • t04 • m4 • m0 ≈ K4567 • K0123 • X34 • K0123 • K4567 • X04 • M4 • M0
step1 = by-assoc-and (cong (cong (Ak4567.proved) (cong (ANK.proved) (cong (At34.proved) (cong (ANK.proved) (Ak4567.proved))))) (cong (At04.proved) (cong (Am4.proved) (Am0.proved)))) Eq.refl Eq.refl

proved : M0 • M4 • X04 • K4567 • K0123 • X34 • K0123 • K4567 ≈ K4567 • K0123 • X34 • K0123 • K4567 • X04 • M4 • M0
proved = trans (sym (step0)) (trans (axiom r101) (step1))
