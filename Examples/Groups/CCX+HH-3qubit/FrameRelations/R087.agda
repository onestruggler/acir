{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R087 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X34 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; m0 ; r087 ; sym ; t34 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At34 as At34

step0 : t34 • m0 ≈ X34 • M0
step0 = by-assoc-and (cong (At34.proved) (Am0.proved)) Eq.refl Eq.refl

step1 : m0 • t34 ≈ M0 • X34
step1 = by-assoc-and (cong (Am0.proved) (At34.proved)) Eq.refl Eq.refl

proved : X34 • M0 ≈ M0 • X34
proved = trans (sym (step0)) (trans (axiom r087) (step1))
