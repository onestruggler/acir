{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R086 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X23 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; m0 ; r086 ; sym ; t23 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At23 as At23

step0 : t23 • m0 ≈ X23 • M0
step0 = by-assoc-and (cong (At23.proved) (Am0.proved)) Eq.refl Eq.refl

step1 : m0 • t23 ≈ M0 • X23
step1 = by-assoc-and (cong (Am0.proved) (At23.proved)) Eq.refl Eq.refl

proved : X23 • M0 ≈ M0 • X23
proved = trans (sym (step0)) (trans (axiom r086) (step1))
