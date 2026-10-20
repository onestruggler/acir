{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R095 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; M4 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; m0 ; m4 ; r095 ; sym ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am4 as Am4

step0 : m0 • m4 ≈ M0 • M4
step0 = by-assoc-and (cong (Am0.proved) (Am4.proved)) Eq.refl Eq.refl

step1 : m4 • m0 ≈ M4 • M0
step1 = by-assoc-and (cong (Am4.proved) (Am0.proved)) Eq.refl Eq.refl

proved : M0 • M4 ≈ M4 • M0
proved = trans (sym (step0)) (trans (axiom r095) (step1))
