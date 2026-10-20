{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R088 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; X45 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; m0 ; r088 ; sym ; t45 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At45 as At45

step0 : t45 • m0 ≈ X45 • M0
step0 = by-assoc-and (cong (At45.proved) (Am0.proved)) Eq.refl Eq.refl

step1 : m0 • t45 ≈ M0 • X45
step1 = by-assoc-and (cong (Am0.proved) (At45.proved)) Eq.refl Eq.refl

proved : X45 • M0 ≈ M0 • X45
proved = trans (sym (step0)) (trans (axiom r088) (step1))
