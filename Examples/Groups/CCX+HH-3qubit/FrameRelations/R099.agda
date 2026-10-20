{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R099 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; NK ; X13 ; X23 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; r099 ; sym ; t13 ; t23 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At13 as At13
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At23 as At23

step0 : t23 • NK ≈ X23 • K0123
step0 = by-assoc-and (cong (At23.proved) (ANK.proved)) Eq.refl Eq.refl

step1 : NK • t13 ≈ K0123 • X13
step1 = by-assoc-and (cong (ANK.proved) (At13.proved)) Eq.refl Eq.refl

proved : X23 • K0123 ≈ K0123 • X13
proved = trans (sym (step0)) (trans (axiom r099) (step1))
