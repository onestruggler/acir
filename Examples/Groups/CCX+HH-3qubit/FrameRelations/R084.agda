{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R084 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; NK ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; r084 ; refl ; sym ; trans ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK

step0 : NK • NK ≈ K0123 • K0123
step0 = by-assoc-and (cong (ANK.proved) (ANK.proved)) Eq.refl Eq.refl

step1 : ε ≈ ε
step1 = by-assoc-and (refl {w = ε}) Eq.refl Eq.refl

proved : K0123 • K0123 ≈ ε
proved = trans (sym (step0)) (trans (axiom r084) (step1))
