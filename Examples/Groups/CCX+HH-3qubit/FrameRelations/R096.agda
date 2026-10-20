{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R096 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K4567 ; NK ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; k4567 ; r096 ; sym ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Ak4567 as Ak4567

step0 : NK • k4567 ≈ K0123 • K4567
step0 = by-assoc-and (cong (ANK.proved) (Ak4567.proved)) Eq.refl Eq.refl

step1 : k4567 • NK ≈ K4567 • K0123
step1 = by-assoc-and (cong (Ak4567.proved) (ANK.proved)) Eq.refl Eq.refl

proved : K0123 • K4567 ≈ K4567 • K0123
proved = trans (sym (step0)) (trans (axiom r096) (step1))
