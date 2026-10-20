{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R091 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; NK ; X45 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; r091 ; sym ; t45 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At45 as At45

step0 : t45 • NK ≈ X45 • K0123
step0 = by-assoc-and (cong (At45.proved) (ANK.proved)) Eq.refl Eq.refl

step1 : NK • t45 ≈ K0123 • X45
step1 = by-assoc-and (cong (ANK.proved) (At45.proved)) Eq.refl Eq.refl

proved : X45 • K0123 ≈ K0123 • X45
proved = trans (sym (step0)) (trans (axiom r091) (step1))
