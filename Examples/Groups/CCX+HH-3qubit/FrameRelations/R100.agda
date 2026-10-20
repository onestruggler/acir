{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R100 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; K0124 ; K1345 ; K2345 ; NK ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; k0124 ; k1345 ; k2345 ; r100 ; sym ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Ak0124 as Ak0124
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Ak1345 as Ak1345
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Ak2345 as Ak2345

step0 : NK • k1345 ≈ K0123 • K1345
step0 = by-assoc-and (cong (ANK.proved) (Ak1345.proved)) Eq.refl Eq.refl

step1 : k2345 • k0124 ≈ K2345 • K0124
step1 = by-assoc-and (cong (Ak2345.proved) (Ak0124.proved)) Eq.refl Eq.refl

proved : K0123 • K1345 ≈ K2345 • K0124
proved = trans (sym (step0)) (trans (axiom r100) (step1))
