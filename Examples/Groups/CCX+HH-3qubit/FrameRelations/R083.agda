{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R083 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (M0 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; m0 ; r083 ; refl ; sym ; trans ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.Am0 as Am0

step0 : m0 • m0 ≈ M0 • M0
step0 = by-assoc-and (cong (Am0.proved) (Am0.proved)) Eq.refl Eq.refl

step1 : ε ≈ ε
step1 = by-assoc-and (refl {w = ε}) Eq.refl Eq.refl

proved : M0 • M0 ≈ ε
proved = trans (sym (step0)) (trans (axiom r083) (step1))
