{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameRelations.R093 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (K0123 ; NK ; X67 ; _•_ ; _≈_ ; axiom ; by-assoc-and ; cong ; r093 ; sym ; t67 ; trans ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FrameAliases.ANK as ANK
import Examples.Groups.CCX+HH-3qubit.FrameAliases.At67 as At67

step0 : t67 • NK ≈ X67 • K0123
step0 = by-assoc-and (cong (At67.proved) (ANK.proved)) Eq.refl Eq.refl

step1 : NK • t67 ≈ K0123 • X67
step1 = by-assoc-and (cong (ANK.proved) (At67.proved)) Eq.refl Eq.refl

proved : X67 • K0123 ≈ K0123 • X67
proved = trans (sym (step0)) (trans (axiom r093) (step1))
