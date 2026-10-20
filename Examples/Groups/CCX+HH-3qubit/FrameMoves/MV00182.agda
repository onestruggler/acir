{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00182 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X34 ; X35 ; _•_ ; _≈_ ; by-assoc-and ; p ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00147 as E

proved : p (s4) • X34 ≈ X35 • p (s4)
proved = by-assoc-and E.proved Eq.refl Eq.refl
