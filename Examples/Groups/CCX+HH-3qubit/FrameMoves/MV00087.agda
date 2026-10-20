{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00087 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; X05 ; _•_ ; _≈_ ; by-assoc-and ; p ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00044 as E

proved : p (s4) • X05 ≈ X04 • p (s4)
proved = by-assoc-and E.proved Eq.refl Eq.refl
