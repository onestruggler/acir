{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00114 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X13 ; _•_ ; _≈_ ; by-assoc-and ; p ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00079 as E

proved : p (s4) • X13 ≈ X13 • p (s4)
proved = by-assoc-and E.proved Eq.refl Eq.refl
