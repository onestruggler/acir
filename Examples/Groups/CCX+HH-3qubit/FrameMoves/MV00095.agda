{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00095 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X06 ; _•_ ; _≈_ ; by-assoc-and ; p ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00053 as E

proved : p (s5) • X06 ≈ X05 • p (s5)
proved = by-assoc-and E.proved Eq.refl Eq.refl
