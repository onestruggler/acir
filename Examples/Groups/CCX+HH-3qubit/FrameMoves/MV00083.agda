{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00083 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; X15 ; _•_ ; _≈_ ; by-assoc-and ; p ; s0 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00066 as E

proved : p (s0) • X05 ≈ X15 • p (s0)
proved = by-assoc-and E.proved Eq.refl Eq.refl
