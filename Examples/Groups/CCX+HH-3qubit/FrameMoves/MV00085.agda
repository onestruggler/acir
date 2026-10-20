{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00085 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X05 ; _•_ ; _≈_ ; by-assoc-and ; p ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00042 as E

proved : p (s2) • X05 ≈ X05 • p (s2)
proved = by-assoc-and E.proved Eq.refl Eq.refl
