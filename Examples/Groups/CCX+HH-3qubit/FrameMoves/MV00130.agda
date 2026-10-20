{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00130 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; _•_ ; _≈_ ; by-assoc-and ; p ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00095 as E

proved : p (s6) • X15 ≈ X15 • p (s6)
proved = by-assoc-and E.proved Eq.refl Eq.refl
