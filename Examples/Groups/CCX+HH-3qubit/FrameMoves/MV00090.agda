{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00090 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X06 ; X16 ; _•_ ; _≈_ ; by-assoc-and ; p ; s0 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00067 as E

proved : p (s0) • X06 ≈ X16 • p (s0)
proved = by-assoc-and E.proved Eq.refl Eq.refl
