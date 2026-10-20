{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00179 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X34 ; _•_ ; _≈_ ; by-assoc-and ; p ; s0 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00144 as E

proved : p (s0) • X34 ≈ X34 • p (s0)
proved = by-assoc-and E.proved Eq.refl Eq.refl
