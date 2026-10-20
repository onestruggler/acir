{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00180 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X34 ; _•_ ; _≈_ ; by-assoc-and ; p ; s1 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00145 as E

proved : p (s1) • X34 ≈ X34 • p (s1)
proved = by-assoc-and E.proved Eq.refl Eq.refl
