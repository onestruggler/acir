{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00181 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; X34 ; _•_ ; _≈_ ; by-assoc-and ; p ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00146 as E

proved : p (s2) • X34 ≈ X24 • p (s2)
proved = by-assoc-and E.proved Eq.refl Eq.refl
