{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00166 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; X26 ; _•_ ; _≈_ ; by-assoc-and ; p ; s1 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00131 as E

proved : p (s1) • X26 ≈ X16 • p (s1)
proved = by-assoc-and E.proved Eq.refl Eq.refl
