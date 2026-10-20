{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00129 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X15 ; X16 ; _•_ ; _≈_ ; by-assoc-and ; p ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00094 as E

proved : p (s5) • X15 ≈ X16 • p (s5)
proved = by-assoc-and E.proved Eq.refl Eq.refl
