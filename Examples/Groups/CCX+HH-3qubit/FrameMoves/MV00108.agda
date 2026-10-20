{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00108 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X12 ; _•_ ; _≈_ ; by-assoc-and ; p ; s5 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00073 as E

proved : p (s5) • X12 ≈ X12 • p (s5)
proved = by-assoc-and E.proved Eq.refl Eq.refl
