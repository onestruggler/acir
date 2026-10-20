{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00078 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; _•_ ; _≈_ ; by-assoc-and ; p ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00034 as E

proved : p (s2) • X04 ≈ X04 • p (s2)
proved = by-assoc-and E.proved Eq.refl Eq.refl
