{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00216 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X46 ; X56 ; _•_ ; _≈_ ; by-assoc-and ; p ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00181 as E

proved : p (s4) • X46 ≈ X56 • p (s4)
proved = by-assoc-and E.proved Eq.refl Eq.refl
