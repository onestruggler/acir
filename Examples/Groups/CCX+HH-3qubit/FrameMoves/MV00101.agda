{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00101 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X07 ; _•_ ; _≈_ ; by-assoc-and ; p ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00060 as E

proved : p (s4) • X07 ≈ X07 • p (s4)
proved = by-assoc-and E.proved Eq.refl Eq.refl
