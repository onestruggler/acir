{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00228 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X56 ; _•_ ; _≈_ ; by-assoc-and ; p ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00193 as E

proved : p (s2) • X56 ≈ X56 • p (s2)
proved = by-assoc-and E.proved Eq.refl Eq.refl
