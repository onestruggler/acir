{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00174 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X27 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; p ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00139 as E

proved : p (s2) • X27 ≈ X37 • p (s2)
proved = by-assoc-and E.proved Eq.refl Eq.refl
