{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00171 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X26 ; X27 ; _•_ ; _≈_ ; by-assoc-and ; p ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00136 as E

proved : p (s6) • X26 ≈ X27 • p (s6)
proved = by-assoc-and E.proved Eq.refl Eq.refl
