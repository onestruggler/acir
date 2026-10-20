{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00157 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X24 ; _•_ ; _≈_ ; by-assoc-and ; p ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00122 as E

proved : p (s6) • X24 ≈ X24 • p (s6)
proved = by-assoc-and E.proved Eq.refl Eq.refl
