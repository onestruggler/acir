{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00137 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X16 ; X17 ; _•_ ; _≈_ ; by-assoc-and ; p ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00102 as E

proved : p (s6) • X16 ≈ X17 • p (s6)
proved = by-assoc-and E.proved Eq.refl Eq.refl
