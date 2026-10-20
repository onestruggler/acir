{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00236 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X47 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; p ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00201 as E

proved : p (s4) • X57 ≈ X47 • p (s4)
proved = by-assoc-and E.proved Eq.refl Eq.refl
