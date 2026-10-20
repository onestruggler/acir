{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00238 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X56 ; X57 ; _•_ ; _≈_ ; by-assoc-and ; p ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00203 as E

proved : p (s6) • X57 ≈ X56 • p (s6)
proved = by-assoc-and E.proved Eq.refl Eq.refl
