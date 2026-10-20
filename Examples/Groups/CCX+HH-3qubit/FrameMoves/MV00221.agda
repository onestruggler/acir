{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00221 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X47 ; _•_ ; _≈_ ; by-assoc-and ; p ; s2 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00186 as E

proved : p (s2) • X47 ≈ X47 • p (s2)
proved = by-assoc-and E.proved Eq.refl Eq.refl
