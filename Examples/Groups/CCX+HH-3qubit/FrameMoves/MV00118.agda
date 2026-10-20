{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00118 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X14 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; p ; s1 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00083 as E

proved : p (s1) • X14 ≈ X24 • p (s1)
proved = by-assoc-and E.proved Eq.refl Eq.refl
