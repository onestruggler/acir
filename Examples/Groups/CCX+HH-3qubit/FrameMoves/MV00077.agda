{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00077 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X04 ; _•_ ; _≈_ ; by-assoc-and ; p ; s1 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00033 as E

proved : p (s1) • X04 ≈ X04 • p (s1)
proved = by-assoc-and E.proved Eq.refl Eq.refl
