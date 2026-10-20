{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00070 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X03 ; _•_ ; _≈_ ; by-assoc-and ; p ; s1 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00025 as E

proved : p (s1) • X03 ≈ X03 • p (s1)
proved = by-assoc-and E.proved Eq.refl Eq.refl
