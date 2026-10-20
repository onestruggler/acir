{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00059 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; _•_ ; _≈_ ; by-assoc-and ; p ; s4 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00012 as E

proved : p (s4) • X01 ≈ X01 • p (s4)
proved = by-assoc-and E.proved Eq.refl Eq.refl
