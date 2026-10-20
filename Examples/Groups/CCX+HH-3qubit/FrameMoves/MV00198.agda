{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00198 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X36 ; X37 ; _•_ ; _≈_ ; by-assoc-and ; p ; s6 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00163 as E

proved : p (s6) • X36 ≈ X37 • p (s6)
proved = by-assoc-and E.proved Eq.refl Eq.refl
