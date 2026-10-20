{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00199 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X37 ; _•_ ; _≈_ ; by-assoc-and ; p ; s0 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00164 as E

proved : p (s0) • X37 ≈ X37 • p (s0)
proved = by-assoc-and E.proved Eq.refl Eq.refl
