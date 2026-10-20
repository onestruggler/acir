{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV01624 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X45 ; _•_ ; _≈_ ; by-assoc-and ; p ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00005 as E

proved : p (ε) • X45 ≈ X45 • p (ε)
proved = by-assoc-and E.proved Eq.refl Eq.refl
