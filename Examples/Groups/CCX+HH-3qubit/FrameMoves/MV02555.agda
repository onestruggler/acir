{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02555 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X01 ; _•_ ; _≈_ ; by-assoc-and ; p ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00000 as E

proved : p (ε) • X01 ≈ X01 • p (ε)
proved = by-assoc-and E.proved Eq.refl Eq.refl
