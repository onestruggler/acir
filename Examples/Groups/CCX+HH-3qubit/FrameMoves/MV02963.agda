{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV02963 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X23 ; _•_ ; _≈_ ; by-assoc-and ; p ; ε ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00003 as E

proved : p (ε) • X23 ≈ X23 • p (ε)
proved = by-assoc-and E.proved Eq.refl Eq.refl
