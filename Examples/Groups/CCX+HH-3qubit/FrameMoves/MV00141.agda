{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00141 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X17 ; _•_ ; _≈_ ; by-assoc-and ; p ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00106 as E

proved : p (s3) • X17 ≈ X17 • p (s3)
proved = by-assoc-and E.proved Eq.refl Eq.refl
