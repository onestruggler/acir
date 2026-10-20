{-# OPTIONS --without-K --safe #-}

module Examples.Groups.CCX+HH-3qubit.FrameMoves.MV00154 where

import Examples.Groups.CCX+HH-3qubit.FrameKit as K using (X23 ; X24 ; _•_ ; _≈_ ; by-assoc-and ; p ; s3 ; module Eq)
open K
import Examples.Groups.CCX+HH-3qubit.FramePermutations.PE00119 as E

proved : p (s3) • X24 ≈ X23 • p (s3)
proved = by-assoc-and E.proved Eq.refl Eq.refl
